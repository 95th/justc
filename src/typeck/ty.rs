use crate::{
    err::{Handler, Result},
    lex::Span,
    symbol::Symbol,
};
use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};
use std::{
    collections::{BTreeMap, HashMap},
    fmt,
    rc::Rc,
};

#[derive(Default, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TypeVar(u32);

impl fmt::Debug for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

impl From<u32> for TypeVar {
    fn from(n: u32) -> Self {
        Self(n)
    }
}

impl UnifyKey for TypeVar {
    type Value = TypeVarValue;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "TypeVar"
    }
}

#[derive(Debug)]
pub struct CommonTypes {
    pub bool: TypeVar,
    pub unit: TypeVar,
    pub int: TypeVar,
    pub float: TypeVar,
    pub str: TypeVar,
}

#[derive(Debug)]
pub struct TyContext {
    table: InPlaceUnificationTable<TypeVar>,
    pub handler: Rc<Handler>,
    var_stack: Vec<TypeVar>,
    methods: HashMap<TypeVar, HashMap<Symbol, TypeVar>>,
    pub common: CommonTypes,
}

impl TyContext {
    pub fn new(handler: &Rc<Handler>) -> Self {
        let mut table = InPlaceUnificationTable::new();
        let common = CommonTypes {
            bool: table.new_key(TypeVarValue::Known(Ty::Bool)),
            unit: table.new_key(TypeVarValue::Known(Ty::Unit)),
            int: table.new_key(TypeVarValue::Known(Ty::Int)),
            float: table.new_key(TypeVarValue::Known(Ty::Float)),
            str: table.new_key(TypeVarValue::Known(Ty::Str)),
        };
        Self {
            table,
            handler: handler.clone(),
            var_stack: Vec::new(),
            methods: HashMap::new(),
            common,
        }
    }

    pub fn new_type_var(&mut self) -> TypeVar {
        self.table.new_key(TypeVarValue::Unknown)
    }

    pub fn alloc_ty(&mut self, ty: Ty) -> TypeVar {
        self.table.new_key(TypeVarValue::Known(ty))
    }

    pub fn get_method(&self, struct_id: TypeVar, name: Symbol) -> Option<TypeVar> {
        self.methods
            .get(&struct_id)
            .and_then(|methods| methods.get(&name).copied())
    }

    pub fn add_method(&mut self, struct_id: TypeVar, name: Symbol, ty: TypeVar) -> bool {
        self.methods
            .entry(struct_id)
            .or_insert_with(HashMap::new)
            .insert(name, ty)
            .is_some()
    }

    pub fn resolve_ty(&mut self, var: TypeVar) -> Ty {
        self.table
            .probe_value(var)
            .known()
            .unwrap_or_else(|| Ty::Infer(var))
    }

    pub fn unify(&mut self, expected: TypeVar, actual: TypeVar, span: Span) -> Result<()> {
        let a = self.resolve_ty(expected);
        let b = self.resolve_ty(actual);

        match (a, b) {
            (Ty::Infer(a), Ty::Infer(b)) => self.table.union(a, b),
            (Ty::Infer(v), other) | (other, Ty::Infer(v)) => {
                self.table.union_value(v, TypeVarValue::Known(other))
            }
            (Ty::Fn(params, ret), Ty::Fn(params2, ret2)) => {
                for (p1, p2) in params.into_iter().zip(params2) {
                    self.unify(p1, p2, span)?;
                }
                self.unify(ret, ret2, span)?;
            }
            (Ty::Struct(id, name, fields), Ty::Struct(id2, name2, fields2)) => {
                if id != id2 {
                    return self
                        .handler
                        .mk_err(span, &format!("Expected type {}, Actual: {}", name, name2));
                }
                for ((_, f1), (_, f2)) in fields.into_iter().zip(fields2) {
                    self.unify(f1, f2, span)?;
                }
            }
            (Ty::Unit, Ty::Unit)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Int, Ty::Int)
            | (Ty::Float, Ty::Float)
            | (Ty::Str, Ty::Str) => {}
            (a, b) => self
                .handler
                .mk_err(span, &format!("Expected type {}, Actual: {}", a, b))?,
        }

        Ok(())
    }

    pub fn fill_ty(&mut self, ty: &mut Ty) -> Result<()> {
        log::debug!("fill_ty: {:?}", ty);

        self.var_stack.clear();
        let var = ty.type_var().map(|v| self.table.find(v));
        self.fill_ty_inner(ty, var)
    }

    pub fn fill_methods(&mut self) -> Result<()> {
        let mut methods = std::mem::take(&mut self.methods);
        for method in methods.values_mut().flat_map(|map| map.values_mut()) {
            // FIXME: What to do here
            // self.fill_ty(method)?;
        }
        self.methods = methods;
        Ok(())
    }

    fn fill_ty_inner(&mut self, ty: &mut Ty, var: Option<TypeVar>) -> Result<()> {
        match ty {
            Ty::Infer(v) => {
                let root_v = self.table.find(*v);
                if self.var_stack.contains(&root_v) {
                    log::warn!("Type {:?} contains cycles", root_v);
                    return if var == Some(root_v) { Err(()) } else { Ok(()) };
                }

                if let Some(found) = self.table.probe_value(root_v).known() {
                    log::trace!("found: {:?} == {:?}", root_v, found);
                    self.var_stack.push(root_v);
                    *ty = found;
                    self.fill_ty_inner(ty, var)?;
                    self.var_stack.pop();
                }
            }
            Ty::Fn(params, ret) => {
                for p in params {
                    *p = self.table.find(*p);
                }
                *ret = self.table.find(*ret);
            }
            Ty::Struct(_, _, fields) => {
                log::trace!("fill fields");
                for f in fields.values_mut() {
                    *f = self.table.find(*f);
                }
            }
            _ => {}
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq)]
pub enum Ty {
    Infer(TypeVar),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(
        /* params: */ Vec<TypeVar>,
        /* return_ty: */ TypeVar,
    ),
    Struct(
        /* id: */ TypeVar,
        /* name: */ Symbol,
        /* fields: */ BTreeMap<Symbol, TypeVar>,
    ),
}

impl Ty {
    pub fn type_var(&self) -> Option<TypeVar> {
        match self {
            Ty::Infer(id) => Some(*id),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeVarValue {
    Known(Ty),
    Unknown,
}

impl TypeVarValue {
    pub fn known(self) -> Option<Ty> {
        match self {
            TypeVarValue::Known(t) => Some(t),
            TypeVarValue::Unknown => None,
        }
    }
}

impl UnifyValue for TypeVarValue {
    type Error = NoError;

    fn unify_values(t1: &Self, t2: &Self) -> std::result::Result<Self, Self::Error> {
        match (t1, t2) {
            (TypeVarValue::Known(..), TypeVarValue::Known(..)) => panic!(
                "equating two type variables, both of which have known types: {:?} and {:?}",
                t1, t2
            ),
            (TypeVarValue::Known(..), TypeVarValue::Unknown) => Ok(t1.clone()),
            (TypeVarValue::Unknown, TypeVarValue::Known(..)) => Ok(t2.clone()),
            (TypeVarValue::Unknown, TypeVarValue::Unknown) => Ok(TypeVarValue::Unknown),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Infer(id) => write!(f, "{{unknown {:?}}}", id.0)?,
            Ty::Unit => f.write_str("unit")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(params, ret) => {
                f.write_str("fn(")?;
                let mut first = true;
                for p in params {
                    if first {
                        first = false;
                    } else {
                        f.write_str(", ")?;
                    }
                    write!(f, "{:?}", p)?;
                }
                f.write_str(")")?;
                write!(f, " -> {:?}", ret)?;
            }
            Ty::Struct(_, name, _) => write!(f, "{}", name)?,
        }
        Ok(())
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Infer(id) => write!(f, "{:?}", id)?,
            Ty::Unit => f.write_str("unit")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(params, ret) => {
                f.write_str("fn(")?;
                let mut first = true;
                for p in params {
                    if first {
                        first = false;
                    } else {
                        f.write_str(", ")?;
                    }
                    write!(f, "{:?}", p)?;
                }
                f.write_str(")")?;
                write!(f, " -> {:?}", ret)?;
            }
            Ty::Struct(id, name, fields) => {
                write!(f, "struct {}{} {{ ", name, id.0)?;
                let mut first = true;
                for (name, ty) in fields {
                    if first {
                        first = false;
                    } else {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}: {:?}", name, ty)?;
                }
                write!(f, " }}")?;
            }
        }
        Ok(())
    }
}
