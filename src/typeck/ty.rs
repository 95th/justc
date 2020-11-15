use crate::{
    err::{Handler, Result},
    lex::Span,
    symbol::Symbol,
};
use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    iter::FromIterator,
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
    common: CommonTypes,
    done: HashSet<TypeVar>,
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
            done: HashSet::new(),
        }
    }

    pub fn bool(&self) -> TypeVar {
        self.common.bool
    }

    pub fn unit(&self) -> TypeVar {
        self.common.unit
    }

    pub fn int(&self) -> TypeVar {
        self.common.int
    }

    pub fn float(&self) -> TypeVar {
        self.common.float
    }

    pub fn str(&self) -> TypeVar {
        self.common.str
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
        self.table.probe_value(var).known().unwrap_or_else(|| Ty::Infer(var))
    }

    pub fn unify_value(&mut self, var: TypeVar, ty: Ty) {
        self.table.union_value(var, TypeVarValue::Known(ty));
    }

    pub fn unify(&mut self, expected: TypeVar, actual: TypeVar, span: Span) -> Result<()> {
        self.done.clear();
        self.unify_inner(expected, actual, span)
    }

    fn unify_inner(&mut self, expected: TypeVar, actual: TypeVar, span: Span) -> Result<()> {
        if expected == actual || self.table.unioned(expected, actual) {
            return Ok(());
        }

        if !self.done.insert(expected) && !self.done.insert(actual) {
            return Ok(());
        }

        let a = self.resolve_ty(expected);
        let b = self.resolve_ty(actual);

        log::trace!("Unify {:?} with {:?}", a, b);

        match (a, b) {
            (Ty::Infer(a), Ty::Infer(b)) => self.table.union(a, b),
            (Ty::Infer(v), other) | (other, Ty::Infer(v)) => self.table.union_value(v, TypeVarValue::Known(other)),
            (Ty::Fn(params, ret), Ty::Fn(params2, ret2)) => {
                if params.len() != params2.len() {
                    return self
                        .handler
                        .mk_err(span, "Type mismatch: Incorrect number of parameters");
                }
                for (p1, p2) in params.iter().zip(params2.iter()) {
                    self.unify_inner(*p1, *p2, span)?;
                }
                self.unify_inner(ret, ret2, span)?;
            }
            (Ty::Struct(id, name, fields), Ty::Struct(id2, name2, fields2)) => {
                if id != id2 {
                    return self.handler.mk_err(
                        span,
                        &format!("Type mismatch: Expected type `{}`, Actual: `{}`", name, name2),
                    );
                }
                for (f1, t1) in fields.iter() {
                    for (f2, t2) in fields2.iter() {
                        if f1 == f2 {
                            self.unify_inner(t1, t2, span)?;
                            break;
                        }
                    }
                }
            }
            (Ty::Tuple(tys), Ty::Tuple(tys2)) => {
                if tys.len() != tys2.len() {
                    return self.handler.mk_err(
                        span,
                        &format!(
                            "Tuple size mismatch: Expected `{}`, Actual: `{}`",
                            tys.len(),
                            tys2.len()
                        ),
                    );
                }
                for (a, b) in tys.iter().zip(tys2.iter()) {
                    self.unify_inner(*a, *b, span)?;
                }
            }
            (Ty::Unit, Ty::Unit)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Int, Ty::Int)
            | (Ty::Float, Ty::Float)
            | (Ty::Str, Ty::Str) => {}
            (a, b) => self
                .handler
                .mk_err(span, &format!("Expected type `{}`, Actual: `{}`", a, b))?,
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
    Fn(/* params: */ Rc<Vec<TypeVar>>, /* return_ty: */ TypeVar),
    Struct(
        /* id: */ TypeVar,
        /* name: */ Symbol,
        /* fields: */ Rc<StructFields>,
    ),
    Tuple(Rc<Vec<TypeVar>>),
}

#[derive(Debug, PartialEq)]
pub struct StructFields {
    fields: Vec<(Symbol, TypeVar)>,
}

impl StructFields {
    pub fn get(&self, name: Symbol) -> Option<TypeVar> {
        self.fields
            .iter()
            .find_map(|(n, v)| if *n == name { Some(*v) } else { None })
    }

    pub fn iter(&self) -> impl Iterator<Item = (Symbol, TypeVar)> + '_ {
        self.fields.iter().copied()
    }

    pub fn keys(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.fields.iter().map(|(k, _)| k).copied()
    }

    pub fn values(&self) -> impl Iterator<Item = TypeVar> + '_ {
        self.fields.iter().map(|(_, v)| v).copied()
    }

    pub fn len(&self) -> usize {
        self.fields.len()
    }
}

impl FromIterator<(Symbol, TypeVar)> for StructFields {
    fn from_iter<T: IntoIterator<Item = (Symbol, TypeVar)>>(iter: T) -> Self {
        Self {
            fields: iter.into_iter().collect(),
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
            Ty::Infer(..) => f.write_str("{unknown}")?,
            Ty::Unit => f.write_str("()")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(..) => f.write_str("Function")?,
            Ty::Struct(_, name, _) => write!(f, "{}", name)?,
            Ty::Tuple(..) => f.write_str("Tuple")?,
        }
        Ok(())
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Infer(id) => write!(f, "{:?}", id)?,
            Ty::Unit => f.write_str("()")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(params, ret) => {
                f.write_str("fn(")?;
                let mut first = true;
                for p in params.iter() {
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
                for (name, ty) in fields.iter() {
                    if first {
                        first = false;
                    } else {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}: {:?}", name, ty)?;
                }
                write!(f, " }}")?;
            }
            Ty::Tuple(tys) => {
                f.write_str("(")?;
                let mut first = true;
                for t in tys.iter() {
                    if first {
                        first = false;
                    } else {
                        f.write_str(", ")?;
                    }
                    write!(f, "{:?}", t)?;
                }
                f.write_str(")")?;
            }
        }
        Ok(())
    }
}
