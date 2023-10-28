use crate::{
    err::{ErrHandler, Result},
    lex::Span,
    symbol::Symbol,
};
use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    fmt::Write,
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
    pub handler: Rc<ErrHandler>,
    fields: HashMap<TypeVar, StructFields>,
    methods: HashMap<TypeVar, HashMap<Symbol, TypeVar>>,
    common: CommonTypes,
    done: HashSet<TypeVar>,
}

impl TyContext {
    pub fn new(handler: &Rc<ErrHandler>) -> Self {
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
            fields: HashMap::new(),
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

    pub fn new_generic(&mut self, name: Symbol) -> TypeVar {
        self.table.new_key(TypeVarValue::Known(Ty::Generic(name)))
    }

    pub fn alloc_ty(&mut self, ty: Ty) -> TypeVar {
        self.table.new_key(TypeVarValue::Known(ty))
    }

    pub fn generic_params(&mut self, ty: TypeVar) -> Rc<[TypeVar]> {
        match self.resolve_ty(ty) {
            Ty::Struct(.., generic_params) => generic_params,
            _ => Rc::from([]),
        }
    }

    pub fn instantiate_generic_ty(&mut self, ty_var: TypeVar) -> TypeVar {
        let generic_params = self.generic_params(ty_var);
        if generic_params.is_empty() {
            return ty_var;
        }

        let mut subst = HashMap::new();
        for &g in generic_params.iter() {
            if let Ty::Generic(_) = self.resolve_ty(g) {
                subst.insert(g, self.new_type_var());
            }
        }

        self.subst_ty(ty_var, &subst)
    }

    pub fn subst_ty(&mut self, ty: TypeVar, subst: &HashMap<TypeVar, TypeVar>) -> TypeVar {
        match self.resolve_ty(ty) {
            Ty::Generic(_) => subst.get(&ty).copied().unwrap_or(ty),
            Ty::Fn(params, ret) => {
                let params = params.iter().map(|&ty| self.subst_ty(ty, subst)).collect();
                let ret = self.subst_ty(ret, subst);
                self.alloc_ty(Ty::Fn(params, ret))
            }
            Ty::Struct(id, name, generics) => {
                dbg!(&generics);
                let generics = generics.iter().map(|&ty| self.subst_ty(ty, subst)).collect();
                dbg!(&generics);
                let new_ty = self.alloc_ty(Ty::Struct(id, name, generics));
                if let Some(fields) = self.fields.get(&ty).cloned() {
                    let fields = fields
                        .iter()
                        .map(|(name, ty)| (name, self.subst_ty(ty, subst)))
                        .collect();
                    dbg!(subst);
                    self.add_fields(new_ty, fields);
                }
                new_ty
            }
            Ty::Tuple(tys) => {
                let tys = tys.iter().map(|&ty| self.subst_ty(ty, subst)).collect();
                self.alloc_ty(Ty::Tuple(tys))
            }
            Ty::Array(ty) => {
                let ty = self.subst_ty(ty, subst);
                self.alloc_ty(Ty::Array(ty))
            }
            Ty::Bool | Ty::Int | Ty::Float | Ty::Str | Ty::Unit | Ty::Infer(_) => ty,
        }
    }

    pub fn get_field(&self, struct_id: TypeVar, name: Symbol) -> Option<TypeVar> {
        self.fields.get(&struct_id).and_then(|fields| fields.get(name))
    }

    pub fn get_fields(&self, struct_id: TypeVar) -> Option<StructFields> {
        self.fields.get(&struct_id).cloned()
    }

    pub fn add_fields(&mut self, struct_id: TypeVar, fields: StructFields) {
        let existing = self.fields.insert(dbg!(struct_id), dbg!(fields));
        debug_assert!(existing.is_none());
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
        self.table.probe_value(var).known().unwrap_or(Ty::Infer(var))
    }

    pub fn unify_value(&mut self, var: TypeVar, ty: Ty) {
        self.table.union_value(var, TypeVarValue::Known(ty));
    }

    pub fn unify(&mut self, expected: TypeVar, actual: TypeVar, span: Span) -> Result<()> {
        self.done.clear();
        self.unify_inner(expected, actual, span)
    }

    fn unify_inner(&mut self, expected: TypeVar, actual: TypeVar, span: Span) -> Result<()> {
        if self.unify_inner_no_raise(expected, actual).is_ok() {
            return Ok(());
        }

        let a = self.resolve_ty(expected);
        let b = self.resolve_ty(actual);

        match (a, b) {
            (Ty::Infer(_), _) | (_, Ty::Infer(_)) => unreachable!(),
            (Ty::Struct(_, name, generics), Ty::Struct(_, name2, generics2)) => {
                fn write_generics(generics: &[TypeVar], buf: &mut String, mut f: impl FnMut(TypeVar) -> Ty) {
                    if generics.is_empty() {
                        return;
                    }
                    buf.push('<');
                    for (i, &g) in generics.iter().enumerate() {
                        if i > 0 {
                            buf.push_str(", ");
                        }
                        let t = f(g);
                        write!(buf, "{}", t).unwrap();
                    }
                    buf.push('>');
                }

                let mut buf = format!("Type mismatch: Expected type `{}", name);
                write_generics(&generics, &mut buf, |g| self.resolve_ty(g));
                write!(&mut buf, "`, Actual: `{}", name2).unwrap();
                write_generics(&generics2, &mut buf, |g| self.resolve_ty(g));
                buf.push('`');
                return self.handler.mk_err(span, &buf);
            }
            (a, b) => self
                .handler
                .mk_err(span, &format!("Expected type `{}`, Actual: `{}`", a, b))?,
        }

        Ok(())
    }

    fn unify_inner_no_raise(&mut self, expected: TypeVar, actual: TypeVar) -> Result<()> {
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
                    return Err(());
                }
                for (p1, p2) in params.iter().zip(params2.iter()) {
                    self.unify_inner_no_raise(*p1, *p2)?;
                }
                self.unify_inner_no_raise(ret, ret2)?;
            }
            (Ty::Struct(id, _, generics), Ty::Struct(id2, _, generics2)) => {
                if id != id2 {
                    return Err(());
                }

                if generics.len() != generics2.len() {
                    return Err(());
                }

                for (g1, g2) in generics.iter().zip(generics2.iter()) {
                    self.unify_inner_no_raise(*g1, *g2)?;
                }
            }
            (Ty::Tuple(tys), Ty::Tuple(tys2)) => {
                if tys.len() != tys2.len() {
                    return Err(());
                }
                for (a, b) in tys.iter().zip(tys2.iter()) {
                    self.unify_inner_no_raise(*a, *b)?;
                }
            }
            (Ty::Array(t1), Ty::Array(t2)) => {
                self.unify_inner_no_raise(t1, t2)?;
            }
            (Ty::Unit, Ty::Unit)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Int, Ty::Int)
            | (Ty::Float, Ty::Float)
            | (Ty::Str, Ty::Str) => {}
            _ => return Err(()),
        }

        Ok(())
    }
}

#[derive(Clone, PartialEq)]
pub enum Ty {
    Infer(TypeVar),
    Generic(Symbol),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(/* params: */ Rc<[TypeVar]>, /* return_ty: */ TypeVar),
    Struct(
        /* id: */ TypeVar,
        /* name: */ Symbol,
        /* generics: */ Rc<[TypeVar]>,
    ),
    Tuple(Rc<[TypeVar]>),
    Array(TypeVar),
}

#[derive(PartialEq, Clone)]
pub struct StructFields {
    fields: Rc<[(Symbol, TypeVar)]>,
}

impl fmt::Debug for StructFields {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("{ ")?;
        let mut first = true;
        for (name, ty) in self.iter() {
            if first {
                first = false;
            } else {
                f.write_str(", ")?;
            }
            write!(f, "{}: {:?}", name, ty)?;
        }
        f.write_str(" }")?;
        Ok(())
    }
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
            Ty::Generic(name) => write!(f, "{}", name)?,
            Ty::Unit => f.write_str("()")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(..) => f.write_str("Function")?,
            Ty::Struct(_, name, generics) => {
                write!(f, "{name}")?;
                if generics.len() > 0 {
                    f.write_str("<")?;
                    for (i, g) in generics.iter().enumerate() {
                        if i > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{:?}", g)?;
                    }
                    f.write_str(">")?;
                }
            }
            Ty::Tuple(..) => f.write_str("Tuple")?,
            Ty::Array(t) => write!(f, "[{:?}]", t)?,
        }
        Ok(())
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Infer(id) => write!(f, "{id:?}")?,
            Ty::Generic(name) => write!(f, "{name}")?,
            Ty::Unit => f.write_str("()")?,
            Ty::Bool => f.write_str("bool")?,
            Ty::Int => f.write_str("int")?,
            Ty::Float => f.write_str("float")?,
            Ty::Str => f.write_str("str")?,
            Ty::Fn(params, ret) => {
                f.write_str("fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{p:?}")?;
                }
                f.write_str(")")?;
                write!(f, " -> {ret:?}")?;
            }
            Ty::Struct(id, name, generics) => {
                write!(f, "struct {name}({id:?})<{generics:?}>")?;
            }
            Ty::Tuple(tys) => fmt_tys(f, &tys[..])?,
            Ty::Array(t) => write!(f, "[{:?}]", t)?,
        }
        Ok(())
    }
}

fn fmt_tys(f: &mut fmt::Formatter<'_>, tys: &[TypeVar]) -> fmt::Result {
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
    Ok(())
}
