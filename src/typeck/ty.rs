use crate::{
    err::{Handler, Result},
    lex::Span,
    symbol::Symbol,
};
use ena::unify::{InPlaceUnificationTable, NoError, UnifyKey, UnifyValue};
use std::{borrow::Cow, collections::BTreeMap, fmt, rc::Rc};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
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

pub struct TyContext {
    table: InPlaceUnificationTable<TypeVar>,
    pub handler: Rc<Handler>,
}

impl TyContext {
    pub fn new(handler: &Rc<Handler>) -> Self {
        Self {
            table: InPlaceUnificationTable::new(),
            handler: handler.clone(),
        }
    }

    pub fn new_type_var(&mut self) -> Ty {
        Ty::Infer(self.table.new_key(TypeVarValue::Unknown))
    }

    pub fn resolve_ty<'a>(&mut self, ty: &'a Ty) -> Cow<'a, Ty> {
        match ty {
            Ty::Infer(v) => match self.table.inlined_probe_value(*v).known() {
                Some(t) => Cow::Owned(t),
                None => Cow::Borrowed(ty),
            },
            _ => Cow::Borrowed(ty),
        }
    }

    pub fn unify(&mut self, expected: &Ty, actual: &Ty, span: Span) -> Result<()> {
        let a = self.resolve_ty(expected);
        let b = self.resolve_ty(actual);

        match (&*a, &*b) {
            (Ty::Infer(a), Ty::Infer(b)) => self.table.union(*a, *b),
            (Ty::Infer(v), other) | (other, Ty::Infer(v)) => self
                .table
                .union_value(*v, TypeVarValue::Known(other.clone())),
            (Ty::Fn(params, ret), Ty::Fn(params2, ret2)) => {
                for (p1, p2) in params.iter().zip(params2) {
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
                for ((_, f1), (_, f2)) in fields.iter().zip(fields2) {
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
        self.fill_ty_inner(ty)
    }

    fn fill_ty_inner(&mut self, ty: &mut Ty) -> Result<()> {
        match ty {
            Ty::Infer(v) => {
                if let Some(found) = self.table.probe_value(*v).known() {
                    match self.occurs(*v, &found, 0) {
                        Occurs::Yes => return Err(()),
                        Occurs::Indirectly => return Ok(()),
                        Occurs::No => {}
                    }
                    *ty = found;
                    self.fill_ty_inner(ty)?;
                }
                Ok(())
            }
            Ty::Fn(params, ret) => {
                for p in params {
                    self.fill_ty_inner(p)?;
                }
                self.fill_ty_inner(ret)
            }
            Ty::Struct(.., fields) => {
                for (_, f) in fields {
                    self.fill_ty_inner(f)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn occurs(&mut self, var: TypeVar, ty: &Ty, mut depth: u32) -> Occurs {
        depth += 1;
        if depth > 1000 {
            return Occurs::Indirectly;
        }
        match ty {
            Ty::Infer(v) => {
                if self.table.unioned(*v, var) {
                    return Occurs::Yes;
                }
                if let Some(t) = self.table.inlined_probe_value(*v).known() {
                    return self.occurs(var, &t, depth);
                }
                Occurs::No
            }
            Ty::Fn(params, ret) => {
                for p in params {
                    let occurs = self.occurs(var, p, depth);
                    if occurs != Occurs::No {
                        return occurs;
                    }
                }
                self.occurs(var, ret, depth)
            }
            Ty::Struct(.., fields) => {
                for (_, f) in fields {
                    let occurs = self.occurs(var, f, depth);
                    if occurs != Occurs::No {
                        return occurs;
                    }
                }
                Occurs::No
            }
            _ => Occurs::No,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Occurs {
    Yes,
    Indirectly,
    No,
}

#[derive(Clone, PartialEq)]
pub enum Ty {
    Infer(TypeVar),
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(Vec<Ty>, Box<Ty>),
    Struct(u32, Symbol, BTreeMap<Symbol, Ty>),
}

impl Ty {
    pub fn type_var_id(&self) -> Option<u32> {
        match self {
            Ty::Infer(id) => Some(id.0),
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
                    write!(f, "{}", p)?;
                }
                f.write_str(")")?;
                write!(f, " -> {}", ret)?;
            }
            Ty::Struct(_, name, _) => write!(f, "{}", name)?,
        }
        Ok(())
    }
}

impl fmt::Debug for Ty {
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
            Ty::Struct(id, name, fields) => {
                write!(f, "struct {}{} {{ ", name, id)?;
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
