use crate::{err::Handler, lex::Span, symbol::Symbol};
use ena::unify::{InPlaceUnificationTable, UnifyKey, UnifyValue};
use std::{collections::BTreeMap, fmt, rc::Rc};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Tvar(u32);

impl From<u32> for Tvar {
    fn from(n: u32) -> Self {
        Self(n)
    }
}

impl UnifyKey for Tvar {
    type Value = Option<Ty>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "Tvar"
    }
}

pub struct CommonTypes {
    pub unit: Tvar,
    pub bool: Tvar,
    pub int: Tvar,
    pub float: Tvar,
    pub str: Tvar,
}

impl CommonTypes {
    fn new(table: &mut InPlaceUnificationTable<Tvar>) -> Self {
        Self {
            unit: table.new_key(Some(TyKind::Unit.into())),
            bool: table.new_key(Some(TyKind::Bool.into())),
            int: table.new_key(Some(TyKind::Int.into())),
            float: table.new_key(Some(TyKind::Float.into())),
            str: table.new_key(Some(TyKind::Str.into())),
        }
    }
}

pub struct TyContext {
    table: InPlaceUnificationTable<Tvar>,
    handler: Rc<Handler>,
    pub common: CommonTypes,
}

impl TyContext {
    pub fn new(handler: &Rc<Handler>) -> Self {
        let mut table = InPlaceUnificationTable::new();
        let common = CommonTypes::new(&mut table);
        Self {
            table,
            handler: handler.clone(),
            common,
        }
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn new_tvar(&mut self) -> Tvar {
        self.table.new_key(None)
    }

    pub fn new_tvar_with_ty(&mut self, ty: TyKind) -> Tvar {
        self.table.new_key(Some(ty.into()))
    }

    pub fn unify(&mut self, a: Tvar, b: Tvar, span: Span) -> Option<()> {
        if let Err(e) = self.table.unify_var_var(a, b) {
            self.handler.report(span, &e);
            None
        } else {
            Some(())
        }
    }

    pub fn unify_ty(&mut self, a: Tvar, ty: TyKind, span: Span) -> Option<()> {
        if let Err(e) = self.table.unify_var_value(a, Some(ty.into())) {
            self.handler.report(span, &e);
            None
        } else {
            Some(())
        }
    }

    pub fn get_ty(&mut self, t: Tvar, span: Span) -> Option<Ty> {
        match self.table.probe_value(t) {
            Some(t) => Some(t),
            None => {
                self.handler.report(span, "Cannot infer type");
                None
            }
        }
    }

    pub fn get_ty_direct(&mut self, t: impl Into<Tvar>) -> Option<Ty> {
        self.table.probe_value(t)
    }

    pub fn find_root(&mut self, t: impl Into<Tvar>) -> Tvar {
        self.table.find(t)
    }
}

#[derive(Clone, PartialEq)]
pub enum TyKind {
    Unit,
    Bool,
    Int,
    Float,
    Str,
    Fn(Vec<Tvar>, Tvar),
    Struct(Symbol, BTreeMap<Symbol, Tvar>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ty(pub Rc<TyKind>);

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Self {
        Ty(Rc::new(kind))
    }
}

impl UnifyValue for Ty {
    type Error = String;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (&*value1.0, &*value2.0) {
            (TyKind::Unit, TyKind::Unit)
            | (TyKind::Bool, TyKind::Bool)
            | (TyKind::Int, TyKind::Int)
            | (TyKind::Float, TyKind::Float)
            | (TyKind::Str, TyKind::Str) => Ok(value1.clone()),
            (TyKind::Fn(params, ret), TyKind::Fn(params2, ret2)) => {
                if params.len() != params2.len() {
                    return Err(format!(
                        "Number of parameters mismatch: Expected: {}, Actual: {}",
                        params.len(),
                        params2.len()
                    ));
                }

                for (a, b) in params.iter().zip(params2) {
                    if a.0 != b.0 {
                        return Err(format!(
                            "Type mismatch: Expected: {:?}, Actual: {:?}",
                            a.0, b.0
                        ));
                    }
                }

                if ret.0 != ret2.0 {
                    return Err(format!(
                        "Type mismatch: Expected: {:?}, Actual: {:?}",
                        ret.0, ret2.0
                    ));
                }

                Ok(value1.clone())
            }
            (TyKind::Struct(name, fields), TyKind::Struct(name2, fields2)) => {
                if name != name2 {
                    return Err(format!(
                        "Type mismatch: Expected: {}, Actual: {}",
                        name, name2
                    ));
                }

                if fields.len() != fields2.len() {
                    return Err(format!(
                        "Number of fields mismatch: Expected: {} Actual: {}",
                        fields.len(),
                        fields2.len()
                    ));
                }

                for (name, f) in fields {
                    let f2 = match fields2.get(name) {
                        Some(f) => f,
                        None => {
                            return Err(format!("Field missing: {}", name));
                        }
                    };

                    if f.0 != f2.0 {
                        return Err(format!(
                            "Type mismatch: Expected: {:?}, Actual: {:?}",
                            f.0, f2.0
                        ));
                    }
                }
                Ok(value1.clone())
            }
            (a, b) => Err(format!("Type mismatch: Expected: {:?}, Actual: {:?}", a, b)),
        }
    }
}

impl fmt::Debug for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyKind::Unit => f.write_str("unit")?,
            TyKind::Bool => f.write_str("bool")?,
            TyKind::Int => f.write_str("int")?,
            TyKind::Float => f.write_str("float")?,
            TyKind::Str => f.write_str("str")?,
            TyKind::Fn(params, ret) => {
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
            TyKind::Struct(name, ..) => write!(f, "{}", name)?,
        }
        Ok(())
    }
}
