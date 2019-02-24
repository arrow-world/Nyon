use super::typechk::*;
use super::explicit_subst::*;
use std::fmt;

fn write_indent(f: &mut fmt::Formatter, lvl: usize) -> fmt::Result {
    for _ in 0..lvl {
        write!(f, "\t")?;
    }
    Ok(())
}

impl fmt::Display for HoledTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn with_indent(self_: &HoledTerm, lvl: usize, f: &mut fmt::Formatter) -> fmt::Result {
            write_indent(f, lvl)?;

            match self_ {
                HoledTerm::Const(const_id) => write!(f, "#{}", const_id),
                HoledTerm::DBI(i) => write!(f, "@{}", i),
                HoledTerm::Universe => write!(f, "Type"),
                HoledTerm::App{s,t} => write!(f, "{} {}", s.0, t.0),
                HoledTerm::Lam(HoledAbs{A,t}) => write!(f, "(\\:{} -> {})", A.0, t.0),
                HoledTerm::Pi(HoledAbs{A,t}) => write!(f, "(|:{}| {})", A.0, t.0),
                HoledTerm::Let{env, t} => {
                    writeln!(f, "let {{")?;
                    env.fmt_with_indent(f, lvl+1)?;
                    write_indent(f, lvl)?; write!(f, "}} in ({})", t.0)
                },
                HoledTerm::Case{t, cases, datatype} => {
                    writeln!(f, "case{} {} {{", datatype.map(|i| format!("[#{}]", i)).unwrap_or("".into()), t.0)?;
                    for case in cases {
                        write_indent(f, lvl+1)?;
                        writeln!(f, "{}", case.0)?;
                    }
                    write_indent(f, lvl)?; write!(f, "}}")
                },
                HoledTerm::Hole(maybe_id) => write!(f, "?{}", maybe_id.map(|i| i.to_string()).unwrap_or("".into())),
                HoledTerm::Value(v) => write!(f, "{}", v),
            }
        }

        with_indent(self, 0, f)
    }
}

impl HoledEnv {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter, lvl: usize) -> fmt::Result {
        for (id, (c, loc)) in self.consts.iter().enumerate() {
            write_indent(f, lvl)?;
            match c {
                HoledConst::Def((t, _loc)) => writeln!(f, "#{} := {}", id, t)?,
                HoledConst::DataType{param_types, ..} => {
                    write!(f, "datatype #{}", id)?;
                    for (param_type, loc) in param_types {
                        write!(f, " @:{}", param_type)?;
                    }
                    writeln!(f, " {{ ... }}")?
                },
                HoledConst::Ctor{datatype, param_types} => {
                    write!(f, "#{}.#{}", datatype, id)?;
                    for (param_type, loc) in param_types {
                        write!(f, " @:{}", param_type)?;
                    }
                    writeln!(f, "")?
                },
            }
            writeln!(f, "")?;
        }

        for (t,T) in &self.typings {
            write_indent(f, lvl)?;
            writeln!(f, "{} : {}", t.0, T.0)?;
        }

        write_indent(f, lvl)?;
        writeln!(f, "[nof_named_hole: {}]", self.nof_named_hole)
    }
}

impl fmt::Display for HoledEnv {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_with_indent(f, 0)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Nat(n) => write!(f, "{}", n),
            Value::Int(i) => write!(f, "{}{}", (if i >= &::num::Zero::zero() { "+" } else { "" }).to_string(), i),
            Value::Str(s) => write!(f, "\"{}\"", s),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn with_indent(self_: &Expr, lvl: usize, f: &mut fmt::Formatter) -> fmt::Result {
            write_indent(f, lvl)?;

            match self_ {
                Expr::Const(const_id) => write!(f, "#{}", const_id),
                Expr::DBI(i) => write!(f, "@{}", i),
                Expr::Universe => write!(f, "Type"),
                Expr::App{s,t} => write!(f, "({} {})", s, t),
                Expr::Lam(InferAbs{A,t}) => write!(f, "(\\:{} -> {})", A, t),
                Expr::Pi(InferAbs{A,t}) => write!(f, "(|:{}| {})", A, t),
                Expr::Let{env, t} => {
                    writeln!(f, "(let {{")?;
                    fmt_infer_env(env, f, lvl+1)?;
                    write_indent(f, lvl)?; write!(f, "}} in {})", t)
                },
                Expr::Case{t, cases, datatype} => {
                    writeln!(f, "(case{} {} {{", datatype.map(|i| format!("[#{}]", i)).unwrap_or("".into()), t)?;
                    for case in cases {
                        write_indent(f, lvl+1)?;
                        writeln!(f, "{}", case)?;
                    }
                    write_indent(f, lvl)?; write!(f, "}}")
                },
                Expr::Value(v) => write!(f, "{}", v),
                Expr::Infer{id} => write!(f, "?{}", id.get()),
                Expr::Subst(s,e) => write!(f, "[{}]{}", s, e.0),
            }
        }

        with_indent(self, 0, f)
    }
}

impl fmt::Display for InferTypedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}:{})", self.tower[0].0, self.tower[1].0)
    }
}

fn fmt_infer_env(env: &InferEnv, f: &mut fmt::Formatter, lvl: usize) -> fmt::Result {
    for (id, c) in env.iter().enumerate() {
        write_indent(f, lvl)?;
        match c.c {
            InferConst::Def(ref t) => writeln!(f, "#{} := {} : {}", id, t, c.type_)?,
            InferConst::DataType{ref param_types, ..} => {
                write!(f, "datatype #{} : {}", id, c.type_)?;
                for param_type in param_types {
                    write!(f, " @:{}", param_type)?;
                }
                writeln!(f, " {{ ... }}")?;
            },
            InferConst::Ctor{ref datatype, ref param_types} => {
                write!(f, "#{}.#{} : {}", datatype, id, c.type_)?;
                for param_type in param_types {
                    write!(f, " @:{}", param_type)?;
                }
                writeln!(f, "")?
            },
        }
        writeln!(f, "")?;
    }
    Ok(())
}

pub struct InferEnvDummy<'a>(&'a InferEnv);
impl<'a> fmt::Display for InferEnvDummy<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt_infer_env(self.0, f, 0)
    }
}

impl fmt::Display for InferCtx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{{")?;
        fmt_infer_env(&self.consts, f, 1)?;
        writeln!(f, "}}")?;

        writeln!(f, "[")?;
        for c in &self.local {
            write_indent(f, 1)?;
            writeln!(f, "{}", c)?;
        }
        writeln!(f, "]")?;

        writeln!(f, "<")?;
        for (t,T) in &self.typings {
            write_indent(f, 1)?;
            writeln!(f, "{} : {}", t, T)?;
        }
        writeln!(f, ">")?;

        Ok(())
    }
}

impl fmt::Display for Equal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Equal::ToId(id_a, id_b) => write!(f, "?{} = ?{}", id_a.get(), id_b.get()),
            Equal::Instantiate(id, t) => write!(f, "?{} := {}", id.get(), t.0),
            Equal::Defer(e0, e1, _ctx) => write!(f, "{} = {} -| <ctx>", e0.0, e1.0),
        }
    }
}

impl fmt::Display for Subst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Subst::Shift(n) => write!(f, "↑{}", n),
            Subst::Dot(e,s) => write!(f, "{}.{}", e.0, s),
        }
    }
}