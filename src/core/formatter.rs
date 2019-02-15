use super::typechk::*;
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
                HoledTerm::App{s,t} => write!(f, "{} {}", s, t),
                HoledTerm::Lam(HoledAbs{A,t}) => write!(f, "(\\:{} -> {})", A, t),
                HoledTerm::Pi(HoledAbs{A,t}) => write!(f, "(|:{}| {})", A, t),
                HoledTerm::Let{env, t} => {
                    writeln!(f, "let {{")?;
                    env.fmt_with_indent(f, lvl+1)?;
                    write_indent(f, lvl)?; write!(f, "}} in ({})", t)
                },
                HoledTerm::Case{t, cases, datatype} => {
                    writeln!(f, "case{} {} {{", datatype.map(|i| format!("[#{}]", i)).unwrap_or("".into()), t)?;
                    for case in cases {
                        write_indent(f, lvl+1)?;
                        writeln!(f, "{}", case)?;
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
        for (id, c) in self.consts.iter().enumerate() {
            write_indent(f, lvl)?;
            match c {
                HoledConst::Def(t) => writeln!(f, "#{} := {}", id, t)?,
                HoledConst::DataType{param_types, ..} => {
                    write!(f, "datatype #{}", id)?;
                    for param_type in param_types {
                        write!(f, " @:{}", param_type)?;
                    }
                    writeln!(f, " {{ ... }}")?
                },
                HoledConst::Ctor{datatype, param_types} => {
                    write!(f, "#{}.#{}", datatype, id)?;
                    for param_type in param_types {
                        write!(f, " @:{}", param_type)?;
                    }
                    writeln!(f, "")?
                },
            }
            writeln!(f, "")?;
        }

        for (t,T) in &self.typings {
            write_indent(f, lvl)?;
            writeln!(f, "{} : {}", t, T)?;
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

impl fmt::Display for InferTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn with_indent(self_: &InferTerm, lvl: usize, f: &mut fmt::Formatter) -> fmt::Result {
            write_indent(f, lvl)?;

            match self_ {
                InferTerm::Const(const_id) => write!(f, "#{}", const_id),
                InferTerm::DBI(i) => write!(f, "@{}", i),
                InferTerm::Universe => write!(f, "Type"),
                InferTerm::App{s,t} => write!(f, "({} {})", s, t),
                InferTerm::Lam(InferAbs{A,t}) => write!(f, "(\\:{} -> {})", A, t),
                InferTerm::Pi(InferAbs{A,t}) => write!(f, "(|:{}| {})", A, t),
                InferTerm::Let{env, t} => {
                    writeln!(f, "(let {{")?;
                    fmt_infer_env(env, f, lvl+1)?;
                    write_indent(f, lvl)?; write!(f, "}} in {})", t)
                },
                InferTerm::Case{t, cases, datatype} => {
                    writeln!(f, "(case{} {} {{", datatype.map(|i| format!("[#{}]", i)).unwrap_or("".into()), t)?;
                    for case in cases {
                        write_indent(f, lvl+1)?;
                        writeln!(f, "{}", case)?;
                    }
                    write_indent(f, lvl)?; write!(f, "}})")
                },
                InferTerm::Value(v) => write!(f, "{}", v),
                InferTerm::Infer{id} => write!(f, "?{}", id.get()),
                InferTerm::Subst{t, dbi, u} => write!(f, "{}[{}/{}]", t, dbi, u),
            }
        }

        with_indent(self, 0, f)
    }
}

impl fmt::Display for InferTypedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}:{})", self.tower[0], self.tower[1])
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

impl fmt::Display for Subst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Subst::Eq(id_a, id_b) => write!(f, "?{} = ?{}", id_a.get(), id_b.get()),
            Subst::Instantiate(id, t) => write!(f, "?{} := {}", id.get(), t),
        }
    }
}