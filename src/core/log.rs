use super::typechk::*;
use std::io::{Write, BufWriter};

struct Logger<W: Write> {
    out: BufWriter<W>,
    does_log: bool,
}
impl<W: Write> Logger<W> {
    pub(super) fn new(inner: W) -> Self {
        Logger {
            out: BufWriter::new(inner),
            does_log: true,
        }
    }

    pub(super) fn on(&mut self) {
        self.does_log = true;
    }

    pub(super) fn off(&mut self) {
        self.does_log = false;
    }

    pub(super) fn log_start_typechk(&mut self) {
        if !self.does_log { return; }

        writeln!(self.out, "start type checking.").unwrap();
    }

    pub(super) fn log_ctx(&mut self, ctx: &InferCtx) {
        if !self.does_log { return; }

        writeln!(self.out, "current context:\n{}", ctx).unwrap();
    }
}