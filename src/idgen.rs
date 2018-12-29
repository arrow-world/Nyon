pub struct IdGen<N: ::num::Zero + ::num::One + ::std::ops::AddAssign + Clone> {
    next: N,
}
impl<N: ::num::Zero + ::num::One + ::std::ops::AddAssign + Clone> IdGen<N> {
    pub fn new() -> Self {
        IdGen { next: ::num::zero() }
    }

    pub fn gen(&mut self) -> N {
        let n = self.next.clone();
        self.next += ::num::one();
        n
    }
}