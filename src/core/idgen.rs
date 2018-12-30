pub trait Generator {
    type Id;
    fn gen(&mut self) -> Self::Id;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Inc<N>
    where N : ::num::Zero + ::num::One + ::std::ops::AddAssign + Clone
{
    next: N,
}
impl<N> Inc<N>
    where N : ::num::Zero + ::num::One + ::std::ops::AddAssign + Clone
{
    pub fn new() -> Self {
        Inc { next: ::num::zero() }
    }
    
    pub fn advance(&mut self, n: N) {
        self.next += n;
    }
}
impl<N> Generator for Inc<N>
    where N : ::num::Zero + ::num::One + ::std::ops::AddAssign + Clone
{
    type Id = N;

    fn gen(&mut self) -> N {
        let n = self.next.clone();
        self.next += ::num::one();
        n
    }
}