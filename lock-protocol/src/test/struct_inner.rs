use vstd::prelude::*;

verus! {

struct Inner {
    a: u8,
    b: u8,
}

impl Inner {
    fn change(&mut self)
        requires
            old(self).a == 0,
        ensures
            self.b == old(self).b,
            self.a == old(self).a + 1,
    {
        self.a = self.a + 1;
    }
}

struct Outer(pub Inner);

impl Outer {
    fn test(&mut self)
        requires
            old(self).0.a == 0,
    {
        self.0.change();
        assert(self.0.b == old(self).0.b);
        assert(self.0.a == old(self).0.a + 1);
    }
}

} // verus!
