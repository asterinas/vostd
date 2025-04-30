#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use vstd::prelude::*;

verus! {

struct Hole {
    // v: Vec<usize>,
    ptr: *mut usize,
}

impl Hole {
    #[verifier::external_body]
    fn new(v: &mut Vec<usize>) -> (s: Self)
        ensures
            v@ =~= old(v)@,
    {
        Self {
            // v: v.view(),
            ptr: v.as_mut_ptr(),
        }
    }

    #[verifier::external_body]
    fn get(&self, i: usize) -> &usize {
        unsafe { &*self.ptr.add(i) }
    }

    #[verifier::external_body]
    fn set(&mut self, i: usize, value: usize, v: &mut Vec<usize>)
        ensures
            v@ =~= old(v)@.insert(i as int, value),
    {
        unsafe {
            *self.ptr.add(i) = value;
        }
    }
}

fn vec_ptr(v: &mut Vec<usize>) {
    let mut h = Hole::new(v);
    h.set(0, 1, v);
    assert(!(old(v)@ =~= v@));
}

} // verus!
