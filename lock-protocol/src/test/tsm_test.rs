use vstd::prelude::*;
use state_machines_macros::*;

verus! {

pub const ENTRIES: usize = 512;

#[derive(Clone, Copy)]
pub struct B {
    pub flag: bool,
}

#[derive(Clone, Copy)]
pub struct A {
    pub bs: [B; ENTRIES],
}

tokenized_state_machine!{
X {

    fields {
        #[sharding(variable)]
        pub a: Map<int, A>,
    }

    init!{
        initialize() {
            init a = Map::empty().insert(0, A {
                bs: [B {
                    flag: true,
                }; ENTRIES],
            });
        }
    }

    transition! {
        // set child relationship
        set(key: int, index: int, value: bool) {
            require key != 0;
            require pre.a.contains_key(key);

            update a = pre.a.insert(key, A {
                bs: {
                    let mut bs = pre.a[key].bs;
                    // bs[index].flag = value;
                    bs
                },
            });
        }
    }

    #[inductive(set)]
    fn tr_set_invariant(pre: Self, post: Self, key: int, index: int, value: bool) {
    }
}
}

} // verus!
