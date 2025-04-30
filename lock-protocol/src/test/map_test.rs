use std::collections::HashMap;

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::hash_map::*;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
verus! {

fn test() {
    // assume(vstd::std_specs::hash::obeys_key_model::<u64>());
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    // let mut map = alloc_page_table_entries();

    let mut map = HashMap::<u64, u64>::new();
    for i in 0..10
        invariant
            0 <= i <= 10,
    // map.len() == i + 1,
    // forall |j:u64| 0 <= j < i ==> {
    //     map@.contains_key(j)
    // }
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;

        map.insert(i, 0);
        // assert(map@.len() == i + 1);
        assert(map@.contains_key(i));
    }
    // map.insert(1, 1);
    // let b = map.len();
    // assert(b == 10);
    // assert(map.len() == 1);
    // // assert(map.len() == 10);
    // // assert(map.len() == 10);
    // map.insert(1, 1);
    // // assert(map.len() == 1);
    // // assert(map.len() == 10);
    // map.insert(1, 2);
    // map.remove(&2);
    // // assert(map.len() == 1);
    // // assert(map.len() == 9);
}

// #[verifier::external_body]
// fn alloc_page_table_entries() -> (res: HashMapWithView<u64, u64>)
//     ensures
//         res.len() == 10,
//         forall |i:u64| 0 <= i < 10 ==> {
//             res@.contains_key(i)
//         }
//     {
//         let mut map = HashMapWithView::new();
//         for i in 0..11 {
//             map.insert(i as u64, i);
//         }
//         assert(map.len() == 10);
//         map
//     }
} // verus!
