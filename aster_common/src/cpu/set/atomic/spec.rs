#![allow(non_snake_case)]

use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

tokenized_state_machine!{
    AtomicCpuSetSpec {
        fields {
            #[sharding(persistent_set)]
            pub cpu_set_inv: Set<Option<nat>>,
        }

        init! {
            initialize(cpu_set_inv: Set<nat>) {
                init cpu_set_inv = Set::new(|e: Option<nat>| {
                    e is None || {
                        &&& e is Some
                        &&& cpu_set_inv.contains(e.unwrap())
                    }
                });
            }
        }

        transition! {
            remove(cpu: nat) {
                add cpu_set_inv (union)= set {Some(cpu)};
            }
        }
    }
}

} // verus!
