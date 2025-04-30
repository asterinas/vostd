#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

tokenized_state_machine!{
    #[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(T))]
    SpinLockSpec<T> {
        fields {
            #[sharding(constant)]
            pub user_inv: Set<T>,

            #[sharding(storage_option)]
            pub storage: Option<T>,

            #[sharding(variable)]
            pub locked: bool,

            #[sharding(option)]
            pub guard: Option<()>,
        }

        init!{
            initialize(init_t: T, user_inv: Set<T>) {
                require(user_inv.contains(init_t));
                init user_inv = user_inv;
                init storage = Option::Some(init_t);
                init locked = false;
                init guard = Option::None;
            }
        }

        transition!{
            lock() {
                require(!pre.locked);
                update locked = true;
                add guard += Some(());

                birds_eye let x = pre.storage.get_Some_0();

                withdraw storage -= Some(x);
                assert(pre.user_inv.contains(x));
            }
        }

        transition!{
            release(t: T) {
                require(pre.user_inv.contains(t));
                update locked = false;
                remove guard -= Some(());
                deposit storage += Some(t);
            }
        }

        ///// Invariants and proofs

        #[invariant]
        pub fn sto_user_inv(&self) -> bool {
            self.storage.is_Some() ==>
                self.user_inv.contains(self.storage.get_Some_0())
        }

        #[invariant]
        pub fn lock_inv(&self) -> bool {
            &&& self.locked <==> self.guard.is_Some()
            &&& self.storage.is_Some() <==> self.guard.is_None()
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, init_t: T,  user_inv: Set<T>) {}

        #[inductive(lock)]
        fn lock_inductive(pre: Self, post: Self) {}

        #[inductive(release)]
        fn release_inductive(pre: Self, post: Self, t: T) {}
    }
}

} // verus!
