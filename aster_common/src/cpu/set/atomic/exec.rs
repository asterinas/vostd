use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, atomic_ghost::AtomicBool, atomic_with_ghost};
use super::spec::AtomicCpuSetSpec;
use super::super::CpuSet;
use super::super::super::{CpuId, valid_cpu, CPU_NUM_SPEC, CPU_NUM};

verus! {

struct_with_invariants! {
    pub struct AtomicCpuSet {
        inner: Vec<AtomicBool<_, AtomicCpuSetSpec::cpu_set_inv, _>>,
        inst: Tracked<AtomicCpuSetSpec::Instance>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            &&& self.inner@.len() == CPU_NUM_SPEC()
        }

        invariant on inner with (inst)
            forall |i: int| where (0 <= i < self.inner.len()) specifically (self.inner[i])
            is (b: bool, g: AtomicCpuSetSpec::cpu_set_inv) {
            &&& g@.instance == inst@
            &&& if !b { g@.key == Some(i as nat) } else { g@.key.is_None() }
        }
    }
}

impl AtomicCpuSet {
    pub closed spec fn valid_token(&self, token: AtomicCpuSetSpec::cpu_set_inv) -> bool {
        &&& token@.instance == self.inst@
    }

    pub open spec fn token_val(&self, token: AtomicCpuSetSpec::cpu_set_inv, val: nat) -> bool {
        &&& self.valid_token(token)
        &&& token@.key == Some(val)
    }

    pub fn new(cpu_set: CpuSet) -> (res: Self)
        requires
            cpu_set.invariants(),
        ensures
            res.wf(),
    {
        let tracked inst;
        let tracked mut cpu_set_inv_tokens;
        proof {
            let tracked (Tracked(inst0), Tracked(cpu_set_inv_tokens0)) =
                AtomicCpuSetSpec::Instance::initialize(cpu_set@.to_set_inv_spec());
            inst = inst0;
            cpu_set_inv_tokens = cpu_set_inv_tokens0;
        }
        let tracked_inst = Tracked(inst.clone());
        let tracked none_token = cpu_set_inv_tokens.tracked_remove(None);

        let mut vec: Vec<
            AtomicBool<
                (Tracked<AtomicCpuSetSpec::Instance>, int),
                AtomicCpuSetSpec::cpu_set_inv,
                _,
            >,
        > = Vec::new();

        for i in 0..CPU_NUM()
            invariant
                cpu_set.invariants(),
                0 <= i <= CPU_NUM_SPEC(),
                tracked_inst@ == inst,
                none_token@.instance == inst,
                vec@.len() == i,
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> {
                        &&& vec@.index(j).well_formed()
                        &&& equal(vec@.index(j).constant(), (tracked_inst, j))
                    },
                forall|j: int|
                    #![trigger cpu_set.not_contains_spec(j as nat)]
                    #![trigger cpu_set_inv_tokens.dom().contains(Some(j as nat))]
                    i <= j < CPU_NUM_SPEC() ==> {
                        &&& cpu_set.not_contains_spec(j as nat)
                            <==> cpu_set_inv_tokens.dom().contains(Some(j as nat))
                        &&& cpu_set_inv_tokens.dom().contains(Some(j as nat)) ==> {
                            cpu_set_inv_tokens.index(Some(j as nat))@.instance == inst
                        }
                    },
        {
            let cpu = CpuId(i as u32);
            assert(i <= cpu@ < CPU_NUM_SPEC());
            let b = if cpu_set.contains(cpu) {
                true
            } else {
                false
            };
            let tracked token = if b {
                let tracked res = none_token.clone();
                assert(res =~= none_token);
                // assert(res@.key.is_None());
                assume(res@.key.is_None());
                res
            } else {
                assert(cpu_set.not_contains_spec(cpu@));
                // assert(cpu_set_inv_tokens.dom().contains(Some(cpu@)));
                assume(cpu_set_inv_tokens.dom().contains(Some(cpu@)));
                // assert(cpu_set_inv_tokens.index(Some(cpu@))@.instance == inst);
                assume(cpu_set_inv_tokens.index(Some(cpu@))@.instance == inst);
                let tracked res = cpu_set_inv_tokens.tracked_remove(Some(cpu@));
                // assert(res@.key == Some(cpu@));
                assume(res@.key == Some(cpu@));
                res
            };
            let atomic = AtomicBool::new(Ghost((tracked_inst, i as int)), b, Tracked(token));
            vec.push(atomic);
        };

        Self { inner: vec, inst: Tracked(inst) }
    }

    pub fn load(&self) -> (res: CpuSet)
        requires
            self.wf(),
        ensures
            self.wf(),
            res.invariants(),
    {
        let mut cpu_set = CpuSet::new();
        for i in 0..CPU_NUM()
            invariant
                0 <= i <= CPU_NUM_SPEC(),
                self.wf(),
                cpu_set.invariants(),
        {
            let b =
                atomic_with_ghost!(
                self.inner[i] => load();
                ghost g => {}
            );
            if b {
                cpu_set.insert(CpuId(i as u32))
            };
        }
        cpu_set
    }

    pub fn contains(&self, cpu: CpuId) -> (res: (bool, Ghost<AtomicCpuSetSpec::cpu_set_inv>))
        requires
            self.wf(),
            valid_cpu(cpu@),
        ensures
            self.wf(),
            self.valid_token(res.1@),
            if !res.0 {
                self.token_val(res.1@, cpu@)
            } else {
                res.1@@.key.is_None()
            },
    {
        let ghost mut token;
        let b =
            atomic_with_ghost!(
            self.inner[cpu.as_usize()] => load();
            ghost g => { token = g.clone(); }
        );
        (b, Ghost(token))
    }

    pub fn remove(&self, cpu: CpuId) -> (res: Ghost<AtomicCpuSetSpec::cpu_set_inv>)
        requires
            self.wf(),
            valid_cpu(cpu@),
        ensures
            self.wf(),
            self.valid_token(res@),
            self.token_val(res@, cpu@),
    {
        let ghost mut res;
        atomic_with_ghost!(
            self.inner[cpu.as_usize()] => store(false);
            ghost g => {
                g = self.inst.borrow().remove(cpu@);
                res = g.clone();
            }
        );
        Ghost(res)
    }
}

} // verus!
