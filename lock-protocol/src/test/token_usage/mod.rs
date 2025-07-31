mod common;
mod exec_nid;
mod spin_lock;

use std::collections::HashMap;

use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::hash_map::*;
use vstd::tokens::*;

use super::super::spec::{common::*, utils::*, concrete_tree_spec::ConcreteSpec};

use common::*;
use spin_lock::*;
use exec_nid::*;

verus! {

// Configurations
pub spec const GLOBAL_CPU_NUM: nat = 2;

type NodeToken = ConcreteSpec::nodes;

type CursorToken = ConcreteSpec::cursors;

pub tracked struct CursorModel {
    pub ghost cpu: CpuId,
    pub tracked token: CursorToken,
    pub tracked inst: ConcreteSpec::Instance,
}

impl CursorModel {
    pub open spec fn inv(&self) -> bool {
        &&& valid_cpu(GLOBAL_CPU_NUM, self.cpu)
        &&& self.inst.cpu_num() == GLOBAL_CPU_NUM
        &&& self.token.instance_id() == self.inst.id()
        &&& self.token.key() == self.cpu
    }

    pub open spec fn pred_cursor_Empty(&self) -> bool {
        self.token.value().is_Empty()
    }

    pub open spec fn relate_state_Empty(&self, state: CursorState) -> bool {
        &&& state.is_Empty()
        &&& self.pred_cursor_Empty()
    }

    pub open spec fn pred_cursor_Creating(&self, st: NodeId, en: NodeId, cur_nid: NodeId) -> bool {
        let state = self.token.value();
        {
            &&& state.is_Creating()
            &&& st == state.get_Creating_0()
            &&& en == state.get_Creating_1()
            &&& cur_nid == state.get_Creating_2()
        }
    }

    pub open spec fn relate_state_Creating(&self, state: CursorState) -> bool {
        &&& state.is_Creating()
        &&& self.pred_cursor_Creating(
            state.get_Creating_0(),
            state.get_Creating_1(),
            state.get_Creating_2(),
        )
    }

    pub open spec fn pred_cursor_Hold(&self, st: NodeId, en: NodeId) -> bool {
        let state = self.token.value();
        {
            &&& state.is_Hold()
            &&& st == state.get_Hold_0()
            &&& en == state.get_Hold_1()
        }
    }

    pub open spec fn relate_state_Hold(&self, state: CursorState) -> bool {
        &&& state.is_Hold()
        &&& self.pred_cursor_Hold(state.get_Hold_0(), state.get_Hold_1())
    }

    pub open spec fn pred_cursor_Destroying(
        &self,
        st: NodeId,
        en: NodeId,
        cur_nid: NodeId,
    ) -> bool {
        let state = self.token.value();
        {
            &&& state.is_Destroying()
            &&& st == state.get_Destroying_0()
            &&& en == state.get_Destroying_1()
            &&& cur_nid == state.get_Destroying_2()
        }
    }

    pub open spec fn relate_state_Destroying(&self, state: CursorState) -> bool {
        &&& state.is_Destroying()
        &&& self.pred_cursor_Destroying(
            state.get_Destroying_0(),
            state.get_Destroying_1(),
            state.get_Destroying_2(),
        )
    }

    pub open spec fn relate_state(&self, state: CursorState) -> bool {
        match state {
            CursorState::Empty => self.relate_state_Empty(state),
            CursorState::Creating(_, _, _) => self.relate_state_Creating(state),
            CursorState::Hold(_, _) => self.relate_state_Hold(state),
            CursorState::Destroying(_, _, _) => self.relate_state_Destroying(state),
        }
    }

    pub proof fn new(
        cpu: CpuId,
        tracked token: CursorToken,
        tracked inst: ConcreteSpec::Instance,
    ) -> (tracked s: Self)
        requires
            valid_cpu(GLOBAL_CPU_NUM, cpu),
            inst.cpu_num() == GLOBAL_CPU_NUM,
            token.instance_id() == inst.id(),
            token.key() == cpu,
        ensures
            s.cpu == cpu,
            s.token =~= token,
            s.inst =~= inst,
            s.inv(),
    {
        Self { cpu, token, inst }
    }
}

pub struct FrameAllocater;

impl FrameAllocater {
    pub fn allocate() -> Paddr {
        0
    }
}

pub struct Page {
    pub paddr: Paddr,
    pub lock: PageLock,
}

impl Page {
    pub open spec fn inv(&self) -> bool {
        &&& valid_paddr(self.paddr)
        // &&& self.lock.paddr == self.paddr

    }

    pub open spec fn valid_perm(&self, perm: &PagePerm) -> bool {
        self.paddr == perm.paddr
    }

    fn new(paddr: Paddr) -> (res: Self)
        requires
            valid_paddr(paddr),
        ensures
            res.inv(),
    {
        let tracked perm = PagePerm { paddr };
        let lock = PageLock::new(paddr, Tracked(perm));

        Self { paddr, lock }
    }

    pub open spec fn offset_aligned(offset: Paddr) -> bool {
        true
    }

    pub fn read_u64(&self, offset: Paddr, perm: &PagePerm) -> u64
        requires
            self.inv(),
            Self::offset_aligned(offset),
            self.valid_perm(perm),
    {
        0
    }

    pub fn write_u64(&self, offset: Paddr, val: u64, perm: Tracked<PagePerm>) -> (res: Tracked<
        PagePerm,
    >)
        requires
            self.inv(),
            Self::offset_aligned(offset),
            self.valid_perm(&perm@),
        ensures
            res =~= perm,
    {
        perm
    }
}

pub tracked struct NodeTokenManagement {
    pub ghost nid: NodeId,
    pub ghost childs: Seq<Option<()>>,
    pub tracked tokens: Map<NodeId, NodeToken>,
    pub tracked inst: ConcreteSpec::Instance,
}

impl NodeTokenManagement {
    pub open spec fn inv(&self) -> bool {
        &&& NodeHelper::valid_nid(self.nid)
        &&& self.childs.len() == 512
        &&& forall|nid: NodeId|
            self.tokens.dom().contains(nid) ==> self.tokens[nid].instance_id() == self.inst.id()
        &&& self.inst.cpu_num() == GLOBAL_CPU_NUM
    }

    pub proof fn node_acquire(
        tracked &mut self,
        tracked model: CursorModel,
        state: CursorState,
    ) -> (tracked res: (CursorModel, CursorState))
        requires
            old(self).inv(),
            model.inv(),
            model.relate_state_Creating(state),
            old(self).nid == state.get_Creating_2(),
            old(self).nid < state.get_Creating_1(),
            old(self).inst.id() == model.inst.id(),
        ensures
            self.inv(),
            res.0.inv(),
            res.1 =~= state.trans_node_acquire(self.nid),
            res.0.relate_state_Creating(res.1),
            self.inst.id() == res.0.inst.id(),
    {
        assert(self.tokens.dom().contains(self.nid)) by { admit() };
        let tracked node_token = self.tokens.tracked_remove(self.nid);
        assert(node_token.value().is_Free()) by { admit() };
        let tracked cursor_token = model.token;
        let tracked (Tracked(new_node_token), Tracked(new_cursor_token)) = self.inst.node_acquire(
            model.cpu,
            self.nid,
            node_token,
            cursor_token,
        );
        self.tokens.tracked_insert(self.nid, new_node_token);
        (
            CursorModel::new(model.cpu, new_cursor_token, model.inst),
            state.trans_node_acquire(self.nid),
        )
    }

    pub proof fn node_acquire_skip(
        tracked &mut self,
        child: NodeId,
        tracked model: CursorModel,
        state: CursorState,
    ) -> (tracked res: (CursorModel, CursorState))
        requires
            old(self).inv(),
            NodeHelper::is_child(old(self).nid, child),
            model.inv(),
            model.relate_state_Creating(state),
            child == state.get_Creating_2(),
            child < state.get_Creating_1(),
            old(self).inst.id() == model.inst.id(),
        ensures
            self.inv(),
            res.0.inv(),
            res.1 =~= state.trans_node_acquire_skip(child),
            res.0.relate_state_Creating(res.1),
            self.inst.id() == model.inst.id(),
    {
        let ghost subtree: Set<NodeId> = Set::new(|nid: NodeId| NodeHelper::in_subtree(child, nid));
        assert(subtree.subset_of(self.tokens.dom())) by { admit() };
        let tracked node_tokens = MapToken::from_map(
            self.inst.id(),
            self.tokens.tracked_remove_keys(subtree),
        );
        assert(forall|nid| node_tokens.dom().contains(nid) ==> node_tokens.map()[nid].is_Empty())
            by { admit() };
        let tracked cursor_token = model.token;
        let tracked (Tracked(new_node_tokens), Tracked(new_cursor_token)) =
            self.inst.node_acquire_skip(model.cpu, child, node_tokens, cursor_token);
        let tracked new_node_tokens = new_node_tokens.into_map();
        self.tokens.tracked_union_prefer_right(new_node_tokens);
        (
            CursorModel::new(model.cpu, new_cursor_token, model.inst),
            state.trans_node_acquire_skip(child),
        )
    }
}

struct_with_invariants!{

pub struct PageTablePage {
    pub frame_id: u64,
    pub childs: Ghost<Seq<Option<()>>>,
}

}

struct_with_invariants!{

pub struct PageTableNode {
    pub nid: Ghost<NodeId>, // NodeId of this node
    // pub childs: Ghost<Seq<Option<()>>>,
    pub atomic: AtomicU64<_, Option<NodeTokenManagement>, _>,
    pub page: PCell<Option<PageTablePage>>,
}

pub open spec fn wf(&self) -> bool {
    predicate {

    }
}

}

impl PageTableNode {
    pub open spec fn wf(&self) -> bool {
        &&& NodeHelper::valid_nid(self.nid@)
        &&& self.childs@.len() == 512
    }

    // pub open spec fn valid_tokens(
    //     nid: NodeId,
    //     childs: Seq<Option<()>>,
    //     tokens: Map<NodeId, NodeToken>
    // ) -> bool {
    //     &&& forall |_nid| tokens.dom().contains(_nid) <==> {
    //         ||| _nid == nid
    //         ||| exists |offset: nat| #![auto] {
    //             &&& valid_pte_offset(offset)
    //             &&& childs[offset as int].is_None()
    //             &&& NodeHelper::in_subtree(NodeHelper::get_child(nid, offset), _nid)
    //         }
    //     }
    //     &&& tokens[nid].value().is_Free()
    //     &&& forall |_nid| #![auto] _nid != nid && tokens.dom().contains(_nid) ==>
    //         tokens[_nid].value().is_Empty()
    // }
    pub open spec fn relate_manager(&self) -> bool {
        &&& self.nid@ == self.manager@.nid
        &&& self.childs@ =~= self.manager@.childs
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.wf()
        &&& self.relate_manager()
        &&& self.manager@.inv()
        &&& self.page.inv()
    }

    pub open spec fn child_exist(&self, offset: nat) -> bool {
        self.childs@[offset as int].is_Some()
    }

    #[verifier::external_body]
    pub fn new(
        nid: Ghost<NodeId>,
        tracked tokens: Tracked<MapToken<NodeId, NodeState, NodeToken>>,
        page: Page,
    ) -> (res: Self)
        requires
            NodeHelper::valid_nid(nid@),
            page.inv(),
        ensures
            res.inv(),
    {
        unimplemented!();
        // Self {
        //     nid: Ghost(nid@),
        //     childs: Ghost(Seq::new(512, |i| Option::None)),
        //     manager:
        //     page,
        // }
    }
    // pub fn new_from_paddr(nid: Ghost<NodeId>, paddr: Paddr, tracked tokens: Tracked<Map<NodeId, NodeToken>>) -> (res: Self)
    //     requires
    //         NodeHelper::valid_nid(nid@),
    //         valid_paddr(paddr@),
    //         Self::valid_tokens(nid@, Seq::new(512, |i| Option::None), tokens@),
    //     ensures
    //         res.inv(),
    // {
    //     let page = Page::new(paddr);
    //     Self::new(nid, page, Tracked(tokens.get()))
    // }

}

struct_with_invariants!{

pub struct PageTable {
    pub nodes: Vec<PageTableNode>,
    pub locks: Vec<PageLock>,
    pub inst: Tracked<ConcreteSpec::Instance>,
}

pub open spec fn wf(&self) -> bool {
    predicate {

    }
}

}

impl PageTable {
    pub open spec fn wf(&self) -> bool {
        &&& forall|nid: NodeId| self.nodes@.contains_key(nid as u64) ==> NodeHelper::valid_nid(nid)
        &&& self.nodes@.contains_key(NodeHelper::root_id() as u64)
        &&& forall|nid: NodeId|
            #![auto]
            nid != NodeHelper::root_id() && NodeHelper::valid_nid(nid) ==> {
                self.nodes@.contains_key(nid as u64) ==> self.nodes@.contains_key(
                    NodeHelper::get_parent(nid) as u64,
                )
            }
        &&& forall|nid: NodeId|
            NodeHelper::valid_nid(nid) && self.nodes@.contains_key(nid as u64) ==> {
                forall|offset: nat|
                    #![auto]
                    valid_pte_offset(offset) && self.nodes@[nid as u64].child_exist(offset)
                        ==> self.nodes@.contains_key(NodeHelper::get_child(nid, offset) as u64)
            }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.wf()
        &&& forall|nid|
            NodeHelper::valid_nid(nid) && self.nodes@.contains_key(nid as u64)
                ==> self.nodes@[nid as u64].inv()
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }

    #[verifier::external_body]
    pub fn new(
        tracked inst: Tracked<ConcreteSpec::Instance>,
        tracked tokens: Tracked<Map<NodeId, NodeToken>>,
    ) -> (res: Self)
        requires
            forall|nid| #![auto] tokens@.dom().contains(nid) <==> NodeHelper::valid_nid(nid),
            forall|nid|
                #![auto]
                tokens@.dom().contains(nid) ==> {
                    if nid == NodeHelper::root_id() {
                        tokens@[nid].value().is_Free()
                    } else {
                        tokens@[nid].value().is_Empty()
                    }
                },
        ensures
            res.inv(),
    {
        unimplemented!();
        // let rt_paddr = FrameAllocater::allocate();
        // assert(NodeHelper::valid_nid(NodeHelper::root_id())) by {
        //     NodeHelper::lemma_root_id();
        // };
        // assert(PageTableNode::valid_tokens(0, Seq::new(512, |i| Option::None), tokens@)) by { admit(); };
        // let rt_node = PageTableNode::new_from_paddr(
        //     Ghost(NodeHelper::root_id()),
        //     rt_paddr,
        //     Tracked(tokens.get()),
        // );

        // let mut nodes: HashMap<u64, PageTableNode> = HashMap::new();
        // nodes.insert(0, rt_node);

        // let pt = Self { nodes, inst: Tracked(inst.get()) };
        // assert(pt.inv()) by { admit(); };
        // pt
    }

    pub fn dfs_acquire_lock(
        &mut self,
        nid: u64,
        tracked model: Tracked<CursorModel>,
        state: Ghost<CursorState>,
    ) -> (res: (Tracked<CursorModel>, Ghost<CursorState>))
        requires
            old(self).inv(),
            old(self).nodes@.contains_key(nid),
            NodeHelper::valid_nid(nid as NodeId),
            model@.inv(),
            model@.relate_state_Creating(state@),
            old(self).inst@.id() == model@.inst.id(),
        ensures
            res.0@.inv(),
            res.1@ =~= state@.trans_node_acquire_skip(nid as NodeId),
            res.0@.relate_state_Creating(res.1@),
            self.inst@.id() == res.0@.inst.id(),
    {
        let tracked mut model = model.get();
        let ghost mut state = state@;

        let cur_node: &mut PageTableNode = self.nodes.get_mut(&nid).unwrap();
        let guard = cur_node.page.lock.acquire();
        let tracked res = cur_node.manager@.node_acquire(model, state);
        proof {
            model = res.0;
            state = res.1;
        }

        for offset in 0..512
            invariant
                0 <= offset < 512,
                self.inv(),
                NodeHelper::valid_nid(nid as nat),
        {
            assert(valid_pte_offset(offset as nat));
            let child: u64 = NodeHelperExec::get_child_exec(nid, offset);
            if self.nodes.get(&child).is_some() {
                assert(cur_node.child_exist(child as nat));
                let res = self.dfs_acquire_lock(child, Tracked(model), Ghost(state));
                proof {
                    model = res.0.get();
                    state = res.1@;
                }
            } else {
                let tracked res = cur_node.manager@.node_acquire_skip(child as nat, model, state);
                proof {
                    model = res.0;
                    state = res.1;
                }
            }
        }

        (Tracked(model), Ghost(state))
    }

    pub fn cursor_create(
        &mut self,
        nid: u64,
        tracked model: Tracked<CursorModel>,
    ) -> (tracked new_model: Tracked<CursorModel>)
        requires
            old(self).inv(),
            NodeHelper::valid_nid(nid as NodeId),
            model@.inv(),
            model@.relate_state_Empty(CursorState::Empty),
            old(self).inst@.id() == model@.inst.id(),
        ensures
            new_model@.inv(),
            new_model@.relate_state_Hold(
                CursorState::Hold(nid as NodeId, NodeHelper::next_outside_subtree(nid as NodeId)),
            ),
            self.inst@.id() == new_model@.inst.id(),
    {
        let tracked model_start;
        proof {
            let tracked model = model.get();
            let tracked token = model.token;
            let tracked new_token = self.inst.borrow().cursor_create_start(
                model.cpu,
                nid as NodeId,
                token,
            );
            model_start = CursorModel::new(model.cpu, new_token, model.inst);
        }
        let res = self.dfs_acquire_lock(
            nid,
            Tracked(model_start),
            Ghost(
                CursorState::Creating(
                    nid as NodeId,
                    NodeHelper::next_outside_subtree(nid as NodeId),
                    nid as NodeId,
                ),
            ),
        );
        let tracked model_end;
        proof {
            let tracked model = res.0.get();
            let tracked token = model.token;
            let tracked new_token = self.inst.borrow().cursor_create_end(model.cpu, token);
            model_end = CursorModel::new(model.cpu, new_token, model.inst);
        }
        Tracked(model_end)
    }
}

fn test() {
    // Build tokenized state machine
    let tracked inst;
    let tracked nodes_tokens;
    let tracked mut cursors_tokens;
    proof {
        let tracked (Tracked(inst0), Tracked(nodes_tokens0), Tracked(cursors_tokens0)) =
            ConcreteSpec::Instance::initialize(GLOBAL_CPU_NUM);

        inst = inst0;
        nodes_tokens = nodes_tokens0;
        cursors_tokens = cursors_tokens0;
    }
    let tracked_inst: Tracked<ConcreteSpec::Instance> = Tracked(inst.clone());

    assert(nodes_tokens.dom() =~= Set::new(|nid| NodeHelper::valid_nid(nid)));
    assert(cursors_tokens.dom() =~= Set::new(|cpu| valid_cpu(GLOBAL_CPU_NUM, cpu)));

    let tracked cursor_model_0 = CursorModel::new(0, cursors_tokens.remove(0), inst.clone());
    let tracked cursor_model_1 = CursorModel::new(1, cursors_tokens.remove(1), inst.clone());
    assert(cursors_tokens.dom() =~= Set::empty());

    let mut page_table = PageTable::new(tracked_inst, Tracked(nodes_tokens.into_map()));
}

} // verus!
