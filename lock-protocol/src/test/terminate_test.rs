use vstd::prelude::*;

verus! {

pub open spec fn rc_greater_or_equal(nid: nat, rc: nat, cursors: Set<int>) -> bool
    recommends
        cursors.finite(),
    decreases cursors.len(),
{
    if (cursors.finite()) {
        if rc == 0 {
            false
        } else if cursors.len() == 0 {
            true
        } else {
            let cursor = cursors.choose();
            if (nid > 100) {
                rc_greater_or_equal(nid, rc, cursors.remove(cursor))
            } else {
                rc_greater_or_equal(nid, (rc - 1) as nat, cursors.remove(cursor))
            }
        }
    } else {
        arbitrary()
    }
}

} // verus!
