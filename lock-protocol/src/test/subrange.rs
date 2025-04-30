use vstd::{assert_seqs_equal, prelude::*};

verus! {

proof fn two(s: Seq<usize>, b: Seq<usize>, i: usize, j: usize)
    requires
        s.len() == b.len(),
        s.len() > 0,
        0 < i < j < s.len(),
{
    assume(s.subrange(0, j as _) =~= b.subrange(0, j as _));
    assert_seqs_equal!(s.subrange(0, i as _) == b.subrange(0, i as _), idx => {
            assert(s.subrange(0, i as _)[idx] == s.subrange(0, j as _)[idx]);
            assert(b.subrange(0, i as _)[idx] == s.subrange(0, j as _)[idx]);
        });
    // subrange_eq_implies_elements_eq(s, b, 0, j as int, 0, j as int);
    // assert(s.subrange(0, i as _) =~= b.subrange(0, i as _));
}

proof fn subrange_eq_implies_elements_eq<A>(
    s1: Seq<A>,
    s2: Seq<A>,
    j1: int,
    k1: int,
    j2: int,
    k2: int,
)
    requires
        0 <= j1 <= k1 <= s1.len(),
        0 <= j2 <= k2 <= s2.len(),
        s1.subrange(j1, k1) =~= s2.subrange(j2, k2),
    ensures
        k1 - j1 == k2 - j2,
        forall|i: int| 0 <= i < k1 - j1 ==> #[trigger] s1[i + j1] == s2[i + j2],
{
    let sub1 = s1.subrange(j1, k1);
    let sub2 = s2.subrange(j2, k2);

    assert(sub1 =~= sub2);
    assert(sub1.len() == sub2.len());

    assert forall|i: int| 0 <= i < sub1.len() implies {
        sub1[i] == sub2[i] && sub1[i] == s1[i + j1] && sub2[i] == s2[i + j2] && #[trigger] s1[i
            + j1] == s2[i + j2]
    } by {
        assert(sub1[i] == sub2[i]);
        assert(i + j1 < s1.len());
        assert(i + j2 < s2.len());
        assert(sub1[i] == s1[i + j1]);
        assert(sub2[i] == s2[i + j2]);
    }
}

} // verus!
