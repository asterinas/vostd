//! Extra properties of [`vstd::seq::Seq`](https://verus-lang.github.io/verus/verusdoc/vstd/seq/struct.Seq.html).
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

/// Splits a tracked sequence at position `n`, leaving `[0, n)` in `s`
/// and returning `[n, len)`.
pub proof fn seq_tracked_split_at<T>(tracked s: &mut Seq<T>, n: int) -> (tracked result: Seq<T>)
    requires
        0 <= n <= old(s).len(),
    ensures
        *final(s) == old(s).subrange(0, n),
        result == old(s).subrange(n, old(s).len() as int),
    decreases old(s).len() - n,
{
    if n == s.len() {
        Seq::tracked_empty()
    } else {
        let ghost orig = *s;
        let tracked last = s.tracked_pop();
        let tracked mut result = seq_tracked_split_at(s, n);
        result.tracked_push(last);
        result
    }
}

pub broadcast proof fn lemma_seq_add_head_back<T>(s: Seq<T>)
    requires
        s.len() > 0,
    ensures
        s == #[trigger] seq![s[0]].add(s.drop_first()),
{
}

pub broadcast proof fn lemma_seq_push_head<T>(s: Seq<T>, hd: T)
    ensures
        #[trigger] seq![hd].add(s) == s.reverse().push(hd).reverse(),
{
}

pub broadcast proof fn lemma_seq_drop_pushed_head<T>(s: Seq<T>, hd: T)
    ensures
        #[trigger] seq![hd].add(s).drop_first() == s,
{
}

pub broadcast proof fn lemma_seq_push_head_take_head<T>(s: Seq<T>, hd: T)
    ensures
        #[trigger] seq![hd].add(s)[0] == hd,
{
}

} // verus!
verus! {

/// The result of pushing element `needle` into the sequence `s` contains `needle`.
pub proof fn lemma_push_contains_same<T>(s: Seq<T>, needle: T)
    ensures
        #[trigger] s.push(needle).contains(needle),
{
    assert(s.push(needle).last() == needle);
}

/// If element `needle` is different from `new_elem`, then whether the sequence `s` contains `needle`
/// after pushing `new_elem` depends on whether `s` contains `needle` before the push.
pub proof fn lemma_push_contains_different<T>(s: Seq<T>, new_elem: T, needle: T)
    requires
        new_elem != needle,
    ensures
        #[trigger] s.push(new_elem).contains(needle) == s.contains(needle),
{
    if s.contains(needle) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == needle;
        lemma_seq_push_index_different(s, needle, i);
        assert(0 <= i < s.push(new_elem).len() && s.push(new_elem)[i] == needle);
    }
}

/// If the last element of the sequence `s` is different from `needle`, then whether the sequence
/// `s` contains `needle` after dropping the last element depends on whether `s` contains `needle`
/// before the drop.
pub proof fn lemma_drop_last_contains_different<T>(s: Seq<T>, needle: T)
    requires
        s.len() > 0,
        s.last() != needle,
    ensures
        #[trigger] s.drop_last().contains(needle) == s.contains(needle),
{
    if s.contains(needle) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == needle;
        assert(0 <= i < s.drop_last().len() && s.drop_last()[i] == needle);
    }
}

} // verus!
verus! {

/// Returns true if predicate `f(i,seq[i])` holds for all indices `i`.
pub open spec fn forall_seq<T>(seq: Seq<T>, f: spec_fn(int, T) -> bool) -> bool {
    forall|i| #![trigger seq[i]] 0 <= i < seq.len() ==> f(i, seq[i])
}

pub broadcast group group_forall_seq_lemmas {
    lemma_forall_seq_push,
    lemma_seq_all_push,
    lemma_forall_seq_drop_last,
    lemma_seq_all_drop_last,
    lemma_seq_all_add,
    lemma_seq_all_index,
}

/// Index `i` of the sequence `s` satisfies `f(i,s[i])` if `forall_seq(s,f)` holds.
pub proof fn lemma_forall_seq_index<T>(s: Seq<T>, f: spec_fn(int, T) -> bool, i: int)
    requires
        forall_seq(s, f),
        0 <= i < s.len(),
    ensures
        f(i, s[i]),
{
}

/// Index `i` of the sequence `s` satisfies `f(s[i])` if `s.all(f)` holds.
/// This proof is required due to the change of trigger by replacing the original `forall_seq_values` with `Seq::all`.
pub broadcast proof fn lemma_seq_all_index<T>(s: Seq<T>, f: spec_fn(T) -> bool, i: int)
    requires
        0 <= i < s.len(),
        #[trigger] s.all(f),
    ensures
        f(#[trigger] (s[i])),
{
}

/// `forall_seq(s.push(v),f)` is equivalent to `forall_seq(s,f)` and `f(s.len(),v)`.
pub broadcast proof fn lemma_forall_seq_push<T>(s: Seq<T>, f: spec_fn(int, T) -> bool, v: T)
    ensures
        forall_seq(s, f) && f(s.len() as int, v) <==> #[trigger] forall_seq(s.push(v), f),
{
    if forall_seq(s.push(v), f) {
        assert forall|i| 0 <= i < s.len() implies f(i, s[i]) by {
            assert(s[i] == s.push(v)[i]);
        }
        assert(s.push(v)[s.len() as int] == v);
    }
}

/// s.push(v).all(f)` is equivalent to `s.all(f)` and `f(v)`.
pub broadcast proof fn lemma_seq_all_push<T>(s: Seq<T>, f: spec_fn(T) -> bool, v: T)
    ensures
        #[trigger] s.push(v).all(f) <==> s.all(f) && f(v),
{
    if s.push(v).all(f) {
        assert forall|i| 0 <= i < s.len() implies f(s[i]) by {
            assert(s[i] == s.push(v)[i]);
        }
        assert(s.push(v)[s.len() as int] == v);
    }
}

/// `forall_seq(s,f)` is equivalent to `forall_seq(s.drop_last(),f)` and `f(s.len() as int - 1, s.last())`.
pub broadcast proof fn lemma_forall_seq_drop_last<T>(s: Seq<T>, f: spec_fn(int, T) -> bool)
    requires
        s.len() > 0,
    ensures
        forall_seq(s, f) <==> #[trigger] forall_seq(s.drop_last(), f) && f(
            s.len() as int - 1,
            s.last(),
        ),
{
    assert(s == s.drop_last().push(s.last()));
}

/// `s.all(f)` is equivalent to `s.drop_last().all(f)` and `f(s.last())`.
pub broadcast proof fn lemma_seq_all_drop_last<T>(s: Seq<T>, f: spec_fn(T) -> bool)
    requires
        s.len() > 0,
    ensures
        s.all(f) <==> #[trigger] s.drop_last().all(f) && f(s.last()),
{
    assert(s == s.drop_last().push(s.last()));
}

pub broadcast proof fn lemma_seq_all_add<T>(s1: Seq<T>, s2: Seq<T>, f: spec_fn(T) -> bool)
    ensures
        s1.all(f) && s2.all(f) <==> #[trigger] (s1 + s2).all(f),
    decreases s2.len(),
{
    if s2.len() == 0 {
        assert(s1 + s2 == s1);
    } else {
        lemma_seq_all_add(s1, s2.drop_last(), f);
        if s1.all(f) && s2.all(f) {
            assert((s1 + s2).all(f));
        }
        if (s1 + s2).all(f) {
            assert((s1 + s2).drop_last() == s1 + s2.drop_last());
            assert(s2 == s2.drop_last().push(s2.last()));
            assert((s1 + s2).last() == s2.last());
        }
    }
}

/// If `source1` and `source2` are prefixes of `child`, then either `source1` is equal to `source2` or
/// one of them is a prefix of the other.
pub proof fn lemma_prefix_of_common_sequence(source1: Seq<nat>, source2: Seq<nat>, child: Seq<nat>)
    requires
        source1.is_prefix_of(child),
        source2.is_prefix_of(child),
    ensures
        source1 == source2 || source1.len() < source2.len() && source1.is_prefix_of(source2)
            || source2.len() < source1.len() && source2.is_prefix_of(source1),
{
}

pub broadcast proof fn lemma_seq_to_set_map_contains<T, U>(s: Seq<T>, f: spec_fn(T) -> U, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #![trigger s.map_values(f), s[i]]
        (s.map_values(f)).to_set().contains(f(s[i])),
{
    assert(s.contains(s[i]));
    assert(f(s[i]) == s.map_values(f)[i]);
}

pub broadcast group group_seq_extra_lemmas {
    lemma_seq_add_head_back,
    lemma_seq_push_head,
    lemma_seq_drop_pushed_head,
    lemma_seq_push_head_take_head,
    lemma_seq_to_set_map_contains,
}

} // verus!
verus! {

/// The index of the first `false` bit in `s`, or `s.len()` if every bit is `true`.
pub open spec fn is_first_zero(s: Seq<bool>, i: int) -> bool {
    &&& 0 <= i <= s.len()
    &&& (forall|j: int| #![trigger s[j]] 0 <= j < i ==> s[j])
    &&& (i < s.len() ==> !s[i])
}

/// Index of the first `false` bit, or `s.len()` if every bit is `true`. Defined
/// recursively so it is deterministic and the SMT solver can unfold it.
pub open spec fn first_zero_index(s: Seq<bool>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if !s[0] {
        0
    } else {
        1 + first_zero_index(s.subrange(1, s.len() as int))
    }
}

/// `is_first_zero` is uniquely satisfied.
pub proof fn lemma_is_first_zero_unique(s: Seq<bool>, i: int, j: int)
    requires
        is_first_zero(s, i),
        is_first_zero(s, j),
    ensures
        #![auto]
        i == j,
{
}

/// `first_zero_index(s)` itself satisfies `is_first_zero` (induction on `s.len()`).
pub proof fn lemma_first_zero_index_is_first_zero(s: Seq<bool>)
    ensures
        is_first_zero(s, first_zero_index(s)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else if !s[0] {
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_first_zero_index_is_first_zero(sub);
        let i2 = first_zero_index(sub);
        assert(is_first_zero(s, 1 + i2)) by {
            assert forall|j: int| 0 <= j < 1 + i2 implies s[j] by {
                if j == 0 {
                } else {
                    assert(s[j] == sub[j - 1]);
                }
            }
            if 1 + i2 < s.len() {
            }
        }
    }
}

/// If the prefix `[0, k)` of `s` is all `true`, then the first zero of `s` is
/// `k` plus the first zero of the remainder (induction on `s.len()`).
pub proof fn lemma_first_zero_index_after_true_prefix(s: Seq<bool>, k: int)
    requires
        0 <= k <= s.len(),
        forall|j: int| #![trigger s[j]] 0 <= j < k ==> s[j],
    ensures
        first_zero_index(s) == k + first_zero_index(s.subrange(k, s.len() as int)),
    decreases s.len(),
{
    if k == 0 {
        assert(s.subrange(0, s.len() as int) =~= s) by {}
    } else if s.len() == 0 {
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_first_zero_index_after_true_prefix(sub, k - 1);
        assert(sub.subrange(k - 1, sub.len() as int) =~= s.subrange(k, s.len() as int)) by {}
    }
}

/// Setting the bit at `k - 1` (the current first zero) to `true`, when the prefix
/// `[0, k - 1)` is all `true`, advances the first zero to
/// `k + first_zero_index(s.subrange(k, len))`.
pub proof fn lemma_first_zero_index_advance_after_set(s: Seq<bool>, k: int)
    requires
        0 < k <= s.len(),
        is_first_zero(s, k - 1),
    ensures
        first_zero_index(s.update(k - 1, true)) == k + first_zero_index(
            s.subrange(k, s.len() as int),
        ),
{
    let t = s.update(k - 1, true);
    lemma_first_zero_index_after_true_prefix(t, k);
    assert(t.subrange(k, s.len() as int) =~= s.subrange(k, s.len() as int)) by {}
}

/// Clearing a `true` bit at `i` moves the first zero to `min(first_zero_index(s), i)`.
pub proof fn lemma_first_zero_index_clear(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len(),
        s[i],
    ensures
        first_zero_index(s.update(i, false)) == if first_zero_index(s) <= i {
            first_zero_index(s)
        } else {
            i
        },
    decreases s.len(),
{
    let fz = first_zero_index(s);
    lemma_first_zero_index_is_first_zero(s);
    let t = s.update(i, false);
    lemma_first_zero_index_is_first_zero(t);
    if fz <= i {
        assert(is_first_zero(t, fz)) by {
            if fz < s.len() {
                assert(!t[fz]) by {
                    if fz == i {
                        assert(t[fz] == false);
                    } else {
                        assert(t[fz] == s[fz]);
                        assert(!s[fz]);
                    }
                }
            }
            assert(forall|j: int| 0 <= j < fz ==> t[j]) by {
                assert(forall|j: int| 0 <= j < fz ==> s[j]);
            }
        }
        lemma_is_first_zero_unique(t, first_zero_index(t), fz);
    } else {
        assert(is_first_zero(t, i)) by {
            assert(!t[i]);
            assert(forall|j: int| 0 <= j < i ==> t[j]) by {
                assert(forall|j: int| 0 <= j < i ==> s[j]);
            }
        }
        lemma_is_first_zero_unique(t, first_zero_index(t), i);
    }
}

/// Clearing all bits in `[start, end)` moves the first zero to
/// `min(first_zero_index(s), start)`.
pub proof fn lemma_first_zero_index_clear_range(s: Seq<bool>, t: Seq<bool>, start: int, end: int)
    requires
        s.len() == t.len(),
        0 <= start < end <= s.len(),
        forall|j: int| #![trigger t[j]] 0 <= j < start ==> t[j] == s[j],
        forall|j: int| #![trigger t[j]] start <= j < end ==> !t[j],
        forall|j: int| #![trigger t[j]] end <= j < s.len() ==> t[j] == s[j],
    ensures
        first_zero_index(t) == if first_zero_index(s) <= start {
            first_zero_index(s)
        } else {
            start
        },
{
    let fz = first_zero_index(s);
    lemma_first_zero_index_is_first_zero(s);
    lemma_first_zero_index_is_first_zero(t);
    if fz <= start {
        assert(is_first_zero(t, fz)) by {
            if fz < s.len() {
                assert(!t[fz]) by {
                    if fz < start {
                        assert(t[fz] == s[fz]);
                        assert(!s[fz]);
                    }
                }
            }
            assert(forall|j: int| 0 <= j < fz ==> t[j]) by {
                assert(forall|j: int| 0 <= j < fz ==> s[j]);
                assert(forall|j: int| 0 <= j < fz ==> t[j] == s[j]);
            }
        }
        lemma_is_first_zero_unique(t, first_zero_index(t), fz);
    } else {
        assert(is_first_zero(t, start)) by {
            assert(!t[start]);
            assert(forall|j: int| 0 <= j < start ==> t[j]) by {
                assert(forall|j: int| 0 <= j < start ==> s[j]);
            }
        }
        lemma_is_first_zero_unique(t, first_zero_index(t), start);
    }
}

/// Setting a `false` bit at `i` that is strictly past the first zero leaves the
/// first zero unchanged.
pub proof fn lemma_first_zero_index_set_after_first_zero(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len(),
        first_zero_index(s) < i,
        !s[i],
    ensures
        first_zero_index(s.update(i, true)) == first_zero_index(s),
{
    let fz = first_zero_index(s);
    lemma_first_zero_index_is_first_zero(s);
    let t = s.update(i, true);
    lemma_first_zero_index_is_first_zero(t);
    assert(is_first_zero(t, fz)) by {
        if fz < s.len() {
            assert(!t[fz]) by {
                assert(fz < i);
                assert(t[fz] == s[fz]);
                assert(!s[fz]);
            }
        }
        assert forall|j: int| 0 <= j < fz implies t[j] by {
            assert(t[j] == s[j]);
            assert(s[j]);
        }
    }
    lemma_is_first_zero_unique(t, first_zero_index(t), fz);
}

} // verus!
