use vstd::prelude::*;
use vstd::relations::*;

verus! {

/// A function is injective on a domain if it never maps two distinct domain elements to the same image.
pub open spec fn injective_on<A, B>(f: spec_fn(A) -> B, domain: Set<A>) -> bool {
    forall|x: A, y: A|
        #![trigger domain.contains(x), domain.contains(y)]
        domain.contains(x) && domain.contains(y) && f(x) == f(y) ==> x == y
}

/// A function is bijective from `domain` to `codomain`
/// if it is injective on `domain` and its image equals `codomain`.
pub open spec fn bijective_on<A, B>(f: spec_fn(A) -> B, domain: Set<A>, codomain: Set<B>) -> bool {
    injective_on(f, domain) && domain.map(f) =~= codomain
}

/// `g` is a left inverse of `f` on `domain` if `g(f(x)) == x` for all `x` in `domain`,
/// and `f(x)` lies in `codomain`.
pub open spec fn left_inverse_on<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
) -> bool {
    domain.all(|x: A| codomain.contains(f(x)) && g(f(x)) == x)
}

/// `g` is a right inverse of `f` on `codomain` if `f(g(y)) == y` for all `y` in `codomain`,
/// and `g(y)` lies in `domain`.
pub open spec fn right_inverse_on<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
) -> bool {
    codomain.all(|y: B| domain.contains(g(y)) && f(g(y)) == y)
}

/// `g` is a two-sided inverse of `f` if it is both a left and right inverse.
pub open spec fn inverse_on<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
) -> bool {
    left_inverse_on(f, g, domain, codomain) && right_inverse_on(f, g, domain, codomain)
}

/// Constructs a left inverse function `g` of `f` when `f` is injective on `domain`.
/// For each `b` in the image, returns the unique `a` such that `f(a) = b`.
pub open spec fn construct_left_inverse<A, B>(f: spec_fn(A) -> B, domain: Set<A>) -> spec_fn(B) -> A
    recommends
        injective_on(f, domain),
{
    |b: B| choose|a: A| domain.contains(a) && f(a) == b
}

/// Constructs the inverse of a bijective function `f` from `domain` to `codomain`.
/// For each `b` in `codomain`, returns the unique `a` in `domain` such that `f(a) == b`.
pub open spec fn construct_inverse<A, B>(
    f: spec_fn(A) -> B,
    domain: Set<A>,
    codomain: Set<B>,
) -> spec_fn(B) -> A
    recommends
        bijective_on(f, domain, codomain),
{
    |b: B| choose|a: A| domain.contains(a) && f(a) == b
}

/// If `f` is injective on `domain`, then `construct_left_inverse(f, domain)`
/// is a left inverse of `f` on that domain.
/// That is, for all `x ∈ domain`, we have `g(f(x)) == x`.
pub proof fn lemma_construct_left_inverse_sound<A, B>(f: spec_fn(A) -> B, domain: Set<A>)
    requires
        injective_on(f, domain),
    ensures
        left_inverse_on(f, construct_left_inverse(f, domain), domain, domain.map(f)),
{
}

/// If `f` is bijective from `domain` to `codomain`, then `construct_inverse(f, domain, codomain)`
/// is a two-sided inverse of `f` on that domain and codomain.
/// That is, for all `x ∈ domain`, we have `g(f(x)) == x` and for all `y ∈ codomain`, we have `f(g(y)) == y`.
pub proof fn lemma_construct_inverse_sound<A, B>(
    f: spec_fn(A) -> B,
    domain: Set<A>,
    codomain: Set<B>,
)
    requires
        bijective_on(f, domain, codomain),
    ensures
        inverse_on(f, construct_inverse(f, domain, codomain), domain, codomain),
{
}

/// A function is injective on the whole type implies that it is injective on any sub-domain.
pub proof fn lemma_injective_implies_injective_on<T, U>(f: spec_fn(T) -> U, dom: Set<T>)
    requires
        injective(f),
    ensures
        injective_on(f, dom),
{
}

/// If `f` has a two-sided inverse `g` on `domain` and `codomain`, then `f` is bijective on that domain and codomain.
pub proof fn lemma_two_sided_inverse_implies_bijective<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
)
    requires
        inverse_on(f, g, domain, codomain),
    ensures
        bijective_on(f, domain, codomain),
{
}

/// If `f` is a bijection from `domain` to `codomain`, and `g` is its left inverse,
/// then `g` is a bijection from `codomain` to `domain`.
pub proof fn lemma_left_inverse_of_bijection_is_bijective<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
)
    requires
        bijective_on(f, domain, codomain),
        left_inverse_on(f, g, domain, codomain),
    ensures
        bijective_on(g, codomain, domain),
{
}

/// If `f` is a bijection from `domain` to `codomain`, and `g` is its right inverse,
/// then `g` is a bijection from `codomain` to `domain`.
pub proof fn lemma_right_inverse_of_bijection_is_bijective<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
)
    requires
        bijective_on(f, domain, codomain),
        right_inverse_on(f, g, domain, codomain),
    ensures
        bijective_on(g, codomain, domain),
{
    // Prove that g is injective on codomain
    assert forall|x| #[trigger] codomain.map(g).contains(x) == domain.contains(x) by {
        if domain.contains(x) {
            assert(codomain.contains(f(x)));
        }
    }
}

/// If `f` is a bijection from `domain` to `codomain`, and `g` is either its left or right inverse,
/// then `g` is a bijection from `codomain` to `domain`.
pub proof fn lemma_inverse_of_bijection_is_bijective<A, B>(
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
    domain: Set<A>,
    codomain: Set<B>,
)
    requires
        bijective_on(f, domain, codomain),
        left_inverse_on(f, g, domain, codomain) || right_inverse_on(f, g, domain, codomain),
    ensures
        bijective_on(g, codomain, domain),
{
    if left_inverse_on(f, g, domain, codomain) {
        lemma_left_inverse_of_bijection_is_bijective(f, g, domain, codomain);
    } else {
        lemma_right_inverse_of_bijection_is_bijective(f, g, domain, codomain);
    }
}

/// Mapping a finite set with an injective function results in a set of the same cardinality.
pub proof fn lemma_injective_map_cardinality<T, U>(f: spec_fn(T) -> U, dom: Set<T>, s: Set<T>)
    requires
        injective_on(f, dom),
        s.finite(),
        s <= dom,
    ensures
        s.len() == s.map(f).len(),
        s.map(f).finite(),
    decreases s.len(),
{
    if s.is_empty() {
        assert(s.map(f) =~= Set::empty());
    } else {
        let x = s.choose();
        lemma_injective_map_cardinality(f, dom, s.remove(x));
        assert(s.map(f) =~= s.remove(x).map(f).insert(f(x)));
    }
}

pub proof fn lemma_bijective_cardinality<A, B>(f: spec_fn(A) -> B, domain: Set<A>, codomain: Set<B>)
    requires
        bijective_on(f, domain, codomain),
        domain.finite(),
    ensures
        codomain.finite(),
        domain.len() == codomain.len(),
{
    lemma_injective_map_cardinality(f, domain, domain);
}

pub proof fn lemma_bijective_subset_still_bijective<A, B>(
    f: spec_fn(A) -> B,
    domain: Set<A>,
    codomain: Set<B>,
    s: Set<A>,
)
    requires
        bijective_on(f, domain, codomain),
        s <= domain,
    ensures
        bijective_on(f, s, s.map(f)),
{
}

} // verus!
