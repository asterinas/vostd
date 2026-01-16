//! This module defines a reference counting PCM with authority and tokens.
//!
//! Authority can produce new tokens and tracks how many are outstanding.
//! Tokens can be returned to authority or combined.
use vstd::pcm::PCM;
use vstd::prelude::*;

verus! {

/// A reference-counting PCM with authority and tokens.
#[verifier::ext_equal]
pub tracked enum CountR {
    /// Unit element with no actual meaning.
    Unit,
    /// Authority: tracks how many tokens have been minted
    Auth(nat),
    /// Token: represents one reference
    Token,
    /// Combination of tokens
    Tokens(nat),
    /// Invalid state
    Invalid,
}

impl PCM for CountR {
    open spec fn valid(self) -> bool {
        self !is Invalid
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            // Unit is identity element
            (CountR::Unit, x) | (x, CountR::Unit) => x,
            // Token combinations
            (CountR::Token, CountR::Token) => CountR::Tokens(2),
            (CountR::Token, CountR::Tokens(n))
            | (CountR::Tokens(n), CountR::Token) => CountR::Tokens(n + 1),
            (CountR::Tokens(n1), CountR::Tokens(n2)) => CountR::Tokens(n1 + n2),
            // Auth reclaims tokens: Auth(n) + Token -> Auth(n-1) 
            (CountR::Auth(n), CountR::Token) | (CountR::Token, CountR::Auth(n)) => {
                if n > 0 { CountR::Auth((n - 1) as nat) } else { CountR::Invalid }
            },
            // Auth reclaims multiple tokens: Auth(n) + Tokens(m) -> Auth(n-m)
            (CountR::Auth(n), CountR::Tokens(m)) | (CountR::Tokens(m), CountR::Auth(n)) => {
                if n >= m { CountR::Auth((n - m) as nat) } else { CountR::Invalid }
            },
            // Invalid combinations (Auth + Auth)
            _ => CountR::Invalid,
        }
    }

    open spec fn unit() -> Self {
        CountR::Unit
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

} // verus!
