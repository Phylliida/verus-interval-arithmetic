use crate::interval::Interval;
use verus_algebra::traits::*;
use verus_rational::Rational;
use vstd::prelude::*;

verus! {

// ── Equivalence ─────────────────────────────────────────────────────

impl Equivalence for Interval {
    open spec fn eqv(self, other: Self) -> bool {
        self.lo.eqv_spec(other.lo) && self.hi.eqv_spec(other.hi)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        Rational::lemma_eqv_reflexive(a.lo);
        Rational::lemma_eqv_reflexive(a.hi);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        Rational::lemma_eqv_symmetric(a.lo, b.lo);
        Rational::lemma_eqv_symmetric(a.hi, b.hi);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        Rational::lemma_eqv_transitive(a.lo, b.lo, c.lo);
        Rational::lemma_eqv_transitive(a.hi, b.hi, c.hi);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        // Note: Interval uses Rational's eqv_spec directly
        // If intervals are equal (==), their lo and hi are equal
    }
}

// ── AdditiveCommutativeMonoid ───────────────────────────────────────

impl AdditiveCommutativeMonoid for Interval {
    open spec fn zero() -> Self {
        Self::from_point_spec(Rational::from_int_spec(0))
    }

    open spec fn add(self, other: Self) -> Self {
        self.add_spec(other)
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        // a.add_spec(b).lo = a.lo + b.lo, and b.add_spec(a).lo = b.lo + a.lo
        // Rational::lemma_add_commutative gives eqv_spec
        Interval::lemma_add_commutative(a, b);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        // Delegates to existing lemma which proves component-wise eqv_spec
        Interval::lemma_add_associative(a, b, c);
    }

    proof fn axiom_add_zero_right(a: Self) {
        // lemma_add_zero_identity gives structural ==, which implies eqv
        Interval::lemma_add_zero_identity(a);
        Rational::lemma_eqv_reflexive(a.lo);
        Rational::lemma_eqv_reflexive(a.hi);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        // a ≡ b means a.lo ≡ b.lo and a.hi ≡ b.hi
        // Need: a+c ≡ b+c, i.e. (a.lo+c.lo) ≡ (b.lo+c.lo) and (a.hi+c.hi) ≡ (b.hi+c.hi)
        Rational::lemma_eqv_add_congruence_left(a.lo, b.lo, c.lo);
        Rational::lemma_eqv_add_congruence_left(a.hi, b.hi, c.hi);
    }
}

// ── PartialOrder ────────────────────────────────────────────────────

impl PartialOrder for Interval {
    open spec fn le(self, other: Self) -> bool {
        other.contains_interval_spec(self)  // self ⊆ other
    }

    proof fn axiom_le_reflexive(a: Self) {
        // a ⊆ a: need a.lo ≤ a.lo and a.hi ≤ a.hi
        // le_spec is reflexive since a.num * a.denom() <= a.num * a.denom()
    }

    proof fn axiom_le_antisymmetric(a: Self, b: Self) {
        // a ⊆ b and b ⊆ a means:
        //   b.lo ≤ a.lo and a.hi ≤ b.hi  (a ⊆ b)
        //   a.lo ≤ b.lo and b.hi ≤ a.hi  (b ⊆ a)
        // So a.lo ≤ b.lo ≤ a.lo → a.lo ≡ b.lo
        // And a.hi ≤ b.hi ≤ a.hi → a.hi ≡ b.hi
        Rational::lemma_le_antisymmetric(a.lo, b.lo);
        Rational::lemma_le_antisymmetric(a.hi, b.hi);
    }

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {
        // a ⊆ b ⊆ c: delegates to existing lemma
        // a.le(b) = b ⊇ a, b.le(c) = c ⊇ b, need c ⊇ a
        Interval::lemma_contains_interval_transitive(a, b, c);
    }

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {
        // a1 ≡ a2, b1 ≡ b2, a1 ⊆ b1 → a2 ⊆ b2
        // a1 ⊆ b1 means b1.lo ≤ a1.lo and a1.hi ≤ b1.hi
        // Need: b2.lo ≤ a2.lo and a2.hi ≤ b2.hi
        //
        // a1.lo ≡ a2.lo: from a1 ≡ a2
        // b1.lo ≡ b2.lo: from b1 ≡ b2
        //
        // b1.lo ≤ a1.lo, b1.lo ≡ b2.lo, a1.lo ≡ a2.lo → b2.lo ≤ a2.lo
        // Use: eqv_symmetric on b1.lo/b2.lo, then eqv_implies_le to get b2.lo ≤ b1.lo,
        // then transitivity b2.lo ≤ b1.lo ≤ a1.lo, then eqv_implies_le a1.lo ≤ a2.lo,
        // then transitivity b2.lo ≤ a2.lo

        // For lo: b2.lo ≤ a2.lo
        Rational::lemma_eqv_symmetric(b1.lo, b2.lo);
        Rational::lemma_eqv_implies_le(b2.lo, b1.lo);
        Rational::lemma_le_transitive(b2.lo, b1.lo, a1.lo);
        Rational::lemma_eqv_implies_le(a1.lo, a2.lo);
        Rational::lemma_le_transitive(b2.lo, a1.lo, a2.lo);

        // For hi: a2.hi ≤ b2.hi
        Rational::lemma_eqv_symmetric(a1.hi, a2.hi);
        Rational::lemma_eqv_implies_le(a2.hi, a1.hi);
        Rational::lemma_le_transitive(a2.hi, a1.hi, b1.hi);
        Rational::lemma_eqv_implies_le(b1.hi, b2.hi);
        Rational::lemma_le_transitive(a2.hi, b1.hi, b2.hi);
    }
}

} // verus!
