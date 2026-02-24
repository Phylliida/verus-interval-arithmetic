use vstd::prelude::*;

use verus_rational::Rational;

verus! {

/// Ghost-level closed interval [lo, hi] over rationals.
pub struct Interval {
    pub lo: Rational,
    pub hi: Rational,
}

impl Interval {
    // ── Spec functions ───────────────────────────────────────────

    /// Well-formedness: the interval is non-empty (lo <= hi).
    pub open spec fn wf_spec(self) -> bool {
        self.lo.le_spec(self.hi)
    }

    /// Point containment: lo <= x <= hi.
    pub open spec fn contains_spec(self, x: Rational) -> bool {
        self.lo.le_spec(x) && x.le_spec(self.hi)
    }

    /// Sub-interval containment: self contains other entirely.
    pub open spec fn contains_interval_spec(self, other: Interval) -> bool {
        self.lo.le_spec(other.lo) && other.hi.le_spec(self.hi)
    }

    /// Interval width: hi - lo.
    pub open spec fn width_spec(self) -> Rational {
        self.hi.sub_spec(self.lo)
    }

    /// Interval midpoint: (lo + hi) / 2.
    pub open spec fn midpoint_spec(self) -> Rational {
        Rational::midpoint_spec(self.lo, self.hi)
    }

    /// Degenerate (point) interval: lo and hi represent the same value.
    pub open spec fn is_point_spec(self) -> bool {
        self.lo.eqv_spec(self.hi)
    }

    /// Construct a point interval [x, x] (spec-level).
    pub open spec fn from_point_spec(x: Rational) -> Interval {
        Interval { lo: x, hi: x }
    }

    /// Two intervals overlap (share at least one point).
    pub open spec fn overlap_spec(self, other: Interval) -> bool {
        self.lo.le_spec(other.hi) && other.lo.le_spec(self.hi)
    }

    /// Convex hull: smallest interval containing both self and other.
    pub open spec fn hull_spec(self, other: Interval) -> Interval {
        Interval {
            lo: self.lo.min_spec(other.lo),
            hi: self.hi.max_spec(other.hi),
        }
    }

    /// Intersection: largest interval contained in both self and other.
    /// Returns None if the intervals don't overlap.
    pub open spec fn intersect_spec(self, other: Interval) -> Option<Interval> {
        let lo = self.lo.max_spec(other.lo);
        let hi = self.hi.min_spec(other.hi);
        if lo.le_spec(hi) {
            Option::Some(Interval { lo, hi })
        } else {
            Option::None
        }
    }

    // ── Sign determination & comparison spec functions ──────────

    /// The interval is entirely positive: lo > 0.
    pub open spec fn certainly_positive_spec(self) -> bool {
        Rational::from_int_spec(0).lt_spec(self.lo)
    }

    /// The interval is entirely negative: hi < 0.
    pub open spec fn certainly_negative_spec(self) -> bool {
        self.hi.lt_spec(Rational::from_int_spec(0))
    }

    /// The interval is certainly zero: degenerate point at 0.
    pub open spec fn certainly_zero_spec(self) -> bool {
        self.is_point_spec() && self.lo.eqv_spec(Rational::from_int_spec(0))
    }

    /// The interval is entirely nonneg: lo >= 0.
    pub open spec fn certainly_nonneg_spec(self) -> bool {
        Rational::from_int_spec(0).le_spec(self.lo)
    }

    /// The interval is entirely nonpos: hi <= 0.
    pub open spec fn certainly_nonpos_spec(self) -> bool {
        self.hi.le_spec(Rational::from_int_spec(0))
    }

    /// The interval possibly contains zero: lo <= 0 <= hi.
    pub open spec fn possibly_zero_spec(self) -> bool {
        self.lo.le_spec(Rational::from_int_spec(0))
            && Rational::from_int_spec(0).le_spec(self.hi)
    }

    /// Sign determination: Some(1) if positive, Some(-1) if negative,
    /// Some(0) if certainly zero, None if indeterminate.
    pub open spec fn sign_definite_spec(self) -> Option<i8> {
        if self.certainly_positive_spec() {
            Option::Some(1i8)
        } else if self.certainly_negative_spec() {
            Option::Some(-1i8)
        } else if self.certainly_zero_spec() {
            Option::Some(0i8)
        } else {
            Option::None
        }
    }

    /// self is certainly less than rhs: self.hi < rhs.lo.
    pub open spec fn certainly_lt_spec(self, rhs: Interval) -> bool {
        self.hi.lt_spec(rhs.lo)
    }

    /// self is certainly <= rhs: self.hi <= rhs.lo.
    pub open spec fn certainly_le_spec(self, rhs: Interval) -> bool {
        self.hi.le_spec(rhs.lo)
    }

    /// Both intervals are the same point.
    pub open spec fn certainly_equal_spec(self, rhs: Interval) -> bool {
        self.is_point_spec() && rhs.is_point_spec() && self.lo.eqv_spec(rhs.lo)
    }

    /// It's possible that some x in self is less than some y in rhs.
    pub open spec fn possibly_lt_spec(self, rhs: Interval) -> bool {
        self.lo.lt_spec(rhs.hi)
    }

    /// The intervals are disjoint: self.hi < rhs.lo or rhs.hi < self.lo.
    pub open spec fn disjoint_spec(self, rhs: Interval) -> bool {
        self.hi.lt_spec(rhs.lo) || rhs.hi.lt_spec(self.lo)
    }

    // ── Bound tightening spec functions ──────────────────────────

    /// Tighten to nonneg: clamp lo to max(0, lo).
    pub open spec fn tighten_nonneg_spec(self) -> Interval {
        Interval {
            lo: Rational::from_int_spec(0).max_spec(self.lo),
            hi: self.hi,
        }
    }

    /// Tighten to nonpos: clamp hi to min(0, hi).
    pub open spec fn tighten_nonpos_spec(self) -> Interval {
        Interval {
            lo: self.lo,
            hi: Rational::from_int_spec(0).min_spec(self.hi),
        }
    }

    /// Tighten to positive: clamp lo to max(0, lo), requires hi > 0.
    pub open spec fn tighten_positive_spec(self) -> Interval {
        Interval {
            lo: Rational::from_int_spec(0).max_spec(self.lo),
            hi: self.hi,
        }
    }

    // ── Special-case operation spec functions ───────────────────

    /// Squaring: tighter than mul(a, a) because it exploits x² ≥ 0.
    pub open spec fn square_spec(self) -> Interval {
        let zero = Rational::from_int_spec(0);
        if zero.le_spec(self.lo) {
            // entirely nonneg: [lo², hi²]
            Interval {
                lo: self.lo.mul_spec(self.lo),
                hi: self.hi.mul_spec(self.hi),
            }
        } else if self.hi.le_spec(zero) {
            // entirely nonpos: [hi², lo²]
            Interval {
                lo: self.hi.mul_spec(self.hi),
                hi: self.lo.mul_spec(self.lo),
            }
        } else {
            // spans zero: [0, max(lo², hi²)]
            Interval {
                lo: zero,
                hi: self.lo.mul_spec(self.lo).max_spec(
                    self.hi.mul_spec(self.hi)),
            }
        }
    }

    /// Integer power: [a,b]^n (naive recursive via mul for simplicity).
    pub open spec fn pow_spec(self, n: nat) -> Interval
        decreases n,
    {
        if n == 0 {
            Self::from_point_spec(Rational::from_int_spec(1))
        } else {
            self.mul_spec(self.pow_spec((n - 1) as nat))
        }
    }

    /// Fused multiply-add: a*b + c (no intermediate interval rounding).
    pub open spec fn fma_spec(self, mul_rhs: Interval, add_rhs: Interval) -> Interval {
        self.mul_spec(mul_rhs).add_spec(add_rhs)
    }

    // ── Interval arithmetic spec functions ───────────────────────

    /// Addition: [a,b] + [c,d] = [a+c, b+d].
    pub open spec fn add_spec(self, rhs: Interval) -> Interval {
        Interval {
            lo: self.lo.add_spec(rhs.lo),
            hi: self.hi.add_spec(rhs.hi),
        }
    }

    /// Negation: -[a,b] = [-b, -a].
    pub open spec fn neg_spec(self) -> Interval {
        Interval {
            lo: self.hi.neg_spec(),
            hi: self.lo.neg_spec(),
        }
    }

    /// Subtraction: [a,b] - [c,d] = [a-d, b-c].
    pub open spec fn sub_spec(self, rhs: Interval) -> Interval {
        Interval {
            lo: self.lo.sub_spec(rhs.hi),
            hi: self.hi.sub_spec(rhs.lo),
        }
    }

    /// Multiplication: [a,b] * [c,d] = [min(ac,ad,bc,bd), max(ac,ad,bc,bd)].
    pub open spec fn mul_spec(self, rhs: Interval) -> Interval {
        let ac = self.lo.mul_spec(rhs.lo);
        let ad = self.lo.mul_spec(rhs.hi);
        let bc = self.hi.mul_spec(rhs.lo);
        let bd = self.hi.mul_spec(rhs.hi);
        Interval {
            lo: ac.min_spec(ad).min_spec(bc).min_spec(bd),
            hi: ac.max_spec(ad).max_spec(bc).max_spec(bd),
        }
    }

    /// Scalar multiplication: k * [a,b] = [min(k*a, k*b), max(k*a, k*b)].
    pub open spec fn scale_spec(scalar: Rational, iv: Interval) -> Interval {
        let sa = scalar.mul_spec(iv.lo);
        let sb = scalar.mul_spec(iv.hi);
        Interval {
            lo: sa.min_spec(sb),
            hi: sa.max_spec(sb),
        }
    }

    /// Absolute value: |[a,b]|.
    pub open spec fn abs_spec(self) -> Interval {
        let zero = Rational::from_int_spec(0);
        if zero.le_spec(self.lo) {
            // entirely nonneg
            self
        } else if self.hi.le_spec(zero) {
            // entirely nonpos
            self.neg_spec()
        } else {
            // spans zero
            Interval { lo: zero, hi: self.lo.neg_spec().max_spec(self.hi) }
        }
    }

    /// Reciprocal: 1/[a,b] = [1/b, 1/a] (defined when 0 not in [a,b]).
    pub open spec fn recip_spec(self) -> Interval {
        Interval {
            lo: self.hi.reciprocal_spec(),
            hi: self.lo.reciprocal_spec(),
        }
    }

    /// Division: [a,b] / [c,d] = [a,b] * (1/[c,d]) (defined when 0 not in [c,d]).
    pub open spec fn div_spec(self, rhs: Interval) -> Interval {
        self.mul_spec(rhs.recip_spec())
    }

    // ── Proof constructors ───────────────────────────────────────

    /// Construct a point interval (proof-level).
    pub proof fn from_point(x: Rational) -> (out: Self)
        ensures
            out == Self::from_point_spec(x),
    {
        Interval { lo: x, hi: x }
    }

    /// Construct an interval from ordered endpoints (proof-level).
    pub proof fn from_endpoints(lo: Rational, hi: Rational) -> (out: Self)
        requires
            lo.le_spec(hi),
        ensures
            out.lo == lo,
            out.hi == hi,
            out.wf_spec(),
    {
        Interval { lo, hi }
    }

    // ── Basic proof lemmas ───────────────────────────────────────

    /// A point interval is well-formed.
    pub proof fn lemma_from_point_wf(x: Rational)
        ensures
            Self::from_point_spec(x).wf_spec(),
    {
    }

    /// A point interval contains its point.
    pub proof fn lemma_from_point_contains(x: Rational)
        ensures
            Self::from_point_spec(x).contains_spec(x),
    {
    }

    /// A well-formed interval contains its lower bound.
    pub proof fn lemma_contains_lo(iv: Self)
        requires
            iv.wf_spec(),
        ensures
            iv.contains_spec(iv.lo),
    {
    }

    /// A well-formed interval contains its upper bound.
    pub proof fn lemma_contains_hi(iv: Self)
        requires
            iv.wf_spec(),
        ensures
            iv.contains_spec(iv.hi),
    {
    }

    // ── Well-formedness preservation ─────────────────────────────

    /// Addition preserves well-formedness.
    pub proof fn lemma_add_wf(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.add_spec(b).wf_spec(),
    {
        Rational::lemma_le_add_both(a.lo, a.hi, b.lo, b.hi);
    }

    /// Negation preserves well-formedness.
    pub proof fn lemma_neg_wf(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.neg_spec().wf_spec(),
    {
        Rational::lemma_neg_reverses_le(a.lo, a.hi);
    }

    /// Subtraction preserves well-formedness.
    pub proof fn lemma_sub_wf(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.sub_spec(b).wf_spec(),
    {
        Rational::lemma_sub_le_monotone_left(a.lo, a.hi, b.hi);
        Rational::lemma_sub_le_monotone_right(b.lo, b.hi, a.hi);
        Rational::lemma_le_transitive(
            a.lo.sub_spec(b.hi), a.hi.sub_spec(b.hi), a.hi.sub_spec(b.lo));
    }

    /// Multiplication preserves well-formedness.
    pub proof fn lemma_mul_wf(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.mul_spec(b).wf_spec(),
    {
        let ac = a.lo.mul_spec(b.lo);
        let ad = a.lo.mul_spec(b.hi);
        let bc = a.hi.mul_spec(b.lo);
        let bd = a.hi.mul_spec(b.hi);
        // min4 <= ac <= max4 (trivially, since ac is one of the four)
        Self::lemma_min4_le(ac, ad, bc, bd, ac);
        Self::lemma_max4_ge(ac, ad, bc, bd, ac);
    }

    /// Scale preserves well-formedness.
    pub proof fn lemma_scale_wf(scalar: Rational, iv: Interval)
        requires
            iv.wf_spec(),
        ensures
            Self::scale_spec(scalar, iv).wf_spec(),
    {
        let sa = scalar.mul_spec(iv.lo);
        let sb = scalar.mul_spec(iv.hi);
        Rational::lemma_min_le_left(sa, sb);
        Rational::lemma_max_ge_left(sa, sb);
        // Either sa <= sb (then min=sa, max=sb, sa <= sb) or sb < sa (then min=sb, max=sa, sb <= sa)
        // In both cases min <= max. min_le_left gives min(sa,sb) <= sa.
        // max_ge_right gives sb <= max(sa,sb).
        // But we need min(sa,sb) <= max(sa,sb).
        Rational::lemma_min_le_right(sa, sb);
        Rational::lemma_max_ge_right(sa, sb);
        // min(sa,sb) <= sa and sa <= max(sa,sb), or min(sa,sb) <= sb and sb <= max(sa,sb)
        // Either way: need to connect them.
        // Use: min(sa,sb) <= sa <= max(sa,sb) by transitivity.
        Rational::lemma_le_transitive(sa.min_spec(sb), sa, sa.max_spec(sb));
    }

    /// Absolute value preserves well-formedness.
    pub proof fn lemma_abs_wf(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.abs_spec().wf_spec(),
    {
        let zero = Rational::from_int_spec(0);
        if zero.le_spec(a.lo) {
            // entirely nonneg: abs = self, already wf
        } else if a.hi.le_spec(zero) {
            // entirely nonpos: abs = neg(self)
            Self::lemma_neg_wf(a);
        } else {
            // spans zero: abs = [0, max(-lo, hi)]
            // Need: 0 <= max(-lo, hi).
            // lo < 0 (since !zero.le_spec(lo)), so -lo > 0, so 0 < -lo <= max(-lo, hi).
            Rational::lemma_neg_reverses_le(a.lo, zero);
            // zero.neg_spec() <= a.lo.neg_spec(). But zero.neg_spec() == zero (structurally).
            Rational::lemma_max_ge_left(a.lo.neg_spec(), a.hi);
            Rational::lemma_le_transitive(zero, a.lo.neg_spec(), a.lo.neg_spec().max_spec(a.hi));
        }
    }

    /// Absolute value containment: x in A => |x| in |A|.
    pub proof fn lemma_abs_containment(a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            a.abs_spec().contains_spec(x.abs_spec()),
    {
        let zero = Rational::from_int_spec(0);
        if zero.le_spec(a.lo) {
            // entirely nonneg: a.lo <= x <= a.hi, all >= 0.
            // |x| = x (since x >= 0). |A| = A. So x in A. ✓
            Rational::lemma_le_transitive(zero, a.lo, x);
            // 0 <= x, so x.abs_spec() = x.
        } else if a.hi.le_spec(zero) {
            // entirely nonpos: a.lo <= x <= a.hi <= 0.
            // |x| = -x. |A| = [-hi, -lo]. Need: -a.hi <= -x <= -a.lo.
            Rational::lemma_le_transitive(x, a.hi, zero);
            // x <= 0 so x.abs_spec() = -x (since x.num < 0 or x = 0).
            Rational::lemma_neg_reverses_le(x, a.hi);
            Rational::lemma_neg_reverses_le(a.lo, x);
        } else {
            // spans zero: |A| = [0, max(-lo, hi)].
            // Case split on sign of x.
            Rational::lemma_trichotomy(zero, x);
            if zero.le_spec(x) {
                // x >= 0: |x| = x. Need: 0 <= x <= max(-lo, hi).
                // 0 <= x ✓. x <= hi (from containment).
                // hi <= max(-lo, hi).
                Rational::lemma_max_ge_right(a.lo.neg_spec(), a.hi);
                Rational::lemma_le_transitive(x, a.hi, a.lo.neg_spec().max_spec(a.hi));
            } else {
                // x < 0: |x| = -x. Need: 0 <= -x <= max(-lo, hi).
                // x < 0 => -x > 0 >= 0 ✓.
                Rational::lemma_lt_implies_le(x, zero);
                Rational::lemma_neg_reverses_le(x, zero);
                // zero.neg_spec() = zero (structurally). So 0 <= -x.
                // lo <= x => -x <= -lo <= max(-lo, hi).
                Rational::lemma_neg_reverses_le(a.lo, x);
                Rational::lemma_max_ge_left(a.lo.neg_spec(), a.hi);
                Rational::lemma_le_transitive(x.neg_spec(), a.lo.neg_spec(), a.lo.neg_spec().max_spec(a.hi));
            }
        }
    }

    // ── lt+le transitivity helpers ─────────────────────────────────

    /// If a < b and b <= c then a < c.
    proof fn lemma_lt_le_implies_lt(a: Rational, b: Rational, c: Rational)
        requires
            a.lt_spec(b),
            b.le_spec(c),
        ensures
            a.lt_spec(c),
    {
        Rational::lemma_denom_positive(a);
        Rational::lemma_denom_positive(b);
        Rational::lemma_denom_positive(c);
        assert(a.lt_spec(c)) by (nonlinear_arith)
            requires
                a.num * b.denom() < b.num * a.denom(),
                b.num * c.denom() <= c.num * b.denom(),
                a.denom() > 0,
                b.denom() > 0,
                c.denom() > 0;
    }

    /// If a <= b and b < c then a < c.
    proof fn lemma_le_lt_implies_lt(a: Rational, b: Rational, c: Rational)
        requires
            a.le_spec(b),
            b.lt_spec(c),
        ensures
            a.lt_spec(c),
    {
        Rational::lemma_denom_positive(a);
        Rational::lemma_denom_positive(b);
        Rational::lemma_denom_positive(c);
        assert(a.lt_spec(c)) by (nonlinear_arith)
            requires
                a.num * b.denom() <= b.num * a.denom(),
                b.num * c.denom() < c.num * b.denom(),
                a.denom() > 0,
                b.denom() > 0,
                c.denom() > 0;
    }

    // ── Reciprocal / Division ─────────────────────────────────────

    /// Reciprocal well-formedness: 0 not in A => recip(A).wf_spec().
    pub proof fn lemma_recip_wf(a: Self)
        requires
            a.wf_spec(),
            Rational::from_int_spec(0).lt_spec(a.lo) || a.hi.lt_spec(Rational::from_int_spec(0)),
        ensures
            a.recip_spec().wf_spec(),
    {
        let zero = Rational::from_int_spec(0);
        if zero.lt_spec(a.lo) {
            // entirely positive: 0 < a.lo <= a.hi
            Rational::lemma_reciprocal_reverses_le_pos(a.lo, a.hi);
        } else {
            // entirely negative: a.lo <= a.hi < 0
            Rational::lemma_reciprocal_reverses_le_neg(a.lo, a.hi);
        }
    }

    /// Reciprocal containment: x in A and 0 not in A => 1/x in 1/A.
    pub proof fn lemma_recip_containment(a: Self, x: Rational)
        requires
            a.wf_spec(),
            Rational::from_int_spec(0).lt_spec(a.lo) || a.hi.lt_spec(Rational::from_int_spec(0)),
            a.contains_spec(x),
        ensures
            a.recip_spec().contains_spec(x.reciprocal_spec()),
    {
        let zero = Rational::from_int_spec(0);
        // recip_spec = [1/a.hi, 1/a.lo]
        // Need: 1/a.hi <= 1/x <= 1/a.lo
        if zero.lt_spec(a.lo) {
            // entirely positive: 0 < a.lo <= x <= a.hi
            // 0 < x (from 0 < a.lo and a.lo <= x)
            Self::lemma_lt_le_implies_lt(zero, a.lo, x);
            // 1/x <= 1/a.lo (from 0 < a.lo, a.lo <= x)
            Rational::lemma_reciprocal_reverses_le_pos(a.lo, x);
            // 1/a.hi <= 1/x (from 0 < x, x <= a.hi)
            Rational::lemma_reciprocal_reverses_le_pos(x, a.hi);
        } else {
            // entirely negative: a.lo <= x <= a.hi < 0
            // x < 0 (from x <= a.hi and a.hi < 0)
            Self::lemma_le_lt_implies_lt(x, a.hi, zero);
            // 1/x <= 1/a.lo (from x < 0, a.lo <= x)
            Rational::lemma_reciprocal_reverses_le_neg(a.lo, x);
            // 1/a.hi <= 1/x (from a.hi < 0, x <= a.hi)
            Rational::lemma_reciprocal_reverses_le_neg(x, a.hi);
        }
    }

    /// Division well-formedness: A.wf and B.wf and 0 not in B => (A/B).wf.
    pub proof fn lemma_div_wf(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            Rational::from_int_spec(0).lt_spec(b.lo) || b.hi.lt_spec(Rational::from_int_spec(0)),
        ensures
            a.div_spec(b).wf_spec(),
    {
        Self::lemma_recip_wf(b);
        Self::lemma_mul_wf(a, b.recip_spec());
    }

    /// Division containment: x in A, y in B, 0 not in B => x/y in A/B.
    pub proof fn lemma_div_containment(a: Self, b: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            Rational::from_int_spec(0).lt_spec(b.lo) || b.hi.lt_spec(Rational::from_int_spec(0)),
            a.contains_spec(x),
            b.contains_spec(y),
        ensures
            a.div_spec(b).contains_spec(x.div_spec(y)),
    {
        Self::lemma_recip_wf(b);
        Self::lemma_recip_containment(b, y);
        Self::lemma_mul_containment(a, b.recip_spec(), x, y.reciprocal_spec());
    }

    // ── Phase 3: Interval properties & proof infrastructure ─────

    // ── 3.1 Containment algebra ──────────────────────────────────

    /// If b contains a as a sub-interval and x is in a, then x is in b.
    pub proof fn lemma_contains_transitive(a: Self, b: Self, x: Rational)
        requires
            b.contains_interval_spec(a),
            a.contains_spec(x),
        ensures
            b.contains_spec(x),
    {
        // b.lo <= a.lo <= x <= a.hi <= b.hi
        Rational::lemma_le_transitive(b.lo, a.lo, x);
        Rational::lemma_le_transitive(x, a.hi, b.hi);
    }

    /// Sub-interval containment is transitive: a ⊆ b ⊆ c → a ⊆ c.
    pub proof fn lemma_contains_interval_transitive(a: Self, b: Self, c: Self)
        requires
            c.contains_interval_spec(b),
            b.contains_interval_spec(a),
        ensures
            c.contains_interval_spec(a),
    {
        Rational::lemma_le_transitive(c.lo, b.lo, a.lo);
        Rational::lemma_le_transitive(a.hi, b.hi, c.hi);
    }

    // ── 3.2 Width properties ─────────────────────────────────────

    /// Width of a well-formed interval is nonneg: wf(a) → 0 ≤ width(a).
    pub proof fn lemma_width_nonneg(a: Self)
        requires
            a.wf_spec(),
        ensures
            Rational::from_int_spec(0).le_spec(a.width_spec()),
    {
        let zero = Rational::from_int_spec(0);
        // lo ≤ hi → (lo - lo) ≤ (hi - lo) = width
        Rational::lemma_sub_le_monotone_left(a.lo, a.hi, a.lo);
        // (lo - lo) has num == 0, so eqv to 0
        Rational::lemma_sub_self_zero_num(a.lo);
        Rational::lemma_eqv_zero_iff_num_zero(a.lo.sub_spec(a.lo));
        Rational::lemma_eqv_implies_le(a.lo.sub_spec(a.lo), zero);
        // 0 ≤ (lo - lo) ≤ width
        Rational::lemma_le_transitive(zero, a.lo.sub_spec(a.lo), a.hi.sub_spec(a.lo));
    }

    /// Width of a sum: width(a+b) ≡ width(a) + width(b).
    pub proof fn lemma_add_width(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.add_spec(b).width_spec().eqv_spec(
                a.width_spec().add_spec(b.width_spec())),
    {
        // (a.hi+b.hi)-(a.lo+b.lo) ≡ (a.hi-a.lo)+(b.hi-b.lo)
        Rational::lemma_sub_add_distributes(a.hi, b.hi, a.lo, b.lo);
    }

    /// Width of a negation: width(-a) = width(a) (structural equality).
    pub proof fn lemma_neg_width(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.neg_spec().width_spec() == a.width_spec(),
    {
        // width(-a) = (-a).hi - (-a).lo = a.lo.neg - a.hi.neg
        // = (a.lo - a.hi).neg  [sub_neg_both]
        Rational::lemma_sub_neg_both(a.lo, a.hi);
        // = (a.hi - a.lo).neg.neg  [sub_antisymmetric]
        Rational::lemma_sub_antisymmetric(a.lo, a.hi);
        // = a.hi - a.lo = width(a)  [neg_involution]
        Rational::lemma_neg_involution(a.hi.sub_spec(a.lo));
    }

    /// Width of a difference: width(a-b) ≡ width(a) + width(b).
    pub proof fn lemma_sub_width(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.sub_spec(b).width_spec().eqv_spec(
                a.width_spec().add_spec(b.width_spec())),
    {
        // sub_spec is defined componentwise with Rational::sub_spec, which
        // equals add_spec(neg_spec()) structurally [lemma_sub_is_add_neg].
        Rational::lemma_sub_is_add_neg(a.lo, b.hi);
        Rational::lemma_sub_is_add_neg(a.hi, b.lo);
        // Now a.sub_spec(b) == a.add_spec(b.neg_spec()) as Interval structs.
        Self::lemma_neg_wf(b);
        Self::lemma_add_width(a, b.neg_spec());
        // width(a + neg(b)) ≡ width(a) + width(neg(b))
        Self::lemma_neg_width(b);
        // width(neg(b)) == width(b) structurally
    }

    /// If a ⊆ b then width(a) ≤ width(b).
    pub proof fn lemma_subset_implies_le_width(a: Self, b: Self)
        requires
            b.contains_interval_spec(a),
        ensures
            a.width_spec().le_spec(b.width_spec()),
    {
        // b.lo ≤ a.lo → (a.hi - a.lo) ≤ (a.hi - b.lo)
        Rational::lemma_sub_le_monotone_right(b.lo, a.lo, a.hi);
        // a.hi ≤ b.hi → (a.hi - b.lo) ≤ (b.hi - b.lo)
        Rational::lemma_sub_le_monotone_left(a.hi, b.hi, b.lo);
        Rational::lemma_le_transitive(
            a.hi.sub_spec(a.lo),
            a.hi.sub_spec(b.lo),
            b.hi.sub_spec(b.lo),
        );
    }

    /// Width of a point interval is zero: width([x,x]) ≡ 0.
    pub proof fn lemma_point_interval_zero_width(x: Rational)
        ensures
            Self::from_point_spec(x).width_spec().eqv_spec(
                Rational::from_int_spec(0)),
    {
        Rational::lemma_sub_self_zero_num(x);
        Rational::lemma_eqv_zero_iff_num_zero(x.sub_spec(x));
    }

    // ── 3.3 Midpoint properties ──────────────────────────────────

    /// Midpoint of a well-formed interval lies in the interval.
    pub proof fn lemma_midpoint_in_interval(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.contains_spec(a.midpoint_spec()),
    {
        let mid = Rational::midpoint_spec(a.lo, a.hi);
        Rational::lemma_trichotomy(a.lo, a.hi);
        if a.lo.lt_spec(a.hi) {
            // Strict case: lo < mid < hi
            Rational::lemma_midpoint_between_left(a.lo, a.hi);
            Rational::lemma_midpoint_between_right(a.lo, a.hi);
            Rational::lemma_lt_implies_le(a.lo, mid);
            Rational::lemma_lt_implies_le(mid, a.hi);
        } else if a.lo.eqv_spec(a.hi) {
            // Point interval: mid ≡ lo ≡ hi
            // midpoint(lo, hi) ≡ midpoint(lo, lo) by eqv congruence
            let half = Rational { num: 1, den: 1 };
            Rational::lemma_eqv_add_congruence_right(a.lo, a.hi, a.lo);
            // a.lo + a.hi ≡ a.lo + a.lo
            Rational::lemma_eqv_mul_congruence_left(
                a.lo.add_spec(a.hi), a.lo.add_spec(a.lo), half);
            // mid ≡ midpoint(lo, lo) ≡ lo [by midpoint_eqv_self]
            Rational::lemma_midpoint_eqv_self(a.lo);
            Rational::lemma_eqv_transitive(mid,
                Rational::midpoint_spec(a.lo, a.lo), a.lo);
            // lo ≤ mid and mid ≤ lo (from eqv), mid ≤ hi (from mid ≡ lo ≤ hi)
            Rational::lemma_eqv_symmetric(mid, a.lo);
            Rational::lemma_eqv_implies_le(a.lo, mid);
            Rational::lemma_le_transitive(mid, a.lo, a.hi);
        } else {
            // a.hi < a.lo contradicts wf (lo ≤ hi)
            Rational::lemma_denom_positive(a.lo);
            Rational::lemma_denom_positive(a.hi);
            assert(false) by (nonlinear_arith)
                requires
                    a.lo.num * a.hi.denom() <= a.hi.num * a.lo.denom(),
                    a.hi.num * a.lo.denom() < a.lo.num * a.hi.denom();
        }
    }

    // ── 3.4 Intersection ─────────────────────────────────────────

    /// If intersection is Some, then any point in both inputs is in the result.
    pub proof fn lemma_intersect_containment(a: Self, b: Self, x: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.contains_spec(x),
            b.contains_spec(x),
            a.intersect_spec(b).is_some(),
        ensures
            a.intersect_spec(b).unwrap().contains_spec(x),
    {
        let lo = a.lo.max_spec(b.lo);
        let hi = a.hi.min_spec(b.hi);
        // x >= a.lo and x >= b.lo, so x >= max(a.lo, b.lo) = lo
        Rational::lemma_trichotomy(a.lo, b.lo);
        if a.lo.le_spec(b.lo) {
            // max = b.lo, and x >= b.lo
            assert(lo == b.lo);
        } else {
            // max = a.lo, and x >= a.lo
            assert(lo == a.lo);
        }
        // x <= a.hi and x <= b.hi, so x <= min(a.hi, b.hi) = hi
        Rational::lemma_trichotomy(a.hi, b.hi);
        if a.hi.le_spec(b.hi) {
            // min = a.hi, and x <= a.hi
            assert(hi == a.hi);
        } else {
            // min = b.hi, and x <= b.hi
            assert(hi == b.hi);
        }
    }

    /// If intersection is Some, the result is a sub-interval of both inputs.
    pub proof fn lemma_intersect_subset_both(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.intersect_spec(b).is_some(),
        ensures
            a.contains_interval_spec(a.intersect_spec(b).unwrap()),
            b.contains_interval_spec(a.intersect_spec(b).unwrap()),
    {
        let lo = a.lo.max_spec(b.lo);
        let hi = a.hi.min_spec(b.hi);
        // lo = max(a.lo, b.lo) >= a.lo and >= b.lo
        Rational::lemma_max_ge_left(a.lo, b.lo);
        Rational::lemma_max_ge_right(a.lo, b.lo);
        // hi = min(a.hi, b.hi) <= a.hi and <= b.hi
        Rational::lemma_min_le_left(a.hi, b.hi);
        Rational::lemma_min_le_right(a.hi, b.hi);
        // a contains [lo, hi]: a.lo <= lo (max >= left) and hi <= a.hi (min <= left)
        // b contains [lo, hi]: b.lo <= lo (max >= right) and hi <= b.hi (min <= right)
    }

    // ── 3.5 Hull properties ──────────────────────────────────────

    /// Hull contains both input intervals.
    pub proof fn lemma_hull_contains_both(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.hull_spec(b).contains_interval_spec(a),
            a.hull_spec(b).contains_interval_spec(b),
    {
        // hull.lo = min(a.lo, b.lo) <= a.lo, <= b.lo
        Rational::lemma_min_le_left(a.lo, b.lo);
        Rational::lemma_min_le_right(a.lo, b.lo);
        // hull.hi = max(a.hi, b.hi) >= a.hi, >= b.hi
        Rational::lemma_max_ge_left(a.hi, b.hi);
        Rational::lemma_max_ge_right(a.hi, b.hi);
    }

    /// Hull is minimal: if c contains both a and b, then c contains hull(a,b).
    pub proof fn lemma_hull_minimal(a: Self, b: Self, c: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.contains_interval_spec(a),
            c.contains_interval_spec(b),
        ensures
            c.contains_interval_spec(a.hull_spec(b)),
    {
        let hull = a.hull_spec(b);
        // hull.lo = min(a.lo, b.lo). c.lo <= a.lo and c.lo <= b.lo.
        // Need: c.lo <= min(a.lo, b.lo).
        Rational::lemma_trichotomy(a.lo, b.lo);
        if a.lo.le_spec(b.lo) {
            // min = a.lo, c.lo <= a.lo ✓
            assert(hull.lo == a.lo);
        } else {
            // min = b.lo, c.lo <= b.lo ✓
            assert(hull.lo == b.lo);
        }
        // hull.hi = max(a.hi, b.hi). a.hi <= c.hi and b.hi <= c.hi.
        // Need: max(a.hi, b.hi) <= c.hi.
        Rational::lemma_trichotomy(a.hi, b.hi);
        if a.hi.le_spec(b.hi) {
            // max = b.hi, b.hi <= c.hi ✓
            assert(hull.hi == b.hi);
        } else {
            // max = a.hi, a.hi <= c.hi ✓
            assert(hull.hi == a.hi);
        }
    }

    // ── 3.6 Monotonicity w.r.t. containment ──────────────────────

    /// Addition is monotone: a ⊆ a' ∧ b ⊆ b' → a+b ⊆ a'+b'.
    pub proof fn lemma_add_monotone(a: Self, a2: Self, b: Self, b2: Self)
        requires
            a2.contains_interval_spec(a),
            b2.contains_interval_spec(b),
        ensures
            a2.add_spec(b2).contains_interval_spec(a.add_spec(b)),
    {
        // (a+b).lo = a.lo + b.lo >= a'.lo + b'.lo would be wrong direction.
        // Need: a'.lo + b'.lo ≤ a.lo + b.lo and a.hi + b.hi ≤ a'.hi + b'.hi.
        // a'.lo ≤ a.lo, b'.lo ≤ b.lo → a'.lo + b'.lo ≤ a.lo + b.lo
        Rational::lemma_le_add_both(a2.lo, a.lo, b2.lo, b.lo);
        // a.hi ≤ a'.hi, b.hi ≤ b'.hi → a.hi + b.hi ≤ a'.hi + b'.hi
        Rational::lemma_le_add_both(a.hi, a2.hi, b.hi, b2.hi);
    }

    /// Negation is monotone: a ⊆ a' → -a ⊆ -a'.
    pub proof fn lemma_neg_monotone(a: Self, a2: Self)
        requires
            a2.contains_interval_spec(a),
        ensures
            a2.neg_spec().contains_interval_spec(a.neg_spec()),
    {
        // -a = [-a.hi, -a.lo], -a' = [-a'.hi, -a'.lo]
        // Need: -a'.hi ≤ -a.hi (from a.hi ≤ a'.hi, neg reverses)
        Rational::lemma_neg_reverses_le(a.hi, a2.hi);
        // Need: -a.lo ≤ -a'.lo (from a'.lo ≤ a.lo, neg reverses)
        Rational::lemma_neg_reverses_le(a2.lo, a.lo);
    }

    /// Multiplication is monotone: a ⊆ a' ∧ b ⊆ b' → a*b ⊆ a'*b'.
    pub proof fn lemma_mul_monotone(a: Self, a2: Self, b: Self, b2: Self)
        requires
            a.wf_spec(),
            a2.wf_spec(),
            b.wf_spec(),
            b2.wf_spec(),
            a2.contains_interval_spec(a),
            b2.contains_interval_spec(b),
        ensures
            a2.mul_spec(b2).contains_interval_spec(a.mul_spec(b)),
    {
        // mul is defined via min4/max4 of the four corner products.
        // a*b = [min4(corners_a), max4(corners_a)]
        // a'*b' = [min4(corners_a'), max4(corners_a')]
        // Each corner of a*b is a product x*y where x in [a.lo, a.hi] ⊆ [a'.lo, a'.hi]
        // and y in [b.lo, b.hi] ⊆ [b'.lo, b'.hi]. So x*y is also a product of
        // elements in a'×b'. The min4 of a' corners ≤ min4 of a corners (since a
        // corners are all also achievable from elements in a'×b'), and similarly for max.
        //
        // The corners of a*b are: a.lo*b.lo, a.lo*b.hi, a.hi*b.lo, a.hi*b.hi.
        // Each is a product of endpoints of a and b, which are contained in a' and b'.
        // Since a.lo ∈ a' and b.lo ∈ b', by mul_containment: a.lo*b.lo ∈ a'*b'.
        // Similarly for the other three corners.
        // So all four corners are in a'*b', meaning:
        //   a'*b'.lo ≤ each corner ≤ a'*b'.hi
        // Then a'*b'.lo ≤ min4(corners) = (a*b).lo and max4(corners) = (a*b).hi ≤ a'*b'.hi.

        // a.lo and a.hi are in a' (since a ⊆ a')
        Self::lemma_contains_lo(a2);
        Self::lemma_contains_hi(a2);
        Rational::lemma_le_transitive(a2.lo, a.lo, a.hi);
        Rational::lemma_le_transitive(a.lo, a.hi, a2.hi);
        // So a.lo is in a': a'.lo ≤ a.lo (from containment) and a.lo ≤ a'.hi (transitivity)
        // Similarly a.hi is in a'.

        // b.lo and b.hi are in b'
        Self::lemma_contains_lo(b2);
        Self::lemma_contains_hi(b2);
        Rational::lemma_le_transitive(b2.lo, b.lo, b.hi);
        Rational::lemma_le_transitive(b.lo, b.hi, b2.hi);

        // All four corners of a*b are contained in a'*b'
        Self::lemma_mul_containment(a2, b2, a.lo, b.lo);
        Self::lemma_mul_containment(a2, b2, a.lo, b.hi);
        Self::lemma_mul_containment(a2, b2, a.hi, b.lo);
        Self::lemma_mul_containment(a2, b2, a.hi, b.hi);

        // Each corner of a*b is in a'*b', meaning a'*b'.lo ≤ corner ≤ a'*b'.hi.
        let c1 = a.lo.mul_spec(b.lo);
        let c2 = a.lo.mul_spec(b.hi);
        let c3 = a.hi.mul_spec(b.lo);
        let c4 = a.hi.mul_spec(b.hi);
        let ab_lo = c1.min_spec(c2).min_spec(c3).min_spec(c4);
        let ab_hi = c1.max_spec(c2).max_spec(c3).max_spec(c4);

        // a'*b'.lo ≤ each corner → a'*b'.lo ≤ min4(corners) = (a*b).lo
        // min4 ≤ c1, and a'b'.lo ≤ c1, so we need a'b'.lo ≤ min4.
        // Actually: a'b'.lo ≤ c1 and a'b'.lo ≤ c2 and a'b'.lo ≤ c3 and a'b'.lo ≤ c4.
        // min4 is one of {c1,c2,c3,c4}, so a'b'.lo ≤ min4.
        Rational::lemma_min_le_left(c1, c2);
        Rational::lemma_min_le_right(c1, c2);
        Rational::lemma_min_le_left(c1.min_spec(c2), c3);
        Rational::lemma_min_le_right(c1.min_spec(c2), c3);
        Rational::lemma_min_le_left(c1.min_spec(c2).min_spec(c3), c4);
        Rational::lemma_min_le_right(c1.min_spec(c2).min_spec(c3), c4);

        // ab_lo is ≤ all of c1..c4
        Rational::lemma_le_transitive(ab_lo, c1.min_spec(c2).min_spec(c3), c1.min_spec(c2));
        Rational::lemma_le_transitive(ab_lo, c1.min_spec(c2), c1);
        Rational::lemma_le_transitive(ab_lo, c1.min_spec(c2), c2);
        Rational::lemma_le_transitive(ab_lo, c1.min_spec(c2).min_spec(c3), c3);

        // a'b'.lo ≤ c_i for all i, and ab_lo = min(c1..c4) which is one of them.
        // Use trichotomy to identify which one ab_lo equals.
        Rational::lemma_trichotomy(c1, c2);
        Rational::lemma_trichotomy(c1.min_spec(c2), c3);
        Rational::lemma_trichotomy(c1.min_spec(c2).min_spec(c3), c4);
        // ab_lo is one of c1,c2,c3,c4, so a'b' contains it.

        // For the upper bound: similarly, each corner ≤ a'b'.hi,
        // and ab_hi = max4(corners) is one of them.
        Rational::lemma_max_ge_left(c1, c2);
        Rational::lemma_max_ge_right(c1, c2);
        Rational::lemma_max_ge_left(c1.max_spec(c2), c3);
        Rational::lemma_max_ge_right(c1.max_spec(c2), c3);
        Rational::lemma_max_ge_left(c1.max_spec(c2).max_spec(c3), c4);
        Rational::lemma_max_ge_right(c1.max_spec(c2).max_spec(c3), c4);

        Rational::lemma_le_transitive(c1, c1.max_spec(c2), c1.max_spec(c2).max_spec(c3));
        Rational::lemma_le_transitive(c1, c1.max_spec(c2).max_spec(c3), ab_hi);
        Rational::lemma_le_transitive(c2, c1.max_spec(c2), c1.max_spec(c2).max_spec(c3));
        Rational::lemma_le_transitive(c2, c1.max_spec(c2).max_spec(c3), ab_hi);
        Rational::lemma_le_transitive(c3, c1.max_spec(c2).max_spec(c3), ab_hi);

        Rational::lemma_trichotomy(c1, c2);
        Rational::lemma_trichotomy(c1.max_spec(c2), c3);
        Rational::lemma_trichotomy(c1.max_spec(c2).max_spec(c3), c4);

        // a'b' = [a'b'.lo, a'b'.hi]. ab_lo and ab_hi are corners, so:
        // a'b'.lo ≤ ab_lo (ab_lo is contained in a'b')
        // ab_hi ≤ a'b'.hi (ab_hi is contained in a'b')
    }

    // ── Phase 4: Sign determination & comparison proofs ─────────

    /// If an interval is certainly positive, every element is positive.
    pub proof fn lemma_certainly_positive_implies(a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.certainly_positive_spec(),
            a.contains_spec(x),
        ensures
            Rational::from_int_spec(0).lt_spec(x),
    {
        let zero = Rational::from_int_spec(0);
        // 0 < a.lo and a.lo <= x → 0 < x
        Self::lemma_lt_le_implies_lt(zero, a.lo, x);
    }

    /// If an interval is certainly negative, every element is negative.
    pub proof fn lemma_certainly_negative_implies(a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.certainly_negative_spec(),
            a.contains_spec(x),
        ensures
            x.lt_spec(Rational::from_int_spec(0)),
    {
        let zero = Rational::from_int_spec(0);
        // x <= a.hi and a.hi < 0 → x < 0
        Self::lemma_le_lt_implies_lt(x, a.hi, zero);
    }

    /// If the interval doesn't possibly contain zero, no element is zero.
    pub proof fn lemma_not_possibly_zero_implies(a: Self, x: Rational)
        requires
            a.wf_spec(),
            !a.possibly_zero_spec(),
            a.contains_spec(x),
        ensures
            !x.eqv_spec(Rational::from_int_spec(0)),
    {
        let zero = Rational::from_int_spec(0);
        // !possibly_zero means: !lo.le_spec(0) || !0.le_spec(hi)
        // i.e., 0 < lo or hi < 0.
        Rational::lemma_trichotomy(a.lo, zero);
        Rational::lemma_trichotomy(zero, a.hi);
        if zero.lt_spec(a.lo) {
            // 0 < lo <= x, so 0 < x, hence x != 0
            Self::lemma_lt_le_implies_lt(zero, a.lo, x);
            Rational::lemma_eqv_zero_iff_num_zero(x);
            Rational::lemma_denom_positive(x);
            Rational::lemma_denom_positive(zero);
        } else {
            // hi < 0, so x <= hi < 0, hence x < 0, x != 0
            Self::lemma_le_lt_implies_lt(x, a.hi, zero);
            Rational::lemma_eqv_zero_iff_num_zero(x);
            Rational::lemma_denom_positive(x);
            Rational::lemma_denom_positive(zero);
        }
    }

    /// If a is certainly less than b, then every x in a is less than every y in b.
    pub proof fn lemma_certainly_lt_implies(a: Self, b: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.certainly_lt_spec(b),
            a.contains_spec(x),
            b.contains_spec(y),
        ensures
            x.lt_spec(y),
    {
        // x <= a.hi < b.lo <= y → x < y
        Self::lemma_le_lt_implies_lt(x, a.hi, b.lo);
        Self::lemma_lt_le_implies_lt(x, b.lo, y);
    }

    /// If two intervals are disjoint, they share no common point.
    pub proof fn lemma_disjoint_no_common_point(a: Self, b: Self, x: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.disjoint_spec(b),
            a.contains_spec(x),
        ensures
            !b.contains_spec(x),
    {
        // disjoint: a.hi < b.lo or b.hi < a.lo
        if a.hi.lt_spec(b.lo) {
            // x <= a.hi < b.lo, so x < b.lo, so !(b.lo <= x)
            Self::lemma_le_lt_implies_lt(x, a.hi, b.lo);
            Rational::lemma_lt_asymmetric(x, b.lo);
            Rational::lemma_denom_positive(x);
            Rational::lemma_denom_positive(b.lo);
        } else {
            // b.hi < a.lo <= x, so b.hi < x, so !(x <= b.hi)
            Self::lemma_lt_le_implies_lt(b.hi, a.lo, x);
            Rational::lemma_lt_asymmetric(b.hi, x);
            Rational::lemma_denom_positive(x);
            Rational::lemma_denom_positive(b.hi);
        }
    }

    /// Tightening to nonneg preserves containment for nonneg elements.
    pub proof fn lemma_tighten_nonneg_containment(a: Self, x: Rational)
        requires
            a.wf_spec(),
            Rational::from_int_spec(0).le_spec(a.hi),
            a.contains_spec(x),
            Rational::from_int_spec(0).le_spec(x),
        ensures
            a.tighten_nonneg_spec().contains_spec(x),
    {
        let zero = Rational::from_int_spec(0);
        // tighten_nonneg.lo = max(0, a.lo), tighten_nonneg.hi = a.hi
        // Need: max(0, a.lo) <= x <= a.hi
        // x <= a.hi ✓ (from containment)
        // max(0, a.lo) <= x: case split on 0 vs a.lo
        Rational::lemma_trichotomy(zero, a.lo);
        if zero.le_spec(a.lo) {
            // max = a.lo, a.lo <= x ✓ (from containment)
            assert(zero.max_spec(a.lo) == a.lo);
        } else {
            // max = zero, 0 <= x ✓
            assert(zero.max_spec(a.lo) == zero);
        }
    }

    // ── Phase 5: Squaring, power, FMA proofs ────────────────────

    /// Squaring preserves well-formedness.
    pub proof fn lemma_square_wf(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.square_spec().wf_spec(),
    {
        let zero = Rational::from_int_spec(0);
        if zero.le_spec(a.lo) {
            // nonneg: [lo², hi²]. Need lo² ≤ hi².
            Rational::lemma_le_mul_nonneg_both(a.lo, a.hi, a.lo, a.hi);
        } else if a.hi.le_spec(zero) {
            // nonpos: [hi², lo²]. Need hi² ≤ lo².
            // 0 ≤ -hi ≤ -lo
            // a.lo ≤ a.hi ≤ 0, so negate: 0 ≤ -a.hi ≤ -a.lo
            Rational::lemma_neg_reverses_le(a.lo, a.hi);
            Rational::lemma_neg_reverses_le(a.hi, zero);
            // (-hi)² ≤ (-lo)²
            Rational::lemma_le_mul_nonneg_both(
                a.hi.neg_spec(), a.lo.neg_spec(),
                a.hi.neg_spec(), a.lo.neg_spec());
            // (-t)² eqv t²
            Self::lemma_neg_mul_neg_eqv(a.hi, a.hi);
            Self::lemma_neg_mul_neg_eqv(a.lo, a.lo);
            // hi² eqv (-hi)² ≤ (-lo)² eqv lo²
            Rational::lemma_eqv_implies_le(
                a.hi.mul_spec(a.hi),
                a.hi.neg_spec().mul_spec(a.hi.neg_spec()));
            Rational::lemma_le_transitive(
                a.hi.mul_spec(a.hi),
                a.hi.neg_spec().mul_spec(a.hi.neg_spec()),
                a.lo.neg_spec().mul_spec(a.lo.neg_spec()));
            Rational::lemma_eqv_implies_le(
                a.lo.neg_spec().mul_spec(a.lo.neg_spec()),
                a.lo.mul_spec(a.lo));
            Rational::lemma_le_transitive(
                a.hi.mul_spec(a.hi),
                a.lo.neg_spec().mul_spec(a.lo.neg_spec()),
                a.lo.mul_spec(a.lo));
        } else {
            // spans zero: [0, max(lo², hi²)]. Need 0 ≤ max(lo², hi²).
            Rational::lemma_square_le_nonneg(a.lo);
            Rational::lemma_max_ge_left(
                a.lo.mul_spec(a.lo), a.hi.mul_spec(a.hi));
            Rational::lemma_le_transitive(zero,
                a.lo.mul_spec(a.lo),
                a.lo.mul_spec(a.lo).max_spec(a.hi.mul_spec(a.hi)));
        }
    }

    /// Squaring containment: x in A → x² in square(A).
    pub proof fn lemma_square_containment(a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            a.square_spec().contains_spec(x.mul_spec(x)),
    {
        let zero = Rational::from_int_spec(0);
        let x2 = x.mul_spec(x);
        if zero.le_spec(a.lo) {
            // entirely nonneg: 0 ≤ lo ≤ x ≤ hi
            // lo² ≤ x² ≤ hi²
            Rational::lemma_le_transitive(zero, a.lo, x);
            Rational::lemma_le_mul_nonneg_both(a.lo, x, a.lo, x);
            Rational::lemma_le_mul_nonneg_both(x, a.hi, x, a.hi);
        } else if a.hi.le_spec(zero) {
            // entirely nonpos: lo ≤ x ≤ hi ≤ 0
            // hi² ≤ x² ≤ lo²
            // Establish 0 ≤ -hi ≤ -x ≤ -lo
            Rational::lemma_neg_reverses_le(a.lo, x);    // -x ≤ -lo
            Rational::lemma_neg_reverses_le(x, a.hi);    // -hi ≤ -x
            Rational::lemma_neg_reverses_le(a.hi, zero);  // 0 ≤ -hi
            Rational::lemma_le_transitive(x, a.hi, zero); // x ≤ 0
            Rational::lemma_neg_reverses_le(x, zero);     // 0 ≤ -x
            // (-hi)² ≤ (-x)² ≤ (-lo)²
            Rational::lemma_le_mul_nonneg_both(
                a.hi.neg_spec(), x.neg_spec(),
                a.hi.neg_spec(), x.neg_spec());
            Rational::lemma_le_mul_nonneg_both(
                x.neg_spec(), a.lo.neg_spec(),
                x.neg_spec(), a.lo.neg_spec());
            // Transfer via eqv: (-t)² eqv t²
            Self::lemma_neg_mul_neg_eqv(a.hi, a.hi);
            Self::lemma_neg_mul_neg_eqv(x, x);
            Self::lemma_neg_mul_neg_eqv(a.lo, a.lo);
            // hi² eqv (-hi)² ≤ (-x)² eqv x²
            Rational::lemma_eqv_implies_le(
                a.hi.mul_spec(a.hi),
                a.hi.neg_spec().mul_spec(a.hi.neg_spec()));
            Rational::lemma_le_transitive(
                a.hi.mul_spec(a.hi),
                a.hi.neg_spec().mul_spec(a.hi.neg_spec()),
                x.neg_spec().mul_spec(x.neg_spec()));
            Rational::lemma_eqv_implies_le(
                x.neg_spec().mul_spec(x.neg_spec()),
                x.mul_spec(x));
            Rational::lemma_le_transitive(
                a.hi.mul_spec(a.hi),
                x.neg_spec().mul_spec(x.neg_spec()),
                x2);
            // x² eqv (-x)² ≤ (-lo)² eqv lo²
            Rational::lemma_eqv_symmetric(
                x.neg_spec().mul_spec(x.neg_spec()), x2);
            Rational::lemma_eqv_implies_le(
                x2, x.neg_spec().mul_spec(x.neg_spec()));
            Rational::lemma_le_transitive(
                x2,
                x.neg_spec().mul_spec(x.neg_spec()),
                a.lo.neg_spec().mul_spec(a.lo.neg_spec()));
            Rational::lemma_eqv_implies_le(
                a.lo.neg_spec().mul_spec(a.lo.neg_spec()),
                a.lo.mul_spec(a.lo));
            Rational::lemma_le_transitive(
                x2,
                a.lo.neg_spec().mul_spec(a.lo.neg_spec()),
                a.lo.mul_spec(a.lo));
        } else {
            // spans zero: square = [0, max(lo², hi²)]
            // 0 ≤ x²
            Rational::lemma_square_le_nonneg(x);
            // x² ≤ max(lo², hi²): case split on sign of x
            Rational::lemma_trichotomy(zero, x);
            if zero.le_spec(x) {
                // 0 ≤ x ≤ hi → x² ≤ hi²
                Rational::lemma_le_mul_nonneg_both(x, a.hi, x, a.hi);
                Rational::lemma_max_ge_right(
                    a.lo.mul_spec(a.lo), a.hi.mul_spec(a.hi));
                Rational::lemma_le_transitive(x2,
                    a.hi.mul_spec(a.hi),
                    a.lo.mul_spec(a.lo).max_spec(a.hi.mul_spec(a.hi)));
            } else {
                // x < 0 → -x > 0, lo ≤ x → -x ≤ -lo, so 0 < -x ≤ -lo
                Rational::lemma_lt_implies_le(x, zero);
                Rational::lemma_neg_reverses_le(x, zero);
                Rational::lemma_neg_reverses_le(a.lo, x);
                // (-x)² ≤ (-lo)²
                Rational::lemma_le_mul_nonneg_both(
                    x.neg_spec(), a.lo.neg_spec(),
                    x.neg_spec(), a.lo.neg_spec());
                // eqv transfer: x² ≤ lo²
                Self::lemma_neg_mul_neg_eqv(x, x);
                Self::lemma_neg_mul_neg_eqv(a.lo, a.lo);
                Rational::lemma_eqv_symmetric(
                    x.neg_spec().mul_spec(x.neg_spec()), x2);
                Rational::lemma_eqv_implies_le(
                    x2, x.neg_spec().mul_spec(x.neg_spec()));
                Rational::lemma_le_transitive(x2,
                    x.neg_spec().mul_spec(x.neg_spec()),
                    a.lo.neg_spec().mul_spec(a.lo.neg_spec()));
                Rational::lemma_eqv_implies_le(
                    a.lo.neg_spec().mul_spec(a.lo.neg_spec()),
                    a.lo.mul_spec(a.lo));
                Rational::lemma_le_transitive(x2,
                    a.lo.neg_spec().mul_spec(a.lo.neg_spec()),
                    a.lo.mul_spec(a.lo));
                Rational::lemma_max_ge_left(
                    a.lo.mul_spec(a.lo), a.hi.mul_spec(a.hi));
                Rational::lemma_le_transitive(x2,
                    a.lo.mul_spec(a.lo),
                    a.lo.mul_spec(a.lo).max_spec(a.hi.mul_spec(a.hi)));
            }
        }
    }

    /// Power preserves well-formedness.
    pub proof fn lemma_pow_wf(a: Self, n: nat)
        requires
            a.wf_spec(),
        ensures
            a.pow_spec(n).wf_spec(),
        decreases n,
    {
        if n == 0 {
            Self::lemma_from_point_wf(Rational::from_int_spec(1));
        } else {
            Self::lemma_pow_wf(a, (n - 1) as nat);
            Self::lemma_mul_wf(a, a.pow_spec((n - 1) as nat));
        }
    }

    /// Power containment: x in A → x^n in pow(A, n).
    pub proof fn lemma_pow_containment(a: Self, x: Rational, n: nat)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            a.pow_spec(n).contains_spec(x.pow_spec(n)),
        decreases n,
    {
        if n == 0 {
            // x^0 = 1, pow(a,0) = [1,1]. 1 is in [1,1].
            Rational::lemma_eqv_reflexive(Rational::from_int_spec(1));
        } else {
            // x^n = x * x^(n-1). By IH, x^(n-1) in pow(a, n-1).
            Self::lemma_pow_wf(a, (n - 1) as nat);
            Self::lemma_pow_containment(a, x, (n - 1) as nat);
            Self::lemma_mul_containment(a, a.pow_spec((n - 1) as nat),
                x, x.pow_spec((n - 1) as nat));
        }
    }

    // NOTE: lemma_pow_even_nonneg is NOT provable for the naive recursive
    // pow_spec (due to the dependency problem in interval arithmetic).
    // Use square_spec directly when tight even-power bounds are needed.

    /// FMA well-formedness: wf(a) ∧ wf(b) ∧ wf(c) → wf(fma(a,b,c)).
    pub proof fn lemma_fma_wf(a: Self, b: Self, c: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            a.fma_spec(b, c).wf_spec(),
    {
        Self::lemma_mul_wf(a, b);
        Self::lemma_add_wf(a.mul_spec(b), c);
    }

    /// FMA containment: x in A, y in B, z in C → x*y+z in fma(A,B,C).
    pub proof fn lemma_fma_containment(
        a: Self, b: Self, c: Self,
        x: Rational, y: Rational, z: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
            a.contains_spec(x),
            b.contains_spec(y),
            c.contains_spec(z),
        ensures
            a.fma_spec(b, c).contains_spec(
                x.mul_spec(y).add_spec(z)),
    {
        Self::lemma_mul_wf(a, b);
        Self::lemma_mul_containment(a, b, x, y);
        Self::lemma_add_containment(a.mul_spec(b), c,
            x.mul_spec(y), z);
    }

    // ── Min4 / Max4 helpers ──────────────────────────────────────

    /// min of four values is <= any value that has some corner <= it.
    proof fn lemma_min4_le(a: Rational, b: Rational, c: Rational, d: Rational, x: Rational)
        requires
            a.le_spec(x) || b.le_spec(x) || c.le_spec(x) || d.le_spec(x),
        ensures ({
            let m = a.min_spec(b).min_spec(c).min_spec(d);
            m.le_spec(x)
        }),
    {
        let m = a.min_spec(b).min_spec(c).min_spec(d);
        Rational::lemma_min_le_left(a, b);
        Rational::lemma_min_le_right(a, b);
        Rational::lemma_min_le_left(a.min_spec(b), c);
        Rational::lemma_min_le_right(a.min_spec(b), c);
        Rational::lemma_min_le_left(a.min_spec(b).min_spec(c), d);
        Rational::lemma_min_le_right(a.min_spec(b).min_spec(c), d);

        // m <= a
        Rational::lemma_le_transitive(m, a.min_spec(b).min_spec(c), a.min_spec(b));
        Rational::lemma_le_transitive(m, a.min_spec(b), a);
        // m <= b
        Rational::lemma_le_transitive(m, a.min_spec(b), b);
        // m <= c
        Rational::lemma_le_transitive(m, a.min_spec(b).min_spec(c), c);

        if a.le_spec(x) {
            Rational::lemma_le_transitive(m, a, x);
        } else if b.le_spec(x) {
            Rational::lemma_le_transitive(m, b, x);
        } else if c.le_spec(x) {
            Rational::lemma_le_transitive(m, c, x);
        } else {
            Rational::lemma_le_transitive(m, d, x);
        }
    }

    /// max of four values is >= any value that has some corner >= it.
    proof fn lemma_max4_ge(a: Rational, b: Rational, c: Rational, d: Rational, x: Rational)
        requires
            x.le_spec(a) || x.le_spec(b) || x.le_spec(c) || x.le_spec(d),
        ensures ({
            let m = a.max_spec(b).max_spec(c).max_spec(d);
            x.le_spec(m)
        }),
    {
        let m = a.max_spec(b).max_spec(c).max_spec(d);
        Rational::lemma_max_ge_left(a, b);
        Rational::lemma_max_ge_right(a, b);
        Rational::lemma_max_ge_left(a.max_spec(b), c);
        Rational::lemma_max_ge_right(a.max_spec(b), c);
        Rational::lemma_max_ge_left(a.max_spec(b).max_spec(c), d);
        Rational::lemma_max_ge_right(a.max_spec(b).max_spec(c), d);

        // a <= m
        Rational::lemma_le_transitive(a, a.max_spec(b), a.max_spec(b).max_spec(c));
        Rational::lemma_le_transitive(a, a.max_spec(b).max_spec(c), m);
        // b <= m
        Rational::lemma_le_transitive(b, a.max_spec(b), a.max_spec(b).max_spec(c));
        Rational::lemma_le_transitive(b, a.max_spec(b).max_spec(c), m);
        // c <= m
        Rational::lemma_le_transitive(c, a.max_spec(b).max_spec(c), m);

        if x.le_spec(a) {
            Rational::lemma_le_transitive(x, a, m);
        } else if x.le_spec(b) {
            Rational::lemma_le_transitive(x, b, m);
        } else if x.le_spec(c) {
            Rational::lemma_le_transitive(x, c, m);
        } else {
            Rational::lemma_le_transitive(x, d, m);
        }
    }

    // ── Containment lemmas ───────────────────────────────────────

    /// Addition containment: x in A, y in B => x+y in A+B.
    pub proof fn lemma_add_containment(a: Self, b: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.contains_spec(x),
            b.contains_spec(y),
        ensures
            a.add_spec(b).contains_spec(x.add_spec(y)),
    {
        Rational::lemma_le_add_both(a.lo, x, b.lo, y);
        Rational::lemma_le_add_both(x, a.hi, y, b.hi);
    }

    /// Negation containment: x in A => -x in -A.
    pub proof fn lemma_neg_containment(a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            a.neg_spec().contains_spec(x.neg_spec()),
    {
        Rational::lemma_neg_reverses_le(x, a.hi);
        Rational::lemma_neg_reverses_le(a.lo, x);
    }

    /// Subtraction containment: x in A, y in B => x-y in A-B.
    pub proof fn lemma_sub_containment(a: Self, b: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.contains_spec(x),
            b.contains_spec(y),
        ensures
            a.sub_spec(b).contains_spec(x.sub_spec(y)),
    {
        // Lower bound: a.lo - b.hi <= x - y
        Rational::lemma_sub_le_monotone_left(a.lo, x, b.hi);
        Rational::lemma_sub_le_monotone_right(y, b.hi, x);
        Rational::lemma_le_transitive(
            a.lo.sub_spec(b.hi), x.sub_spec(b.hi), x.sub_spec(y));

        // Upper bound: x - y <= a.hi - b.lo
        Rational::lemma_sub_le_monotone_left(x, a.hi, y);
        Rational::lemma_sub_le_monotone_right(b.lo, y, a.hi);
        Rational::lemma_le_transitive(
            x.sub_spec(y), a.hi.sub_spec(y), a.hi.sub_spec(b.lo));
    }

    /// Helper: for fixed y, multiplication is monotone or anti-monotone in x.
    /// Specifically: lo <= x <= hi implies min(lo*y, hi*y) <= x*y <= max(lo*y, hi*y).
    proof fn lemma_mul_between(lo: Rational, hi: Rational, y: Rational, x: Rational)
        requires
            lo.le_spec(x),
            x.le_spec(hi),
        ensures
            lo.mul_spec(y).min_spec(hi.mul_spec(y)).le_spec(x.mul_spec(y)),
            x.mul_spec(y).le_spec(lo.mul_spec(y).max_spec(hi.mul_spec(y))),
    {
        let zero = Rational::from_int_spec(0);
        let ly = lo.mul_spec(y);
        let xy = x.mul_spec(y);
        let hy = hi.mul_spec(y);

        // Use trichotomy to determine sign of y
        Rational::lemma_trichotomy(zero, y);

        if zero.le_spec(y) {
            // y >= 0: multiplication preserves order
            // lo <= x => lo*y <= x*y
            Rational::lemma_le_mul_nonneg(lo, x, y);
            // x <= hi => x*y <= hi*y
            Rational::lemma_le_mul_nonneg(x, hi, y);
            // ly <= xy, so min(ly, hy) <= ly <= xy
            Rational::lemma_min_le_left(ly, hy);
            Rational::lemma_le_transitive(ly.min_spec(hy), ly, xy);
            // xy <= hy, so xy <= hy <= max(ly, hy)
            Rational::lemma_max_ge_right(ly, hy);
            Rational::lemma_le_transitive(xy, hy, ly.max_spec(hy));
        } else {
            // y < 0, so -y > 0. Multiplication reverses order.
            // lo <= x and y < 0 => x*y <= lo*y
            // Use: lemma_le_mul_nonneg on negated y.
            // -y > 0 (from y < 0)
            // We need 0 <= -y. y < 0 => y <= 0 => -0 <= -y => 0 <= -y.
            // We need: lo <= x and (-y) >= 0 => lo*(-y) <= x*(-y)
            //   i.e., -(lo*y) <= -(x*y) i.e., x*y <= lo*y
            let ny = y.neg_spec();
            // 0 <= -y (from y <= 0; actually y < 0 so -y > 0)
            // But we need 0.le_spec(ny). y.lt_spec(zero) means y < 0,
            // which means -y > 0 which means 0 <= -y.
            // lemma_neg_reverses_le: y.le_spec(zero) => zero.neg_spec().le_spec(y.neg_spec())
            // zero.neg_spec() = {num: 0, den: 0} = zero. So zero.le_spec(ny).
            // But first we need y.le_spec(zero). From y.lt_spec(zero):
            Rational::lemma_lt_implies_le(y, zero);
            Rational::lemma_neg_reverses_le(y, zero);
            // Now: zero.neg_spec().le_spec(y.neg_spec())
            // zero.neg_spec() has num = -0 = 0, den = 0. So structurally it might
            // differ from zero = {num: 0, den: 0}... -0 as int == 0, so it's the same.

            // lo <= x, 0 <= ny => lo * ny <= x * ny
            Rational::lemma_le_mul_nonneg(lo, x, ny);
            // lo * (-y) <= x * (-y)
            // By mul_neg_right: a * (-b) eqv -(a * b)
            Rational::lemma_mul_neg_right(lo, y);
            Rational::lemma_mul_neg_right(x, y);
            // lo * ny eqv -(lo * y), x * ny eqv -(x * y)
            // So -(lo*y) <= -(x*y) => x*y <= lo*y
            // Need: eqv + le relationship. If a eqv a' and b eqv b' and a <= b, then a' <= b'.
            Rational::lemma_eqv_symmetric(lo.mul_spec(ny), lo.mul_spec(y).neg_spec());
            Rational::lemma_eqv_symmetric(x.mul_spec(ny), x.mul_spec(y).neg_spec());
            // lo.mul_spec(y).neg_spec() eqv lo.mul_spec(ny) and lo.mul_spec(ny) <= x.mul_spec(ny)
            // and x.mul_spec(ny) eqv x.mul_spec(y).neg_spec()
            // So lo.mul_spec(y).neg_spec() <= x.mul_spec(y).neg_spec()
            Rational::lemma_cross_mul_le(lo.mul_spec(ny), x.mul_spec(ny));
            Rational::lemma_cross_mul_le(lo.mul_spec(y).neg_spec(), lo.mul_spec(ny));
            // This is getting very verbose. Let me use a different approach.
            // x <= hi, 0 <= ny => x * ny <= hi * ny
            Rational::lemma_le_mul_nonneg(x, hi, ny);
            // So: lo*ny <= x*ny <= hi*ny
            // Which means: -(lo*y) <= -(x*y) <= -(hi*y)
            // Which means: hi*y <= x*y <= lo*y
            // So min(lo*y, hi*y) = hi*y <= x*y <= lo*y = max(lo*y, hi*y)
            // We need to connect eqv to le_spec properly.

            // Actually, let me try the direct approach using lemma_neg_reverses_le
            // We have lo*ny <= x*ny (proven above)
            // mul_neg_right: lo * ny eqv -(lo*y), x * ny eqv -(x*y)
            // So -(lo*y) eqv lo*ny and lo*ny <= x*ny and x*ny eqv -(x*y)
            // Need: -(lo*y) <= -(x*y)
            // Then: neg_reverses_le gives x*y <= lo*y.

            // Instead of going through eqv, let me use a cleaner factoring.
            // Direct: lo <= x => lo*y >= x*y when y < 0. I.e., x*y <= lo*y.
            // Proof: lo <= x => x - lo >= 0. y < 0. (x-lo)*y <= 0.
            // x*y - lo*y <= 0 => x*y <= lo*y.
            // But expressing this in terms of available lemmas is hard.

            // Simplest available: lemma_lt_mul_negative(a, b, c):
            //   a < b && c < 0 => b*c < a*c (strict, reverses order)
            // But we need non-strict. Use le = lt_or_eqv.

            // Or: just use lemma_neg_reverses_le twice.
            // We proved: lo*ny <= x*ny and x*ny <= hi*ny
            // We know: lo*ny eqv -(lo*y) and x*ny eqv -(x*y) and hi*ny eqv -(hi*y)
            // From -(lo*y) <= -(x*y) we get x*y <= lo*y (by neg_reverses_le on negatives)
            // Hmm but we need to go from the eqv to the le relationship.

            // Let me just use neg_reverses_le with mul_nonneg:
            // lo*ny <= x*ny (from le_mul_nonneg, proven)
            // Negate both: -(x*ny) <= -(lo*ny)
            Rational::lemma_neg_reverses_le(lo.mul_spec(ny), x.mul_spec(ny));
            // -(x*ny) <= -(lo*ny)
            // Now: -(x*ny) eqv x*y and -(lo*ny) eqv lo*y
            // by neg_involution + mul_neg_right:
            // x * ny = x * (-y). -(x * (-y)) = x * y (by neg of neg in mul)
            // Hmm, we need lemma_neg_involution or lemma_neg_involution.
            // Or: mul_neg_right says a*(-b) eqv -(a*b). So -(a*(-b)) eqv -(-(a*b)) eqv a*b.

            // This proof path is correct but requires many steps through eqv.
            // For now, let me restructure to avoid this complexity.
            // I'll just accept that the y >= 0 case works and note that the y < 0
            // case needs a lemma_le_mul_nonpos or similar.

            // CLEAN APPROACH: Since we need le between eqv-related terms,
            // and le + eqv should compose, let me check if there's a direct lemma.
            // There's no lemma_le_mul_nonpos in the existing library.
            // But there IS this combination that should work:

            // We want: hi*y <= x*y <= lo*y (when y <= 0).
            // Equivalent to: -lo*y <= -x*y <= -hi*y (negate all)
            // i.e., lo*(-y) <= x*(-y) <= hi*(-y)  (using mul_neg_right eqv)
            // We proved lo*ny <= x*ny <= hi*ny with ny = -y >= 0.
            // Now use neg_reverses_le:
            //   x*ny <= hi*ny => -(hi*ny) <= -(x*ny)
            //   lo*ny <= x*ny => -(x*ny) <= -(lo*ny)
            // Then mul_neg_right + neg_involution give:
            //   -(a * ny) eqv -(a * (-y)) eqv a * y  (for any a)
            // So -(hi*ny) eqv hi*y, -(x*ny) eqv x*y, -(lo*ny) eqv lo*y.
            // Need to transfer le through eqv. Use cross_mul_le or direct eqv_implies_le + le_transitive.

            // OK - I'll write out the detailed proof. It's verbose but correct.

            // Step 1: x*ny <= hi*ny => -(hi*ny) <= -(x*ny)
            Rational::lemma_neg_reverses_le(x.mul_spec(ny), hi.mul_spec(ny));

            // Step 2: lo*ny <= x*ny => -(x*ny) <= -(lo*ny)
            Rational::lemma_neg_reverses_le(lo.mul_spec(ny), x.mul_spec(ny));

            // Step 3: Relate negated products to original products via eqv.
            // a * (-y) eqv -(a * y) means -(a * (-y)) eqv a * y (by neg_neg / neg_involution)
            Rational::lemma_mul_neg_right(hi, y); // hi*(-y) eqv -(hi*y)
            Rational::lemma_neg_involution(hi.mul_spec(y)); // -(-(hi*y)) eqv hi*y
            // So -(hi*ny) eqv -(hi*(-y)) = -(-(hi*y)) eqv hi*y
            // But -(hi*ny) and -(hi*(-y)) — are these the same structurally?
            // ny = y.neg_spec() = {num: -y.num, den: y.den}
            // hi * ny is hi.mul_spec(ny). And hi*(-y) = hi.mul_spec(y.neg_spec()) = hi.mul_spec(ny).
            // So yes, they're the same. -(hi*ny) eqv hi*y by neg_neg composed with mul_neg_right.

            // We need: hi*y.le_spec(x*y) from -(hi*ny).le_spec(-(x*ny))
            // and -(hi*ny) eqv hi*y, -(x*ny) eqv x*y.
            // Use the eqv+le chain.

            // For -(x*ny) eqv x*y:
            Rational::lemma_mul_neg_right(x, y);
            Rational::lemma_neg_involution(x.mul_spec(y));

            // For -(lo*ny) eqv lo*y:
            Rational::lemma_mul_neg_right(lo, y);
            Rational::lemma_neg_involution(lo.mul_spec(y));

            // Now: -(hi*ny) eqv hi*y (via mul_neg_right + neg_neg)
            // and: -(hi*ny) <= -(x*ny) (from step 1)
            // and: -(x*ny) eqv x*y (via mul_neg_right + neg_neg)
            // So: hi*y eqv -(hi*ny) <= -(x*ny) eqv x*y
            // Need: hi*y.le_spec(x*y)
            // Use eqv_implies_le + le_transitive.
            // -(hi*ny).eqv_spec(hi*y) means hi*y.eqv_spec(-(hi*ny))
            Rational::lemma_eqv_symmetric(hi.mul_spec(ny).neg_spec(), hi.mul_spec(y));
            // Now hi*y eqv -(hi*ny). eqv_implies_le: hi*y <= -(hi*ny)
            Rational::lemma_eqv_implies_le(hi.mul_spec(y), hi.mul_spec(ny).neg_spec());
            // -(hi*ny) <= -(x*ny) (step 1)
            Rational::lemma_le_transitive(hi.mul_spec(y), hi.mul_spec(ny).neg_spec(), x.mul_spec(ny).neg_spec());
            // -(x*ny) eqv x*y => -(x*ny) <= x*y
            Rational::lemma_eqv_implies_le(x.mul_spec(ny).neg_spec(), x.mul_spec(y));
            Rational::lemma_le_transitive(hi.mul_spec(y), x.mul_spec(ny).neg_spec(), x.mul_spec(y));
            // hi*y <= x*y ✓

            // Similarly: x*y <= lo*y
            // -(x*ny) <= -(lo*ny) (step 2)
            // -(x*ny) eqv x*y, -(lo*ny) eqv lo*y
            Rational::lemma_eqv_implies_le(x.mul_spec(y), x.mul_spec(ny).neg_spec());
            Rational::lemma_le_transitive(x.mul_spec(y), x.mul_spec(ny).neg_spec(), lo.mul_spec(ny).neg_spec());
            Rational::lemma_eqv_implies_le(lo.mul_spec(ny).neg_spec(), lo.mul_spec(y));
            Rational::lemma_le_transitive(x.mul_spec(y), lo.mul_spec(ny).neg_spec(), lo.mul_spec(y));
            // x*y <= lo*y ✓

            // So when y < 0: hi*y <= x*y <= lo*y
            // min(ly, hy) = hy, max(ly, hy) = ly
            Rational::lemma_min_le_right(ly, hy);
            Rational::lemma_le_transitive(ly.min_spec(hy), hy, xy);
            Rational::lemma_max_ge_left(ly, hy);
            Rational::lemma_le_transitive(xy, ly, ly.max_spec(hy));
        }
    }

    /// Multiplication containment: x in A, y in B => x*y in A*B.
    ///
    /// Proof strategy: two applications of lemma_mul_between.
    /// Step 1: Fix y. a.lo <= x <= a.hi => min(a.lo*y, a.hi*y) <= x*y <= max(a.lo*y, a.hi*y).
    /// Step 2: Fix a.lo/a.hi. b.lo <= y <= b.hi => each endpoint product is bounded by corners.
    /// Step 3: Combine via min4/max4.
    pub proof fn lemma_mul_containment(a: Self, b: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.contains_spec(x),
            b.contains_spec(y),
        ensures
            a.mul_spec(b).contains_spec(x.mul_spec(y)),
    {
        let xy = x.mul_spec(y);
        let ac = a.lo.mul_spec(b.lo);
        let ad = a.lo.mul_spec(b.hi);
        let bc = a.hi.mul_spec(b.lo);
        let bd = a.hi.mul_spec(b.hi);
        let lo_y = a.lo.mul_spec(y);
        let hi_y = a.hi.mul_spec(y);

        // Step 1: x in [a.lo, a.hi] => min(a.lo*y, a.hi*y) <= x*y <= max(a.lo*y, a.hi*y)
        Self::lemma_mul_between(a.lo, a.hi, y, x);

        // Step 2a: y in [b.lo, b.hi] => min(a.lo*b.lo, a.lo*b.hi) <= a.lo*y <= max(a.lo*b.lo, a.lo*b.hi)
        // Use mul_between with roles swapped: we need a.lo * [b.lo..b.hi] bounds.
        // lemma_mul_between(lo, hi, multiplier, x) gives bounds on x*multiplier.
        // We want bounds on a.lo * y where y in [b.lo, b.hi].
        // That's: b.lo <= y <= b.hi => min(b.lo*a.lo, b.hi*a.lo) <= y*a.lo <= max(b.lo*a.lo, b.hi*a.lo)
        // Then use commutativity: y*a.lo = a.lo*y.
        Self::lemma_mul_between(b.lo, b.hi, a.lo, y);
        // This gives: min(b.lo*a.lo, b.hi*a.lo) <= y*a.lo <= max(b.lo*a.lo, b.hi*a.lo)
        // By commutativity: b.lo*a.lo eqv a.lo*b.lo = ac, b.hi*a.lo eqv a.lo*b.hi = ad
        // And y*a.lo eqv a.lo*y = lo_y
        Rational::lemma_mul_commutative(b.lo, a.lo);
        Rational::lemma_mul_commutative(b.hi, a.lo);
        Rational::lemma_mul_commutative(y, a.lo);
        // Now we have eqv relationships. Need to transfer the le through eqv.
        // b.lo*a.lo eqv ac, b.hi*a.lo eqv ad, y*a.lo eqv lo_y
        // min(b.lo*a.lo, b.hi*a.lo) <= y*a.lo
        // Need: min(ac, ad) <= lo_y (via eqv transfer)
        // This requires careful le+eqv chaining... but since eqv means cross-multiplication
        // equality, and min_spec is defined via le_spec which is cross-multiplication,
        // the SMT solver should handle eqv terms that are literally == (structural).
        // Actually, b.lo*a.lo and a.lo*b.lo may not be structurally equal.
        // mul_spec(a, b) = { num: a.num * b.num, den: a.den * b.den + a.den + b.den }
        // mul_spec(b, a) = { num: b.num * a.num, den: b.den * a.den + b.den + a.den }
        // These differ structurally if a != b! So we can't just substitute.
        // The eqv relationship holds but structural equality doesn't.
        // We need to propagate through eqv explicitly.

        // This approach is getting very complex. Let me use a simpler, direct approach
        // that avoids the commutativity issue: use lemma_le_mul_nonneg with case splits
        // on the sign of the fixed multiplier.

        // Step 2b: Similarly for a.hi * y.
        Self::lemma_mul_between(b.lo, b.hi, a.hi, y);
        Rational::lemma_mul_commutative(b.lo, a.hi);
        Rational::lemma_mul_commutative(b.hi, a.hi);
        Rational::lemma_mul_commutative(y, a.hi);

        // OK, the commutativity issue means this two-step approach needs eqv transfer
        // which is very verbose. Let me take a completely different strategy:
        // Just use the min4/max4 helpers with direct case analysis on signs.

        // We need: min4(ac,ad,bc,bd) <= xy <= max4(ac,ad,bc,bd)
        // Strategy: show there exists a corner product <= xy and a corner product >= xy.
        // Case-split on signs of x and y, using trichotomy.
        let zero = Rational::from_int_spec(0);
        Rational::lemma_trichotomy(zero, x);
        Rational::lemma_trichotomy(zero, y);

        // For the lower bound, we need: SOME corner <= xy
        // For the upper bound, we need: xy <= SOME corner

        if zero.le_spec(x) {
            if zero.le_spec(y) {
                // x >= 0, y >= 0
                // Upper: x <= a.hi, y <= b.hi, both >= 0 => xy <= bd
                Rational::lemma_le_transitive(zero, x, a.hi);
                Rational::lemma_le_transitive(zero, y, b.hi);
                Rational::lemma_le_mul_nonneg_both(x, a.hi, y, b.hi);
                Self::lemma_max4_ge(ac, ad, bc, bd, xy);
                // Lower: a.lo <= x, 0 <= y => a.lo*y <= x*y.
                //   b.lo <= y, 0 <= x => ... but we need a corner <= xy.
                //   Since 0 <= x*y (product of nonneg), we just need a corner <= 0 or a corner <= xy.
                //   If a.lo >= 0 and b.lo >= 0: ac <= xy by le_mul_nonneg_both.
                //   If a.lo < 0: ad = a.lo * b.hi. If b.hi >= 0, ad <= 0 <= xy (since a.lo < 0, b.hi >= 0).
                //     Actually ad could be negative or zero, but we need ad.le_spec(xy).
                //     a.lo <= 0 <= x and 0 <= y: a.lo * y <= 0 <= xy (since a.lo <= 0 and y >= 0 => a.lo*y <= 0)
                //     and a.lo * y <= a.lo * b.hi = ad (since a.lo <= 0 and y <= b.hi => ... no, reversed)
                //     Hmm.
                // Let me use the fact from Step 1: min(lo_y, hi_y) <= xy.
                // Then show min(lo_y, hi_y) >= some corner.
                // lo_y = a.lo * y. y >= 0, so a.lo*y is between a.lo*b.lo and a.lo*b.hi
                //   (i.e., lo_y is between ac and ad... if a.lo >= 0 then ac <= lo_y <= ad,
                //    if a.lo <= 0 then ad <= lo_y <= ac).
                // In either case: min(ac, ad) <= lo_y <= max(ac, ad).
                // Similarly hi_y = a.hi * y is between bc and bd.
                // So min(lo_y, hi_y) >= min(min(ac,ad), min(bc,bd)) = min4(ac,ad,bc,bd).
                // And max(lo_y, hi_y) <= max(max(ac,ad), max(bc,bd)) = max4(ac,ad,bc,bd).
                // This is the right approach but requires bounding lo_y and hi_y by corners.

                // lo_y = a.lo * y. Since y >= 0:
                // b.lo <= y => a.lo*b.lo and a.lo*y have relationship depending on sign of a.lo.
                // Direct: use lemma_le_mul_nonneg(b.lo, y, a.lo) if a.lo >= 0 => a.lo*b.lo <= a.lo*y = lo_y, so ac <= lo_y
                // Or use le_mul_nonneg(y, b.hi, a.lo) => a.lo*y <= a.lo*b.hi = ad
                // If a.lo < 0 then reversed: a.lo*y <= a.lo*b.lo = ac (since y >= b.lo and a.lo < 0)

                // Regardless of sign of a.lo: min(ac, ad) <= lo_y.
                // Similarly: min(bc, bd) <= hi_y (since a.hi >= a.lo >= ... and y >= 0).
                // Then min4 <= min(min(ac,ad), min(bc,bd)) <= min(lo_y, hi_y) <= xy.

                // But this requires more min/max chaining. Let me just do the simple case split.
                if zero.le_spec(a.lo) {
                    // 0 <= a.lo <= x, 0 <= b.lo <= y => ac <= xy
                    if zero.le_spec(b.lo) {
                        Rational::lemma_le_mul_nonneg_both(a.lo, x, b.lo, y);
                    } else {
                        // 0 <= a.lo, b.lo < 0 but y >= 0
                        // ac = a.lo * b.lo <= 0 (since a.lo >= 0, b.lo <= 0)
                        // xy >= 0 (since x >= 0, y >= 0)
                        Rational::lemma_lt_implies_le(b.lo, zero);
                        Rational::lemma_le_mul_nonneg(b.lo, zero, a.lo);
                        Rational::lemma_mul_commutative(b.lo, a.lo);
                        Rational::lemma_mul_commutative(zero, a.lo);
                        // a.lo * b.lo <= a.lo * 0
                        Rational::lemma_mul_one_identity(a.lo);
                        // a.lo * 0: need to show this eqv 0. Use mul_zero.
                        Rational::lemma_mul_zero(a.lo);
                        Rational::lemma_eqv_implies_le(a.lo.mul_spec(zero), zero);
                        Rational::lemma_le_transitive(ac, a.lo.mul_spec(zero), zero);
                        // ac <= 0
                        // 0 <= xy: x >= 0, y >= 0
                        Rational::lemma_le_mul_nonneg_both(zero, x, zero, y);
                        Rational::lemma_mul_zero(zero);
                        Rational::lemma_eqv_implies_le(zero, zero.mul_spec(zero));
                        Rational::lemma_le_transitive(zero, zero.mul_spec(zero), xy);
                        // 0 <= xy
                        Rational::lemma_le_transitive(ac, zero, xy);
                    }
                } else {
                    // a.lo < 0, x >= 0, y >= 0
                    // ad = a.lo * b.hi. a.lo < 0. If b.hi >= 0: ad <= 0 <= xy.
                    Rational::lemma_lt_implies_le(a.lo, zero);
                    Rational::lemma_le_transitive(a.lo, zero, a.hi);
                    // b.hi >= b.lo (wf), and b.hi >= y >= 0
                    Rational::lemma_le_transitive(zero, y, b.hi);
                    // ad = a.lo * b.hi. a.lo <= 0, b.hi >= 0 => ad <= 0
                    Rational::lemma_le_mul_nonneg(a.lo, zero, b.hi);
                    Rational::lemma_mul_commutative(a.lo, b.hi);
                    Rational::lemma_mul_commutative(zero, b.hi);
                    Rational::lemma_mul_zero(b.hi);
                    Rational::lemma_eqv_implies_le(b.hi.mul_spec(zero), zero);
                    // a.lo * b.hi <= 0 * b.hi eqv 0 => ad <= 0
                    Rational::lemma_le_transitive(ad, b.hi.mul_spec(zero), zero);
                    // 0 <= xy (same as above)
                    Rational::lemma_le_mul_nonneg_both(zero, x, zero, y);
                    Rational::lemma_mul_zero(zero);
                    Rational::lemma_eqv_implies_le(zero, zero.mul_spec(zero));
                    Rational::lemma_le_transitive(zero, zero.mul_spec(zero), xy);
                    Rational::lemma_le_transitive(ad, zero, xy);
                }
                Self::lemma_min4_le(ac, ad, bc, bd, xy);
            } else {
                // x >= 0, y < 0
                Rational::lemma_lt_implies_le(y, zero);
                // Upper: need xy <= SOME corner.
                // x >= 0, y <= 0 => xy <= 0. Need a corner >= 0.
                // bc = a.hi * b.lo. a.hi >= x >= 0 and b.lo <= y < 0.
                // If a.hi >= 0 and b.lo <= 0, bc <= 0. Hmm.
                // ac = a.lo * b.lo. If a.lo <= 0 and b.lo <= 0, ac >= 0. That's a corner >= 0 >= xy.
                // If a.lo > 0, ac = a.lo * b.lo < 0 (since b.lo < 0). So ac < 0.
                // Then try ad = a.lo * b.hi. b.hi >= b.lo, and if b.hi >= 0, ad >= 0 (if a.lo >= 0).
                // This is getting into many subcases. Let me use a systematic approach.

                // For x >= 0, y < 0:
                // xy <= 0 (since x >= 0, y < 0, or x = 0 => xy = 0)
                // Upper bound: need corner >= 0 or corner >= xy.
                // a.lo * b.lo: if a.lo < 0 and b.lo < 0 then >= 0 (product of negatives)
                // a.hi * b.hi: if a.hi >= 0 and b.hi >= 0 then >= 0

                // Lower bound: xy >= x * b.lo (since y >= b.lo and x >= 0... no, y < b.lo??)
                // Wait: y in [b.lo, b.hi] means b.lo <= y <= b.hi. And y < 0.
                // x >= 0: x * b.lo <= x * y (if... no, b.lo <= y and x >= 0 => x*b.lo <= x*y)
                // Hmm: lemma_le_mul_nonneg(b.lo, y, x): b.lo <= y, 0 <= x => b.lo*x <= y*x
                // i.e., x*b.lo <= x*y = xy. But x*b.lo = bc? No, bc = a.hi * b.lo.
                // We need a.lo*b.lo or a.hi*b.lo <= xy... Let's use:

                // b.lo <= y, x >= 0 => x*b.lo <= x*y (= xy)
                Rational::lemma_le_mul_nonneg(b.lo, y, x);
                Rational::lemma_mul_commutative(b.lo, x);
                Rational::lemma_mul_commutative(y, x);
                // x * b.lo <= xy. And a.lo <= x, b.lo <= 0... a.hi >= x >= 0 so
                // a.hi * b.lo <= x * b.lo (since b.lo <= 0 and a.hi >= x, reversed mult)
                // Actually: a.hi >= x >= 0 and b.lo <= 0 => a.hi * b.lo <= x * b.lo
                // This is: le_mul_nonneg with b.lo reversed...
                // Use: x <= a.hi, 0 <= (-b.lo) => x*(-b.lo) <= a.hi*(-b.lo)
                // => -(x*b.lo) <= -(a.hi*b.lo) => a.hi*b.lo <= x*b.lo
                // So bc <= x*b.lo <= xy. We found: bc <= xy. ✓ for lower bound.
                // But proving bc <= x*b.lo requires the neg manipulation again.
                // Let me use lemma_mul_between instead.
                // a.lo <= x <= a.hi, fix b.lo as multiplier.
                Self::lemma_mul_between(a.lo, a.hi, b.lo, x);
                // min(a.lo*b.lo, a.hi*b.lo) <= x*b.lo
                // And we showed x*b.lo <= xy.
                // So min(ac, bc) <= xy.
                let xblo = x.mul_spec(b.lo);
                Rational::lemma_le_transitive(ac.min_spec(bc), xblo, xy);
                // min(ac, bc) <= xy => ac <= xy or bc <= xy (in the min sense)
                // Use: min4(ac,ad,bc,bd) <= min(ac, bc) by being a further min.
                Rational::lemma_min_le_left(ac, bc);
                Rational::lemma_min_le_right(ac, bc);
                // min(ac, bc) <= ac and min(ac, bc) <= bc
                // min4 <= ac and min4 <= bc (via the general min4 relationships)
                // Actually, we need: min4 <= min(ac, bc) to chain.
                // min4 = min(min(min(ac, ad), bc), bd)
                // min(ac, ad) <= ac. min(min(ac,ad), bc) <= min(ac,ad) <= ac
                // and min(min(ac,ad), bc) <= bc.
                // So min(min(ac,ad), bc) <= min(ac, bc).
                // And min4 <= min(min(ac,ad), bc).
                // Hmm, this is getting complicated. Let me just directly use lemma_min4_le.
                // We showed min(ac, bc) <= xy. Need: ac <= xy or bc <= xy (one of them).
                // Actually min(ac, bc) <= xy means: if ac <= bc then ac <= xy, else bc <= xy.
                // But we can just assert: since min(ac,bc) <= xy, and ac <= xy or bc <= xy
                // follows from ac being the min or bc being the min.
                // The simplest: ac.min_spec(bc).le_spec(xy) was just proven.
                // We need min4 <= xy. Since min4 <= ac and min4 <= bc:
                Rational::lemma_min_le_left(ac.min_spec(ad), bc);
                Rational::lemma_min_le_left(ac, ad);
                Rational::lemma_le_transitive(ac.min_spec(ad).min_spec(bc), ac.min_spec(ad), ac);
                // min3 <= ac. Similarly min3 <= bc.
                Rational::lemma_min_le_right(ac.min_spec(ad), bc);
                // So min3 <= min(ac, bc)
                // And min4 <= min3
                Rational::lemma_min_le_left(ac.min_spec(ad).min_spec(bc), bd);
                Rational::lemma_le_transitive(ac.min_spec(ad).min_spec(bc).min_spec(bd), ac.min_spec(ad).min_spec(bc), ac);
                // This is too many lines. Let me just use lemma_min4_le directly.
                // We proved: ac.min_spec(bc) <= xy. So either ac <= xy or bc <= xy.
                // In either case, lemma_min4_le applies.
                // Since min(ac, bc) <= xy:
                // If ac.le_spec(bc), then ac = min(ac,bc), so ac <= xy.
                // If !ac.le_spec(bc), then bc = min(ac,bc), so bc <= xy.
                // So ac.le_spec(xy) || bc.le_spec(xy).
                // Either way, lemma_min4_le gives min4 <= xy.

                // Let me try a clean approach: assert both, let SMT figure it out.
                // ac.min_spec(bc).le_spec(xy) was proven.
                // min4_le needs ac <= xy or ad <= xy or bc <= xy or bd <= xy.
                // We can show: if ac <= bc then ac <= xy, else bc <= xy.
                // min_spec(ac, bc) = if ac.le_spec(bc) then ac else bc.
                // So min(ac,bc) = ac when ac <= bc, and = bc otherwise.
                // In first case: ac = min(ac,bc) <= xy, so ac <= xy. ✓
                // In second case: bc = min(ac,bc) <= xy, so bc <= xy. ✓
                if ac.le_spec(bc) {
                    // ac = min(ac, bc) <= xy
                    assert(ac.le_spec(xy));
                } else {
                    // bc = min(ac, bc) <= xy
                    assert(bc.le_spec(xy));
                }
                Self::lemma_min4_le(ac, ad, bc, bd, xy);

                // Upper: x*y <= x*b.hi (since x >= 0, y <= b.hi => x*y <= x*b.hi)
                Rational::lemma_le_mul_nonneg(y, b.hi, x);
                Rational::lemma_mul_commutative(y, x);
                Rational::lemma_mul_commutative(b.hi, x);
                let xbhi = x.mul_spec(b.hi);
                // xy <= xbhi
                // x*b.hi in [min(a.lo*b.hi, a.hi*b.hi), max(a.lo*b.hi, a.hi*b.hi)]
                Self::lemma_mul_between(a.lo, a.hi, b.hi, x);
                // xbhi <= max(a.lo*b.hi, a.hi*b.hi) = max(ad, bd)
                Rational::lemma_max_ge_left(ad, bd);
                Rational::lemma_max_ge_right(ad, bd);
                // max(ad, bd) <= max4
                if ad.le_spec(bd) {
                    // max(ad, bd) = bd, so xbhi <= bd
                    assert(xbhi.le_spec(bd));
                } else {
                    // max(ad, bd) = ad, so xbhi <= ad
                    assert(xbhi.le_spec(ad));
                }
                Rational::lemma_le_transitive(xy, xbhi, ad.max_spec(bd));
                Self::lemma_max4_ge(ac, ad, bc, bd, xy);
            }
        } else {
            // x < 0
            Rational::lemma_lt_implies_le(x, zero);
            if zero.le_spec(y) {
                // x < 0, y >= 0
                // Lower: x*y <= 0 (neg * nonneg). Need corner <= xy.
                // bc = a.hi * b.lo. Hmm.
                // Fix b.lo as multiplier: a.lo <= x <= a.hi, multiply by y.
                // y >= 0 => a.lo*y <= x*y <= a.hi*y (monotone)
                // So lo_y <= xy. Now lo_y = a.lo * y.
                // y in [b.lo, b.hi], fix a.lo as multiplier.
                // a.lo < 0 (since x < 0 and a.lo <= x): a.lo*b.lo >= a.lo*b.hi (reversed by neg mult)
                // So a.lo*y is between a.lo*b.hi and a.lo*b.lo, i.e., ad <= lo_y <= ac.
                // Therefore ad <= lo_y <= xy. ad <= xy. ✓

                // Use lemma_mul_between for y's range:
                Self::lemma_mul_between(b.lo, b.hi, a.lo, y);
                Rational::lemma_mul_commutative(b.lo, a.lo);
                Rational::lemma_mul_commutative(b.hi, a.lo);
                Rational::lemma_mul_commutative(y, a.lo);
                // min(b.lo*a.lo, b.hi*a.lo) <= y*a.lo = lo_y (via commutativity eqv)
                // Ugh, the commutativity issue again.

                // Let me just mirror the x>=0, y<0 case structure.
                // a.lo <= x <= a.hi, fix y as multiplier.
                // y >= 0 => a.lo*y <= x*y <= a.hi*y
                Rational::lemma_le_mul_nonneg(a.lo, x, y);
                // a.lo*y <= x*y = xy.
                // a.lo*y: a.lo in the interval endpoints. y in [b.lo, b.hi].
                // We need: min(a.lo*b.lo, a.lo*b.hi) <= a.lo*y
                Self::lemma_mul_between(b.lo, b.hi, a.lo, y);
                Rational::lemma_mul_commutative(b.lo, a.lo);
                Rational::lemma_mul_commutative(b.hi, a.lo);
                Rational::lemma_mul_commutative(y, a.lo);
                // Hmm same problem.

                // OK let me just use the direct approach like I did for x>=0, y<0.
                // Direct: y >= 0, a.lo <= x => a.lo * y <= x * y = xy
                // (from le_mul_nonneg)
                // So lo_y <= xy.
                // For lo_y = a.lo*y. Fix a.lo as scalar, y in [b.lo, b.hi].
                // If a.lo >= 0: a.lo*b.lo <= a.lo*y <= a.lo*b.hi (monotone since a.lo >= 0)
                //   => ac <= lo_y. Combined: ac <= xy.
                // If a.lo < 0: a.lo*b.hi <= a.lo*y <= a.lo*b.lo (reversed since a.lo < 0)
                //   => ad <= lo_y. Combined: ad <= xy.
                // In either case: ac <= xy or ad <= xy. ✓ for lower bound.

                if zero.le_spec(a.lo) {
                    // This can't happen since x < 0 and a.lo <= x
                    Rational::lemma_le_transitive(zero, a.lo, x);
                    // 0 <= x, contradicts x < 0
                    Rational::lemma_le_antisymmetric(zero, x);
                    // x eqv 0, so x < 0 is false? Wait, we're in the `else` branch of
                    // zero.le_spec(x), so !(zero.le_spec(x)). And now we proved zero.le_spec(x).
                    // Contradiction. But Verus proofs work with requires/ensures, not SMT False.
                    // In this branch, the precondition is self-contradictory, so any ensures holds.
                } else {
                    Rational::lemma_lt_implies_le(a.lo, zero);
                    // a.lo < 0. y >= 0. b.lo <= y <= b.hi.
                    // a.lo*y <= a.lo*b.lo = ac? NO: a.lo < 0 reverses!
                    // a.lo < 0, b.lo <= y => a.lo*y <= a.lo*b.lo (since neg*larger = smaller)
                    // Actually: b.lo <= y, a.lo < 0 => a.lo*y >= a.lo*b.lo? No...
                    // lemma_le_mul_nonneg(b.lo, y, a.lo) requires 0 <= a.lo, which is false.
                    // So we use the negative-multiplier approach.
                    // a.lo < 0, b.lo <= y: (-a.lo) > 0. b.lo <= y, (-a.lo) >= 0 =>
                    //   b.lo * (-a.lo) <= y * (-a.lo) i.e. -(b.lo * a.lo) <= -(y * a.lo)
                    //   i.e. y*a.lo <= b.lo*a.lo i.e. a.lo*y <= a.lo*b.lo = ac (via commutativity)
                    // Hmm, that means ac >= a.lo*y. So lo_y <= ac. But we want something <= xy.
                    // lo_y = a.lo * y <= xy (from le_mul_nonneg(a.lo, x, y) with y >= 0).
                    // And we need a CORNER <= xy.
                    // a.lo*y <= a.lo*b.lo means lo_y <= ac. So ac >= lo_y, and lo_y <= xy.
                    // But ac could be > or < xy. This doesn't directly give us a corner <= xy.
                    // Instead: a.lo < 0, y <= b.hi => a.lo*b.hi <= a.lo*y (neg mult with y <= b.hi reverses to a.lo*b.hi <= a.lo*y)
                    // Wait: a.lo < 0, y <= b.hi: (-a.lo) > 0, y <= b.hi =>
                    //   y * (-a.lo) <= b.hi * (-a.lo) => -(y*a.lo) <= -(b.hi*a.lo)
                    //   => b.hi*a.lo <= y*a.lo => a.lo*b.hi <= a.lo*y
                    // So ad <= lo_y. And lo_y <= xy. Therefore ad <= xy. ✓
                    // Proving ad <= lo_y requires the same neg-factor dance.

                    // Use lemma_mul_between on the "y" dimension with multiplier a.lo:
                    // b.lo <= y <= b.hi, multiplier = a.lo.
                    // lemma_mul_between gives: min(b.lo*a.lo, b.hi*a.lo) <= y*a.lo
                    // But y*a.lo eqv a.lo*y (commutativity), and b.lo*a.lo eqv ac, b.hi*a.lo eqv ad.
                    // Again, the eqv-vs-structural problem.

                    // Let me try yet another strategy: use mul_between with a.lo, a.hi as range.
                    // We proved: a.lo*y <= xy (via le_mul_nonneg(a.lo, x, y) since y >= 0)
                    // Also: xy <= a.hi*y (via le_mul_nonneg(x, a.hi, y) since y >= 0)
                    Rational::lemma_le_mul_nonneg(x, a.hi, y);
                    // So a.lo*y <= xy <= a.hi*y.

                    // Now for a.lo*y: a.lo < 0 and b.lo <= y <= b.hi.
                    // Use lemma_mul_between(b.lo, b.hi, a.lo, y):
                    // This proves min(b.lo*a.lo, b.hi*a.lo) <= y*a.lo <= max(b.lo*a.lo, b.hi*a.lo)
                    // But b.lo*a.lo and a.lo*b.lo differ structurally.
                    // Instead, let's prove ad <= a.lo*y directly.

                    // a.lo < 0 => -a.lo > 0. y <= b.hi, -a.lo >= 0 => y*(-a.lo) <= b.hi*(-a.lo)
                    let na = a.lo.neg_spec();
                    Rational::lemma_neg_reverses_le(a.lo, zero);
                    // zero.neg_spec() <= a.lo.neg_spec() = na. zero.neg_spec() has num=0, den=0.
                    // So 0 <= na... but zero.neg_spec() might not be structurally zero.
                    // Actually zero = from_int_spec(0) = {num: 0, den: 0}
                    // neg_spec = {num: -0, den: 0} = {num: 0, den: 0} = zero. So structurally same.
                    Rational::lemma_le_mul_nonneg(y, b.hi, na);
                    // y * na <= b.hi * na (since 0 <= na)
                    Rational::lemma_mul_neg_right(y, a.lo);
                    Rational::lemma_mul_neg_right(b.hi, a.lo);
                    // y * na eqv -(y * a.lo)
                    // b.hi * na eqv -(b.hi * a.lo)
                    // y*na <= b.hi*na => -(y*a.lo) <= -(b.hi*a.lo)
                    // => b.hi*a.lo <= y*a.lo
                    Rational::lemma_neg_reverses_le(y.mul_spec(na), b.hi.mul_spec(na));
                    // -(b.hi*na) <= -(y*na)
                    // We need: b.hi*a.lo <= y*a.lo
                    // From: -(b.hi * na) eqv b.hi * a.lo (via neg of neg_right)
                    // and: -(y * na) eqv y * a.lo
                    Rational::lemma_neg_involution(y.mul_spec(a.lo));
                    Rational::lemma_neg_involution(b.hi.mul_spec(a.lo));
                    // OK this is insane. I need a cleaner helper.

                    // You know what, let me just write a helper lemma for
                    // "multiplication by non-positive reverses order" and call it done.
                    // That way the containment proof becomes clean.
                    Self::lemma_le_mul_nonpos(a.lo, y, b.hi);
                    // a.lo * b.hi <= a.lo * y (i.e., ad <= lo_y)
                    Rational::lemma_le_transitive(ad, a.lo.mul_spec(y), xy);
                }
                Self::lemma_min4_le(ac, ad, bc, bd, xy);

                // Upper: xy <= a.hi*y. Need: a.hi*y <= SOME corner.
                // a.hi*y: a.hi >= x, and x < 0, so a.hi could be >= 0 or < 0.
                // y >= 0. b.lo <= y <= b.hi.
                // If a.hi >= 0: a.hi*y >= 0. a.hi*b.lo <= a.hi*y <= a.hi*b.hi (since a.hi >= 0, monotone in y).
                //   So xy <= a.hi*y <= a.hi*b.hi = bd.
                // If a.hi < 0: a.hi < 0 and y >= 0 => a.hi*y <= 0.
                //   a.hi * b.hi <= a.hi * y <= a.hi * b.lo (reversed since a.hi < 0)
                //   So xy <= a.hi*y <= a.hi*b.lo = bc.
                let hiy = a.hi.mul_spec(y);
                if zero.le_spec(a.hi) {
                    Rational::lemma_le_mul_nonneg(y, b.hi, a.hi);
                    Rational::lemma_mul_commutative(y, a.hi);
                    Rational::lemma_mul_commutative(b.hi, a.hi);
                    Rational::lemma_le_transitive(xy, hiy, bd);
                } else {
                    Rational::lemma_lt_implies_le(a.hi, zero);
                    Self::lemma_le_mul_nonpos(a.hi, b.lo, y);
                    // a.hi * y <= a.hi * b.lo = bc
                    Rational::lemma_le_transitive(xy, hiy, bc);
                }
                Self::lemma_max4_ge(ac, ad, bc, bd, xy);
            } else {
                // x < 0, y < 0
                Rational::lemma_lt_implies_le(y, zero);
                // Both negative. xy = x*y >= 0.
                // Upper: need corner >= xy.
                // ac = a.lo * b.lo. a.lo <= x < 0 and b.lo <= y < 0. Both negative.
                // Product of two negatives is positive. a.lo <= x (both neg), b.lo <= y (both neg).
                // |a.lo| >= |x|, |b.lo| >= |y|, so |a.lo * b.lo| >= |x * y|.
                // Since both products are >= 0: ac >= xy. ✓
                // Use: x <= 0, y <= 0 => (-x) >= 0, (-y) >= 0
                // a.lo <= x => -x <= -a.lo. b.lo <= y => -y <= -b.lo. All >= 0.
                // (-x)*(-y) <= (-a.lo)*(-b.lo) by le_mul_nonneg_both.
                let nx = x.neg_spec();
                let ny = y.neg_spec();
                let nalo = a.lo.neg_spec();
                let nblo = b.lo.neg_spec();
                Rational::lemma_neg_reverses_le(a.lo, x);
                Rational::lemma_neg_reverses_le(b.lo, y);
                Rational::lemma_neg_reverses_le(x, zero);
                Rational::lemma_neg_reverses_le(y, zero);
                // 0 <= nx, nx <= nalo, 0 <= ny, ny <= nblo
                Rational::lemma_le_mul_nonneg_both(nx, nalo, ny, nblo);
                // nx * ny <= nalo * nblo
                // nx*ny eqv x*y (neg*neg = pos) and nalo*nblo eqv a.lo*b.lo
                // Use mul_neg_right + neg on the result:
                // x * y = (-(-x)) * y = -((-x) * y) (NO, that's not right)
                // Actually: (-x)*(-y) = x*y. Proof:
                // (-x)*(-y) = -(x * (-y)) = -(-(x*y)) = x*y.
                Rational::lemma_mul_neg_right(x, y); // x*(-y) eqv -(x*y)
                Rational::lemma_neg_involution(x.mul_spec(y)); // -(-(x*y)) eqv x*y
                // Also: (-x)*(-y) = -(x*(-y)) (by mul_neg on first arg)
                // Hmm, we need: nx * ny eqv xy.
                // nx = -x. nx * ny = (-x) * (-y).
                // mul_neg_right(-x, y): (-x)*(-y) eqv -((-x)*y)
                Rational::lemma_mul_neg_right(nx, y);
                // nx * ny eqv -(nx * y)
                // Also: nx * y = (-x) * y eqv -(x * y) (by... )
                // Actually there's no direct "mul_neg_left" lemma.
                // But: (-x)*y = y*(-x) (commutativity) eqv -(y*x) (mul_neg_right) eqv -(x*y) (commutativity in neg)
                Rational::lemma_mul_commutative(nx, y);
                // nx * y eqv y * nx
                Rational::lemma_mul_neg_right(y, x);
                // y * nx eqv -(y * x)
                Rational::lemma_mul_commutative(y, x);
                // y * x eqv x * y
                // So y * nx eqv -(y * x) and y * x eqv x * y
                // => y * nx eqv -(x * y)
                // => -(y * nx) eqv x * y (by neg_neg)
                // But we had: nx * ny eqv -(nx * y) eqv -(y * nx) eqv x * y.

                // This chain of eqv is getting absurd. Let me just write a helper lemma
                // lemma_neg_mul_neg that says (-a)*(-b) eqv a*b, and prove it once.

                // For now, let me try a completely different approach to the whole mul_containment.
                // USE SUBTRACTION: x*y - corner = ... and show the sign.
                // Actually no. Let me just write the helper lemmas I need and call them.

                // I'll add: lemma_neg_mul_neg_eqv(a, b): (-a)*(-b) eqv a*b
                //           lemma_le_mul_nonpos(c, a, b): c <= 0, a <= b => c*b <= c*a

                Self::lemma_neg_mul_neg_eqv(x, y);
                Self::lemma_neg_mul_neg_eqv(a.lo, b.lo);
                // nx*ny eqv xy, nalo*nblo eqv ac
                // And nx*ny <= nalo*nblo (proven via le_mul_nonneg_both)
                // So xy eqv nx*ny <= nalo*nblo eqv ac
                // xy <= ac.
                Rational::lemma_eqv_symmetric(nx.mul_spec(ny), xy);
                // xy eqv nx*ny
                Rational::lemma_eqv_implies_le(xy, nx.mul_spec(ny));
                // xy <= nx*ny
                Rational::lemma_le_transitive(xy, nx.mul_spec(ny), nalo.mul_spec(nblo));
                // xy <= nalo*nblo
                Rational::lemma_eqv_implies_le(nalo.mul_spec(nblo), ac);
                // nalo*nblo <= ac
                Rational::lemma_le_transitive(xy, nalo.mul_spec(nblo), ac);
                // xy <= ac ✓
                Self::lemma_max4_ge(ac, ad, bc, bd, xy);

                // Lower: need corner <= xy.
                // x < 0, y < 0. a.hi >= x, b.hi >= y.
                // If a.hi >= 0: a.hi*y <= 0 (since y < 0). And xy >= 0. So a.hi*y <= xy? No, xy >= 0 >= a.hi*y.
                //   ad = a.lo*b.hi. a.lo < 0, b.hi >= y. If b.hi >= 0: ad <= 0 <= xy. ✓
                //   If b.hi < 0: ad = a.lo*b.hi > 0 (neg*neg). And xy >= 0. ad could be > xy.
                //   bc = a.hi*b.lo. a.hi >= 0, b.lo < 0. bc <= 0 <= xy. ✓
                //   bd = a.hi*b.hi. a.hi >= 0, b.hi could be neg or pos.
                //   Just use: bc = a.hi * b.lo. a.hi >= 0 and b.lo <= y < 0.
                //   a.hi * b.lo <= a.hi * y <= 0 <= xy. Wait, a.hi >= 0 and b.lo <= y < 0 => a.hi*b.lo <= a.hi*y
                //   (since a.hi >= 0, monotone). And a.hi*y: a.hi >= 0, y < 0, so a.hi*y <= 0.
                //   And xy >= 0. So bc <= 0 <= xy.
                // If a.hi < 0: all of a.lo, a.hi, b.lo, b.hi, x, y < 0.
                //   ad = a.lo * b.hi. a.lo < a.hi < 0 and b.lo < b.hi < 0.
                //   a.lo*b.hi: a.lo < 0, b.hi < 0 => positive. And a.hi*b.lo: a.hi < 0, b.lo < 0 => positive.
                //   Need a corner <= xy. xy > 0 (both neg).
                //   bd = a.hi*b.hi: both < 0, so bd > 0.
                //   |a.hi| <= |x| and |b.hi| <= |y| (since a.hi >= x and both neg).
                //   Actually a.hi >= x means a.hi >= x. Both neg means |a.hi| <= |x|.
                //   So |a.hi * b.hi| <= |x * y| => a.hi*b.hi <= x*y (both positive).
                //   bd <= xy. ✓
                // In summary: we can find a corner <= xy in all subcases.

                // Let me just use lemma_mul_between + lemma_mul_between approach.
                // Step 1: a.lo <= x <= a.hi, fix y (y < 0).
                Self::lemma_mul_between(a.lo, a.hi, y, x);
                // min(a.lo*y, a.hi*y) <= x*y <= max(a.lo*y, a.hi*y)
                // So min(lo_y, hi_y) <= xy.
                // lo_y = a.lo * y. a.lo <= 0, y <= 0. lo_y >= 0.
                // hi_y = a.hi * y. y <= 0. If a.hi >= 0: hi_y <= 0. If a.hi < 0: hi_y >= 0.
                // In either case, min(lo_y, hi_y) is the smaller of the two.
                // We need: some corner <= min(lo_y, hi_y) <= xy.
                // For lo_y: y < 0 and b.lo <= y <= b.hi.
                //   lemma_le_mul_nonpos for a.lo: a.lo <= 0, b.lo <= y => a.lo*y <= a.lo*b.lo = ac
                //   and a.lo <= 0, y <= b.hi => a.lo*b.hi <= a.lo*y, i.e. ad <= lo_y.
                // So ad <= lo_y. min(lo_y, hi_y) <= lo_y (or = hi_y if hi_y is smaller).
                // And ad <= lo_y. If min = lo_y, we're fine: ad <= lo_y = min <= xy.
                // If min = hi_y, we need corner <= hi_y.

                // For hi_y: a.hi * y. y < 0.
                //   If a.hi >= 0: hi_y = a.hi * y <= 0. a.hi >= 0, b.lo <= y => a.hi*b.lo <= a.hi*y.
                //     So bc <= hi_y.
                //   If a.hi < 0: hi_y = a.hi*y >= 0 (neg*neg).
                //     a.hi < 0, y <= b.hi < 0 => a.hi*b.hi <= a.hi*y (nonpos mult reverses).
                //     So bd <= hi_y.
                // In all cases we can find a corner <= the min. But let me just use a simpler structure.

                // Since we already proved xy <= ac above (for the upper bound), let's focus on lower.
                // For the lower bound, the simplest: use ad or bc or bd.

                // ad = a.lo * b.hi. a.lo < 0.
                // If b.hi >= 0: ad = neg * nonneg <= 0. And xy >= 0. So ad <= xy. ✓
                // If b.hi < 0: ad = neg * neg = pos. Hmm, could be > xy.
                //   Then try bd = a.hi * b.hi.
                //   a.hi >= x > ... a.hi could be < 0 too. Both a.hi < 0 and b.hi < 0 => bd > 0.
                //   |a.hi| <= |x|, |b.hi| <= |y|, so bd <= xy (both pos).
                //   Use: (-a.hi) <= (-x), (-b.hi) <= (-y), all >= 0.
                //   (-a.hi)*(-b.hi) <= (-x)*(-y) by le_mul_nonneg_both.
                //   (-a.hi)*(-b.hi) eqv a.hi*b.hi = bd, (-x)*(-y) eqv x*y = xy.
                //   So bd <= xy. ✓

                if zero.le_spec(b.hi) {
                    // b.hi >= 0, a.lo < 0 => ad <= 0
                    // First establish a.lo <= 0: a.lo <= x and x <= 0.
                    Rational::lemma_le_transitive(a.lo, x, zero);
                    Rational::lemma_le_mul_nonneg(a.lo, zero, b.hi);
                    Rational::lemma_mul_commutative(a.lo, b.hi);
                    Rational::lemma_mul_commutative(zero, b.hi);
                    Rational::lemma_mul_zero(b.hi);
                    Rational::lemma_eqv_implies_le(b.hi.mul_spec(zero), zero);
                    Rational::lemma_le_transitive(ad, b.hi.mul_spec(zero), zero);
                    // ad <= 0. 0 <= xy (product of two negatives).
                    // Actually 0 <= xy: x < 0, y < 0.
                    // (-x) > 0, (-y) > 0. (-x)*(-y) > 0. And (-x)*(-y) eqv xy.
                    Self::lemma_neg_mul_neg_eqv(x, y);
                    // nx * ny eqv xy. And nx > 0, ny > 0, so nx*ny > 0.
                    Rational::lemma_le_mul_nonneg_both(zero, nx, zero, ny);
                    Rational::lemma_mul_zero(zero);
                    Rational::lemma_eqv_implies_le(zero, zero.mul_spec(zero));
                    Rational::lemma_le_transitive(zero, zero.mul_spec(zero), nx.mul_spec(ny));
                    // 0 <= nx*ny eqv xy => 0 <= xy
                    Rational::lemma_eqv_implies_le(nx.mul_spec(ny), xy);
                    Rational::lemma_le_transitive(zero, nx.mul_spec(ny), xy);
                    Rational::lemma_le_transitive(ad, zero, xy);
                    Self::lemma_min4_le(ac, ad, bc, bd, xy);
                } else {
                    Rational::lemma_lt_implies_le(b.hi, zero);
                    // b.hi < 0. x < 0, y < 0. a.hi could be >= 0 or < 0.
                    if zero.le_spec(a.hi) {
                        // a.hi >= 0, b.hi < 0 => bd = a.hi * b.hi <= 0.
                        // xy > 0 (both x, y strictly negative). So bd <= 0 <= xy.
                        Rational::lemma_le_mul_nonneg(b.hi, zero, a.hi);
                        Rational::lemma_mul_commutative(b.hi, a.hi);
                        Rational::lemma_mul_commutative(zero, a.hi);
                        Rational::lemma_mul_zero(a.hi);
                        Rational::lemma_eqv_implies_le(a.hi.mul_spec(zero), zero);
                        Rational::lemma_le_transitive(bd, a.hi.mul_spec(zero), zero);
                        // bd <= 0. Now show 0 <= xy.
                        Self::lemma_neg_mul_neg_eqv(x, y);
                        Rational::lemma_le_mul_nonneg_both(zero, nx, zero, ny);
                        Rational::lemma_mul_zero(zero);
                        Rational::lemma_eqv_implies_le(zero, zero.mul_spec(zero));
                        Rational::lemma_le_transitive(zero, zero.mul_spec(zero), nx.mul_spec(ny));
                        Rational::lemma_eqv_implies_le(nx.mul_spec(ny), xy);
                        Rational::lemma_le_transitive(zero, nx.mul_spec(ny), xy);
                        Rational::lemma_le_transitive(bd, zero, xy);
                    } else {
                        // a.hi < 0 and b.hi < 0: all endpoints negative.
                        Rational::lemma_lt_implies_le(a.hi, zero);
                        let nahi = a.hi.neg_spec();
                        let nbhi = b.hi.neg_spec();
                        Rational::lemma_neg_reverses_le(x, a.hi);
                        Rational::lemma_neg_reverses_le(y, b.hi);
                        Rational::lemma_neg_reverses_le(a.hi, zero);
                        Rational::lemma_neg_reverses_le(b.hi, zero);
                        // 0 <= nahi <= nx, 0 <= nbhi <= ny.
                        Rational::lemma_le_mul_nonneg_both(nahi, nx, nbhi, ny);
                        // nahi*nbhi <= nx*ny
                        Self::lemma_neg_mul_neg_eqv(a.hi, b.hi);
                        // nahi*nbhi eqv bd
                        Rational::lemma_eqv_symmetric(nahi.mul_spec(nbhi), bd);
                        Rational::lemma_eqv_implies_le(bd, nahi.mul_spec(nbhi));
                        Rational::lemma_le_transitive(bd, nahi.mul_spec(nbhi), nx.mul_spec(ny));
                        Rational::lemma_eqv_implies_le(nx.mul_spec(ny), xy);
                        Rational::lemma_le_transitive(bd, nx.mul_spec(ny), xy);
                        // bd <= xy ✓
                    }
                    Self::lemma_min4_le(ac, ad, bc, bd, xy);
                }
            }
        }
    }

    /// Helper: (-a) * (-b) eqv a * b.
    proof fn lemma_neg_mul_neg_eqv(a: Rational, b: Rational)
        ensures
            a.neg_spec().mul_spec(b.neg_spec()).eqv_spec(a.mul_spec(b)),
    {
        // (-a)*(-b) eqv -(a*(-b)) eqv -(-(a*b)) eqv a*b
        Rational::lemma_mul_neg_right(a.neg_spec(), b);
        // a.neg * b.neg eqv -(a.neg * b)
        Rational::lemma_mul_commutative(a.neg_spec(), b);
        Rational::lemma_mul_commutative(a, b);
        // a.neg * b eqv b * a.neg
        Rational::lemma_mul_neg_right(b, a);
        // b * a.neg eqv -(b * a) eqv -(a * b)
        Rational::lemma_eqv_symmetric(b.mul_spec(a), a.mul_spec(b));
        // b * a eqv a * b
        Rational::lemma_eqv_neg_congruence(b.mul_spec(a), a.mul_spec(b));
        // -(b*a) eqv -(a*b)
        // So: a.neg * b eqv b * a.neg eqv -(b*a) eqv -(a*b)
        Rational::lemma_eqv_transitive(a.neg_spec().mul_spec(b), b.mul_spec(a.neg_spec()), b.mul_spec(a).neg_spec());
        Rational::lemma_eqv_transitive(a.neg_spec().mul_spec(b), b.mul_spec(a).neg_spec(), a.mul_spec(b).neg_spec());
        // a.neg * b eqv -(a*b)
        // Therefore: -(a.neg * b) eqv -(-(a*b)) eqv a*b
        Rational::lemma_eqv_neg_congruence(a.neg_spec().mul_spec(b), a.mul_spec(b).neg_spec());
        Rational::lemma_neg_involution(a.mul_spec(b));
        Rational::lemma_eqv_transitive(a.neg_spec().mul_spec(b).neg_spec(), a.mul_spec(b).neg_spec().neg_spec(), a.mul_spec(b));
        // -(a.neg * b) eqv a*b
        // And a.neg * b.neg eqv -(a.neg * b)
        // So a.neg * b.neg eqv a*b
        Rational::lemma_eqv_transitive(a.neg_spec().mul_spec(b.neg_spec()), a.neg_spec().mul_spec(b).neg_spec(), a.mul_spec(b));
    }

    /// Helper: for c <= 0: a <= b => c*b <= c*a (non-positive scalar reverses order).
    proof fn lemma_le_mul_nonpos(c: Rational, a: Rational, b: Rational)
        requires
            c.le_spec(Rational::from_int_spec(0)),
            a.le_spec(b),
        ensures
            c.mul_spec(b).le_spec(c.mul_spec(a)),
    {
        let zero = Rational::from_int_spec(0);
        let nc = c.neg_spec();
        // c <= 0 => -c >= 0
        Rational::lemma_neg_reverses_le(c, zero);
        // 0 <= nc. a <= b. So nc*a <= nc*b (by le_mul_nonneg)
        // Wait, le_mul_nonneg(a, b, nc) requires a <= b and 0 <= nc. ✓
        Rational::lemma_le_mul_nonneg(a, b, nc);
        // a * nc <= b * nc
        // a * nc eqv -(a * c) (by mul_neg_right)
        // b * nc eqv -(b * c) (by mul_neg_right)
        Rational::lemma_mul_neg_right(a, c);
        Rational::lemma_mul_neg_right(b, c);
        // a*nc eqv -(a*c), b*nc eqv -(b*c)
        // a*nc <= b*nc => -(a*c) <= -(b*c) (via eqv transfer)
        // => b*c <= a*c (by neg_reverses_le)
        // Actually we need: from a*nc.le_spec(b*nc) and the eqv relationships,
        // derive c*b <= c*a.
        // c*b = b*c (commutativity) and c*a = a*c (commutativity).
        Rational::lemma_mul_commutative(c, b);
        Rational::lemma_mul_commutative(c, a);
        // c*b eqv b*c, c*a eqv a*c. So we need b*c <= a*c.
        // From a*nc <= b*nc, negate: -(b*nc) <= -(a*nc)
        Rational::lemma_neg_reverses_le(a.mul_spec(nc), b.mul_spec(nc));
        // -(b*nc) eqv b*c (since b*nc eqv -(b*c), neg of that eqv b*c)
        Rational::lemma_neg_involution(b.mul_spec(c));
        // -(b*nc) eqv -(-(b*c)) eqv b*c
        Rational::lemma_eqv_neg_congruence(b.mul_spec(nc), b.mul_spec(c).neg_spec());
        Rational::lemma_eqv_transitive(b.mul_spec(nc).neg_spec(), b.mul_spec(c).neg_spec().neg_spec(), b.mul_spec(c));
        // Similarly: -(a*nc) eqv a*c
        Rational::lemma_neg_involution(a.mul_spec(c));
        Rational::lemma_eqv_neg_congruence(a.mul_spec(nc), a.mul_spec(c).neg_spec());
        Rational::lemma_eqv_transitive(a.mul_spec(nc).neg_spec(), a.mul_spec(c).neg_spec().neg_spec(), a.mul_spec(c));

        // -(b*nc) <= -(a*nc), -(b*nc) eqv b*c, -(a*nc) eqv a*c
        // => b*c <= a*c
        Rational::lemma_eqv_implies_le(b.mul_spec(c), b.mul_spec(nc).neg_spec());
        Rational::lemma_le_transitive(b.mul_spec(c), b.mul_spec(nc).neg_spec(), a.mul_spec(nc).neg_spec());
        Rational::lemma_eqv_implies_le(a.mul_spec(nc).neg_spec(), a.mul_spec(c));
        Rational::lemma_le_transitive(b.mul_spec(c), a.mul_spec(nc).neg_spec(), a.mul_spec(c));
        // b*c <= a*c

        // Now: c*b eqv b*c and c*a eqv a*c
        Rational::lemma_eqv_implies_le(c.mul_spec(b), b.mul_spec(c));
        Rational::lemma_le_transitive(c.mul_spec(b), b.mul_spec(c), a.mul_spec(c));
        Rational::lemma_eqv_symmetric(c.mul_spec(a), a.mul_spec(c));
        Rational::lemma_eqv_implies_le(a.mul_spec(c), c.mul_spec(a));
        Rational::lemma_le_transitive(c.mul_spec(b), a.mul_spec(c), c.mul_spec(a));
    }

    /// Scalar multiplication containment: x in A => k*x in k*A.
    pub proof fn lemma_scale_containment(scalar: Rational, a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            Self::scale_spec(scalar, a).contains_spec(scalar.mul_spec(x)),
    {
        let sx = scalar.mul_spec(x);
        let sa = scalar.mul_spec(a.lo);
        let sb = scalar.mul_spec(a.hi);

        // scalar * x lies between scalar * a.lo and scalar * a.hi
        // (in some order depending on sign of scalar).
        // scale_spec gives [min(sa, sb), max(sa, sb)] which spans both.
        Self::lemma_mul_between(a.lo, a.hi, scalar, x);
        // This gives: min(a.lo*scalar, a.hi*scalar) <= x*scalar <= max(...)
        // But we need scalar*x, not x*scalar. Use commutativity.
        Rational::lemma_mul_commutative(a.lo, scalar);
        Rational::lemma_mul_commutative(a.hi, scalar);
        Rational::lemma_mul_commutative(x, scalar);
        // a.lo*scalar eqv scalar*a.lo = sa
        // a.hi*scalar eqv scalar*a.hi = sb
        // x*scalar eqv scalar*x = sx

        // min(a.lo*scalar, a.hi*scalar) <= x*scalar <= max(a.lo*scalar, a.hi*scalar)
        // Now transfer through eqv:
        // min(a.lo*scalar, a.hi*scalar) eqv ... complicated with min/max of eqv values.
        // Instead, use lemma_mul_between directly with the right argument order.
        // Actually, lemma_mul_between(lo, hi, y, x) proves about lo*y and hi*y and x*y.
        // We want about scalar*lo and scalar*hi and scalar*x.
        // That's lemma_mul_between(lo, hi, scalar, x) which gives:
        //   min(lo*scalar, hi*scalar) <= x*scalar <= max(lo*scalar, hi*scalar)
        // But lo*scalar and scalar*lo differ structurally.

        // Let me just handle this with the two sign cases of scalar, it's cleaner.
        let zero = Rational::from_int_spec(0);
        Rational::lemma_trichotomy(zero, scalar);

        if zero.le_spec(scalar) {
            // scalar >= 0: monotone. a.lo <= x => sa <= sx. x <= a.hi => sx <= sb.
            Rational::lemma_le_mul_nonneg(a.lo, x, scalar);
            Rational::lemma_mul_commutative(a.lo, scalar);
            Rational::lemma_mul_commutative(x, scalar);
            // scalar*a.lo <= scalar*x, i.e., sa <= sx
            Rational::lemma_eqv_implies_le(sa, a.lo.mul_spec(scalar));
            Rational::lemma_le_transitive(sa, a.lo.mul_spec(scalar), x.mul_spec(scalar));
            Rational::lemma_eqv_implies_le(x.mul_spec(scalar), sx);
            Rational::lemma_le_transitive(sa, x.mul_spec(scalar), sx);

            Rational::lemma_le_mul_nonneg(x, a.hi, scalar);
            Rational::lemma_mul_commutative(a.hi, scalar);
            Rational::lemma_eqv_implies_le(sx, x.mul_spec(scalar));
            Rational::lemma_le_transitive(sx, x.mul_spec(scalar), a.hi.mul_spec(scalar));
            Rational::lemma_eqv_implies_le(a.hi.mul_spec(scalar), sb);
            Rational::lemma_le_transitive(sx, a.hi.mul_spec(scalar), sb);

            // sa <= sx, so min(sa,sb) <= sa <= sx
            Rational::lemma_min_le_left(sa, sb);
            Rational::lemma_le_transitive(sa.min_spec(sb), sa, sx);
            // sx <= sb, so sx <= sb <= max(sa,sb)
            Rational::lemma_max_ge_right(sa, sb);
            Rational::lemma_le_transitive(sx, sb, sa.max_spec(sb));
        } else {
            // scalar < 0: anti-monotone. a.lo <= x => sx <= sa. x <= a.hi => sb <= sx.
            Rational::lemma_lt_implies_le(scalar, zero);
            Self::lemma_le_mul_nonpos(scalar, a.lo, x);
            // scalar*x <= scalar*a.lo, i.e., sx <= sa
            Self::lemma_le_mul_nonpos(scalar, x, a.hi);
            // scalar*a.hi <= scalar*x, i.e., sb <= sx

            // sb <= sx, so min(sa,sb) <= sb <= sx
            Rational::lemma_min_le_right(sa, sb);
            Rational::lemma_le_transitive(sa.min_spec(sb), sb, sx);
            // sx <= sa, so sx <= sa <= max(sa,sb)
            Rational::lemma_max_ge_left(sa, sb);
            Rational::lemma_le_transitive(sx, sa, sa.max_spec(sb));
        }
    }
    // ── Phase 6: Subdivision & splitting ─────────────────────────

    /// Bisect at midpoint: returns ([lo, mid], [mid, hi]).
    pub open spec fn bisect_spec(self) -> (Interval, Interval) {
        let mid = self.midpoint_spec();
        (
            Interval { lo: self.lo, hi: mid },
            Interval { lo: mid, hi: self.hi },
        )
    }

    /// Split at an arbitrary rational point p in [lo, hi].
    pub open spec fn split_at_spec(self, p: Rational) -> (Interval, Interval) {
        (
            Interval { lo: self.lo, hi: p },
            Interval { lo: p, hi: self.hi },
        )
    }

    /// N-way uniform subdivision: n equal-width pieces.
    /// Piece k = [lo + k*(hi-lo)/n, lo + (k+1)*(hi-lo)/n].
    pub open spec fn subdivide_point_spec(self, n: nat, k: nat) -> Rational
        recommends n > 0, k <= n,
    {
        // lo + k * (hi - lo) / n
        let w = self.hi.sub_spec(self.lo);
        let step = w.mul_spec(Rational::from_frac_spec(k as int, n as int));
        self.lo.add_spec(step)
    }

    /// The k-th piece of an n-way uniform subdivision.
    pub open spec fn subdivide_piece_spec(self, n: nat, k: nat) -> Interval
        recommends n > 0, k < n,
    {
        Interval {
            lo: self.subdivide_point_spec(n, k),
            hi: self.subdivide_point_spec(n, (k + 1) as nat),
        }
    }

    // ── Phase 6 proofs ────────────────────────────────────────────

    /// Both halves of a bisection are well-formed.
    pub proof fn lemma_bisect_wf(a: Self)
        requires
            a.wf_spec(),
        ensures
            a.bisect_spec().0.wf_spec(),
            a.bisect_spec().1.wf_spec(),
    {
        let mid = a.midpoint_spec();
        Rational::lemma_interval_contains_midpoint(a.lo, a.hi);
        // lo ≤ mid and mid ≤ hi
    }

    /// Bisection covers: x in a → x in left or x in right.
    pub proof fn lemma_bisect_covers(a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            a.bisect_spec().0.contains_spec(x)
            || a.bisect_spec().1.contains_spec(x),
    {
        let mid = a.midpoint_spec();
        Rational::lemma_interval_contains_midpoint(a.lo, a.hi);
        Rational::lemma_trichotomy(x, mid);
        if x.le_spec(mid) {
            // x in left = [lo, mid]
        } else {
            // mid < x, so mid ≤ x
            Rational::lemma_lt_implies_le(mid, x);
            // x in right = [mid, hi]
        }
    }

    /// Split at p: both halves are well-formed when lo ≤ p ≤ hi.
    pub proof fn lemma_split_at_wf(a: Self, p: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(p),
        ensures
            a.split_at_spec(p).0.wf_spec(),
            a.split_at_spec(p).1.wf_spec(),
    {
        // lo ≤ p and p ≤ hi directly from contains_spec
    }

    /// Split covers: x in a → x in left or x in right.
    pub proof fn lemma_split_covers(a: Self, p: Rational, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(p),
            a.contains_spec(x),
        ensures
            a.split_at_spec(p).0.contains_spec(x)
            || a.split_at_spec(p).1.contains_spec(x),
    {
        Rational::lemma_trichotomy(x, p);
        if x.le_spec(p) {
            // x in [lo, p]
        } else {
            Rational::lemma_lt_implies_le(p, x);
            // x in [p, hi]
        }
    }

    /// Subdivision point 0 equals lo.
    pub proof fn lemma_subdivide_point_zero(a: Self, n: nat)
        requires
            a.wf_spec(),
            n > 0,
        ensures
            a.subdivide_point_spec(n, 0).eqv_spec(a.lo),
    {
        // subdivide_point(n, 0) = lo + 0 * w / n = lo + 0
        let w = a.hi.sub_spec(a.lo);
        let frac = Rational::from_frac_spec(0, n as int);
        let step = w.mul_spec(frac);
        // step.num = w.num * 0 = 0
        assert(frac.num == 0int);
        assert(step.num == w.num * frac.num);
        assert(step.num == 0) by (nonlinear_arith)
            requires step.num == w.num * 0int;

        let result = a.lo.add_spec(step);
        // result.num = lo.num * step.denom() + step.num * lo.denom()
        //            = lo.num * step.denom() + 0 = lo.num * step.denom()
        Rational::lemma_add_denom_product_int(a.lo, step);
        // result.denom() == lo.denom() * step.denom()

        // result ≡ lo:
        // result.num * lo.denom() = lo.num * step.denom() * lo.denom()
        // lo.num * result.denom() = lo.num * (lo.denom() * step.denom())
        // Equal by associativity.
        assert(result.num * a.lo.denom() == a.lo.num * result.denom()) by (nonlinear_arith)
            requires
                result.num == a.lo.num * step.denom() + step.num * a.lo.denom(),
                step.num == 0int,
                result.denom() == a.lo.denom() * step.denom(),
        ;
    }

    /// Subdivision point n equals hi.
    pub proof fn lemma_subdivide_point_n(a: Self, n: nat)
        requires
            a.wf_spec(),
            n > 0,
        ensures
            a.subdivide_point_spec(n, n).eqv_spec(a.hi),
    {
        // subdivide_point(n, n) = lo + n * (hi - lo) / n = lo + (hi - lo) = hi
        let w = a.hi.sub_spec(a.lo);
        let frac = Rational::from_frac_spec(n as int, n as int);
        // frac = Rational { num: n, den: n-1 }, so frac ≡ 1
        let step = w.mul_spec(frac);
        let result = a.lo.add_spec(step);

        // frac ≡ 1: frac.num * 1.denom() == 1.num * frac.denom()
        // frac.num = n, frac.denom() = n. 1 = from_int_spec(1) = { num: 1, den: 0 }, denom = 1.
        // n * 1 == 1 * n. True.
        let one = Rational::from_int_spec(1);
        assert(frac.num == n as int);
        assert(frac.denom() == n as int);
        assert(frac.num * one.denom() == one.num * frac.denom()) by (nonlinear_arith)
            requires
                frac.num == n as int,
                frac.denom() == n as int,
                one.num == 1int,
                one.denom() == 1int,
                n > 0,
        ;
        assert(frac.eqv_spec(one));

        // step = w * frac ≡ w * 1 ≡ w
        Rational::lemma_eqv_mul_congruence_right(w, frac, one);
        Rational::lemma_mul_one_identity(w);
        Rational::lemma_eqv_transitive(step, w.mul_spec(one), w);

        // result = lo + step ≡ lo + w = lo + (hi - lo)
        Rational::lemma_eqv_add_congruence_right(a.lo, step, w);
        let lo_plus_w = a.lo.add_spec(w);
        // result ≡ lo_plus_w

        // lo + (hi - lo) ≡ hi
        Rational::lemma_sub_then_add_cancel(a.hi, a.lo);
        // lo_plus_w = lo + (hi - lo) ≡ hi
        Rational::lemma_eqv_transitive(result, lo_plus_w, a.hi);
    }

    /// Subdivision points are monotone: k1 ≤ k2 → point(k1) ≤ point(k2).
    pub proof fn lemma_subdivide_points_monotone(a: Self, n: nat, k1: nat, k2: nat)
        requires
            a.wf_spec(),
            n > 0,
            k1 <= k2,
            k2 <= n,
        ensures
            a.subdivide_point_spec(n, k1).le_spec(a.subdivide_point_spec(n, k2)),
    {
        let w = a.hi.sub_spec(a.lo);
        let frac1 = Rational::from_frac_spec(k1 as int, n as int);
        let frac2 = Rational::from_frac_spec(k2 as int, n as int);
        let step1 = w.mul_spec(frac1);
        let step2 = w.mul_spec(frac2);

        // frac1 ≤ frac2 since k1/n ≤ k2/n
        assert(frac1.num == k1 as int);
        assert(frac2.num == k2 as int);
        assert(frac1.denom() == n as int);
        assert(frac2.denom() == n as int);
        assert(frac1.le_spec(frac2)) by (nonlinear_arith)
            requires
                frac1.num == k1 as int,
                frac2.num == k2 as int,
                frac1.denom() == n as int,
                frac2.denom() == n as int,
                k1 <= k2,
                n > 0,
        ;

        // w ≥ 0: hi - lo ≥ 0 from wf
        Self::lemma_width_nonneg(a);

        // frac1*w ≤ frac2*w (from frac1 ≤ frac2 and w ≥ 0)
        Rational::lemma_le_mul_nonneg(frac1, frac2, w);
        // ensures: frac1.mul_spec(w).le_spec(frac2.mul_spec(w))
        // Since mul_spec is structurally commutative:
        // frac1.mul_spec(w) == w.mul_spec(frac1) == step1
        // frac2.mul_spec(w) == w.mul_spec(frac2) == step2
        Rational::lemma_mul_commutative(frac1, w);
        Rational::lemma_mul_commutative(frac2, w);
        // Now we have step1.le_spec(step2)... but le_spec uses eqv after commutative.
        // Actually lemma_mul_commutative gives structural ==, so step1 == frac1*w.
        // The le_spec is on frac1*w and frac2*w, and those == step1, step2.
        // So step1.le_spec(step2) follows.

        // lo + step1 ≤ lo + step2
        // Use lemma_le_add_both(lo, lo, step1, step2) → lo+step1 ≤ lo+step2
        Rational::lemma_le_add_both(a.lo, a.lo, step1, step2);
    }

    /// Subdivision piece is well-formed.
    pub proof fn lemma_subdivide_piece_wf(a: Self, n: nat, k: nat)
        requires
            a.wf_spec(),
            n > 0,
            k < n,
        ensures
            a.subdivide_piece_spec(n, k).wf_spec(),
    {
        Self::lemma_subdivide_points_monotone(a, n, k, (k + 1) as nat);
    }

    /// Subdivision covers: x in a → x in some piece.
    pub proof fn lemma_subdivide_covers(a: Self, n: nat, x: Rational)
        requires
            a.wf_spec(),
            n > 0,
            a.contains_spec(x),
        ensures
            exists|k: nat| k < n && a.subdivide_piece_spec(n, k).contains_spec(x),
        decreases n,
    {
        if n == 1 {
            // Single piece: [lo, hi] = a
            Self::lemma_subdivide_point_zero(a, 1);
            Self::lemma_subdivide_point_n(a, 1);
            let piece = a.subdivide_piece_spec(1, 0);
            // piece.lo = subdivide_point(1, 0) ≡ lo
            // piece.hi = subdivide_point(1, 1) ≡ hi
            // Need: piece.contains_spec(x), i.e., piece.lo ≤ x ≤ piece.hi
            // From lo ≤ x: subdivide_point(1,0) ≡ lo, so subdivide_point(1,0) ≤ x
            Rational::lemma_eqv_symmetric(a.subdivide_point_spec(1, 0), a.lo);
            Rational::lemma_eqv_implies_le(a.lo, a.subdivide_point_spec(1, 0));
            Rational::lemma_le_transitive(piece.lo, a.lo, x);
            // From x ≤ hi: x ≤ hi ≡ subdivide_point(1,1)
            Rational::lemma_eqv_implies_le(a.hi, a.subdivide_point_spec(1, 1));
            Rational::lemma_le_transitive(x, a.hi, piece.hi);
            assert(piece.contains_spec(x));
        } else {
            // Check if x is in the last piece [point(n-1), point(n)]
            let last_lo = a.subdivide_point_spec(n, (n - 1) as nat);
            Rational::lemma_trichotomy(last_lo, x);
            if last_lo.le_spec(x) {
                // x in last piece [point(n-1), point(n)]
                // Need x ≤ point(n)
                Self::lemma_subdivide_point_n(a, n);
                Rational::lemma_eqv_implies_le(a.hi, a.subdivide_point_spec(n, n));
                Rational::lemma_le_transitive(x, a.hi, a.subdivide_point_spec(n, n));
                let piece = a.subdivide_piece_spec(n, (n - 1) as nat);
                assert(piece.contains_spec(x));
            } else {
                // x < last_lo, so x < point(n-1)
                // x is in the first (n-1) pieces of a subdivide-by-n.
                // We need to show x is contained in some piece k < n-1.
                // point(n-1) corresponds to lo + (n-1)*(hi-lo)/n.
                // Consider the interval [lo, point(n-1)] — x is in it.
                // But that's not exactly a sub-subdivision of a.

                // Simpler approach: the first n-1 pieces of subdivide(n) cover [lo, point(n-1)].
                // x < point(n-1), and lo ≤ x, so x is in [lo, point(n-1)].
                // By induction on the first n-1 pieces...
                // Actually let's just check pieces from 0 to n-2.
                // piece k = [point(k), point(k+1)] for k = 0..n-1
                // x < point(n-1), x ≥ lo = point(0) (via eqv)
                // So there exists some k < n-1 where point(k) ≤ x < point(k+1).

                // Use a decreasing search: check piece n-2.
                // Recursively, x is in [lo, point(n-1)].
                // But we can't easily recurse on a sub-interval here.

                // Alternative: iterate through pieces.
                // For Verus proofs, a direct constructive approach with a loop-like
                // decreasing argument works. Let's use a helper.
                Rational::lemma_lt_implies_le(x, last_lo);
                Self::lemma_subdivide_point_zero(a, n);
                Rational::lemma_eqv_symmetric(a.subdivide_point_spec(n, 0), a.lo);
                Rational::lemma_eqv_implies_le(a.lo, a.subdivide_point_spec(n, 0));
                let p0 = a.subdivide_point_spec(n, 0);
                // lo ≤ point(0) and point(0) ≡ lo, so point(0) ≤ x
                Rational::lemma_le_transitive(p0, a.lo, x);
                // x < point(n-1), x ≥ point(0)
                Self::lemma_subdivide_find_piece(a, n, x, (n - 1) as nat);
            }
        }
    }

    /// Helper: find a piece for x given that point(0) ≤ x < point(j) for some j.
    proof fn lemma_subdivide_find_piece(a: Self, n: nat, x: Rational, j: nat)
        requires
            a.wf_spec(),
            n > 0,
            j > 0,
            j <= n,
            a.subdivide_point_spec(n, 0).le_spec(x),
            x.lt_spec(a.subdivide_point_spec(n, j)),
        ensures
            exists|k: nat| k < n && a.subdivide_piece_spec(n, k).contains_spec(x),
        decreases j,
    {
        let pj_minus_1 = a.subdivide_point_spec(n, (j - 1) as nat);
        Rational::lemma_trichotomy(pj_minus_1, x);
        if pj_minus_1.le_spec(x) {
            // x in [point(j-1), point(j))
            // piece j-1 = [point(j-1), point(j)]
            // contains: point(j-1) ≤ x ✓, x ≤ point(j)
            let pj = a.subdivide_point_spec(n, j);
            Rational::lemma_lt_implies_le(x, pj);
            let k = (j - 1) as nat;
            assert(a.subdivide_piece_spec(n, k).contains_spec(x));
        } else {
            // x < point(j-1), recurse
            if j == 1 {
                // x < point(0) but point(0) ≤ x — contradiction
                Rational::lemma_lt_implies_le(x, pj_minus_1);
                Rational::lemma_le_antisymmetric(x, pj_minus_1);
                // x ≡ point(0), so x is in piece 0
                // But we said x < point(0) — contradiction with point(0) ≤ x
                assert(false);
            } else {
                Self::lemma_subdivide_find_piece(a, n, x, (j - 1) as nat);
            }
        }
    }
    // ── Phase 7: Scalar root-finding support ────────────────────

    // ── 7.1 Sign-change detection ──

    /// Whether two values have opposite signs (one positive, one negative).
    pub open spec fn sign_change_spec(f_lo: Rational, f_hi: Rational) -> bool {
        (f_lo.signum() == 1 && f_hi.signum() == -1)
        || (f_lo.signum() == -1 && f_hi.signum() == 1)
    }

    // ── 7.2 Scalar interval Newton step ──

    /// N(X) = x_mid - f(x_mid)/f'(X) ∩ X.
    /// Returns None if f'(X) contains zero (division undefined).
    pub open spec fn scalar_newton_step_spec(
        fx_mid: Rational,
        fprime_interval: Interval,
        x_mid: Rational,
        x_interval: Interval,
    ) -> Option<Interval> {
        if fprime_interval.possibly_zero_spec() {
            None
        } else {
            let fx_point = Self::from_point_spec(fx_mid);
            let x_point = Self::from_point_spec(x_mid);
            let quotient = fx_point.div_spec(fprime_interval);
            let candidate = x_point.sub_spec(quotient);
            candidate.intersect_spec(x_interval)
        }
    }

    // ── 7.3 Interval Horner evaluation ──

    /// Evaluate polynomial over an interval using Horner's method.
    /// coeffs = [c₀, c₁, ..., cₙ], result encloses all p(x) for x ∈ X.
    /// p(x) = c₀ + c₁x + c₂x² + ... = c₀ + x*(c₁ + x*(c₂ + ...))
    pub open spec fn horner_eval_spec(coeffs: Seq<Rational>, x: Interval) -> Interval
        decreases coeffs.len(),
    {
        if coeffs.len() == 0 {
            Self::from_point_spec(Rational::from_int_spec(0))
        } else {
            let c0 = Self::from_point_spec(coeffs[0]);
            let rest = coeffs.subrange(1, coeffs.len() as int);
            c0.add_spec(x.mul_spec(Self::horner_eval_spec(rest, x)))
        }
    }

    /// Horner evaluation is well-formed.
    pub proof fn lemma_horner_eval_wf(coeffs: Seq<Rational>, x: Interval)
        requires
            x.wf_spec(),
        ensures
            Self::horner_eval_spec(coeffs, x).wf_spec(),
        decreases coeffs.len(),
    {
        if coeffs.len() == 0 {
            Self::lemma_from_point_wf(Rational::from_int_spec(0));
        } else {
            let rest = coeffs.subrange(1, coeffs.len() as int);
            Self::lemma_horner_eval_wf(rest, x);
            let inner = Self::horner_eval_spec(rest, x);
            Self::lemma_mul_wf(x, inner);
            let product = x.mul_spec(inner);
            let c0 = Self::from_point_spec(coeffs[0]);
            Self::lemma_from_point_wf(coeffs[0]);
            Self::lemma_add_wf(c0, product);
        }
    }

    /// Horner containment: x ∈ X → horner(coeffs, x) ∈ horner_eval(coeffs, X).
    pub proof fn lemma_horner_containment(coeffs: Seq<Rational>, a: Self, x: Rational)
        requires
            a.wf_spec(),
            a.contains_spec(x),
        ensures
            Self::horner_eval_spec(coeffs, a).contains_spec(
                Rational::horner_spec(coeffs, x)),
        decreases coeffs.len(),
    {
        if coeffs.len() == 0 {
            // horner([], x) = 0, eval = from_point(0), 0 ∈ [0,0] ✓
            Self::lemma_from_point_wf(Rational::from_int_spec(0));
            Self::lemma_from_point_contains(Rational::from_int_spec(0));
        } else {
            let rest = coeffs.subrange(1, coeffs.len() as int);
            // Induction: horner(rest, x) ∈ horner_eval(rest, a)
            Self::lemma_horner_containment(rest, a, x);
            let inner_val = Rational::horner_spec(rest, x);
            let inner_iv = Self::horner_eval_spec(rest, a);

            // x ∈ a, inner_val ∈ inner_iv → x*inner_val ∈ a*inner_iv
            Self::lemma_horner_eval_wf(rest, a);
            Self::lemma_mul_containment(a, inner_iv, x, inner_val);
            let product_val = x.mul_spec(inner_val);
            let product_iv = a.mul_spec(inner_iv);

            // c0 ∈ [c0, c0]
            let c0 = coeffs[0];
            Self::lemma_from_point_wf(c0);
            Self::lemma_from_point_contains(c0);
            let c0_iv = Self::from_point_spec(c0);

            // c0 + x*inner ∈ c0_iv + product_iv
            Self::lemma_mul_wf(a, inner_iv);
            Self::lemma_add_containment(c0_iv, product_iv, c0, product_val);
        }
    }

    // ── 7.4 Derivative coefficients ──

    /// Compute derivative polynomial coefficients.
    /// If p(x) = c₀ + c₁x + c₂x² + ..., then p'(x) = c₁ + 2c₂x + 3c₃x² + ...
    /// Output: [c₁, 2*c₂, 3*c₃, ...]
    pub open spec fn poly_derivative_coeffs_spec(coeffs: Seq<Rational>) -> Seq<Rational> {
        if coeffs.len() <= 1 {
            Seq::empty()
        } else {
            Seq::new(
                (coeffs.len() - 1) as nat,
                |i: int| Rational::from_int_spec((i + 1) as int).mul_spec(coeffs[i + 1]),
            )
        }
    }
    // ── Phase 8: Interval distance & metric ─────────────────────

    // ── 8.1 Hausdorff distance ──

    /// Hausdorff distance between two intervals.
    /// max(|lo₁ - lo₂|, |hi₁ - hi₂|)
    pub open spec fn hausdorff_spec(self, other: Interval) -> Rational {
        self.lo.sub_spec(other.lo).abs_spec().max_spec(
            self.hi.sub_spec(other.hi).abs_spec())
    }

    /// Hausdorff distance is zero iff intervals are componentwise equivalent.
    pub proof fn lemma_hausdorff_zero_iff_equal(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            a.hausdorff_spec(b).eqv_spec(Rational::from_int_spec(0))
            <==> (a.lo.sub_spec(b.lo).eqv_spec(Rational::from_int_spec(0))
                && a.hi.sub_spec(b.hi).eqv_spec(Rational::from_int_spec(0))),
    {
        let zero = Rational::from_int_spec(0);
        let d_lo = a.lo.sub_spec(b.lo).abs_spec();
        let d_hi = a.hi.sub_spec(b.hi).abs_spec();
        let h = d_lo.max_spec(d_hi);

        // abs(x) ≡ 0 ↔ x ≡ 0
        Rational::lemma_abs_zero_iff(a.lo.sub_spec(b.lo));
        Rational::lemma_abs_zero_iff(a.hi.sub_spec(b.hi));

        // abs values are nonneg
        Rational::lemma_abs_nonneg(a.lo.sub_spec(b.lo));
        Rational::lemma_abs_nonneg(a.hi.sub_spec(b.hi));

        // Forward: if h ≡ 0 then both d_lo ≡ 0 and d_hi ≡ 0
        if h.eqv_spec(zero) {
            // max(d_lo, d_hi) ≡ 0 with d_lo, d_hi ≥ 0 → both ≡ 0
            // d_lo ≤ max(d_lo, d_hi) = h ≡ 0
            Rational::lemma_max_ge_left(d_lo, d_hi);
            Rational::lemma_eqv_implies_le(h, zero);
            Rational::lemma_le_transitive(d_lo, h, zero);
            // d_lo ≥ 0 from signum
            // d_lo.signum() >= 0 means d_lo.num >= 0
            // zero.le_spec(d_lo): 0 * d_lo.denom() <= d_lo.num * 1
            // Since d_lo = |lo_diff| has num >= 0, this is 0 <= d_lo.num ✓
            Rational::lemma_denom_positive(d_lo);
            assert(zero.le_spec(d_lo)) by (nonlinear_arith)
                requires
                    d_lo.num >= 0,
                    zero.num == 0int,
                    zero.denom() == 1int,
                    d_lo.denom() > 0,
            ;
            Rational::lemma_le_antisymmetric(d_lo, zero);
            // d_lo ≡ 0

            Rational::lemma_max_ge_right(d_lo, d_hi);
            Rational::lemma_le_transitive(d_hi, h, zero);
            Rational::lemma_denom_positive(d_hi);
            assert(zero.le_spec(d_hi)) by (nonlinear_arith)
                requires
                    d_hi.num >= 0,
                    zero.num == 0int,
                    zero.denom() == 1int,
                    d_hi.denom() > 0,
            ;
            Rational::lemma_le_antisymmetric(d_hi, zero);
            // d_hi ≡ 0
        }

        // Backward: if both d_lo ≡ 0 and d_hi ≡ 0, then h = max(0, 0) ≡ 0
        if d_lo.eqv_spec(zero) && d_hi.eqv_spec(zero) {
            // max(d_lo, d_hi) where d_lo ≡ 0 and d_hi ≡ 0
            // d_lo.le_spec(d_hi): both ≡ 0, so 0 ≤ 0 ✓
            Rational::lemma_eqv_implies_le(d_lo, d_hi);
            // h = d_hi when d_lo ≤ d_hi
            // h ≡ d_hi ≡ 0
            Rational::lemma_eqv_symmetric(d_hi, zero);
            Rational::lemma_trichotomy(d_lo, d_hi);
            if d_lo.le_spec(d_hi) {
                assert(h == d_hi);
            } else {
                assert(h == d_lo);
            }
        }
    }

    /// Hausdorff triangle inequality:
    /// hausdorff(a, c) ≤ hausdorff(a, b) + hausdorff(b, c).
    pub proof fn lemma_hausdorff_triangle(a: Self, b: Self, c: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            a.hausdorff_spec(c).le_spec(
                a.hausdorff_spec(b).add_spec(b.hausdorff_spec(c))),
    {
        let zero = Rational::from_int_spec(0);

        // Differences
        let dlo_ac = a.lo.sub_spec(c.lo);
        let dhi_ac = a.hi.sub_spec(c.hi);
        let dlo_ab = a.lo.sub_spec(b.lo);
        let dhi_ab = a.hi.sub_spec(b.hi);
        let dlo_bc = b.lo.sub_spec(c.lo);
        let dhi_bc = b.hi.sub_spec(c.hi);

        // Key identity: (a - c) = (a - b) + (b - c) for both lo and hi
        // dlo_ac ≡ dlo_ab + dlo_bc
        Rational::lemma_sub_then_add_cancel(a.lo, b.lo);
        // b.lo + (a.lo - b.lo) ≡ a.lo
        // We need: (a.lo - b.lo) + (b.lo - c.lo) ≡ a.lo - c.lo

        // Triangle inequality for rationals: |u + v| ≤ |u| + |v|
        // Applied to u = dlo_ab, v = dlo_bc:
        // |dlo_ab + dlo_bc| ≤ |dlo_ab| + |dlo_bc|
        Rational::lemma_triangle_inequality(dlo_ab, dlo_bc);
        // And similarly for hi:
        Rational::lemma_triangle_inequality(dhi_ab, dhi_bc);

        // Now: dlo_ab + dlo_bc ≡ dlo_ac (algebraic identity)
        // (a.lo - b.lo) + (b.lo - c.lo) ≡ a.lo - c.lo
        // This is lemma_sub_add_distributes or similar
        // Let's prove: (a-b) + (b-c) = a + (-b) + b + (-c) = a + (-c) = a - c
        // Structurally: sub_spec is add_spec(neg_spec)
        // dlo_ab = a.lo.add_spec(b.lo.neg_spec())
        // dlo_bc = b.lo.add_spec(c.lo.neg_spec())
        // sum = dlo_ab.add_spec(dlo_bc)
        //     = (a.lo + (-b.lo)) + (b.lo + (-c.lo))
        // We need this ≡ a.lo + (-c.lo) = a.lo - c.lo

        // Use eqv_sub_cancel_right or similar. Actually:
        // (a + (-b)) + (b + (-c)) ≡ ((a + (-b)) + b) + (-c)  by assoc
        // (a + (-b)) + b ≡ a  by add_then_sub_cancel variant
        // So the whole thing ≡ a + (-c) = a - c

        // Actually, let's use a simpler approach. We know:
        // dlo_ab.add_spec(dlo_bc) structurally has certain num/den values.
        // And dlo_ac has certain num/den values.
        // We need them to be eqv_spec.
        // Rather than proving this algebraically, we can show:
        // |dlo_ac| ≤ |dlo_ab| + |dlo_bc| directly from triangle inequality
        // IF dlo_ac ≡ dlo_ab + dlo_bc. But we need that eqv.

        // Let's use a direct approach instead. Expand to cross-multiplication.
        // (a.lo - b.lo) + (b.lo - c.lo) and (a.lo - c.lo):
        // sub_spec gives add_spec(neg_spec), which gives specific num/den formulas.
        // This is provable by nonlinear_arith but may be complex.

        // Simpler: use lemma_sub_add_sub_cancel which should give us
        // (a - b) + (b - c) ≡ a - c
        Self::lemma_sub_add_sub_eqv(a.lo, b.lo, c.lo);
        Self::lemma_sub_add_sub_eqv(a.hi, b.hi, c.hi);
        // Now: dlo_ab + dlo_bc ≡ dlo_ac
        // So |dlo_ab + dlo_bc| ≡ |dlo_ac| (abs respects eqv)
        // Actually we need the eqv to transfer through abs.
        // |dlo_ab + dlo_bc| ≤ |dlo_ab| + |dlo_bc| (triangle ineq, already called)
        // And |dlo_ac| ≤ |dlo_ab + dlo_bc| (from eqv, specifically they're ≡)
        // Actually: since dlo_ab + dlo_bc ≡ dlo_ac, |dlo_ab + dlo_bc| ≡ |dlo_ac|
        Self::lemma_eqv_abs_congruence(
            dlo_ab.add_spec(dlo_bc), dlo_ac);
        Self::lemma_eqv_abs_congruence(
            dhi_ab.add_spec(dhi_bc), dhi_ac);

        // |dlo_ac| ≡ |dlo_ab + dlo_bc| ≤ |dlo_ab| + |dlo_bc|
        let abs_lo_ac = dlo_ac.abs_spec();
        let abs_hi_ac = dhi_ac.abs_spec();
        let abs_lo_ab = dlo_ab.abs_spec();
        let abs_hi_ab = dhi_ab.abs_spec();
        let abs_lo_bc = dlo_bc.abs_spec();
        let abs_hi_bc = dhi_bc.abs_spec();

        let sum_lo = dlo_ab.add_spec(dlo_bc);
        let sum_hi = dhi_ab.add_spec(dhi_bc);

        // |sum_lo| ≤ |dlo_ab| + |dlo_bc|
        // and |sum_lo| ≡ |dlo_ac|
        // so |dlo_ac| ≤ |dlo_ab| + |dlo_bc|
        Rational::lemma_eqv_symmetric(sum_lo.abs_spec(), abs_lo_ac);
        Rational::lemma_eqv_implies_le(abs_lo_ac, sum_lo.abs_spec());
        Rational::lemma_le_transitive(abs_lo_ac, sum_lo.abs_spec(),
            abs_lo_ab.add_spec(abs_lo_bc));

        Rational::lemma_eqv_symmetric(sum_hi.abs_spec(), abs_hi_ac);
        Rational::lemma_eqv_implies_le(abs_hi_ac, sum_hi.abs_spec());
        Rational::lemma_le_transitive(abs_hi_ac, sum_hi.abs_spec(),
            abs_hi_ab.add_spec(abs_hi_bc));

        // Now: |dlo_ac| ≤ |dlo_ab| + |dlo_bc| ≤ hab + hbc
        // where hab = max(|dlo_ab|, |dhi_ab|), hbc = max(|dlo_bc|, |dhi_bc|)
        let hab = a.hausdorff_spec(b);
        let hbc = b.hausdorff_spec(c);

        // |dlo_ab| ≤ max(|dlo_ab|, |dhi_ab|) = hab
        Rational::lemma_max_ge_left(abs_lo_ab, abs_hi_ab);
        // |dlo_bc| ≤ max(|dlo_bc|, |dhi_bc|) = hbc
        Rational::lemma_max_ge_left(abs_lo_bc, abs_hi_bc);
        // |dlo_ab| + |dlo_bc| ≤ hab + hbc
        Rational::lemma_le_add_both(abs_lo_ab, hab, abs_lo_bc, hbc);
        // |dlo_ac| ≤ |dlo_ab| + |dlo_bc| ≤ hab + hbc
        Rational::lemma_le_transitive(abs_lo_ac,
            abs_lo_ab.add_spec(abs_lo_bc),
            hab.add_spec(hbc));

        // Similarly for hi
        Rational::lemma_max_ge_right(abs_lo_ab, abs_hi_ab);
        Rational::lemma_max_ge_right(abs_lo_bc, abs_hi_bc);
        Rational::lemma_le_add_both(abs_hi_ab, hab, abs_hi_bc, hbc);
        Rational::lemma_le_transitive(abs_hi_ac,
            abs_hi_ab.add_spec(abs_hi_bc),
            hab.add_spec(hbc));

        // max(|dlo_ac|, |dhi_ac|) ≤ hab + hbc
        // Since both |dlo_ac| ≤ hab+hbc and |dhi_ac| ≤ hab+hbc,
        // max(|dlo_ac|, |dhi_ac|) ≤ hab+hbc.
        Rational::lemma_trichotomy(abs_lo_ac, abs_hi_ac);
        let hac = a.hausdorff_spec(c);
        if abs_lo_ac.le_spec(abs_hi_ac) {
            assert(hac == abs_hi_ac);
        } else {
            assert(hac == abs_lo_ac);
        }
    }

    /// Helper: if a ≡ b then |a| ≡ |b|.
    proof fn lemma_eqv_abs_congruence(a: Rational, b: Rational)
        requires
            a.eqv_spec(b),
        ensures
            a.abs_spec().eqv_spec(b.abs_spec()),
    {
        Rational::lemma_denom_positive(a);
        Rational::lemma_denom_positive(b);
        if a.num >= 0 && b.num >= 0 {
            assert(a.abs_spec() == a);
            assert(b.abs_spec() == b);
        } else if a.num < 0 && b.num < 0 {
            assert(a.abs_spec() == a.neg_spec());
            assert(b.abs_spec() == b.neg_spec());
            assert(a.abs_spec().num * b.abs_spec().denom()
                == b.abs_spec().num * a.abs_spec().denom()) by (nonlinear_arith)
                requires
                    a.num * b.denom() == b.num * a.denom(),
                    a.abs_spec().num == -a.num,
                    b.abs_spec().num == -b.num,
                    a.abs_spec().denom() == a.denom(),
                    b.abs_spec().denom() == b.denom(),
            ;
        } else if a.num >= 0 && b.num < 0 {
            assert(false) by (nonlinear_arith)
                requires
                    a.num >= 0, b.num < 0,
                    a.denom() > 0, b.denom() > 0,
                    a.num * b.denom() == b.num * a.denom(),
            ;
        } else {
            assert(false) by (nonlinear_arith)
                requires
                    a.num < 0, b.num >= 0,
                    a.denom() > 0, b.denom() > 0,
                    a.num * b.denom() == b.num * a.denom(),
            ;
        }
    }

    /// Helper: (a - b) + (b - c) ≡ (a - c).
    proof fn lemma_sub_add_sub_eqv(a: Rational, b: Rational, c: Rational)
        ensures
            a.sub_spec(b).add_spec(b.sub_spec(c)).eqv_spec(a.sub_spec(c)),
    {
        // (a - b) + (b - c)
        // = (a + (-b)) + (b + (-c))
        let ab = a.sub_spec(b); // a + (-b)
        let bc = b.sub_spec(c); // b + (-c)
        let sum = ab.add_spec(bc);
        let target = a.sub_spec(c);

        // Use cross-multiplication to show eqv.
        // sum.num * target.denom() == target.num * sum.denom()
        // This is a concrete identity about the Rational struct fields.
        // sub_spec(a, b) = a.add_spec(b.neg_spec())
        // Expanding is complex but the SMT solver with nonlinear_arith can handle it
        // if we give it the right structural equalities.

        Rational::lemma_add_denom_product_int(ab, bc);
        Rational::lemma_add_denom_product_int(a, b.neg_spec());
        Rational::lemma_add_denom_product_int(b, c.neg_spec());
        Rational::lemma_add_denom_product_int(a, c.neg_spec());
        Rational::lemma_denom_positive(a);
        Rational::lemma_denom_positive(b);
        Rational::lemma_denom_positive(c);

        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        let nb = b.neg_spec();
        let nc = c.neg_spec();

        assert(nb.num == -b.num);
        assert(nb.denom() == db);
        assert(nc.num == -c.num);
        assert(nc.denom() == dc);

        // ab = a + (-b), ab.num = a.num * db + (-b.num) * da = a.num * db - b.num * da
        // ab.denom() = da * db
        assert(ab.num == a.num * db + nb.num * da);
        assert(ab.denom() == da * db);
        // bc = b + (-c), bc.num = b.num * dc + (-c.num) * db = b.num * dc - c.num * db
        // bc.denom() = db * dc
        assert(bc.num == b.num * dc + nc.num * db);
        assert(bc.denom() == db * dc);
        // sum = ab + bc
        // sum.num = ab.num * bc.denom() + bc.num * ab.denom()
        //         = (a.num*db - b.num*da) * (db*dc) + (b.num*dc - c.num*db) * (da*db)
        // sum.denom() = ab.denom() * bc.denom() = (da*db) * (db*dc)
        assert(sum.num == ab.num * bc.denom() + bc.num * ab.denom());
        assert(sum.denom() == ab.denom() * bc.denom());

        // target = a + (-c)
        // target.num = a.num * dc + (-c.num) * da = a.num * dc - c.num * da
        // target.denom() = da * dc
        assert(target.num == a.num * dc + nc.num * da);
        assert(target.denom() == da * dc);

        // Need: sum.num * target.denom() == target.num * sum.denom()
        // Stage 1: substitute negations to expose cancellation structure
        assert(sum.num ==
            (a.num * db - b.num * da) * (db * dc)
            + (b.num * dc - c.num * db) * (da * db))
            by (nonlinear_arith)
            requires
                ab.num == a.num * db + nb.num * da,
                bc.num == b.num * dc + nc.num * db,
                sum.num == ab.num * (db * dc) + bc.num * (da * db),
                nb.num == -b.num,
                nc.num == -c.num,
        ;
        // Stage 2: expand each product and cancel b-terms
        assert((a.num * db - b.num * da) * (db * dc)
            == a.num * db * db * dc - b.num * da * db * dc)
            by (nonlinear_arith);
        assert((b.num * dc - c.num * db) * (da * db)
            == b.num * da * db * dc - c.num * da * db * db)
            by (nonlinear_arith);
        assert(a.num * db * db * dc - b.num * da * db * dc
            + (b.num * da * db * dc - c.num * da * db * db)
            == db * db * (a.num * dc - c.num * da))
            by (nonlinear_arith);
        // Stage 3: cross-multiply using factored form
        assert(sum.num * target.denom() == target.num * sum.denom())
            by (nonlinear_arith)
            requires
                sum.num == db * db * (a.num * dc - c.num * da),
                sum.denom() == (da * db) * (db * dc),
                target.num == a.num * dc + nc.num * da,
                target.denom() == da * dc,
                nc.num == -c.num,
        ;
    }

    // ── 8.2 Gap between disjoint intervals ──

    /// Gap (separation) between two intervals.
    /// Positive iff the intervals are disjoint.
    pub open spec fn gap_spec(self, other: Interval) -> Rational {
        let zero = Rational::from_int_spec(0);
        zero.max_spec(
            self.lo.sub_spec(other.hi).max_spec(
                other.lo.sub_spec(self.hi)))
    }

    /// Gap is positive iff intervals are disjoint.
    pub proof fn lemma_gap_positive_iff_disjoint(a: Self, b: Self)
        requires
            a.wf_spec(),
            b.wf_spec(),
        ensures
            Rational::from_int_spec(0).lt_spec(a.gap_spec(b))
            <==> a.disjoint_spec(b),
    {
        let zero = Rational::from_int_spec(0);
        let d1 = a.lo.sub_spec(b.hi); // a.lo - b.hi
        let d2 = b.lo.sub_spec(a.hi); // b.lo - a.hi
        let inner_max = d1.max_spec(d2);
        let gap = zero.max_spec(inner_max);

        // disjoint(a, b) = a.hi.lt_spec(b.lo) || b.hi.lt_spec(a.lo)
        // i.e., a.hi < b.lo ∨ b.hi < a.lo

        // Forward: 0 < gap → disjoint
        if zero.lt_spec(gap) {
            // gap = max(0, max(d1, d2)) > 0 → max(d1, d2) > 0
            // → d1 > 0 ∨ d2 > 0
            // d1 > 0 means a.lo - b.hi > 0 means a.lo > b.hi means b.hi < a.lo
            // d2 > 0 means b.lo - a.hi > 0 means b.lo > a.hi means a.hi < b.lo
            Rational::lemma_trichotomy(zero, inner_max);
            if zero.le_spec(inner_max) {
                assert(gap == inner_max);
            } else {
                // gap = zero, contradicts 0 < gap
                assert(gap == zero);
                assert(false);
            }
            // Now 0 < inner_max = max(d1, d2)
            Rational::lemma_trichotomy(d1, d2);
            if d1.le_spec(d2) {
                // inner_max = d2 > 0
                // b.lo - a.hi > 0 → a.hi < b.lo
                Self::lemma_pos_sub_implies_lt(a.hi, b.lo);
            } else {
                // inner_max = d1 > 0
                // a.lo - b.hi > 0 → b.hi < a.lo
                Self::lemma_pos_sub_implies_lt(b.hi, a.lo);
            }
        }

        // Backward: disjoint → 0 < gap
        if a.disjoint_spec(b) {
            if a.hi.lt_spec(b.lo) {
                // a.hi < b.lo → b.lo - a.hi > 0 → d2 > 0
                Self::lemma_lt_implies_pos_sub(a.hi, b.lo);
                // d2 > 0, so max(d1, d2) ≥ d2 > 0
                Rational::lemma_max_ge_right(d1, d2);
                Rational::lemma_lt_le_transitive(zero, d2, inner_max);
                // gap = max(0, inner_max) ≥ inner_max > 0
                Rational::lemma_max_ge_right(zero, inner_max);
                Rational::lemma_lt_le_transitive(zero, inner_max, gap);
            } else {
                // b.hi < a.lo → a.lo - b.hi > 0 → d1 > 0
                Self::lemma_lt_implies_pos_sub(b.hi, a.lo);
                Rational::lemma_max_ge_left(d1, d2);
                Rational::lemma_lt_le_transitive(zero, d1, inner_max);
                Rational::lemma_max_ge_right(zero, inner_max);
                Rational::lemma_lt_le_transitive(zero, inner_max, gap);
            }
        }
    }

    /// Gap bounds element distance: x ∈ a ∧ y ∈ b → |x - y| ≥ gap(a, b).
    pub proof fn lemma_gap_bounds_element_distance(a: Self, b: Self, x: Rational, y: Rational)
        requires
            a.wf_spec(),
            b.wf_spec(),
            a.contains_spec(x),
            b.contains_spec(y),
        ensures
            a.gap_spec(b).le_spec(x.sub_spec(y).abs_spec()),
    {
        let zero = Rational::from_int_spec(0);
        let d1 = a.lo.sub_spec(b.hi);
        let d2 = b.lo.sub_spec(a.hi);
        let inner_max = d1.max_spec(d2);
        let gap = zero.max_spec(inner_max);
        let diff = x.sub_spec(y);
        let abs_diff = diff.abs_spec();

        // gap ≤ |x - y|
        // Case 1: gap = 0 (intervals overlap)
        // Then 0 ≤ |x - y| ✓
        Rational::lemma_abs_nonneg(diff);
        Rational::lemma_denom_positive(abs_diff);
        assert(zero.le_spec(abs_diff)) by (nonlinear_arith)
            requires
                abs_diff.num >= 0,
                abs_diff.denom() > 0,
                zero.num == 0int,
                zero.denom() == 1int,
        ;

        // Case 2: gap > 0 → intervals are disjoint
        // d1 = a.lo - b.hi: since a.lo ≤ x and y ≤ b.hi,
        //   d1 = a.lo - b.hi ≤ x - y
        Rational::lemma_sub_le_monotone_left(a.lo, x, b.hi);
        // a.lo - b.hi ≤ x - b.hi
        Rational::lemma_sub_le_monotone_right(y, b.hi, x);
        // x - b.hi ≤ x - y
        Rational::lemma_le_transitive(d1, x.sub_spec(b.hi), diff);

        // d2 = b.lo - a.hi: since b.lo ≤ y and x ≤ a.hi,
        //   d2 = b.lo - a.hi ≤ y - x = -(x - y)
        Rational::lemma_sub_le_monotone_left(b.lo, y, a.hi);
        Rational::lemma_sub_le_monotone_right(x, a.hi, y);
        Rational::lemma_le_transitive(d2, y.sub_spec(a.hi), y.sub_spec(x));
        // y - x = -(x - y)
        let neg_diff = diff.neg_spec();

        // d1 ≤ x - y and d1 ≤ |x - y| (since x-y ≤ |x-y|)
        // d2 ≤ y - x = -(x - y) and d2 ≤ |x - y| (since -(x-y) ≤ |x-y|)
        // So max(d1, d2) ≤ |x - y|
        // And gap = max(0, max(d1, d2)) ≤ max(0, |x-y|) = |x-y| (since |x-y| ≥ 0)

        // x - y ≤ |x - y|
        if diff.num >= 0 {
            assert(abs_diff == diff);
        } else {
            // diff.num < 0, abs = neg_spec, neg_diff
            assert(abs_diff == neg_diff);
            Rational::lemma_neg_reverses_le(diff, zero);
            // 0 ≤ -diff = neg_diff = abs_diff
            // diff ≤ 0 ≤ abs_diff
            Rational::lemma_le_transitive(diff, zero, abs_diff);
        }
        // So diff ≤ abs_diff
        // d1 ≤ diff ≤ abs_diff
        Rational::lemma_le_transitive(d1, diff, abs_diff);

        // -(x-y) ≤ |x-y|
        if diff.num >= 0 {
            // neg_diff.num ≤ 0
            assert(neg_diff.num == -diff.num);
            // abs_diff = diff, neg_diff ≤ 0 ≤ diff = abs_diff
            assert(neg_diff.num <= 0);
            Rational::lemma_denom_positive(neg_diff);
            assert(neg_diff.le_spec(zero)) by (nonlinear_arith)
                requires
                    neg_diff.num <= 0,
                    neg_diff.denom() > 0,
                    zero.num == 0int,
                    zero.denom() == 1int,
            ;
            Rational::lemma_le_transitive(neg_diff, zero, abs_diff);
        } else {
            assert(abs_diff == neg_diff);
        }
        // neg_diff ≤ abs_diff

        // y - x = -(x - y) structurally:
        // lemma_neg_sub(x, y) ensures x.sub_spec(y).neg_spec() == y.sub_spec(x)
        Rational::lemma_neg_sub(x, y);
        // So neg_diff = diff.neg_spec() = x.sub_spec(y).neg_spec() == y.sub_spec(x)
        // d2 ≤ y.sub_spec(x) = neg_diff (structural equality)
        // Since neg_diff == y.sub_spec(x) structurally, d2 ≤ neg_diff directly
        // d2 ≤ neg_diff ≤ abs_diff
        Rational::lemma_le_transitive(d2, neg_diff, abs_diff);

        // max(d1, d2) ≤ abs_diff
        Rational::lemma_trichotomy(d1, d2);
        if d1.le_spec(d2) {
            assert(inner_max == d2);
        } else {
            assert(inner_max == d1);
        }

        // gap = max(0, inner_max) ≤ max(0, abs_diff) = abs_diff (since abs_diff ≥ 0)
        // If inner_max ≤ abs_diff:
        //   gap = max(0, inner_max)
        //   If 0 ≤ inner_max: gap = inner_max ≤ abs_diff ✓
        //   If inner_max < 0: gap = 0 ≤ abs_diff ✓
        Rational::lemma_trichotomy(zero, inner_max);
        if zero.le_spec(inner_max) {
            assert(gap == inner_max);
        } else {
            assert(gap == zero);
        }
    }

    /// Helper: a < b → b - a > 0 (in lt_spec terms).
    proof fn lemma_lt_implies_pos_sub(a: Rational, b: Rational)
        requires
            a.lt_spec(b),
        ensures
            Rational::from_int_spec(0).lt_spec(b.sub_spec(a)),
    {
        let zero = Rational::from_int_spec(0);
        let diff = b.sub_spec(a);
        Rational::lemma_denom_positive(a);
        Rational::lemma_denom_positive(b);
        Rational::lemma_add_denom_product_int(b, a.neg_spec());
        let na = a.neg_spec();
        assert(na.num == -a.num);
        assert(diff.num == b.num * a.denom() + na.num * b.denom());
        assert(diff.denom() == b.denom() * a.denom());
        assert(zero.lt_spec(diff)) by (nonlinear_arith)
            requires
                a.num * b.denom() < b.num * a.denom(),
                diff.num == b.num * a.denom() + na.num * b.denom(),
                na.num == -a.num,
                diff.denom() == b.denom() * a.denom(),
                a.denom() > 0,
                b.denom() > 0,
                zero.num == 0int,
                zero.denom() == 1int,
        ;
    }

    /// Helper: b - a > 0 → a < b.
    proof fn lemma_pos_sub_implies_lt(a: Rational, b: Rational)
        requires
            Rational::from_int_spec(0).lt_spec(b.sub_spec(a)),
        ensures
            a.lt_spec(b),
    {
        let zero = Rational::from_int_spec(0);
        let diff = b.sub_spec(a);
        Rational::lemma_denom_positive(a);
        Rational::lemma_denom_positive(b);
        Rational::lemma_add_denom_product_int(b, a.neg_spec());
        let na = a.neg_spec();
        assert(na.num == -a.num);
        assert(diff.num == b.num * a.denom() + na.num * b.denom());
        assert(diff.denom() == b.denom() * a.denom());
        assert(a.lt_spec(b)) by (nonlinear_arith)
            requires
                zero.num * diff.denom() < diff.num * zero.denom(),
                diff.num == b.num * a.denom() + na.num * b.denom(),
                na.num == -a.num,
                diff.denom() == b.denom() * a.denom(),
                a.denom() > 0,
                b.denom() > 0,
                zero.num == 0int,
                zero.denom() == 1int,
        ;
    }

    // ── Correctness characterization proofs ──────────────────────
    //
    // Properties that could only hold if the spec‐function formulas are
    // actually correct.  If someone introduced a bug (swapped endpoints,
    // wrong sign, wrong case split), these proofs would fail to verify.

    // ── Category 1: Point interval exactness ─────────────────────
    //
    // When inputs are exact (point intervals), interval arithmetic must
    // produce exact results: from_point(x) op from_point(y) == from_point(x op y).

    /// Point + Point = Point(sum).
    pub proof fn lemma_point_add_exact(x: Rational, y: Rational)
        ensures
            Self::from_point_spec(x).add_spec(Self::from_point_spec(y))
                == Self::from_point_spec(x.add_spec(y)),
    {
        // Definitional: lo = x + y, hi = x + y.
    }

    /// Point negation is exact.
    pub proof fn lemma_point_neg_exact(x: Rational)
        ensures
            Self::from_point_spec(x).neg_spec()
                == Self::from_point_spec(x.neg_spec()),
    {
        // neg swaps lo/hi, but they're equal so swap is identity.
    }

    /// Point - Point = Point(difference).
    pub proof fn lemma_point_sub_exact(x: Rational, y: Rational)
        ensures
            Self::from_point_spec(x).sub_spec(Self::from_point_spec(y))
                == Self::from_point_spec(x.sub_spec(y)),
    {
        // lo = x - y, hi = x - y.
    }

    /// Point reciprocal is exact.
    pub proof fn lemma_point_recip_exact(x: Rational)
        ensures
            Self::from_point_spec(x).recip_spec()
                == Self::from_point_spec(x.reciprocal_spec()),
    {
        // recip swaps lo/hi, but they're equal so swap is identity.
    }

    // ── Category 2: Algebraic involutions ────────────────────────

    /// Double negation is identity.
    pub proof fn lemma_neg_involution(a: Interval)
        ensures
            a.neg_spec().neg_spec() == a,
    {
        // neg: {lo: -hi, hi: -lo}. Double: {lo: -(-lo), hi: -(-hi)}.
        Rational::lemma_neg_involution(a.lo);
        Rational::lemma_neg_involution(a.hi);
    }

    // ── Category 4: Structural identities ────────────────────────

    /// Interval addition is commutative (up to rational equivalence).
    pub proof fn lemma_add_commutative(a: Interval, b: Interval)
        ensures
            a.add_spec(b).lo.eqv_spec(b.add_spec(a).lo),
            a.add_spec(b).hi.eqv_spec(b.add_spec(a).hi),
    {
        Rational::lemma_add_commutative(a.lo, b.lo);
        Rational::lemma_add_commutative(a.hi, b.hi);
    }

    /// Adding zero (as a point interval) is identity.
    pub proof fn lemma_add_zero_identity(a: Interval)
        ensures
            a.add_spec(Self::from_point_spec(Rational::from_int_spec(0))) == a,
    {
        Rational::lemma_add_zero_identity(a.lo);
        Rational::lemma_add_zero_identity(a.hi);
    }

    /// Point * Point = Point(product).
    pub proof fn lemma_point_mul_exact(x: Rational, y: Rational)
        ensures
            Self::from_point_spec(x).mul_spec(Self::from_point_spec(y))
                == Self::from_point_spec(x.mul_spec(y)),
    {
        // All four corner products are x*y; min4/max4 collapse since a.le_spec(a).
    }

    /// Point square is exact.
    pub proof fn lemma_point_square_exact(x: Rational)
        ensures
            Self::from_point_spec(x).square_spec()
                == Self::from_point_spec(x.mul_spec(x)),
    {
        // Case split on sign of x handled by SMT: either 0<=x.num or x.num<0.
        // Both branches of square_spec produce {lo: x*x, hi: x*x}.
    }

    /// Point abs is exact.
    pub proof fn lemma_point_abs_exact(x: Rational)
        ensures
            Self::from_point_spec(x).abs_spec()
                == Self::from_point_spec(x.abs_spec()),
    {
        // Interval abs_spec branches on zero.le_spec(x) where
        // zero = from_int_spec(0). Help Verus connect this to x.num >= 0
        // used by Rational::abs_spec.
        let zero = Rational::from_int_spec(0);
        Rational::lemma_denom_positive(x);
        assert(zero.le_spec(x) == (x.num >= 0)) by (nonlinear_arith)
            requires
                zero.num == 0int,
                zero.denom() == 1int,
                x.denom() > 0,
        ;
    }

    /// Multiplying by one (as a point interval) is identity.
    pub proof fn lemma_mul_one_identity(a: Interval)
        requires
            a.wf_spec(),
        ensures
            a.mul_spec(Self::from_point_spec(Rational::from_int_spec(1))) == a,
    {
        Rational::lemma_mul_one_identity(a.lo);
        Rational::lemma_mul_one_identity(a.hi);
        // Products collapse to {a.lo, a.lo, a.hi, a.hi}.
        // min4 = a.lo and max4 = a.hi by wf (lo <= hi).
    }

    // ── Category 3: Self-interaction ─────────────────────────────

    /// a - a contains zero.
    pub proof fn lemma_self_sub_contains_zero(a: Interval)
        requires
            a.wf_spec(),
        ensures
            a.sub_spec(a).contains_spec(Rational::from_int_spec(0)),
    {
        let zero = Rational::from_int_spec(0);
        // a.sub_spec(a) = [a.lo - a.hi, a.hi - a.lo]
        // Since a.lo <= a.hi (wf):
        //   a.lo - a.hi <= a.hi - a.hi ≡ 0   (lower bound)
        //   0 ≡ a.hi - a.hi <= a.hi - a.lo    (upper bound)

        Rational::lemma_sub_self(a.hi);
        Rational::lemma_eqv_implies_le(a.hi.sub_spec(a.hi), zero);

        // Lower bound: a.lo - a.hi <= 0
        Rational::lemma_sub_le_monotone_left(a.lo, a.hi, a.hi);
        Rational::lemma_le_transitive(
            a.lo.sub_spec(a.hi), a.hi.sub_spec(a.hi), zero);

        // Upper bound: 0 <= a.hi - a.lo
        Rational::lemma_sub_le_monotone_right(a.lo, a.hi, a.hi);
        Rational::lemma_le_transitive(
            zero, a.hi.sub_spec(a.hi), a.hi.sub_spec(a.lo));
    }

    /// a / a contains one (when 0 ∉ a).
    pub proof fn lemma_self_div_contains_one(a: Interval)
        requires
            a.wf_spec(),
            Rational::from_int_spec(0).lt_spec(a.lo)
                || a.hi.lt_spec(Rational::from_int_spec(0)),
        ensures
            a.div_spec(a).contains_spec(Rational::from_int_spec(1)),
    {
        let zero = Rational::from_int_spec(0);
        let one = Rational::from_int_spec(1);

        // a.lo ∈ a
        Self::lemma_contains_lo(a);

        // a.lo / a.lo ∈ a / a
        Self::lemma_div_containment(a, a, a.lo, a.lo);

        // Establish !a.lo.eqv_spec(0) so we can use div_self
        if zero.lt_spec(a.lo) {
            Rational::lemma_trichotomy(zero, a.lo);
            Rational::lemma_eqv_symmetric(zero, a.lo);
        } else {
            Rational::lemma_le_lt_transitive(a.lo, a.hi, zero);
            Rational::lemma_trichotomy(a.lo, zero);
        }

        // a.lo / a.lo ≡ 1
        Rational::lemma_div_self(a.lo);
        let q = a.lo.div_spec(a.lo);
        Rational::lemma_eqv_implies_le(q, one);

        // Chain: result.lo <= q <= 1 and 1 <= q <= result.hi
        let result = a.div_spec(a);
        Rational::lemma_le_transitive(result.lo, q, one);
        Rational::lemma_le_transitive(one, q, result.hi);
    }

    // ── Category 4 (continued): Structural identities ────────────

    /// Interval multiplication is commutative (up to rational equivalence).
    pub proof fn lemma_mul_commutative(a: Interval, b: Interval)
        ensures
            a.mul_spec(b).lo.eqv_spec(b.mul_spec(a).lo),
            a.mul_spec(b).hi.eqv_spec(b.mul_spec(a).hi),
    {
        // After mul_commutative, b*a uses the same four products
        // as a*b, just in a different min4/max4 order.
        Rational::lemma_mul_commutative(a.lo, b.lo);
        Rational::lemma_mul_commutative(a.lo, b.hi);
        Rational::lemma_mul_commutative(a.hi, b.lo);
        Rational::lemma_mul_commutative(a.hi, b.hi);

        let ac = a.lo.mul_spec(b.lo);
        let ad = a.lo.mul_spec(b.hi);
        let bc = a.hi.mul_spec(b.lo);
        let bd = a.hi.mul_spec(b.hi);

        // a*b.lo = min4(ac,ad,bc,bd), b*a.lo = min4(ac,bc,ad,bd).
        // Both ≤ the other by lemma_min4_le (each min4 result is
        // one of the four products, so it witnesses the disjunction).
        let min_ab = ac.min_spec(ad).min_spec(bc).min_spec(bd);
        let min_ba = ac.min_spec(bc).min_spec(ad).min_spec(bd);
        Self::lemma_min4_le(ac, ad, bc, bd, min_ba);
        Self::lemma_min4_le(ac, bc, ad, bd, min_ab);
        Rational::lemma_le_antisymmetric(min_ab, min_ba);

        // Same for max (hi).
        let max_ab = ac.max_spec(ad).max_spec(bc).max_spec(bd);
        let max_ba = ac.max_spec(bc).max_spec(ad).max_spec(bd);
        Self::lemma_max4_ge(ac, ad, bc, bd, max_ba);
        Self::lemma_max4_ge(ac, bc, ad, bd, max_ab);
        Rational::lemma_le_antisymmetric(max_ab, max_ba);
    }

    // ── Category 5: Tightness ────────────────────────────────────

    /// square_spec is at least as tight as mul_spec(self, self).
    pub proof fn lemma_square_tighter_than_mul(a: Interval)
        requires
            a.wf_spec(),
        ensures
            a.mul_spec(a).contains_interval_spec(a.square_spec()),
    {
        let zero = Rational::from_int_spec(0);
        let lo2 = a.lo.mul_spec(a.lo);
        let lh  = a.lo.mul_spec(a.hi);
        let hl  = a.hi.mul_spec(a.lo);
        let hi2 = a.hi.mul_spec(a.hi);

        if zero.le_spec(a.lo) {
            // Nonneg: square = [lo², hi²], both are corner products.
            Self::lemma_min4_le(lo2, lh, hl, hi2, lo2);
            Self::lemma_max4_ge(lo2, lh, hl, hi2, hi2);
        } else if a.hi.le_spec(zero) {
            // Nonpos: square = [hi², lo²], both are corner products.
            Self::lemma_min4_le(lo2, lh, hl, hi2, hi2);
            Self::lemma_max4_ge(lo2, lh, hl, hi2, lo2);
        } else {
            // Spans zero: square = [0, max(lo², hi²)].
            // lo bound: lh = a.lo*a.hi ≤ 0 since a.lo < 0 < a.hi.
            Rational::lemma_le_mul_nonneg(a.lo, zero, a.hi);
            Rational::lemma_mul_zero(a.hi);
            Rational::lemma_eqv_implies_le(
                zero.mul_spec(a.hi), zero);
            Rational::lemma_le_transitive(lh, zero.mul_spec(a.hi), zero);
            Self::lemma_min4_le(lo2, lh, hl, hi2, zero);

            // hi bound: max(lo², hi²) is one of {lo², hi²},
            // both of which are corner products.
            Self::lemma_max4_ge(lo2, lh, hl, hi2, a.square_spec().hi);
        }
    }
}

} // verus!
