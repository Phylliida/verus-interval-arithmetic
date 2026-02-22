#[cfg(verus_keep_ghost)]
use crate::interval::Interval;
#[cfg(verus_keep_ghost)]
use verus_rational::Rational;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

use verus_rational::RuntimeRational;

#[cfg(not(verus_keep_ghost))]
compile_error!(
    "verus-interval-arithmetic exposes a single verified implementation; \
     build with Verus (`cfg(verus_keep_ghost)`, e.g. `cargo verus verify`)"
);

#[cfg(not(verus_keep_ghost))]
pub struct RuntimeInterval;

#[cfg(verus_keep_ghost)]
verus! {

/// Runtime interval backed by RuntimeRational endpoints.
pub struct RuntimeInterval {
    pub lo: RuntimeRational,
    pub hi: RuntimeRational,
    pub model: Ghost<Interval>,
}

impl RuntimeInterval {
    /// Well-formedness invariant tying runtime witnesses to the ghost model.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.lo.wf_spec()
        &&& self.hi.wf_spec()
        &&& self.lo@ == self@.lo
        &&& self.hi@ == self@.hi
        &&& self@.wf_spec()
    }

    /// Construct an interval from ordered endpoints [lo, hi].
    /// Takes ownership of both RuntimeRationals.
    pub fn from_endpoints(lo: RuntimeRational, hi: RuntimeRational) -> (out: Self)
        requires
            lo.wf_spec(),
            hi.wf_spec(),
            lo@.le_spec(hi@),
        ensures
            out.wf_spec(),
            out@.lo == lo@,
            out@.hi == hi@,
    {
        let ghost lo_model = lo@;
        let ghost hi_model = hi@;
        let ghost iv = Interval { lo: lo_model, hi: hi_model };
        RuntimeInterval {
            lo,
            hi,
            model: Ghost(iv),
        }
    }

    /// Construct a point interval [x, x] from a single rational.
    pub fn from_point(x: &RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
        ensures
            out.wf_spec(),
            out@.lo == x@,
            out@.hi == x@,
    {
        let lo = RuntimeRational {
            numerator: x.numerator.copy_small_total(),
            denominator: x.denominator.copy_small_total(),
            model: Ghost(x@),
        };
        let hi = RuntimeRational {
            numerator: x.numerator.copy_small_total(),
            denominator: x.denominator.copy_small_total(),
            model: Ghost(x@),
        };
        let ghost iv = Interval { lo: x@, hi: x@ };
        RuntimeInterval {
            lo,
            hi,
            model: Ghost(iv),
        }
    }

    // ── Interval arithmetic exec functions ───────────────────────

    /// Addition: [a,b] + [c,d] = [a+c, b+d].
    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.add_spec(rhs@),
            out.wf_spec(),
    {
        let lo = self.lo.add(&rhs.lo);
        let hi = self.hi.add(&rhs.hi);
        let ghost iv = self@.add_spec(rhs@);
        let out = RuntimeInterval {
            lo,
            hi,
            model: Ghost(iv),
        };
        proof {
            Interval::lemma_add_wf(self@, rhs@);
        }
        out
    }

    /// Negation: -[a,b] = [-b, -a].
    pub fn neg(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.neg_spec(),
            out.wf_spec(),
    {
        let lo = self.hi.neg();
        let hi = self.lo.neg();
        let ghost iv = self@.neg_spec();
        let out = RuntimeInterval {
            lo,
            hi,
            model: Ghost(iv),
        };
        proof {
            Interval::lemma_neg_wf(self@);
        }
        out
    }

    /// Subtraction: [a,b] - [c,d] = [a-d, b-c].
    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.sub_spec(rhs@),
            out.wf_spec(),
    {
        let lo = self.lo.sub(&rhs.hi);
        let hi = self.hi.sub(&rhs.lo);
        let ghost iv = self@.sub_spec(rhs@);
        let out = RuntimeInterval {
            lo,
            hi,
            model: Ghost(iv),
        };
        proof {
            Interval::lemma_sub_wf(self@, rhs@);
        }
        out
    }

    /// Multiplication: [a,b] * [c,d] = [min(ac,ad,bc,bd), max(ac,ad,bc,bd)].
    pub fn mul(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.mul_spec(rhs@),
            out.wf_spec(),
    {
        let ac = self.lo.mul(&rhs.lo);
        let ad = self.lo.mul(&rhs.hi);
        let bc = self.hi.mul(&rhs.lo);
        let bd = self.hi.mul(&rhs.hi);
        let lo = ac.min(&ad).min(&bc).min(&bd);
        let hi = ac.max(&ad).max(&bc).max(&bd);
        let ghost iv = self@.mul_spec(rhs@);
        let out = RuntimeInterval {
            lo,
            hi,
            model: Ghost(iv),
        };
        proof {
            // wf: lo <= hi because min(S) <= max(S) for any non-empty S.
            // min of the four is <= max of the four.
            // The min/max chain produces correct values by the spec
            // definitions of min_spec/max_spec.
            Rational::lemma_min_le_left(
                self@.lo.mul_spec(rhs@.lo).min_spec(self@.lo.mul_spec(rhs@.hi)).min_spec(self@.hi.mul_spec(rhs@.lo)),
                self@.hi.mul_spec(rhs@.hi));
            Rational::lemma_max_ge_left(
                self@.lo.mul_spec(rhs@.lo).max_spec(self@.lo.mul_spec(rhs@.hi)).max_spec(self@.hi.mul_spec(rhs@.lo)),
                self@.hi.mul_spec(rhs@.hi));
        }
        out
    }

    /// Scalar multiplication: k * [a,b].
    pub fn scale(scalar: &RuntimeRational, iv: &Self) -> (out: Self)
        requires
            scalar.wf_spec(),
            iv.wf_spec(),
        ensures
            out@ == Interval::scale_spec(scalar@, iv@),
            out.wf_spec(),
    {
        let sa = scalar.mul(&iv.lo);
        let sb = scalar.mul(&iv.hi);
        let lo = sa.min(&sb);
        let hi = sa.max(&sb);
        let ghost model = Interval::scale_spec(scalar@, iv@);
        let out = RuntimeInterval {
            lo,
            hi,
            model: Ghost(model),
        };
        proof {
            Rational::lemma_min_le_left(scalar@.mul_spec(iv@.lo), scalar@.mul_spec(iv@.hi));
            Rational::lemma_max_ge_left(scalar@.mul_spec(iv@.lo), scalar@.mul_spec(iv@.hi));
        }
        out
    }
    /// Absolute value: |[a,b]|.
    pub fn abs(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.abs_spec(),
            out.wf_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        let lo_nonneg = zero.le(&self.lo);
        if lo_nonneg {
            // lo >= 0: entirely nonneg, abs = self
            let lo = RuntimeRational {
                numerator: self.lo.numerator.copy_small_total(),
                denominator: self.lo.denominator.copy_small_total(),
                model: Ghost(self@.lo),
            };
            let hi = RuntimeRational {
                numerator: self.hi.numerator.copy_small_total(),
                denominator: self.hi.denominator.copy_small_total(),
                model: Ghost(self@.hi),
            };
            let ghost iv = self@;
            RuntimeInterval { lo, hi, model: Ghost(iv) }
        } else {
            let hi_nonpos = self.hi.le(&zero);
            if hi_nonpos {
                // hi <= 0: entirely nonpos, abs = neg
                let out = self.neg();
                proof {
                    Interval::lemma_neg_wf(self@);
                }
                out
            } else {
                // spans zero: [0, max(-lo, hi)]
                let neg_lo = self.lo.neg();
                let hi_copy = RuntimeRational {
                    numerator: self.hi.numerator.copy_small_total(),
                    denominator: self.hi.denominator.copy_small_total(),
                    model: Ghost(self@.hi),
                };
                let hi_out = neg_lo.max(&hi_copy);
                let lo_out = RuntimeRational::from_int(0i64);
                let ghost iv = self@.abs_spec();
                let out = RuntimeInterval {
                    lo: lo_out,
                    hi: hi_out,
                    model: Ghost(iv),
                };
                proof {
                    Interval::lemma_abs_wf(self@);
                }
                out
            }
        }
    }

    /// Reciprocal: 1/[a,b] = [1/b, 1/a].
    /// Requires 0 not in the interval (entirely positive or entirely negative).
    pub fn recip(&self) -> (out: Option<Self>)
        requires
            self.wf_spec(),
            Rational::from_int_spec(0).lt_spec(self@.lo)
                || self@.hi.lt_spec(Rational::from_int_spec(0)),
        ensures
            match out {
                Option::Some(r) => {
                    &&& r@ == self@.recip_spec()
                    &&& r.wf_spec()
                },
                Option::None => false,  // always succeeds given precondition
            },
    {
        // Compute 1/hi and 1/lo
        let inv_hi = self.hi.recip();
        let inv_lo = self.lo.recip();
        // Both must succeed since 0 is not in the interval.
        proof {
            // hi != 0 and lo != 0 since 0 not in [lo, hi]
            let zero = Rational::from_int_spec(0);
            if zero.lt_spec(self@.lo) {
                Rational::lemma_lt_implies_le(zero, self@.lo);
                Rational::lemma_le_transitive(zero, self@.lo, self@.hi);
                // 0 <= hi, and 0 < lo, so both nonzero.
                // lo != 0 trivially (0 < lo).
                // hi != 0: if hi == 0, then lo <= hi = 0, contradicting 0 < lo.
                // We need !lo@.eqv_spec(0) and !hi@.eqv_spec(0).
                Rational::lemma_eqv_zero_iff_num_zero(self@.lo);
                Rational::lemma_eqv_zero_iff_num_zero(self@.hi);
                Rational::lemma_denom_positive(self@.lo);
                Rational::lemma_denom_positive(self@.hi);
                Rational::lemma_denom_positive(zero);
                // 0 < lo.num (from 0 < lo)
                assert(self@.lo.num > 0) by (nonlinear_arith)
                    requires zero.num * self@.lo.denom() < self@.lo.num * zero.denom(),
                        zero.num == 0, zero.denom() > 0;
                // lo <= hi and lo.num > 0 implies hi.num > 0
                assert(self@.hi.num > 0) by (nonlinear_arith)
                    requires self@.lo.num * self@.hi.denom() <= self@.hi.num * self@.lo.denom(),
                        self@.lo.num > 0, self@.lo.denom() > 0, self@.hi.denom() > 0;
            } else {
                // hi < 0, so both negative, both nonzero
                Rational::lemma_eqv_zero_iff_num_zero(self@.lo);
                Rational::lemma_eqv_zero_iff_num_zero(self@.hi);
                Rational::lemma_denom_positive(self@.lo);
                Rational::lemma_denom_positive(self@.hi);
                Rational::lemma_denom_positive(zero);
                assert(self@.hi.num < 0) by (nonlinear_arith)
                    requires self@.hi.num * zero.denom() < zero.num * self@.hi.denom(),
                        zero.num == 0, zero.denom() > 0;
                assert(self@.lo.num < 0) by (nonlinear_arith)
                    requires self@.lo.num * self@.hi.denom() <= self@.hi.num * self@.lo.denom(),
                        self@.hi.num < 0, self@.lo.denom() > 0, self@.hi.denom() > 0;
            }
        }
        let lo_r = inv_hi.unwrap();
        let hi_r = inv_lo.unwrap();
        let ghost iv = self@.recip_spec();
        let out = RuntimeInterval {
            lo: lo_r,
            hi: hi_r,
            model: Ghost(iv),
        };
        proof {
            Interval::lemma_recip_wf(self@);
        }
        Option::Some(out)
    }

    /// Division: [a,b] / [c,d] = [a,b] * (1/[c,d]).
    /// Requires 0 not in the divisor interval.
    pub fn div(&self, rhs: &Self) -> (out: Option<Self>)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            Rational::from_int_spec(0).lt_spec(rhs@.lo)
                || rhs@.hi.lt_spec(Rational::from_int_spec(0)),
        ensures
            match out {
                Option::Some(r) => {
                    &&& r@ == self@.div_spec(rhs@)
                    &&& r.wf_spec()
                },
                Option::None => false,
            },
    {
        let recip = rhs.recip();
        let recip_iv = recip.unwrap();
        let result = self.mul(&recip_iv);
        Option::Some(result)
    }
    /// Intersection of two intervals.
    /// Returns None if they don't overlap, Some(result) otherwise.
    pub fn intersect(&self, other: &Self) -> (out: Option<Self>)
        requires
            self.wf_spec(),
            other.wf_spec(),
        ensures
            match out {
                Option::Some(r) => {
                    &&& self@.intersect_spec(other@).is_some()
                    &&& r@ == self@.intersect_spec(other@).unwrap()
                    &&& r.wf_spec()
                },
                Option::None => self@.intersect_spec(other@).is_none(),
            },
    {
        let lo = self.lo.max(&other.lo);
        let hi = self.hi.min(&other.hi);
        if lo.le(&hi) {
            let ghost iv = Interval { lo: lo@, hi: hi@ };
            let out = RuntimeInterval {
                lo: lo,
                hi: hi,
                model: Ghost(iv),
            };
            Option::Some(out)
        } else {
            Option::None
        }
    }

    // ── Phase 4: Sign determination & comparison ─────────────────

    /// Is the interval certainly positive? (lo > 0)
    pub fn certainly_positive(&self) -> (out: bool)
        requires self.wf_spec(),
        ensures out == self@.certainly_positive_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        zero.lt(&self.lo)
    }

    /// Is the interval certainly negative? (hi < 0)
    pub fn certainly_negative(&self) -> (out: bool)
        requires self.wf_spec(),
        ensures out == self@.certainly_negative_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        self.hi.lt(&zero)
    }

    /// Is the interval certainly zero? (point at 0)
    pub fn certainly_zero(&self) -> (out: bool)
        requires self.wf_spec(),
        ensures out == self@.certainly_zero_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        self.lo.eq(&self.hi) && self.lo.eq(&zero)
    }

    /// Is the interval certainly nonneg? (lo >= 0)
    pub fn certainly_nonneg(&self) -> (out: bool)
        requires self.wf_spec(),
        ensures out == self@.certainly_nonneg_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        zero.le(&self.lo)
    }

    /// Is the interval certainly nonpos? (hi <= 0)
    pub fn certainly_nonpos(&self) -> (out: bool)
        requires self.wf_spec(),
        ensures out == self@.certainly_nonpos_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        self.hi.le(&zero)
    }

    /// Does the interval possibly contain zero? (lo <= 0 <= hi)
    pub fn possibly_zero(&self) -> (out: bool)
        requires self.wf_spec(),
        ensures out == self@.possibly_zero_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        self.lo.le(&zero) && zero.le(&self.hi)
    }

    /// Sign determination: 1 if positive, -1 if negative, 0 if zero, None if indeterminate.
    pub fn sign_definite(&self) -> (out: Option<i8>)
        requires self.wf_spec(),
        ensures out == self@.sign_definite_spec(),
    {
        if self.certainly_positive() {
            Option::Some(1i8)
        } else if self.certainly_negative() {
            Option::Some(-1i8)
        } else if self.certainly_zero() {
            Option::Some(0i8)
        } else {
            Option::None
        }
    }

    /// Is self certainly less than rhs? (self.hi < rhs.lo)
    pub fn certainly_lt(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out == self@.certainly_lt_spec(rhs@),
    {
        self.hi.lt(&rhs.lo)
    }

    /// Is self certainly <= rhs? (self.hi <= rhs.lo)
    pub fn certainly_le(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out == self@.certainly_le_spec(rhs@),
    {
        self.hi.le(&rhs.lo)
    }

    /// Are both intervals the same point?
    pub fn certainly_equal(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out == self@.certainly_equal_spec(rhs@),
    {
        self.lo.eq(&self.hi) && rhs.lo.eq(&rhs.hi) && self.lo.eq(&rhs.lo)
    }

    /// Is it possible that some x in self < some y in rhs? (self.lo < rhs.hi)
    pub fn possibly_lt(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out == self@.possibly_lt_spec(rhs@),
    {
        self.lo.lt(&rhs.hi)
    }

    /// Are the intervals disjoint?
    pub fn disjoint(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out == self@.disjoint_spec(rhs@),
    {
        self.hi.lt(&rhs.lo) || rhs.hi.lt(&self.lo)
    }

    /// Tighten to nonneg: clamp lo to max(0, lo).
    pub fn tighten_nonneg(&self) -> (out: Self)
        requires
            self.wf_spec(),
            Rational::from_int_spec(0).le_spec(self@.hi),
        ensures
            out@ == self@.tighten_nonneg_spec(),
            out.wf_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        let lo = zero.max(&self.lo);
        let hi_copy = RuntimeRational {
            numerator: self.hi.numerator.copy_small_total(),
            denominator: self.hi.denominator.copy_small_total(),
            model: Ghost(self.hi@),
        };
        let ghost iv = self@.tighten_nonneg_spec();
        let out = RuntimeInterval {
            lo: lo,
            hi: hi_copy,
            model: Ghost(iv),
        };
        proof {
            // wf: max(0, lo) <= hi.
            // Case: if 0 <= lo, max = lo, and lo <= hi from wf. ✓
            // Case: if lo < 0, max = 0, and 0 <= hi from precondition. ✓
            Rational::lemma_trichotomy(Rational::from_int_spec(0), self@.lo);
        }
        out
    }

    /// Tighten to nonpos: clamp hi to min(0, hi).
    pub fn tighten_nonpos(&self) -> (out: Self)
        requires
            self.wf_spec(),
            self@.lo.le_spec(Rational::from_int_spec(0)),
        ensures
            out@ == self@.tighten_nonpos_spec(),
            out.wf_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        let hi = zero.min(&self.hi);
        let lo_copy = RuntimeRational {
            numerator: self.lo.numerator.copy_small_total(),
            denominator: self.lo.denominator.copy_small_total(),
            model: Ghost(self.lo@),
        };
        let ghost iv = self@.tighten_nonpos_spec();
        let out = RuntimeInterval {
            lo: lo_copy,
            hi: hi,
            model: Ghost(iv),
        };
        proof {
            Rational::lemma_trichotomy(Rational::from_int_spec(0), self@.hi);
        }
        out
    }

    // ── Phase 5: Squaring, power, FMA ────────────────────────────

    /// Squaring: tighter than mul(self, self).
    pub fn square(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.square_spec(),
            out.wf_spec(),
    {
        let zero = RuntimeRational::from_int(0i64);
        let lo_nonneg = zero.le(&self.lo);
        if lo_nonneg {
            // entirely nonneg: [lo², hi²]
            let lo2 = self.lo.mul(&self.lo);
            let hi2 = self.hi.mul(&self.hi);
            let ghost iv = self@.square_spec();
            let out = RuntimeInterval {
                lo: lo2,
                hi: hi2,
                model: Ghost(iv),
            };
            proof { Interval::lemma_square_wf(self@); }
            out
        } else {
            let hi_nonpos = self.hi.le(&zero);
            if hi_nonpos {
                // entirely nonpos: [hi², lo²]
                let lo2 = self.lo.mul(&self.lo);
                let hi2 = self.hi.mul(&self.hi);
                let ghost iv = self@.square_spec();
                let out = RuntimeInterval {
                    lo: hi2,
                    hi: lo2,
                    model: Ghost(iv),
                };
                proof { Interval::lemma_square_wf(self@); }
                out
            } else {
                // spans zero: [0, max(lo², hi²)]
                let lo2 = self.lo.mul(&self.lo);
                let hi2 = self.hi.mul(&self.hi);
                let hi_out = lo2.max(&hi2);
                let lo_out = RuntimeRational::from_int(0i64);
                let ghost iv = self@.square_spec();
                let out = RuntimeInterval {
                    lo: lo_out,
                    hi: hi_out,
                    model: Ghost(iv),
                };
                proof { Interval::lemma_square_wf(self@); }
                out
            }
        }
    }

    /// Integer power (naive recursive).
    pub fn pow(&self, n: u64) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.pow_spec(n as nat),
            out.wf_spec(),
        decreases n,
    {
        if n == 0 {
            let one = RuntimeRational::from_int(1i64);
            Self::from_point(&one)
        } else {
            let prev = self.pow(n - 1);
            let result = self.mul(&prev);
            proof {
                Interval::lemma_pow_wf(self@, (n - 1) as nat);
            }
            result
        }
    }

    /// Fused multiply-add: self * mul_rhs + add_rhs.
    pub fn fma(&self, mul_rhs: &Self, add_rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            mul_rhs.wf_spec(),
            add_rhs.wf_spec(),
        ensures
            out@ == self@.fma_spec(mul_rhs@, add_rhs@),
            out.wf_spec(),
    {
        let product = self.mul(mul_rhs);
        product.add(add_rhs)
    }
    // ── Phase 6: Subdivision & splitting ─────────────────────────

    /// Bisect at midpoint: returns ([lo, mid], [mid, hi]).
    pub fn bisect(&self) -> (out: (Self, Self))
        requires
            self.wf_spec(),
        ensures
            out.0@ == self@.bisect_spec().0,
            out.1@ == self@.bisect_spec().1,
            out.0.wf_spec(),
            out.1.wf_spec(),
    {
        let mid = self.lo.midpoint(&self.hi);
        proof {
            Interval::lemma_bisect_wf(self@);
        }
        // Copy mid for the right half
        let mid_copy = RuntimeRational {
            numerator: mid.numerator.copy_small_total(),
            denominator: mid.denominator.copy_small_total(),
            model: Ghost(mid@),
        };
        // Copy lo for the left half
        let lo_copy = RuntimeRational {
            numerator: self.lo.numerator.copy_small_total(),
            denominator: self.lo.denominator.copy_small_total(),
            model: Ghost(self@.lo),
        };
        // Copy hi for the right half
        let hi_copy = RuntimeRational {
            numerator: self.hi.numerator.copy_small_total(),
            denominator: self.hi.denominator.copy_small_total(),
            model: Ghost(self@.hi),
        };
        let left = RuntimeInterval {
            lo: lo_copy,
            hi: mid,
            model: Ghost(self@.bisect_spec().0),
        };
        let right = RuntimeInterval {
            lo: mid_copy,
            hi: hi_copy,
            model: Ghost(self@.bisect_spec().1),
        };
        (left, right)
    }

    /// Split at an arbitrary rational point p where lo ≤ p ≤ hi.
    pub fn split_at(&self, p: &RuntimeRational) -> (out: (Self, Self))
        requires
            self.wf_spec(),
            p.wf_spec(),
            self@.contains_spec(p@),
        ensures
            out.0@ == self@.split_at_spec(p@).0,
            out.1@ == self@.split_at_spec(p@).1,
            out.0.wf_spec(),
            out.1.wf_spec(),
    {
        proof {
            Interval::lemma_split_at_wf(self@, p@);
        }
        // Copy p for both halves
        let p_copy1 = RuntimeRational {
            numerator: p.numerator.copy_small_total(),
            denominator: p.denominator.copy_small_total(),
            model: Ghost(p@),
        };
        let p_copy2 = RuntimeRational {
            numerator: p.numerator.copy_small_total(),
            denominator: p.denominator.copy_small_total(),
            model: Ghost(p@),
        };
        // Copy endpoints
        let lo_copy = RuntimeRational {
            numerator: self.lo.numerator.copy_small_total(),
            denominator: self.lo.denominator.copy_small_total(),
            model: Ghost(self@.lo),
        };
        let hi_copy = RuntimeRational {
            numerator: self.hi.numerator.copy_small_total(),
            denominator: self.hi.denominator.copy_small_total(),
            model: Ghost(self@.hi),
        };
        let left = RuntimeInterval {
            lo: lo_copy,
            hi: p_copy1,
            model: Ghost(self@.split_at_spec(p@).0),
        };
        let right = RuntimeInterval {
            lo: p_copy2,
            hi: hi_copy,
            model: Ghost(self@.split_at_spec(p@).1),
        };
        (left, right)
    }
    // ── Phase 7: Scalar root-finding support ────────────────────

    /// Check if two function values indicate a sign change.
    pub fn has_sign_change(f_lo: &RuntimeRational, f_hi: &RuntimeRational) -> (out: bool)
        requires
            f_lo.wf_spec(),
            f_hi.wf_spec(),
        ensures
            out == Interval::sign_change_spec(f_lo@, f_hi@),
    {
        let s_lo = f_lo.signum();
        let s_hi = f_hi.signum();
        (s_lo == 1i8 && s_hi == -1i8) || (s_lo == -1i8 && s_hi == 1i8)
    }

    /// Scalar interval Newton step: N(X) = x_mid - f(x_mid)/f'(X) ∩ X.
    /// Returns None if f'(X) contains zero or intersection is empty.
    pub fn scalar_newton_step(
        fx_mid: &RuntimeRational,
        fprime_interval: &Self,
        x_mid: &RuntimeRational,
        x_interval: &Self,
    ) -> (out: Option<Self>)
        requires
            fx_mid.wf_spec(),
            fprime_interval.wf_spec(),
            x_mid.wf_spec(),
            x_interval.wf_spec(),
        ensures
            match out {
                Some(iv) => {
                    Interval::scalar_newton_step_spec(fx_mid@, fprime_interval@, x_mid@, x_interval@)
                        == Some(iv@)
                    && iv.wf_spec()
                },
                None => {
                    Interval::scalar_newton_step_spec(fx_mid@, fprime_interval@, x_mid@, x_interval@)
                        .is_none()
                },
            },
    {
        if fprime_interval.possibly_zero() {
            return None;
        }
        let fx_point = Self::from_point(fx_mid);
        let x_point = Self::from_point(x_mid);
        // div always succeeds since !possibly_zero
        let quotient = fx_point.div(fprime_interval).unwrap();
        let candidate = x_point.sub(&quotient);
        candidate.intersect(x_interval)
    }

    /// Interval Horner evaluation for a polynomial with given coefficients.
    /// coeffs_view maps indices to the ghost Rational values.
    /// Recursively evaluates c₀ + X*(c₁ + X*(c₂ + ...)).
    pub fn horner_eval(coeffs: &Vec<RuntimeRational>, x: &Self) -> (out: Self)
        requires
            x.wf_spec(),
            forall|i: int| 0 <= i < coeffs@.len() ==> (#[trigger] coeffs@[i]).wf_spec(),
        ensures
            out@ == Interval::horner_eval_spec(
                Seq::new(coeffs@.len() as nat, |i: int| coeffs@[i]@),
                x@),
            out.wf_spec(),
        decreases coeffs.len(),
    {
        let ghost coeffs_seq = Seq::new(coeffs@.len() as nat, |i: int| coeffs@[i]@);
        if coeffs.len() == 0 {
            let zero = RuntimeRational::from_int(0i64);
            proof {
                Interval::lemma_from_point_wf(Rational::from_int_spec(0));
            }
            Self::from_point(&zero)
        } else {
            // c0 as point interval
            let c0 = &coeffs[0];
            let c0_iv = Self::from_point(c0);

            // Build the rest of coefficients as a new Vec
            let mut rest_vec: Vec<RuntimeRational> = Vec::new();
            let mut i: usize = 1;
            while i < coeffs.len()
                invariant
                    1 <= i <= coeffs.len(),
                    rest_vec@.len() == (i - 1) as int,
                    forall|j: int| 0 <= j < rest_vec@.len() ==>
                        (#[trigger] rest_vec@[j]).wf_spec()
                        && rest_vec@[j]@ == coeffs@[j + 1]@,
                    forall|j: int| 0 <= j < coeffs@.len() ==> (#[trigger] coeffs@[j]).wf_spec(),
                decreases coeffs.len() - i,
            {
                let ci = RuntimeRational {
                    numerator: coeffs[i].numerator.copy_small_total(),
                    denominator: coeffs[i].denominator.copy_small_total(),
                    model: Ghost(coeffs@[i as int]@),
                };
                rest_vec.push(ci);
                i = i + 1;
            }

            // Recursive call on rest
            let inner = Self::horner_eval(&rest_vec, x);

            // X * inner
            let product = x.mul(&inner);

            // c0 + X * inner
            let result = c0_iv.add(&product);

            proof {
                // Show rest_vec's ghost seq matches subrange
                let ghost rest_seq = Seq::new(rest_vec@.len() as nat, |i: int| rest_vec@[i]@);
                let ghost expected_rest = coeffs_seq.subrange(1, coeffs_seq.len() as int);
                assert(rest_seq.len() == expected_rest.len());
                assert forall|j: int| 0 <= j < rest_seq.len()
                    implies #[trigger] rest_seq[j] == expected_rest[j]
                by {
                    assert(rest_vec@[j]@ == coeffs@[j + 1]@);
                    assert(rest_seq[j] == rest_vec@[j]@);
                    assert(expected_rest[j] == coeffs_seq[j + 1]);
                    assert(coeffs_seq[j + 1] == coeffs@[j + 1]@);
                }
                assert(rest_seq =~= expected_rest);

                Interval::lemma_horner_eval_wf(rest_seq, x@);
                Interval::lemma_mul_wf(x@, Interval::horner_eval_spec(rest_seq, x@));
                Interval::lemma_from_point_wf(coeffs@[0]@);
                Interval::lemma_add_wf(
                    Interval::from_point_spec(coeffs@[0]@),
                    x@.mul_spec(Interval::horner_eval_spec(rest_seq, x@)));
            }

            result
        }
    }

    // ── Phase 8: Distance & Metric ──

    pub fn hausdorff(&self, other: &Self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
            other.wf_spec(),
        ensures
            out@ == self@.hausdorff_spec(other@),
            out.wf_spec(),
    {
        let d_lo = self.lo.sub(&other.lo).abs();
        let d_hi = self.hi.sub(&other.hi).abs();
        d_lo.max(&d_hi)
    }
}

impl View for RuntimeInterval {
    type V = Interval;

    open spec fn view(&self) -> Interval {
        self.model@
    }
}

} // verus!
