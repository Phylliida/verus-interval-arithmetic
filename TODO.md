# verus-interval-arithmetic — Implementation TODO

Formally verified precise scalar interval arithmetic (using BigInt rationals)
in Rust + Verus.

This crate is **scalar-only**: `[lo, hi]` intervals over `Rational` /
`RuntimeRational`. Interval vectors, interval matrices, Krawczyk /
Hansen-Sengupta operators, and the solver loop belong in a downstream crate
(e.g. `verus-interval-vector` or `verus-certified-solver`).

## Crate layering

```
verus-bigint
  └→ verus-rational
       └→ verus-interval-arithmetic    ← this crate (scalar intervals)
            └→ verus-interval-vector   (boxes, matrices, Krawczyk, solver)
                 └→ VerusCAD
```

## Primitives we build on

| Crate | Type | Role |
|---|---|---|
| `verus-bigint` | `RuntimeBigNatWitness`, `RuntimeBigIntWitness` | Arbitrary-precision integers with ghost `model` |
| `verus-rational` | `Rational` (ghost), `RuntimeRational` (exec) | Exact rational arithmetic with full algebraic proof library |

**Key reuse points from verus-rational** (already proven, do NOT reimplement):
- All ordering lemmas: `lemma_le_transitive`, `lemma_lt_transitive`, `lemma_trichotomy`, `lemma_le_antisymmetric`
- Bilateral addition monotonicity: `lemma_le_add_both`, `lemma_lt_add_both`, `lemma_le_lt_add`
- Multiplication monotonicity: `lemma_le_mul_nonneg`, `lemma_le_mul_nonneg_both`, `lemma_lt_mul_positive`, `lemma_lt_mul_negative`
- Negation reverses order: `lemma_neg_reverses_le`, `lemma_neg_reverses_lt`
- Subtraction monotonicity: `lemma_sub_le_monotone_left`, `lemma_sub_le_monotone_right`
- Division monotonicity: `lemma_div_le_monotone`, `lemma_div_neg_denominator`
- Sign of products: `lemma_pos_mul_pos`, `lemma_neg_mul_neg`, `lemma_pos_mul_neg`, `lemma_neg_mul_pos`
- Min/max: `lemma_min_le_left/right`, `lemma_max_ge_left/right`, `lemma_min_max_sum`
- Midpoint: `midpoint_spec`, `lemma_midpoint_between_left/right`, `lemma_midpoint_eqv_self`
- Absolute value: `lemma_abs_nonneg`, `lemma_abs_mul`, `lemma_triangle_inequality`
- Convex combination: `lemma_convex_between`
- Algebraic identities: distributivity, associativity, commutativity, cancellation
- Reciprocal/division: `lemma_div_cancel`, `lemma_div_mul_cancel`, `lemma_reciprocal_of_product`

---

## Phase 0 — Project scaffolding

- [ ] Create `Cargo.toml` depending on `verus-rational`, `verus-bigint`, `vstd`
- [ ] Create `src/lib.rs` with module structure
- [ ] Verify the empty crate compiles with `cargo-verus`

---

## Phase 1 — Interval type & basic spec model

### 1.1 Ghost interval type

```
pub ghost struct Interval { pub lo: Rational, pub hi: Rational }
```

Spec functions:
- [ ] `wf_spec(self) -> bool` — `lo.le_spec(hi)` (non-empty interval)
- [ ] `contains_spec(self, x: Rational) -> bool` — `lo ≤ x ≤ hi`
- [ ] `contains_interval_spec(self, other: Interval) -> bool` — `lo ≤ other.lo ∧ other.hi ≤ hi`
- [ ] `width_spec(self) -> Rational` — `hi - lo`
- [ ] `midpoint_spec(self) -> Rational` — reuse `Rational::midpoint_spec(lo, hi)`
- [ ] `is_point_spec(self) -> bool` — `lo.eqv_spec(hi)`
- [ ] `from_point_spec(x: Rational) -> Interval` — `[x, x]`
- [ ] `overlap_spec(self, other: Interval) -> bool`
- [ ] `hull_spec(self, other: Interval) -> Interval` — smallest interval containing both

### 1.2 Runtime interval type

```
pub struct RuntimeInterval {
    pub lo: RuntimeRational,
    pub hi: RuntimeRational,
    pub model: Ghost<Interval>,
}
```

- [ ] `wf_spec(&self) -> bool` — both endpoints wf, model consistency, `lo ≤ hi`
- [ ] `View` impl: `self@ -> Interval`
- [ ] Constructors: `from_point(x: RuntimeRational)`, `from_endpoints(lo, hi)`

---

## Phase 2 — Interval arithmetic operations

Every operation must be verified to produce an interval that *contains* the
true result for all operands in the input intervals.

### 2.1 Addition: `[a,b] + [c,d] = [a+c, b+d]`

- [ ] `add_spec(self, rhs: Interval) -> Interval`
- [ ] `lemma_add_containment(a, b, x, y)` — `x ∈ a ∧ y ∈ b → x+y ∈ a+b`
  - Proof reuses: `lemma_le_add_both`
- [ ] Exec `fn add(&self, rhs: &Self) -> Self`

### 2.2 Negation: `-[a,b] = [-b, -a]`

- [ ] `neg_spec(self) -> Interval`
- [ ] `lemma_neg_containment(a, x)` — `x ∈ a → -x ∈ -a`
  - Proof reuses: `lemma_neg_reverses_le`
- [ ] Exec `fn neg(&self) -> Self`

### 2.3 Subtraction: `[a,b] - [c,d] = [a-d, b-c]`

- [ ] `sub_spec(self, rhs: Interval) -> Interval` — define as `add_spec(rhs.neg_spec())`
- [ ] `lemma_sub_containment(a, b, x, y)` — `x ∈ a ∧ y ∈ b → x-y ∈ a-b`
  - Proof reuses: `lemma_sub_le_monotone_left`, `lemma_sub_le_monotone_right`
- [ ] Exec `fn sub(&self, rhs: &Self) -> Self`

### 2.4 Multiplication (general case)

For `[a,b] * [c,d]`, the result is `[min(ac,ad,bc,bd), max(ac,ad,bc,bd)]`.

- [ ] `mul_spec(self, rhs: Interval) -> Interval` — four-product min/max
- [ ] `lemma_mul_containment(a, b, x, y)` — `x ∈ a ∧ y ∈ b → x*y ∈ a*b`
  - Proof reuses: `lemma_le_mul_nonneg`, `lemma_le_mul_nonneg_both`, sign-of-product lemmas, `lemma_neg_reverses_le`
  - Needs case-split on sign combinations (both non-negative, both non-positive, mixed)
- [ ] Exec `fn mul(&self, rhs: &Self) -> Self`

### 2.5 Reciprocal: `1/[a,b] = [1/b, 1/a]` (when `0 ∉ [a,b]`)

- [ ] `recip_spec(self) -> Option<Interval>` — `None` if interval contains zero
- [ ] `lemma_recip_containment(a, x)` — `x ∈ a ∧ 0 ∉ a → 1/x ∈ 1/a`
  - Proof reuses: `lemma_div_le_monotone`, `lemma_div_neg_denominator`
- [ ] Exec `fn recip(&self) -> Option<Self>`

### 2.6 Division: `[a,b] / [c,d] = [a,b] * (1/[c,d])`

- [ ] `div_spec(self, rhs: Interval) -> Option<Interval>`
- [ ] `lemma_div_containment`
- [ ] Exec `fn div(&self, rhs: &Self) -> Option<Self>`

### 2.7 Scalar-interval operations

- [ ] `scale_spec(scalar: Rational, iv: Interval) -> Interval` — multiply interval by a point value
- [ ] `lemma_scale_containment`
- [ ] Exec `fn scale(scalar: &RuntimeRational, iv: &RuntimeInterval) -> RuntimeInterval`

### 2.8 Absolute value: `|[a,b]|`

- [ ] `abs_spec(self) -> Interval` — depends on sign of endpoints
  - If `0 ≤ a`: `[a, b]`
  - If `b ≤ 0`: `[-b, -a]`
  - If `a < 0 < b`: `[0, max(-a, b)]`
- [ ] `lemma_abs_containment(a, x)` — `x ∈ a → |x| ∈ |a|`
  - Proof reuses: `lemma_abs_nonneg`, `lemma_neg_reverses_le`
- [ ] Exec `fn abs(&self) -> Self`

---

## Phase 3 — Interval properties & proof infrastructure

Lemmas about intervals themselves, needed by downstream crates.

### 3.1 Containment algebra

- [ ] `lemma_contains_reflexive(a, x)` — `x ∈ [x,x]`
- [ ] `lemma_contains_transitive(a, b, x)` — `a ⊆ b ∧ x ∈ a → x ∈ b`
- [ ] `lemma_contains_interval_transitive(a, b, c)` — `a ⊆ b ∧ b ⊆ c → a ⊆ c`
- [ ] `lemma_point_interval_contains(x)` — `x ∈ [x,x]`

### 3.2 Width properties

- [ ] `lemma_width_nonneg(a)` — `wf(a) → width(a) ≥ 0`
- [ ] `lemma_add_width(a, b)` — `width(a+b) ≡ width(a) + width(b)`
- [ ] `lemma_neg_width(a)` — `width(-a) ≡ width(a)`
- [ ] `lemma_sub_width(a, b)` — `width(a-b) ≡ width(a) + width(b)`
- [ ] `lemma_subset_implies_le_width(a, b)` — `a ⊆ b → width(a) ≤ width(b)`
- [ ] `lemma_point_interval_zero_width(x)` — `width([x,x]) ≡ 0`

### 3.3 Midpoint properties

- [ ] `lemma_midpoint_in_interval(a)` — `wf(a) → midpoint(a) ∈ a`
  - Proof reuses: `lemma_midpoint_between_left/right`
- [ ] `lemma_midpoint_splits(a)` — midpoint produces two sub-intervals each with half the width

### 3.4 Intersection

- [ ] `intersect_spec(self, other: Interval) -> Option<Interval>`
- [ ] `lemma_intersect_containment` — result contains only points in both inputs
- [ ] `lemma_intersect_subset_both` — result ⊆ self and result ⊆ other
- [ ] Exec `fn intersect(&self, other: &Self) -> Option<Self>`

### 3.5 Hull

- [ ] `lemma_hull_contains_both(a, b)` — `a ⊆ hull(a,b) ∧ b ⊆ hull(a,b)`
- [ ] `lemma_hull_minimal(a, b, c)` — `a ⊆ c ∧ b ⊆ c → hull(a,b) ⊆ c`

### 3.6 Monotonicity of operations w.r.t. containment

These are the "if you feed in a sub-interval, you get a sub-interval" lemmas.
Critical for downstream refinement / subdivision arguments.

- [ ] `lemma_add_monotone(a, a', b, b')` — `a ⊆ a' ∧ b ⊆ b' → a+b ⊆ a'+b'`
- [ ] `lemma_mul_monotone(a, a', b, b')` — `a ⊆ a' ∧ b ⊆ b' → a*b ⊆ a'*b'`
- [ ] `lemma_neg_monotone(a, a')` — `a ⊆ a' → -a ⊆ -a'`

---

## Phase 4 — Sign determination & comparison predicates

The most important thing intervals give a CAD kernel: definite answers when
possible, honest "I don't know" when not. These are the workhorses for
orientation predicates, in-circle tests, and constraint feasibility checks.

### 4.1 Trinary sign determination

- [ ] `certainly_positive_spec(self) -> bool` — `lo > 0` (strictly)
- [ ] `certainly_negative_spec(self) -> bool` — `hi < 0`
- [ ] `certainly_zero_spec(self) -> bool` — `is_point_spec() ∧ lo ≡ 0`
- [ ] `certainly_nonneg_spec(self) -> bool` — `lo ≥ 0`
- [ ] `certainly_nonpos_spec(self) -> bool` — `hi ≤ 0`
- [ ] `possibly_zero_spec(self) -> bool` — `lo ≤ 0 ≤ hi`
- [ ] `sign_definite_spec(self) -> Option<i8>` — `Some(1)`, `Some(-1)`, `Some(0)`, or `None`
- [ ] Exec functions for all of the above
- [ ] `lemma_certainly_positive_implies(a, x)` — `certainly_positive(a) ∧ x ∈ a → x > 0`
- [ ] `lemma_certainly_negative_implies(a, x)` — `certainly_negative(a) ∧ x ∈ a → x < 0`
- [ ] `lemma_not_possibly_zero_implies(a, x)` — `¬possibly_zero(a) ∧ x ∈ a → x ≠ 0`

### 4.2 Interval comparison predicates

- [ ] `certainly_less_than_spec(self, rhs: Interval) -> bool` — `self.hi < rhs.lo`
- [ ] `certainly_le_spec(self, rhs: Interval) -> bool` — `self.hi ≤ rhs.lo`
- [ ] `certainly_equal_spec(self, rhs: Interval) -> bool` — both are the same point
- [ ] `possibly_less_than_spec(self, rhs: Interval) -> bool` — `self.lo < rhs.hi`
- [ ] `disjoint_spec(self, rhs: Interval) -> bool` — `self.hi < rhs.lo ∨ rhs.hi < self.lo`
- [ ] Exec functions for all of the above
- [ ] `lemma_certainly_lt_implies(a, b, x, y)` — `certainly_lt(a,b) ∧ x ∈ a ∧ y ∈ b → x < y`
- [ ] `lemma_disjoint_no_common_point(a, b)` — `disjoint(a,b) → ¬∃x. x ∈ a ∧ x ∈ b`

### 4.3 Bound tightening via known sign

When external reasoning establishes a sign, we can sharpen the interval:

- [ ] `tighten_nonneg_spec(self) -> Interval` — `[max(0, lo), hi]`, requires `0 ≤ hi`
- [ ] `tighten_nonpos_spec(self) -> Interval` — `[lo, min(0, hi)]`, requires `lo ≤ 0`
- [ ] `tighten_positive_spec(self) -> Interval` — requires `hi > 0`, clamps lo
- [ ] `lemma_tighten_nonneg_containment(a, x)` — `x ∈ a ∧ x ≥ 0 → x ∈ tighten_nonneg(a)`
- [ ] Exec functions

---

## Phase 5 — Tighter special-case operations

### 5.1 Squaring: `[a,b]²`

Generic `mul([a,b], [a,b])` ignores the constraint that both operands are
the *same* value, giving unnecessarily wide results (the dependency problem).
A dedicated square exploits `x² ≥ 0`:

- [ ] `square_spec(self) -> Interval`
  - If `0 ≤ a`: `[a², b²]`
  - If `b ≤ 0`: `[b², a²]`
  - If `a < 0 < b`: `[0, max(a², b²)]`
- [ ] `lemma_square_containment(a, x)` — `x ∈ a → x² ∈ square(a)`
  - Proof reuses: `lemma_square_nonneg`, `lemma_square_le_nonneg`, `lemma_le_mul_nonneg_both`
- [ ] `lemma_square_tighter_than_mul(a)` — `square(a) ⊆ mul(a, a)` (never wider)
- [ ] Exec `fn square(&self) -> Self`

Squared-distance `(px-qx)² + (py-qy)²` is everywhere in CAD — avoiding
unnecessary width here propagates tightness throughout.

### 5.2 Integer power: `[a,b]^n`

- [ ] `pow_spec(self, n: nat) -> Interval`
  - Even `n`: similar to square case (result ≥ 0)
  - Odd `n`: monotone, so `[a^n, b^n]`
- [ ] `lemma_pow_containment(a, x, n)` — `x ∈ a → x^n ∈ pow(a, n)`
  - Proof reuses: `lemma_le_mul_nonneg_both` inductively
- [ ] `lemma_pow_even_nonneg(a, n)` — `n even → pow(a, n).lo ≥ 0`
- [ ] Exec `fn pow(&self, n: u64) -> Self`

### 5.3 Fused multiply-add: `[a,b]*[c,d] + [e,f]`

Avoids an intermediate interval and can give tighter results in some cases.
Useful for Horner evaluation.

- [ ] `fma_spec(self, mul_rhs: Interval, add_rhs: Interval) -> Interval`
- [ ] `lemma_fma_containment(a, b, c, x, y, z)` — `x∈a ∧ y∈b ∧ z∈c → x*y+z ∈ fma(a,b,c)`
- [ ] Exec `fn fma(&self, mul_rhs: &Self, add_rhs: &Self) -> Self`

---

## Phase 6 — Subdivision & splitting

### 6.1 Midpoint bisection

- [ ] `bisect_spec(self) -> (Interval, Interval)` — `([lo, mid], [mid, hi])`
- [ ] `lemma_bisect_covers(a, left, right)` — `x ∈ a → x ∈ left ∨ x ∈ right`
- [ ] `lemma_bisect_halves_width(a, left, right)` — `width(left) ≡ width(a)/2`
- [ ] Exec `fn bisect(&self) -> (Self, Self)`

### 6.2 Split at arbitrary rational point

- [ ] `split_at_spec(self, p: Rational) -> (Interval, Interval)` — requires `p ∈ (lo, hi)`
  - Result: `([lo, p], [p, hi])`
- [ ] `lemma_split_covers(a, p, left, right)` — same coverage guarantee
- [ ] Exec `fn split_at(&self, p: &RuntimeRational) -> (Self, Self)`

Useful for adaptive refinement where you have a hint about where the
interesting feature is (e.g., a Newton iterate).

### 6.3 N-way uniform subdivision

- [ ] `subdivide_spec(self, n: nat) -> Seq<Interval>` — `n` equal-width pieces
- [ ] `lemma_subdivide_covers(a, pieces)` — union of pieces ⊇ a
- [ ] `lemma_subdivide_width(a, n, pieces)` — each piece has `width(a)/n`

---

## Phase 7 — Scalar root-finding support

The 1D case is much simpler than multi-dimensional Krawczyk and is useful
on its own for univariate constraint solving (e.g., parameter-on-curve,
circle-line intersection parameter).

### 7.1 Sign-change existence (1D IVT)

In one dimension, Brouwer's fixed-point theorem is just the Intermediate
Value Theorem — no axiom needed.

- [ ] `sign_change_spec(f_lo: Rational, f_hi: Rational) -> bool` — `f_lo` and `f_hi` have opposite signs
- [ ] `lemma_sign_change_implies_root_exists` — if `f` is continuous and
  `f(lo) * f(hi) < 0`, there exists `x ∈ (lo, hi)` with `f(x) = 0`.
  (Stated as a contract/axiom for continuous `f`; verified for polynomials
  via interval evaluation.)
- [ ] Exec `fn has_sign_change(f_lo: &RuntimeRational, f_hi: &RuntimeRational) -> bool`

### 7.2 Scalar interval Newton step

For a univariate function `f` with derivative `f'`:

```
N(X) = x̃ - f(x̃)/f'(X)  ∩  X
```

- [ ] `scalar_newton_step_spec(fx_mid, fprime_interval, x_mid, X) -> Option<Interval>`
- [ ] `lemma_scalar_newton_containment` — any root of `f` in `X` is also in `N(X)`
  - Proof: mean value theorem argument (taken as axiom for continuous `f`)
- [ ] `lemma_scalar_newton_contracts` — if `N(X) ⊂ int(X)`, uniqueness + quadratic convergence
- [ ] Exec function

### 7.3 Univariate polynomial evaluation (Horner form)

Evaluate `p(X) = a_n X^n + ... + a_1 X + a_0` over an interval using
Horner's method: `((a_n X + a_{n-1}) X + ...) X + a_0`.

- [ ] `horner_eval_spec(coeffs: Seq<Rational>, X: Interval) -> Interval`
- [ ] `lemma_horner_containment(coeffs, X, x)` — `x ∈ X → p(x) ∈ horner_eval(coeffs, X)`
  - Proof: induction over coefficients, each step uses `lemma_mul_containment` + `lemma_add_containment`
- [ ] Exec `fn horner_eval(coeffs: &[RuntimeRational], x: &RuntimeInterval) -> RuntimeInterval`

### 7.4 Derivative evaluation

For polynomial `p` with known derivative `p'`, evaluate `p'(X)` to get the
interval enclosure of the derivative — feeds directly into scalar Newton.

- [ ] `poly_derivative_coeffs_spec(coeffs: Seq<Rational>) -> Seq<Rational>`
- [ ] `lemma_derivative_coeffs_correct` — the derivative coefficients compute the derivative
- [ ] Exec `fn poly_derivative_coeffs(coeffs: &[RuntimeRational]) -> Vec<RuntimeRational>`

---

## Phase 8 — Interval distance & metric

Useful for convergence criteria and tolerance checking.

### 8.1 Hausdorff distance between intervals

- [ ] `hausdorff_spec(self, other: Interval) -> Rational` — `max(|lo - other.lo|, |hi - other.hi|)`
- [ ] `lemma_hausdorff_zero_iff_equal(a, b)` — `hausdorff(a,b) ≡ 0 ↔ a ≡ b` (componentwise)
- [ ] `lemma_hausdorff_triangle(a, b, c)` — triangle inequality
- [ ] Exec `fn hausdorff(&self, other: &Self) -> RuntimeRational`

### 8.2 Distance between disjoint intervals

- [ ] `gap_spec(self, other: Interval) -> Rational` — `max(0, max(lo - other.hi, other.lo - hi))`
- [ ] `lemma_gap_positive_iff_disjoint(a, b)`
- [ ] `lemma_gap_bounds_element_distance(a, b, x, y)` — `x ∈ a ∧ y ∈ b → |x-y| ≥ gap(a,b)`

---

## Design notes

- **Normalization strategy**: interval operations accumulate denominator growth
  in `RuntimeRational`. The existing `normalize_constructive` proof in
  verus-rational is available but expensive. Consider normalizing only at
  user-facing boundaries or after a fixed number of operations.
- **Multiplication optimization**: the four-product min/max formulation is
  simple but does 4 multiplies. A sign-case-split implementation does at most
  2 multiplies per call. Start with four-product for proof simplicity, optimize
  later.
- **What stays downstream**: interval vectors/boxes, interval matrices,
  matrix-vector multiply, Krawczyk operator, Hansen-Sengupta, bisection,
  solver loop, CAD constraint assembly, root certificates.
