# Correctness Proof Burndown Plan

Properties that **only verify if the implementation is correct**. If someone
introduced a bug (swapped endpoints, wrong sign, wrong case split, wrong
min/max), these proofs would fail.

All proofs go in `src/interval.rs` inside the `impl Interval` block, in the
correctness characterization section (after line ~3866).

**Target**: ~15 new proof lemmas, 0 errors, no significant verification slowdown.

---

## Group 1: Scale identities (test `scale_spec`)

### 1.1 `lemma_scale_zero` — scaling by 0 annihilates
```
ensures: scale(0, a) == from_point(0)
```
Uses: `Rational::lemma_mul_left_zero_num`. Both `0*lo` and `0*hi` have num=0,
so min/max collapse to a zero-numerator rational == `from_int_spec(0)`.
**Difficulty: Easy**

### 1.2 `lemma_scale_one_identity` — scaling by 1 is identity
```
requires: wf(a)
ensures: scale(1, a) == a
```
Uses: `Rational::lemma_mul_one_identity` (structural ==). Then min/max of
`(a.lo, a.hi)` collapse via wf (lo <= hi).
**Difficulty: Easy**

### 1.3 `lemma_scale_neg_one_eq_neg` — scaling by -1 is negation
```
ensures: scale(-1, a) == neg(a)
```
Uses: `Rational::lemma_mul_neg_right` + `lemma_mul_one_identity` to get
`(-1)*x == -x`. Then min/max of `(-lo, -hi)` — neg reverses order, so
min(-lo,-hi) = -hi and max(-lo,-hi) = -lo, matching neg_spec.
**Difficulty: Easy-Medium**

---

## Group 2: Mul edge cases (test `mul_spec` min/max logic)

### 2.1 `lemma_mul_zero_annihilates` — mul by [0,0] gives zero endpoints
```
requires: wf(a)
ensures: mul(a, from_point(0)).lo.eqv_spec(0), mul(a, from_point(0)).hi.eqv_spec(0)
```
All four corner products have num=0, so min4/max4 selects one of them, which is
eqv to 0.
**Difficulty: Easy-Medium**

---

## Group 3: Cross-operation consistency

### 3.1 `lemma_scale_eq_point_mul` — scale agrees with point-interval mul
```
ensures: scale(k, a).lo.eqv_spec(from_point(k).mul_spec(a).lo),
         scale(k, a).hi.eqv_spec(from_point(k).mul_spec(a).hi)
```
`from_point(k) * a` has corners `{k*lo, k*hi, k*lo, k*hi}` — duplicate pairs.
min4/max4 of duplicate pairs collapses to min/max of the two distinct values,
matching scale_spec.
**Difficulty: Medium**

---

## Group 4: Abs properties (test `abs_spec` case split)

### 4.1 `lemma_abs_idempotent` — abs is idempotent
```
requires: wf(a)
ensures: abs(abs(a)) == abs(a)
```
After first abs, result is nonneg (lo >= 0 in all 3 branches). So the second
abs takes the "entirely nonneg" branch, which is the identity.
**Difficulty: Medium**

---

## Group 5: Interval algebra

### 5.1 `lemma_add_associative` — addition is associative (up to eqv)
```
ensures: (a+b)+c .lo.eqv_spec( a+(b+c) .lo ),
         (a+b)+c .hi.eqv_spec( a+(b+c) .hi )
```
Direct from `Rational::lemma_add_associative` on each endpoint pair.
**Difficulty: Easy**

---

## Group 6: Monotonicity (missing properties)

### 6.1 `lemma_sub_monotone` — subtraction is containment-monotonic
```
requires: a2.contains_interval(a), b2.contains_interval(b)
ensures: a2.sub_spec(b2).contains_interval(a.sub_spec(b))
```
Follows from `lemma_neg_monotone` + `lemma_add_monotone`, since
`sub_spec(a,b) == add_spec(a, neg_spec(b))` structurally.
**Difficulty: Easy**

### 6.2 `lemma_scale_monotone` — scale is containment-monotonic
```
requires: a2.contains_interval(a)
ensures: scale(k, a2).contains_interval(scale(k, a))
```
Need to show min(k*lo', k*hi') <= min(k*lo, k*hi) and
max(k*lo, k*hi) <= max(k*lo', k*hi'). Case-split on sign of k.
**Difficulty: Medium**

---

## Group 7: Comparison soundness

### 7.1 `lemma_certainly_lt_transitive`
```
requires: certainly_lt(a, b) && certainly_lt(b, c)
ensures: certainly_lt(a, c)
```
Chain: `a.hi < b.lo <= b.hi < c.lo`. Uses `Rational::lemma_lt_le_transitive`
or similar.
**Difficulty: Easy**

### 7.2 `lemma_certainly_lt_asymmetric`
```
requires: certainly_lt(a, b)
ensures: !certainly_lt(b, a)
```
`a.hi < b.lo` implies `b.hi >= b.lo > a.hi >= a.lo`, so `b.hi > a.lo`, so
`¬(b.hi < a.lo)`.
**Difficulty: Easy**

### 7.3 `lemma_sign_definite_soundness`
```
requires: wf(a)
ensures:
  sign_definite(a) == Some(1i8)  ==> certainly_positive(a),
  sign_definite(a) == Some(-1i8) ==> certainly_negative(a),
  sign_definite(a) == Some(0i8)  ==> certainly_zero(a),
```
Definitional unfolding of the if-else chain.
**Difficulty: Easy (likely trivial)**

---

## Group 8: Metric properties

### 8.1 `lemma_hausdorff_symmetric`
```
requires: wf(a), wf(b)
ensures: hausdorff(a, b).eqv_spec(hausdorff(b, a))
```
`hausdorff = max(|lo1-lo2|, |hi1-hi2|)`. Uses symmetry of abs (abs(-x) ≡ abs(x))
and commutativity of max.
**Difficulty: Easy-Medium**

### 8.2 `lemma_hausdorff_nonneg`
```
requires: wf(a), wf(b)
ensures: from_int(0).le_spec(hausdorff(a, b))
```
max of two abs values is >= 0.
**Difficulty: Easy-Medium**

---

## Group 9: Subdistributivity (fundamental IA property)

### 9.1 `lemma_subdistributive`
```
requires: wf(a), wf(b), wf(c)
ensures: a.mul_spec(b.add_spec(c)).contains_interval_spec is contained in
         a.mul_spec(b).add_spec(a.mul_spec(c))
```
For all x∈a, y∈b, z∈c: x*(y+z) = x*y + x*z ∈ a*b + a*c. So a*(b+c) ⊆ a*b + a*c.
Uses containment lemmas for mul and add.
**Difficulty: Medium-Hard**

---

## Execution order (recommended)

Easy proofs first to build momentum, hard proofs last:

1. 7.3 sign_definite_soundness (trivial)
2. 5.1 add_associative (easy)
3. 7.1 certainly_lt_transitive (easy)
4. 7.2 certainly_lt_asymmetric (easy)
5. 1.1 scale_zero (easy)
6. 1.2 scale_one_identity (easy)
7. 6.1 sub_monotone (easy)
8. 1.3 scale_neg_one_eq_neg (easy-medium)
9. 2.1 mul_zero_annihilates (easy-medium)
10. 8.1 hausdorff_symmetric (easy-medium)
11. 8.2 hausdorff_nonneg (easy-medium)
12. 4.1 abs_idempotent (medium)
13. 6.2 scale_monotone (medium)
14. 3.1 scale_eq_point_mul (medium)
15. 9.1 subdistributive (medium-hard)
