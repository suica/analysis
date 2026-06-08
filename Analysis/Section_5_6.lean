import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from {name}`Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

@[simp]
lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' n with n hn <;> simp; ring_nf

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' n with n hn <;> simp [Real.pow_succ]; ring_nf; linarith

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n hn <;> simp; ring_nf

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  . intro h
    simp at h
    exact h.left
  intro h
  rw [h]
  simp
  grind

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n hn <;> simp
  exact Left.mul_nonneg hn hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n hn <;> simp
  exact Left.mul_pos hn hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n hn <;> simp
  gcongr
  apply pow_nonneg
  grind

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction' n with n ih <;> simp
  . contradiction
  by_cases h: n = 0
  . simp [h]
    simpa
  gcongr

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n hn <;> simp

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from {name}`DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

lemma Real.zpow_sub_one {x:Real} (n:ℤ) (h:x ≠ 0) : x^(n-1) = x^n / x := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    norm_cast
    simp
    rw [mul_div_assoc, div_self]
    rw [mul_one]
    exact h
  | pred n ih =>
    simp at *
    rw [Int.sub_eq_add_neg, ← neg_add] at ih
    change x ^ (-((n + 1:ℕ):ℤ)) = (x ^ n)⁻¹ / x at ih
    rw [zpow_neg] at ih
    rw [show -(n:ℤ) - 1 - 1 = - ↑((n+1+1):ℕ) by omega]
    rw [zpow_neg]
    rw [pow_succ]
    rw [← div_div, div_eq_mul_inv]
    rw [show -(n:ℤ) - 1  = - ↑((n+1):ℕ) by omega]
    rw [zpow_neg, div_eq_mul_inv]
    ring_nf

lemma Real.zpow_add_one {x:Real} (n:ℤ) (h:x ≠ 0): x^(n+1) = x^n * x := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    norm_cast
  | pred n ih =>
    simp at *
    rw [show -(n:ℤ) - 1 = - ↑((n+1):ℕ) by omega]
    rw [zpow_neg, div_eq_mul_inv]
    simp
    ring_nf
    rw [mul_comm x]
    rw [inv_mul_cancel₀]
    simp
    exact h

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    simp_all
    norm_cast
    rw [pow_succ]
    rw [show n + ↑(m + 1) = n + ↑m + 1 by omega]
    rw [Real.zpow_add_one, ← ih]
    ring_nf
    exact hx
  | pred m ih =>
    simp_all
    rw [show n + (-↑m - 1) = n - ↑m - 1 by omega]
    rw [Real.zpow_sub_one, Real.zpow_sub_one]
    field_simp
    rw [Real.zpow_neg]
    field_simp at *
    norm_cast
    omega
    omega

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  by_cases hx: x = 0
  . rw [hx]
    . by_cases hm: m = 0
      simp [hm]
      by_cases hn: n = 0
      . rw [hn]
        simp
      rw [zero_zpow, zero_zpow, zero_zpow]
      positivity
      positivity
      omega
  by_cases hn: n = 0
  . by_cases hm: m = 0
    . rw [hn, hm]
      simp
    rw [hn]
    simp
  have : x^n ≠ 0 := by
    by_contra h
    rw [zpow_eq_zero_iff] at h
    contradiction
    exact hn
  induction m with
  | zero =>
    simp
  | succ m ih =>
    simp_all
    rw [← Real.zpow_add]
    simp [ih]
    simp [mul_add]
    rw [zpow_add]
    omega
    omega
  | pred m ih =>
    rw [Real.zpow_sub_one, mul_sub]
    rw [Real.zpow_neg] at *
    rw [ih]
    field_simp; ring_nf
    rw [Int.sub_eq_add_neg, zpow_add]
    congr
    ring_nf
    exact hx
    simpa

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  by_cases hx: x = 0
  . by_cases hy: y = 0
    . simp [hx, hy]
      by_cases hn: n = 0
      . rw [hn]
        simp
      rw [zero_zpow]
      simp
      omega
    simp_all
    by_cases hn: n = 0
    . rw [hn]
      simp
    rw [zero_zpow]
    simp
    omega
  by_cases hy: y = 0
  . rw [hy]
    simp
    by_cases hn: n = 0
    . rw [hn]
      simp
    rw [zero_zpow]
    simp
    omega
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [←zpow_add, ih, ← zpow_add, ← zpow_add]
    ring_nf
    field_simp
    omega
    omega
    positivity
  | pred n ih =>
    rw [Int.sub_eq_add_neg, ← zpow_add, ih, ← zpow_add, ← zpow_add]
    field_simp
    repeat simpa
    positivity

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    rw [← zpow_add]
    simp
    positivity
    positivity
  | pred n ih =>
    rw [Int.sub_eq_add_neg, ← zpow_add]
    positivity
    positivity

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  lift n to ℕ using by order
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    rw [← zpow_add]
    simp
    . rw [← zpow_add]
      simp
      by_cases hn: n = 0
      . gcongr
        rw [hn]
        by_cases hx: x = 0
        . rw [hx]
          simp
        simp
      specialize ih (by omega)
      gcongr
      apply pow_nonneg
      grind
      linarith
    positivity

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    contradiction
  | pred n ih =>
    have : x > 0 := by
      order
    have : x * x⁻¹ > 0:= by
      grind
    have : x⁻¹ > 0 := by
      rw [← isPos_iff]
      apply Real.inv_of_pos
      rw [isPos_iff]
      grind
    rw [Int.sub_eq_add_neg, ← zpow_add]
    simp
    by_cases hn: n = 0
    . rw [hn]
      simp
      gcongr
    rw [← zpow_add]
    gcongr
    . simp
      gcongr
    simp
    specialize ih (by omega)
    gcongr
    simp
    . grind
    order

lemma lemma1 : ∀ (x y:Real) (n:ℤ) (hy: y > 0) (hn: n > 0) (hxy: x^n ≤ y^n), x ≤ y := by
  intro x y n hy hn hxy
  lift n to ℕ using by order
  have := Real.pow_gt_pow x y n
  by_contra! h
  simp_all
  specialize this (by order)
  linarith

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  wlog h: x ≥ y
  . specialize this hy hx hn (symm hxy) (by order)
    exact symm this
  have h1: x ≤ y:= by
    wlog hn: n > 0
    . specialize this (x:=x) (y:=y) (n:=-n) (by order) (by order)
      have _: -n>0:= by
        grind
      specialize this (by order)
      apply this
      .
        have h: -n>0:= by
          grind
        lift (-n) to ℕ using (by positivity) with k hk
        rw [show n = -k by omega, Real.zpow_neg, Real.zpow_neg] at hxy
        field_simp at hxy
        symm
        exact_mod_cast hxy
      grind
      grind
    apply lemma1 x y n hy hn
    grind
  linarith

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  induction' n <;> simp

/-- Definition 5.6.2. We permit "junk values" when {lean}`x` is negative or {lean}`n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  simp
  have : 0^n = 0 := by
    simp
    grind
  simp_all

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      sorry
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    sorry
  linarith

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by sorry

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by sorry

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by sorry

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by sorry

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by sorry

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by sorry

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by sorry

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by sorry

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by sorry

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by sorry

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by sorry
    simp_all
  have : a' > 0 := by sorry
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by sorry

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by sorry

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  sorry

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  sorry

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  sorry

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  sorry

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  sorry

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  sorry

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  sorry

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  sorry

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by sorry

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  sorry

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  sorry

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
