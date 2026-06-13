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

lemma lemma1 : ∀ (x y:Real) (n:ℤ) (_: y > 0) (_: n > 0) (_: x^n ≤ y^n), x ≤ y := by
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

lemma le_pow_of_lt {x:Real} (hx: x ≥ 1) (n:ℕ) (hn: n ≥ 1) : x ≤ x^n := by
  induction n with
  | zero =>
    contradiction
  | succ i ih =>
    simp_all
    by_cases hn_1:  i ≥ 1
    . simp_all
      nth_rewrite 1 [← mul_one x]
      gcongr
    simp_all

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      have := Real.pow_gt_pow (x:=y) (y:=1) (n:=n) (by grind) (by grind) (by grind)
      simp_all
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    have h2 := Real.pow_gt_pow (x:=y) (y:=x) (n:=n) (by grind) (by grind) (by grind)
    simp at h2
    have h3 : x ≤ x^n := by
      apply le_pow_of_lt (by linarith) n hn
    grind
  linarith

lemma claim_y_add_eps_pow_n_lt_x {y x: Real} {n:ℕ} { h: n≥1 } {h2: y^n<x} {hy: y≥0}: ∃ ε>0, y+ε>0 ∧ (y+ε)^n < x := by
  set ε := min ((x- (y)^n)/ (2*(y+1)^(n-1) * n)) (1/2)
  have hε_pos: ε > 0 := by
    simp [ε]
    have : x - y ^ n >0 := by linarith
    have : 2 * (y + 1) ^ (n - 1) * ↑n >0 := by
      by_cases h: n = 1
      . simp [h]
      have : (y + 1) ^ (n - 1) ≥ 0 := by
        apply pow_nonneg
        grind
      rcases this with a | b
      . positivity
      . symm at b
        rw [Real.pow_eq_zero] at b
        rw [b]
        rw [zero_pow]
        exfalso
        grind
        grind
        grind
    . positivity
  have h_comm {ε:Real}: Commute (y+ε) y := by
    exact Commute.all (y + ε) y
  have h_decomp {ε:Real} := Commute.mul_geom_sum₂ (x:=y+ε) (y:=y) (n:=n) h_comm
  simp at h_decomp
  have h_sum_est :  ∑ i ∈ Finset.range n, (y + ε) ^ i * y ^ (n - 1 - i) ≤ ∑ i ∈ Finset.range n, ((y+1)^(n-1))  := by
    gcongr
    expose_names
    simp_all
    have : (y+1) ^ (n - 1) = (y+1)^i * (y+1)^(n - 1 - i) := by
      rw [← pow_add]
      grind
    rw [this]
    gcongr
    . simp [ε]
      right
      linarith
    . linarith
  simp [Finset.sum_const] at h_sum_est
  have h_est : ε * ((y+1)^(n-1)) * n ≥ (y+ε)^n - (y)^n := by
    rw [← h_decomp]
    rw [mul_assoc]
    gcongr
    grind
  simp_all
  use ε
  split_ands
  . grind
  . grind
  .
    have h_yeps_lt_x : (y+ε)^n < x := by
      have h_lt_diff : (y+ε)^n - y^n < x - y^n := by
        have: ε * ((y+1)^(n-1)) * n < x - y^n := by
          have : ε ≤ (x - y^n)/(2*(y + 1) ^ (n - 1) * ↑n) := by
            simp [ε]
          calc
            ε * (y + 1) ^ (n - 1) * ↑n
              ≤ (x - y^n)/(2*(y + 1) ^ (n - 1) * ↑n) * (y + 1) ^ (n - 1) * ↑n := by
                gcongr
            _ = (x - y^n)/2 := by
              field_simp
            _ < x - y^n := by
              linarith
        linarith
      linarith
    exact h_yeps_lt_x

lemma lemma2 {n:ℕ} {x y: Real} (hx: x ≥ 0) (hy: y ≥ 0) (hn: n ≥ 1) (hy: ¬y = 0) (h: y = x.root n) : y ^ n = x := by
      have hbdd := Real.rootset_bddAbove (x:=x) n hn
      have hnon := Real.rootset_nonempty (x:=x) hx n hn
      have hglb := Real.LUB_exist hnon hbdd
      have h3 := ExtendedReal.sSup_of_bounded hnon hbdd
      rw [h]
      obtain ⟨ y, hy, h1 ⟩ := hglb
      simp [Real.root]
      rw [Real.isLUB_def] at h3
      obtain ⟨ h3, h4 ⟩ := h3
      have ydef: sSup {y | 0 ≤ y ∧ y ^ n ≤ x} = y := by
        apply le_antisymm
        simp at h3
        . specialize h4 y hy
          exact h4
        simp [Real.lowerBound_def] at h1
        specialize h1 (sSup {y | y ≥ 0 ∧ y ^ n ≤ x}) h3
        exact h1
      simp_all only [ge_iff_le]
      obtain h | h | h := Real.trichotomous' (y ^ n) x
      . exfalso
        have claim1: ∃ ε>0, y-ε>0 ∧ (y-ε)^n > x := by
          set ε := min ((y ^ n - x) / (y^(n-1) * n * 2)) (y/2)
          use ε
          have h_comm {ε:Real}: Commute y (y-ε) := by
            exact Commute.all y (y - ε)
          have h_decomp {ε:Real} := Commute.mul_geom_sum₂ (x:=y) (y:=y-ε) (n:=n) h_comm
          simp at h_decomp
          have : y-ε > 0 := by
            grind
          have : ε > 0 := by
            simp [ε]
            split_ands
            . have : (y ^ n - x) > 0 := by
                grind
              have : (y ^ (n - 1) * ↑n * 2) > 0 := by
                positivity
              positivity
            positivity
          have h_sum_est : ∑ i ∈ Finset.range n, (y^(n-1)) ≥ ∑ i ∈ Finset.range n, y ^ i * (y - ε) ^ (n - 1 - i) := by
            gcongr
            expose_names
            simp_all
            have : y ^ (n - 1) = y^i * y^(n - 1 - i) := by
              rw [Real.pow_add]
              grind
            rw [this]
            gcongr
            grind
            grind
          replace h_sum_est  (h2: ε>0): n * y^(n-1) ≥ ∑ i ∈ Finset.range n, y ^ i * (y - ε) ^ (n - 1 - i) := by
            have : ∑ i ∈ Finset.range n, y ^ (n - 1) = n * y^(n-1) := by
              rw [Finset.sum_const]
              simp
            rw [this] at h_sum_est
            exact h_sum_est
          have h_est : ε * (y^(n-1)) * n ≥ y^n - (y-ε)^n := by
            rw [← h_decomp]
            rw [mul_assoc]
            gcongr
            grind
          simp_all
          have : x < (y - ε) ^ n := by
            have : ε * (n * y^(n-1)) < y^n - x := by
              simp [ε]
              rw [Real.min_eq]
              split_ifs
              . field_simp; ring_nf
                grind
              simp_all
              expose_names
              field_simp at h_2 ⊢; ring_nf
              linarith
            linarith
          exact this
        obtain ⟨ ε, hε, hε' ⟩ := claim1
        have hupper: (y-ε) ∈ upperBounds {y | 0 ≤ y ∧ y ^ n ≤ x} := by
          simp [Real.upperBound_def]
          intro z hz hzn
          have : z^n < (y - ε) ^ n := by
            grind
          apply lemma1 (n:=n)
          . grind
          . grind
          left
          exact this
        have : y-ε ≥ y := by
          specialize h4 (y-ε) hupper
          exact h4
        linarith
      . have : y>0 := by positivity
        obtain ⟨ ε, hε, hε' ⟩ := claim_y_add_eps_pow_n_lt_x (h:=hn) (y:=y) (x:=x) (h2:=h) (hy:=by linarith)
        have h_yeps_in_S : y + ε ∈ {z | 0 ≤ z ∧ z^n ≤ x}:=by
          constructor
          linarith
          linarith
        have : y + ε ≤ y := by
          rw [Real.upperBound_def] at hy
          specialize hy (y + ε) h_yeps_in_S
          exact hy
        linarith
      . exact h

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
    by_cases hy : y = 0
    . simp [hy]
      constructor
      . intro h
        simp [root] at h
        rw [zero_pow]
        symm
        set s:= {y:Real | 0 ≤ y ∧ y ^ n ≤ x}
        have hnon : s.Nonempty := by
          apply Real.rootset_nonempty (x:=x) hx n hn
        have hbdd : BddAbove s := by
          apply Real.rootset_bddAbove (x:=x) n hn
        have h2 := ExtendedReal.sSup_of_bounded hnon hbdd
        rw [← h] at h2
        rw [isLUB_def] at h2
        obtain ⟨ h2, h3 ⟩ := h2
        rw [upperBound_def] at h2
        have : s = {0} := by
          simp [s]
          ext y
          constructor
          . intro h
            simp at h ⊢
            specialize h2 y (by grind)
            grind
          intro h
          simp at h
          rw [h]
          simp
          rw [zero_pow]
          linarith
          linarith
        . have h0_in_s : 0 ∈ s := by
            rw [this]
            simp
          by_contra hx
          have hx: x > 0 := by
            grind
          set y := min 1 x
          have : y ∈ s := by
            simp [y, s]
            split_ands
            . linarith
            rw [min_eq]
            split_ifs
            . have :(1:Real) ^ n = 1 := by
                induction n
                . simp
                rw [pow_succ]
                simp
              rw [this]
              grind
            expose_names
            simp at h_1
            have : y = x := by grind
            have {x: Real} {n: ℕ} (h: x < 1) (h1: x≥0) (h2: n≥1): x^n≤x := by
              induction' n with i ih
              . contradiction
              rw [pow_succ]
              by_cases h: i ≥ 1
              . specialize ih (by grind)
                have : x ^ i * x ≤ x * 1 := by
                  gcongr
                simp at this
                exact this
              simp at h
              rw [h]
              simp
            apply this
            linarith
            linarith
            linarith
          have : y ∈ {y:Real|y=0} := by
            grind
          simp at this
          simp [y] at this
          rw [min_eq] at this
          split_ifs at this
          . linarith
          . linarith
        linarith
      intro h
      rw [zero_pow] at h
      symm at h
      rw [h]
      simp [root]
      have h1 : {y: Real | 0 ≤ y ∧ y ^ n ≤ 0} = {y: Real | y = 0} := by
        ext y
        constructor
        . intro h
          simp_all
          have : y^n ≥ 0 := by
            apply Real.pow_nonneg (n:=n)
            linarith
          have : y ^ n = 0 := by linarith
          rw [Real.pow_eq_zero] at this
          exact this
          . linarith
        intro h
        simp_all
        rw [zero_pow]
        linarith
      rw [h1]
      simp
      linarith
    constructor
    . intro h
      apply lemma2
      . grind
      . grind
      . grind
      . grind
      . grind
    intro h

    by_cases hxeqzero : x = 0
    . simp [root]
      simp [hxeqzero]
      rw [hxeqzero] at h
      rw [Real.pow_eq_zero] at h
      rw [h]
      simp_all
      linarith
    have h_non := Real.rootset_nonempty hx n hn
    have h_bdd := Real.rootset_bddAbove n hn (x:=x)
    have h1 := ExtendedReal.sSup_of_bounded h_non h_bdd
    replace hx : x > 0 := by positivity
    rw [isLUB_def] at h1
    obtain ⟨ h1, h2 ⟩ := h1
    have hxroot_pos: x.root n > 0 := by
        simp [root]
        have : 0 ∈ {y | 0 ≤ y ∧ y ^ n ≤ x} := by
          simp
          rw [zero_pow]
          positivity
          positivity
        have hsup_nonneg: 0 ≤ sSup {y | 0 ≤ y ∧ y ^ n ≤ x} := by
          simp [upperBound_def] at h1
          specialize h1 (0) (by grind) (by grind)
          exact h1
        rcases hsup_nonneg with h | h
        . exact h
        exfalso
        have : 0^n < x := by
          rw [zero_pow]
          linarith
          linarith
        have h1 := @claim_y_add_eps_pow_n_lt_x (y:=0) (x:=x) (h:=hn) (hy:= by linarith) (h2:= this)
        obtain ⟨ ε, hε, ⟨_,hε'⟩⟩ := h1
        simp at hε'
        have : ε ≤ 0 := by
          simp [upperBound_def] at h1
          specialize h1 (ε) (by linarith) (by linarith)
          rw [h]
          exact h1
        linarith
    apply zpow_inj (n:=n)
    . positivity
    . exact hxroot_pos
    . linarith
    norm_cast
    rw [h]
    symm
    apply lemma2
    . grind
    . grind
    . grind
    . grind
    . rfl

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  by_cases hxeqzero : x = 0
  . simp [root]
    simp [hxeqzero]
    have : {y:Real | 0 ≤ y ∧ y ^ n ≤ 0} = {0} := by
      ext y
      simp
      constructor
      . intro ⟨h1, h2⟩
        have : y^n≥ 0:= by
          apply pow_nonneg
          grind
        have : y^n=0:= by grind
        rw [Real.pow_eq_zero] at this
        exact this
        grind
      intro h
      simp [h]
      right
      rw [zero_pow]
      grind
    rw [this]
    simp_all
  have h_non := Real.rootset_nonempty hx n hn
  have h_bdd := Real.rootset_bddAbove n hn (x:=x)
  have h1 := ExtendedReal.sSup_of_bounded h_non h_bdd
  replace hx : x > 0 := by positivity
  rw [isLUB_def] at h1
  obtain ⟨ h1, h2 ⟩ := h1
  simp [root]
  have : 0 ∈ {y | 0 ≤ y ∧ y ^ n ≤ x} := by
    simp
    rw [zero_pow]
    positivity
    positivity
  have hsup_nonneg: 0 ≤ sSup {y | 0 ≤ y ∧ y ^ n ≤ x} := by
    simp [upperBound_def] at h1
    specialize h1 (0) (by grind) (by grind)
    exact h1
  exact hsup_nonneg

lemma zero_root_eq_zero {n:ℕ} (hn: n ≥ 1) : (0:Real).root n = 0 := by
  have : {y:Real | 0 ≤ y ∧ y ^ n ≤ 0} = {0} := by
    ext y
    simp
    constructor
    . intro ⟨h1, h2⟩
      have : y^n≥ 0:= by
        apply pow_nonneg
        grind
      have : y^n=0:= by grind
      rw [Real.pow_eq_zero] at this
      exact this
      grind
    intro h
    simp [h]
    right
    rw [zero_pow]
    grind
  simp [Real.root]
  rw [this]
  simp

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  by_contra! ⟨h1,h2⟩ | ⟨h1, h2⟩
  have : x = 0 := by linarith
  rw [this] at h1
  have : (0:Real).root n = 0 := by
    apply zero_root_eq_zero
    grind
  linarith
  . have h3:= Real.root_nonneg hx hn
    have : x.root n = 0 := by
      linarith
    have h1 := Real.eq_root_iff_pow_eq hx (y:=0) (by grind) (n:=n) (by grind)
    symm at this
    rw [h1] at this
    rw [zero_pow] at this
    linarith
    linarith


theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
    by_cases hx: x = 0
    . simp [hx]
      split_ands
      . apply zero_root_eq_zero
        grind
      grind
    set y:= x.root n
    have hypos: y>0:= by
      rw [Real.root_pos]
      . grind
      grind
      grind
    have hx: x > 0 := by
      grind
    have h1:= Real.eq_root_iff_pow_eq (x:=x) (by grind) (y:=y) (by grind) (n:=n) (by grind)
    rw [← h1]

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
    set y:= x ^ n
    have h1:= Real.eq_root_iff_pow_eq (x:=y) (by positivity) (y:=x) (by positivity) (n:=n) (by grind)
    symm
    rw [h1]

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  constructor
  . intro h
    have h1: (x.root n)^n ≥ (y.root n)^n := by
      rw [Real.pow_of_root, Real.pow_of_root]
      grind
      repeat linarith
    simp at h1
    by_cases hy : y = 0
    . simp [hy]
      rw [zero_root_eq_zero]
      have : x.root n > 0:= by
        rw [root_pos]
        repeat linarith
      exact this
      linarith
    have : y.root n > 0 := by
      rw [Real.root_pos]
      grind
      grind
      grind
    have : x.root n > 0 := by
      rw [Real.root_pos]
      grind
      grind
      grind
    have h2 := lemma1 (y:=x.root n) (x:=y.root n) (n:=n) (by grind) (by grind) (by exact_mod_cast h1)
    simp
    rcases h2 with h | h
    . exact h
    . exfalso
      rw [Real.eq_root_iff_pow_eq _ _ _] at h
      symm at h
      rw [Real.pow_of_root] at h
      repeat linarith
  intro h
  by_cases hy : y = 0
  . simp [hy]
    change x > 0
    have : (x.root n)^n = x := by
      rw [Real.pow_of_root]
      linarith
      linarith
    rw [← this]
    apply pow_pos
    rw [hy, zero_root_eq_zero] at h
    exact h
    grind
  have h1: (x.root n)^n ≥ (y.root n)^n := by
    apply zpow_ge_zpow (n:=n)
    linarith
    rw [root_pos]
    grind
    grind
    grind
    grind
  simp at h1
  have : y.root n > 0 := by
    rw [Real.root_pos]
    grind
    grind
    grind
  rw [pow_of_root, pow_of_root] at h1
  simp
  rcases h1 with h1 | h1
  . simpa
  rw [h1] at h
  exfalso
  repeat linarith


/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  have : x.root k ≤ x.root l := by
    simp at hkl
    rw [lt_iff_exists_add] at hkl
    obtain ⟨c, cpos, hc⟩ := hkl
    rw [hc]
    have : (x.root (l + c))^(l*(l+c)) ≤ (x.root l)^(l*(l+c)) := by
      rw [mul_comm,← Real.pow_mul, pow_of_root]
      rw [mul_comm,← Real.pow_mul, pow_of_root]
      rw [← pow_add]
      nth_rw 1 [← mul_one (x^l)]
      gcongr
      . rw [← pow_zero (x)]
        gcongr
        grind
      linarith
      linarith
      linarith
      linarith
    apply lemma1 (n:= l*(l+c))
    . rw [root_pos]
      grind
      grind
      grind
    . positivity
    exact this
  rcases this with h | h
  . exact h
  . exfalso
    have : (x.root k)^(k*l) = (x.root l)^(k*l) := by
      rw [h]
    rw [← Real.pow_mul, mul_comm, ← Real.pow_mul] at this
    rw [pow_of_root, pow_of_root] at this
    simp at hkl
    rw [lt_iff_exists_add] at hkl
    obtain ⟨c, cpos, hc⟩ := hkl
    rw [hc] at this
    rw [← pow_add] at this
    have h1: x^(c) = 1 := by
      have : x ^ l * (x^l)⁻¹ = (x ^ l * x ^ c) * (x^l)⁻¹ := by
        grind
      field_simp at this
      symm
      exact this
    have : c = 0 := by
      rw [pow_eq_one_iff_cases] at h1
      rcases h1 with h1 | h1 | ⟨ha, hb⟩
      . exact h1
      . linarith
      . linarith
    linarith
    linarith
    linarith
    linarith
    linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  have h1: (root 1 k) ^ k = 1 := by
    rw [Real.pow_of_root]
    grind
    grind
  have h2: (1:Real) ^ k = 1 := by simp
  nth_rw 2 [← h2] at h1
  apply zpow_inj
  rw [root_pos]
  repeat linarith
  exact h1

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  by_cases hx': x = 0
  . simp_all
    repeat rw [zero_root_eq_zero]
    linarith
    linarith
  by_cases hy': y = 0
  . simp_all
    repeat rw [zero_root_eq_zero]
    linarith
    linarith
  set z := (x*y).root n
  have hz: z^n = x*y:= by
    rw [pow_of_root]
    positivity
    linarith
  have hmain: z^n = (x.root n * y.root n)^n:= by
    rw [mul_pow]
    rw [pow_of_root, pow_of_root, pow_of_root]
    repeat linarith
    positivity
    linarith
  have hx_root_pos: x.root n > 0 := by
    rw [root_pos]
    repeat grind
  have hy_root_pos: y.root n > 0 := by
    rw [root_pos]
    repeat grind
  apply zpow_inj (n:=n)
  simp_all [z]
  . change (x * y).root n > 0
    rw [root_pos]
    positivity
    positivity
    linarith
  . positivity
  . positivity
  exact hmain

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  by_cases hx': x = 0
  . simp_all
    repeat rw [zero_root_eq_zero]
    rw [← mul_one 1]
    gcongr
    linarith
    linarith
  set y := (x.root n).root m
  have hy: y^m = x.root n := by
    rw [Real.pow_of_root]
    apply root_nonneg
    grind
    grind
    grind
  have hy: (y^m)^n = (x.root n)^n := by
    congr
  nth_rw 2 [pow_of_root] at hy
  rw [pow_mul] at hy
  rw [← Real.pow_of_root hx (n:=m*n)] at hy
  apply zpow_inj (n:=m*n)
  . rw [root_pos]
    rw [root_pos]
    grind
    linarith
    linarith
    apply root_nonneg
    linarith
    linarith
    linarith
  . rw [root_pos]
    grind
    linarith
    rw [← mul_one 1]
    gcongr
  . positivity

  . norm_cast
    ring_nf
    exact hy
  . rw [← mul_one 1]
    gcongr
  . positivity
  . linarith

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  have : x^1 = x := by simp
  have : (x.root 1)^1 = x^1 := by
    rw [Real.pow_of_root]
    repeat linarith
  simp at this
  exact this

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
    apply zpow_inj (n:=n)
    . linarith
    . linarith
    grind
    exact_mod_cast h

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
    have : a' = 0 := by
      simp_all
      norm_cast at hq
      symm at hq
      rw [Rat.divInt_eq_zero _] at hq
      exact hq
      grind
    simp_all
  have : a' > 0 := by
    norm_cast at hq
    rw [Rat.divInt_eq_divInt_iff] at hq
    have : a' * ↑b > 0 := by
      rw [← hq]
      positivity
    simp at this
    rw [mul_pos_iff_of_pos_right] at this
    grind
    grind
    grind
    grind
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

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  have h1 := ratPow_def hx 1 hn
  simp_all

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  have : (n:ℚ) = (n:ℚ)/1 := by
    simp
  rw [this]
  have h1:= ratPow_def (a:=n) (b:=1) (x:=x) (by grind) (by grind)
  simp_all
  have : x.root 1 ^ n = (x.root 1 ^ 1) ^ n := by
    congr
    simp
  rw [this, pow_of_root]
  linarith
  linarith

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨a,b, hb,hab⟩ := Rat.eq_quot q
  rw [hab, ratPow_def]
  apply zpow_pos
  rw [root_pos]
  repeat linarith

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨a,b,hb, hab⟩ := Rat.eq_quot q
  obtain ⟨a',b',hb', hab'⟩ := Rat.eq_quot r
  rw [hab, hab', ratPow_def, ratPow_def]
  have h1: x ^ ((a / b:ℚ) + ↑a' / ↑b') = x ^ ((a*b' + a'*b: ℤ) / (b*b':ℕ):ℚ) := by
    congr
    field_simp
    norm_cast
    grind
  rw [h1, ratPow_def]
  have : (a/b:ℚ) = ((a*b'):ℤ)/(b*b':ℕ) := by
    field_simp
    norm_cast
    grind
  have h2 :=Real.pow_root_eq_pow_root (hq:=this) (x:=x) (hx:=hx) (hb:=by positivity) (hb':=by positivity)
  rw [← h2]
  have : (a'/b':ℚ) = ((a'*b):ℤ)/(b*b':ℕ) := by
    field_simp
    norm_cast
    grind
  have h2 :=Real.pow_root_eq_pow_root (hq:=this) (x:=x) (hx:=hx) (hb:=by positivity) (hb':=by positivity)
  rw [← h2]
  rw [zpow_add]
  . have : x.root (b * b') > 0 := by
      rw [root_pos]
      linarith
      linarith
      exact Right.one_le_mul hb hb'
    linarith
  . linarith
  . positivity
  . linarith
  . positivity
  . positivity
  . positivity

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨a,b,hb, hab⟩ := Rat.eq_quot q
  obtain ⟨a',b',hb', hab'⟩ := Rat.eq_quot r
  rw [hab, hab', ratPow_def, ratPow_def]
  have h1: (↑a / ↑b:ℚ) * (↑a' / ↑b':ℚ) = ((a * a':ℤ) / (b * b':ℕ):ℚ) := by
    field_simp
    grind
  rw [h1, ratPow_def]
  rw [← zpow_mul]
  congr
  have : a/b = ((a*b':ℤ) / (b*b':ℕ):ℚ) := by
    field_simp
    norm_cast
    grind
  have h2:= Real.pow_root_eq_pow_root (hq:=this) (x:=x) (hx:=by linarith) (hb:=by positivity) (hb':=by positivity)
  rw [← h2]
  rw [← zpow_mul]
  have h1 := root_of_pow (x:= (x.root (b * b') ^ a)) (n:=b') (?_) (by grind)
  exact h1
  . simp
    apply zpow_nonneg
    apply root_nonneg
    linarith
    exact Right.one_le_mul hb hb'
  linarith
  positivity
  linarith
  linarith
  rw [ratPow_def]
  apply zpow_pos
  rw [root_pos]
  repeat linarith

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  obtain ⟨a, b, hbpos, hab⟩ := Rat.eq_quot (q)
  have hq_neg: -q = (↑(-a):ℤ)/(b:ℕ) := by
    rw [hab]
    field_simp
    grind
  simp [hq_neg]
  have h1:= ratPow_def (x:=x) (a:=-a) (b:=b) (by grind) (by grind)
  simp at h1
  rw [h1]
  have : x.root b ^ a =  x ^ q := by
    rw [hab, ratPow_def]
    linarith
    linarith
  rw [this]

lemma pow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x^n > y^n := by
  constructor
  . intro h
    apply Real.pow_gt_pow
    repeat linarith
  intro h
  have : x ≥ y := by
    apply lemma1 (n:=n)
    repeat linarith
    simp
    grind
  rcases this with h1 | h1
  . exact h1
  simp_all

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨a, b, hbpos, hab⟩ := Rat.eq_quot q
  have hapos: a > 0 := by
    simp [hab] at h
    simp_all
  simp [hab]
  constructor
  . intro h
    rw [ratPow_def, ratPow_def]
    lift a to ℕ using by order
    have h1:= Real.root_mono (x:= x) (y:= y) (hy:=by grind) (n:=b) (hn:=hbpos) (by grind)
    simp at h1
    rw [h1] at h
    change x.root b ^ a > y.root b ^ a
    have h2 := pow_gt_pow (x:= x.root b) (y:= y.root b)  (hxy:=by grind) a ?_ (by grind)
    exact h2
    . apply root_nonneg
      linarith
      linarith
    repeat linarith
  intro h
  rw [ratPow_def, ratPow_def] at h
  lift a to ℕ using by order
  simp_all

  have h1 : (y.root b ^ a) ^ b < (x.root b ^ a) ^ b := by
    rw [← gt_iff_lt]
    rw [← pow_mono]
    exact h
    apply pow_pos
    rw [root_pos]
    linarith
    linarith
    linarith
    apply pow_pos
    rw [root_pos]
    linarith
    linarith
    linarith
    linarith
  simp [pow_mul, mul_comm] at h1
  simp [← pow_mul] at h1
  rw [pow_of_root, pow_of_root] at h1
  rw [← gt_iff_lt] at h1
  rw [← pow_mono] at h1
  exact h1
  repeat linarith

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  obtain ⟨a, b, hbpos, hab⟩ := Rat.eq_quot q
  obtain ⟨a', b', hbpos', hab'⟩ := Rat.eq_quot r
  simp [hab, hab']
  rw [ratPow_def, ratPow_def]
  constructor
  . intro h
    have h : ((x.root b' ^ a') ^ b) ^ b' < ((x.root b ^ a) ^ b) ^ b' := by
      rw [← gt_iff_lt]
      rw [← pow_mono]
      rw [← pow_mono]
      exact h
      apply zpow_pos
      rw [root_pos]
      linarith
      linarith
      linarith
      apply zpow_pos
      rw [root_pos]
      repeat linarith
      apply pow_pos
      apply zpow_pos
      rw [root_pos]
      linarith
      linarith
      linarith
      apply pow_pos
      apply zpow_pos
      rw [root_pos]
      repeat linarith

    rw [pow_mul, pow_mul] at h
    change (x.root b' ^ a') ^ (b * b':ℤ) < (x.root b ^ a) ^ (b * b':ℤ) at h
    rw [zpow_mul, zpow_mul] at h
    ring_nf at h
    have : x ^ (a' * ↑b) < x ^ (↑b' * a) := by
      rw [show a' * b * ↑b' =  b' * (a' * ↑b) by ring_nf] at h
      rw [show ↑b * ↑b' * a=  ↑b *(↑b' * a) by ring_nf] at h
      rw [← zpow_mul] at h
      simp at h
      rw [pow_of_root] at h

      rw [← zpow_mul _ b] at h
      simp at h
      rw [pow_of_root] at h
      exact h
      repeat linarith
    field_simp
    by_cases ha' : a' ≥ 0
    . by_cases ha : a ≥ 0
      . lift a to ℕ using by order
        lift a' to ℕ using by order
        simp_all
        exact_mod_cast this
      . simp_all
        exfalso
        have : a' * ↑b ≥ 0 := by
          positivity
        have : ↑b' * a < 0 := by
          refine Int.mul_neg_of_pos_of_neg ?_ ha
          grind
        linarith
    . by_cases ha : a ≥ 0
      . simp_all
        exact_mod_cast this
      . simp_all
        exact_mod_cast this
  . intro h
    sorry
  repeat linarith

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  sorry

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨a, b, hbpos, hab⟩ := Rat.eq_quot q
  rw [hab, ratPow_def, ratPow_def, ratPow_def]
  rw [Real.root_mul, mul_zpow]
  repeat linarith
  positivity
  linarith

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨k, hk⟩ := hn
  rw [hk, ← pow_add]
  rcases trichotomous' 0 (x ^ k) with h | h | h
  . left
    exact mul_pos_of_neg_of_neg h h
  . left
    exact Left.mul_pos h h
  . simp_all
    rw [← h]
    simp

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
