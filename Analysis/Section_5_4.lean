import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

theorem LIM_neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : LIM (-a) = -LIM a := by
  have h1: -a = (fun x:ℕ ↦ (-1:ℚ)) * a := by
    ext n
    simp
  simp_all
  rw [<- Real.LIM_mul, <- Real.ratCast_def]
  simp_all
  . apply Sequence.IsCauchy.const
  exact ha

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hx: x = 0
  . left
    exact hx

  obtain ⟨a, hcauchy, haway, hlim⟩ := Real.boundedAwayZero_of_nonzero hx

  rw [Sequence.isCauchy_def] at hcauchy

  obtain ⟨ε, hε, h⟩ := haway
  rcases hcauchy (ε / 2) (half_pos hε) with ⟨N, Nle, hN⟩

  lift N to ℕ using Nle
  set n := max 0 N
  have : ((a: Sequence).from ↑n).n₀ = n := by
    simp
  rcases lt_trichotomy 0 (a n) with h1 | h1 | h1
  . right
    left
    rw [isPos_def]
    set b := fun n:ℕ ↦ if n ≥ N then a n else ε
    have hbcauchy: (b: Sequence).IsCauchy := by
      rw [Sequence.IsCauchy.coe]
      intro ε hε
      specialize hcauchy ε hε
      rcases hcauchy with ⟨N, haha, hN⟩
      lift N to ℕ using haha
      use max N (max n ((a:Sequence).from N).n₀.toNat)
      intro j hj' k hk'
      simp [Section_4_3.dist]
      rw [Rat.steady_def] at hN
      specialize hN j (by grind) k (by grind)
      rw [Rat.Close] at hN
      simp_all
      simp [b]
      rw [if_pos, if_pos]
      simp_all
      grind
      grind
    use b
    split_ands
    . rw [boundedAwayPos_def]
      use ε/2
      constructor
      . grind
      have: a n ≥ ε := by
        grind
      have h2: ∀ n', n' ≥ N -> a n' ≥ ε / 2 := by
        intro n' hn'
        rw [Rat.steady_def] at hN
        specialize hN n (by grind) n' (by grind)
        rw [Rat.Close] at hN
        simp_all
        rw [if_pos] at hN
        grind
        grind
      intro n'
      by_cases hn': n' ≥ N
      . simp [b, hn']
        apply h2
        grind
      simp [b, hn']
      grind
    . simpa
    rw [hlim]
    rw [LIM_eq_LIM]
    rw [Sequence.equiv_iff]
    intro e he
    use N
    intro n hn
    simp [b]
    rw [if_pos]
    grind
    grind
    simpa
    simpa
  . left
    grind
  right
  right
  rw [isNeg_def]
  set b := fun n:ℕ ↦ if n ≥ N then a n else -ε
  have hbcauchy: (b: Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    specialize hcauchy ε hε
    rcases hcauchy with ⟨N, haha, hN⟩
    lift N to ℕ using haha
    use max N n
    intro j _ k _
    simp [Section_4_3.dist]
    rw [Rat.steady_def] at hN
    specialize hN j (by grind) k (by grind)
    rw [Rat.Close] at hN
    simp_all
    simp [b]
    rw [if_pos, if_pos]
    simp_all
    grind
    grind
  use b
  split_ands
  . rw [boundedAwayNeg_def]
    use ε/2
    constructor
    . grind
    simp_all
    intro n
    have h2: ∀ n', n' ≥ N -> a n' ≤ -(ε / 2) := by
      intro n' hn'
      rw [Rat.steady_def] at hN
      have : ((a: Sequence).from ↑N).n₀ = N := by
        simp
      specialize hN N (by grind) n' (by grind)
      rw [Rat.Close] at hN
      simp_all
      have : a N < 0 := by
        grind
      grind
    by_cases hn': n ≥ N
    . simp [b, hn']
      apply h2
      grind
    simp [b, hn']
    grind
  . simpa
  rw [hlim]
  rw [LIM_eq_LIM]
  rw [Sequence.equiv_iff]
  intro e he
  use N
  intro n hn
  simp [b]
  rw [if_pos]
  grind
  grind
  simpa
  simpa

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  rw [not_and]
  intro h
  rw [h]
  intro h
  rw [isPos_def] at h
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h
  obtain ⟨c, hc, hbound⟩ := hbound
  rw [<- LIM.zero] at hlim
  rw [LIM_eq_LIM] at hlim
  rw [Sequence.equiv_iff] at hlim
  specialize hlim (c/2) (by grind)
  obtain ⟨N, hN⟩ := hlim
  specialize hN N (by grind)
  simp_all
  specialize hbound N
  grind
  apply Sequence.IsCauchy.const
  simpa

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  rw [not_and]
  intro h
  rw [h]
  intro h
  rw [isNeg_def] at h
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h
  obtain ⟨c, hc, hbound⟩ := hbound
  rw [<- LIM.zero] at hlim
  rw [LIM_eq_LIM] at hlim
  rw [Sequence.equiv_iff] at hlim
  specialize hlim (c/2) (by grind)
  obtain ⟨N, hN⟩ := hlim
  specialize hN N (by grind)
  simp_all
  specialize hbound N
  grind
  apply Sequence.IsCauchy.const
  simpa

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rw [not_and]
  intro h1 h2
  rw [isPos_def] at h1
  rw [isNeg_def] at h2
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h1
  obtain ⟨b, hbound', hcauchy', hlim'⟩ := h2

  have lim_eq := (LIM_eq_LIM hcauchy hcauchy').mp (show LIM a = LIM b by grind)
  rw [Sequence.equiv_iff] at lim_eq

  obtain ⟨c, hc, hbound⟩ := hbound
  obtain ⟨d, hc, hbound'⟩ := hbound'

  specialize lim_eq (c/2+d/2) (by grind)
  obtain ⟨N, hN⟩ := lim_eq
  specialize hbound N
  specialize hbound' N
  specialize hN N (by grind)
  have : a N - b N ≥ c +d := by
    rw [Rat.sub_eq_add_neg]
    gcongr
    grind
  have : c + d ≤ c / 2 + d / 2 ∧ c > 0 ∧ d > 0 := by
    split_ands
    <;> grind
  grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  . intro hneg
    obtain ⟨a, hbound, hcauchy, hlim⟩ := hneg
    use (-a)
    constructor
    . rw [boundedAwayNeg_def] at hbound
      obtain ⟨c, hc, hbound⟩ := hbound
      use c
      constructor
      . grind
      simp_all
      grind
    constructor
    . apply Sequence.IsCauchy.neg
      exact hcauchy
    rw [hlim]
    have : -a = (fun x:ℕ ↦ (-1:ℚ)) * a := by
      ext n
      simp
    rw [this]
    rw [<- LIM_mul, <- Real.ratCast_def]
    rfl
    apply Sequence.IsCauchy.const
    repeat simpa
  intro h
  rw [isPos_def] at h
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h
  rw [boundedAwayPos_def] at hbound
  obtain ⟨c, hc, hbound⟩ := hbound
  use (-a)
  constructor
  . rw [boundedAwayNeg_def]
    use c
    constructor
    . simpa
    simp_all
  constructor
  . apply Sequence.IsCauchy.neg
    repeat simpa
  have : -a = (fun x:ℕ ↦ (-1:ℚ)) * a := by
      ext n
      simp
  rw [this]
  rw [<- LIM_mul, <- Real.ratCast_def]
  simp_all
  rw [<- hlim]
  simp
  apply Sequence.IsCauchy.const
  repeat simpa

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨a, hbound, hcauchy, hlim⟩ := hx
  obtain ⟨b, hbound', hcauchy', hlim'⟩ := hy
  rw [isPos_def]

  rw [boundedAwayPos_def] at hbound hbound'
  obtain ⟨c, hc, hbound⟩ := hbound
  obtain ⟨c', hc', hbound'⟩ := hbound'
  use (a+b)
  constructor
  . rw [boundedAwayPos_def]
    use (c+c')
    constructor
    . positivity
    simp_all
    intro n
    specialize hbound n
    specialize hbound' n
    linarith
  constructor
  . apply Sequence.IsCauchy.add
    repeat simpa
  rw [hlim, hlim', LIM_add]
  repeat simpa

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨a, hbound, hcauchy, hlim⟩ := hx
  obtain ⟨b, hbound', hcauchy', hlim'⟩ := hy
  rw [isPos_def]
  rw [boundedAwayPos_def] at hbound hbound'
  obtain ⟨c, hc, hbound⟩ := hbound
  obtain ⟨c', hc', hbound'⟩ := hbound'
  use (a*b)
  constructor
  . use (c*c')
    constructor
    . positivity
    simp_all
    intro n
    specialize hbound n
    specialize hbound' n
    apply mul_le_mul
    repeat grind
  constructor
  . apply Sequence.IsCauchy.mul
    repeat simpa
  rw [hlim, hlim', LIM_mul]
  repeat simpa

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  . intro h
    rw [Real.ratCast_def] at h
    obtain ⟨a, hbound, hcauchy, hlim⟩ := h
    rw [boundedAwayPos_def] at hbound
    obtain ⟨c, hc, hbound⟩ := hbound
    simp_all
    have equiv: Sequence.Equiv a fun x ↦ q := by
      have h1 := Real.LIM_eq_LIM hcauchy (Sequence.IsCauchy.const q)
      rw [<- h1]
      simp_all
    rw [Sequence.equiv_iff] at equiv
    specialize equiv (c/2) (by grind)
    obtain ⟨N, hN⟩ := equiv
    specialize hN N (by grind)
    have : a N - q ≤ |a N - q| := by
      grind
    have : a N - q ≤ c/2 := by
      grind
    have : a N - c/2 ≤ q := by
      linarith
    have : c/2 ≤ q := by
      grind
    grind
  intro h
  use (fun n ↦ q)
  constructor
  . rw [boundedAwayPos_def]
    use q
    simp_all
  constructor
  . apply Sequence.IsCauchy.const
  rw [Real.ratCast_def]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  have := Real.pos_of_coe (-q)
  simp_all

open Classical in
/-- Need to use classical logic here because {name}`IsPos` and {name}`IsNeg` are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  constructor
  . intro h
    rw [isPos_def]
    obtain ⟨a, hbound, hcauchy, hlim⟩ := h
    use (-a)
    constructor
    . rw [boundedAwayPos_def]
      simp_all
      rw [boundedAwayNeg_def] at hbound
      peel hbound with c hc hbound
      grind
    constructor
    . apply Sequence.IsCauchy.neg
      repeat simpa
    rw [LIM_neg, <- hlim]
    ring_nf
    simpa
  intro h
  rw [isPos_def] at h
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h
  rw [boundedAwayPos_def] at hbound
  obtain ⟨c, hc, hbound⟩ := hbound
  use (-a)
  constructor
  . rw [boundedAwayNeg_def]
    simp_all
    use c
  constructor
  . apply Sequence.IsCauchy.neg
    repeat simpa
  rw [LIM_neg, <- hlim]
  ring_nf
  simpa
theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp_all [le_iff]
  rw [eq_comm]

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [ratCast_def, ratCast_def, lt_iff, LIM_sub]
  change q < q' ↔ (LIM ((fun x ↦ (q - q')))).IsNeg
  constructor
  . intro h
    use (fun x ↦ (q - q'))
    constructor
    . rw [boundedAwayNeg_def]
      use (q' - q)
      grind
    constructor
    . apply Sequence.IsCauchy.const
    rfl
  intro h
  rw [isNeg_def] at h
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h
  rw [boundedAwayNeg_def] at hbound
  obtain ⟨c, hc, hbound⟩ := hbound
  have h1:= LIM_eq_LIM hcauchy (Sequence.IsCauchy.const (q - q'))
  have h2: Sequence.Equiv a fun x ↦ q - q' := h1.mp (symm hlim)
  rw [Sequence.equiv_iff] at h2
  specialize h2 (c/2) (by grind)
  obtain ⟨N, hN⟩ := h2
  specialize hN N (by grind)
  rw [abs_sub_le_iff] at hN
  have : q - q'  ≤ c / 2 + a N := by grind
  have : q - q'  ≤ - c / 2 := by grind
  linarith
  repeat apply Sequence.IsCauchy.const

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  simp_all
  constructor
  . intro h
    rw [isPos_def] at h
    obtain ⟨a, hbound, hcauchy, hlim⟩ := h
    rw [boundedAwayPos_def] at hbound
    obtain ⟨c, hc, hbound⟩ := hbound
    use (-a)
    constructor
    . rw [boundedAwayNeg_def]
      simp_all
      use c
    constructor
    . apply Sequence.IsCauchy.neg
      simpa
    rw [LIM_neg, <- hlim]
    grind
    simpa
  intro h
  obtain ⟨a, hbound, hcauchy, hlim⟩ := h
  rw [boundedAwayNeg_def] at hbound
  obtain ⟨c, hc, hbound⟩ := hbound
  use (-a)
  constructor
  . rw [boundedAwayPos_def]
    simp_all
    use c
    constructor
    . positivity
    grind
  constructor
  . apply Sequence.IsCauchy.neg
    simpa
  rw [LIM_neg, <- hlim]
  . grind
  simpa
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  have h1 := Real.isPos_iff (-x)
  have h2: (-x).IsPos ↔ x.IsNeg := by simp_all
  rw [h2] at h1
  convert h1 using 1
  rw [Real.gt_iff, Real.lt_iff]
  constructor
  . intro hneg
    rw [isNeg_def] at hneg
    obtain ⟨a, hbound, hcauchy, hlim⟩ := hneg
    rw [boundedAwayNeg_def] at hbound
    obtain ⟨c, hc, hbound⟩ := hbound
    use (-a)
    constructor
    . rw [boundedAwayPos_def]
      use c
      constructor
      . positivity
      intro n
      specialize hbound n
      simp
      grind
    constructor
    . apply Sequence.IsCauchy.neg
      simpa
    rw [LIM_neg, <- hlim]
    grind
    simpa

  intro hpos
  rw [isPos_def] at hpos
  obtain ⟨a, hbound, hcauchy, hlim⟩ := hpos
  rw [boundedAwayPos_def] at hbound
  obtain ⟨c, hc, hbound⟩ := hbound
  use (-a)
  constructor
  . rw [boundedAwayNeg_def]
    use c
    constructor
    . positivity
    peel hbound with n
    simp
    grind
  constructor
  . apply Sequence.IsCauchy.neg
    simpa
  rw [LIM_neg, <- hlim]
  simp
  simpa

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  rcases trichotomous (x-y) with h1 | h1 | h1
  . right
    right
    grind
  . left
    rw [Real.gt_iff]
    exact h1
  . right
    left
    rw [Real.lt_iff]
    grind

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [Real.lt_iff, Real.gt_iff]
  apply not_pos_neg

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw [Real.gt_iff]
  rw [and_comm]
  have : x - y = 0 <-> x = y:= by
    grind
  rw [<- this]
  apply not_zero_pos

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw [Real.lt_iff]
  rw [and_comm]
  have : x - y = 0 <-> x = y:= by
    grind
  rw [<- this]
  apply not_zero_neg

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by
  rw [Real.lt_iff, Real.gt_iff]
  have h1 := Real.neg_iff_pos_of_neg (x-y)
  rw [h1]
  simp_all

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [lt_iff, isNeg_def] at *
  obtain ⟨a, hbound, hcauchy, hlim⟩ := hxy
  obtain ⟨b, hbound', hcauchy', hlim'⟩ := hyz
  use (a+b)
  constructor
  obtain ⟨c, hc, hbound⟩ := hbound
  . rw [boundedAwayNeg_def]
    use c
    constructor
    . grind
    simp_all
    grind
  constructor
  . apply Sequence.IsCauchy.add
    repeat simpa
  have : x - z = (x-y) + (y-z) := by ring
  rw [<- LIM_add,<- hlim, <- hlim']
  ring_nf
  repeat simpa

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff, isNeg_def] at *
  ring_nf
  exact hxy

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [Real.le_iff] at *
  rcases hxy with h | h
  . left
    have h1 := Real.mul_lt_mul_right h hz
    simpa [mul_comm]
  rw [h]
  right
  rfl

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  obtain ⟨a, hbound, hcauchy, hlim⟩ := hx
  obtain ⟨b, hbound', hcauchy', hlim'⟩ := hy
  rw [boundedAwayPos_def] at hbound
  rw [boundedAwayNeg_def] at hbound'
  obtain ⟨c, hc, hbound⟩ := hbound
  obtain ⟨c', hc', hbound'⟩ := hbound'
  use (a * b)
  constructor
  . use (c*c')
    constructor
    . positivity
    simp
    intro n
    specialize hbound n
    specialize hbound' n
    simp_all
    have prod_neg: a n * b n < 0 := by
      have : a n > 0 := by
        grind
      have : b n < 0 := by
        grind
      (expose_names; exact (Rat.mul_neg_iff_of_pos_left this_1).mpr this)
    have : |a n * b n| ≥ c * c' := by
      simp_all
      gcongr
      grind
      grind
    rw [abs_eq_neg_self.mpr (by grind)] at this
    grind
  constructor
  . apply Sequence.IsCauchy.mul
    repeat simpa
  rw [hlim, hlim', LIM_mul]
  repeat simpa

open Classical in
/--
  (Not from textbook) {name}`Real` has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := fun a => by
    right
    rfl
  le_trans := fun a b c hab hbc => by
    rw [le_iff] at *
    rcases hab with hab | hab
    <;> rcases hbc with hbc | hbc
    . left
      exact lt_trans hab hbc
    . left
      rw [<- hbc]
      exact hab
    . left
      rw [hab]
      exact hbc
    . right
      simp_all
  lt_iff_le_not_ge := by
    intro a b
    constructor
    . intro h
      constructor
      . left
        exact h
      intro h'
      rcases h' with h' | h'
      . rw [lt_iff] at *
        simp_all
        have := Real.not_pos_neg (b-a)
        simp_all
      rw [h'] at h
      rw [lt_iff] at h
      simp_all
      have := Real.nonzero_of_pos h
      contradiction
    intro ⟨hab, hba⟩
    rw [le_iff] at hab
    rcases hab with hab | hab
    . exact hab
    . rw [hab] at hba
      have : b ≤ b := by
        right
        rfl
      simp_all
  le_antisymm := by
    intro a b hab hba
    rw [le_iff] at *
    rcases hab with hab | hab
    <;> rcases hba with hba | hba
    . exfalso
      have := Real.not_gt_and_lt a b
      simp_all
    . simp_all
    . simp_all
    . simp_all
  le_total := by
    intro a b
    rcases trichotomous' a b with h | h | h
    . right
      left
      exact h
    . left
      left
      exact h
    . rw [h]
      left
      right
      rfl
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) {name}`LinearOrder`s come with a definition of absolute value {lean (type := "Real → Real")}`(|·|)`.
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  change max x (-x) =  x.abs
  rw [abs]
  rcases trichotomous x with h | h | h
  . simp_all
  . simp_all
    left
    have : -x < 0 := by
      have hneg: (-x).IsNeg := by
        refine (neg_iff_pos_of_neg (-x)).mpr ?_
        simp
        exact h
      rw [lt_iff, isNeg_def] at *
      simp_all
    apply lt_trans this
    rw [lt_iff, isPos_def] at *
    simp_all
  simp_all
  have hneg: x.IsNeg := (Real.neg_iff_pos_of_neg x).mpr h
  rw [if_neg]
  have :-x > x :=by
    rw [gt_iff] at *
    simp_all [isPos_def]
    obtain ⟨a, hbound, hcauchy, hlim⟩ := h
    use (a+a)
    obtain ⟨c, cpos, hc⟩ := hbound
    constructor
    . rw [boundedAwayPos_def]
      use c
      constructor
      grind
      peel hc with n
      simp_all
      grind
    constructor
    . apply Sequence.IsCauchy.add
      repeat simpa
    rw [hlim, sub_eq_add_neg, hlim, LIM_add]
    . repeat simpa
    simpa
  simp_all
  left
  exact this
  intro h
  apply not_pos_neg x
  simp_all

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [div_eq_mul_inv]
  have : y⁻¹.IsPos := inv_of_pos hy
  apply pos_mul
  repeat simpa

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) {name}`Real` has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b ha c
    rw [le_iff] at *
    rcases ha with ha | ha
    . left
      exact add_lt_add_right c ha
    right
    simp_all
  add_le_add_right := by
    intro a b ha c
    rw [le_iff] at *
    rcases ha with ha | ha
    . left
      simp_all [lt_iff]
    right
    simp_all
  mul_lt_mul_of_pos_left := by
    intro a apos b c h
    rw [lt_iff] at *
    simp_all
    rw [<- mul_sub_left_distrib]
    apply pos_mul
    repeat simpa
  mul_lt_mul_of_pos_right := by
    intro c hc a b h
    rw [lt_iff] at *
    simp_all
    rw [<- mul_sub_right_distrib]
    apply pos_mul
    repeat simpa
  le_of_add_le_add_left := by
    intro a b c h
    rw [le_iff] at *
    rcases h with h | h
    . left
      have := add_lt_add_right (-a) h
      ring_nf at this
      exact this
    right
    grind
  zero_le_one := by
    left
    rw [lt_iff]
    simp_all
    use 1
    constructor
    . use 1
      simp_all
    constructor
    . apply Sequence.IsCauchy.const
    have h:= ratCast_def 1
    change 1 = LIM (fun _ ↦ 1)
    rw [<- h]
    simp

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  simp_all
  have hh := Sequence.IsCauchy.harmonic'
  simp at hh
  split_ands
  . apply Sequence.IsCauchy.add
    apply Sequence.IsCauchy.const
    exact hh
  . apply Sequence.IsCauchy.sub
    apply Sequence.IsCauchy.const
    exact hh
  . intro n
    field_simp; ring_nf
    grind
  right
  . have h1 : (LIM fun n ↦ 1 + ((n:ℚ) + 1)⁻¹) = (LIM fun n ↦ (1:ℚ)) + LIM fun n ↦ (↑n + 1)⁻¹ := by
      rw [LIM_add]
      rfl
      apply Sequence.IsCauchy.const
      exact hh
    have h2 : (LIM fun n ↦ 1 - ((n:ℚ) + 1)⁻¹) = (LIM fun n ↦ (1:ℚ)) - LIM fun n ↦ (↑n + 1)⁻¹ := by
      rw [LIM_sub]
      rfl
      apply Sequence.IsCauchy.const
      exact hh
    rw [h1, h2]
    have h3 := Real.LIM.harmonic
    simp at h3
    simp [h3]

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith


lemma Sequence.IsCauchy.ad_hoc_if {a:ℕ → ℚ} {N: ℕ}: ((a: Sequence).IsCauchy) ->((fun n:ℕ ↦ if n ≥ N then a n - q else -k): Sequence).IsCauchy := by
  intro hacauchy
  rw [Sequence.isCauchy_def]
  intro ε hε
  rw [Rat.eventuallySteady_def]
  rw [Sequence.isCauchy_def] at hacauchy
  specialize hacauchy ε hε
  rw [Rat.eventuallySteady_def] at hacauchy
  obtain ⟨N', hN', hsteady⟩ := hacauchy
  rw [Rat.steady_def] at hsteady

  use max N N'
  split_ands
  . have: ((fun n ↦ if n ≥ N then a n - q else -k): Sequence).n₀ = 0:=by
      simp
    rw [this]
    grind
  rw [Rat.steady_def]
  intro n hn m hm
  rw [Rat.Close]
  simp
  rw [if_pos, if_pos, if_pos, if_pos, if_pos, if_pos]
  . simp
    have := hsteady n (by grind) m (by grind)
    rw [Rat.Close] at this
    simp_all
    rw [if_pos, if_pos] at this
    . exact this
    . grind
    . grind
  grind
  grind
  split_ands
  repeat grind

lemma Sequence.equiv_if_eventually_eq {a b:ℕ → ℚ} (N: ℕ):  (∀ n ≥ N, a n = b n) -> Sequence.Equiv a b := by
  intro h
  rw [Sequence.equiv_iff]
  intro ε hε
  use N
  intro n hn
  specialize h n hn
  simp [h]
  grind

theorem Real.rat_between {x y : Real} (hxy : x < y) : ∃ q : ℚ, x < (q : Real) ∧ (q : Real) < y := by
  -- 1. 取代表元（你已经做了）
  obtain ⟨a, hacauchy, hlima⟩ := eq_lim x
  obtain ⟨b, hbcauchy, hlimb⟩ := eq_lim y

  -- 2. 从 x < y 得到 y - x 是正数
  have hxy_pos : (y - x).IsPos := by
    rw [lt_iff] at hxy
    rw [neg_iff_pos_of_neg] at hxy
    simp at hxy
    simpa

  -- 3. 展开 IsPos 定义，得到正有理数间隙
  rw [isPos_def] at hxy_pos
  obtain ⟨c, hcpos, hccauchy, hlimc⟩ := hxy_pos

  -- 4. 关键：y - x = LIM b - LIM a = LIM (b - a)
  have hlim_diff : LIM (b - a) = y - x := by
    rw [hlima, hlimb]
    rw [LIM_sub]
    simpa
    simpa

  -- 5. c 和 b - a 有相同极限，且 c 是 boundedAwayPos
  rw [←hlim_diff] at hlimc
  rw [LIM_eq_LIM] at hlimc  -- c ≈ b - a

  -- 6. 从 c 的 boundedAwayPos 得到某个正下界 k
  rw [boundedAwayPos_def] at hcpos
  obtain ⟨k, hkpos, hcbound⟩ := hcpos

  -- 7. 利用 c ≈ b - a，找到 N 使得 |(b-a) n - c n| < k/2 对 n ≥ N
  have hequiv := hlimc (k/4) (by positivity)
  obtain ⟨N1, hN1⟩ := hequiv

  -- 8. a 的 Cauchy 条件，控制尾部波动
  have hacauchy' := hacauchy (k/8) (by positivity)
  rcases hacauchy' with ⟨N2, hN2_le, hN2⟩

  -- b 的 Cauchy 条件，控制尾部波动
  have hbcauchy' := hbcauchy (k/8) (by positivity)
  rcases hbcauchy' with ⟨N3, hN3_le, hN3⟩
  lift N3 to ℕ using hN3_le

  set N := max N1.toNat (max N2.toNat N3)

  -- 9. 在位置 N 取值
  have hcN := hcbound N
  have hN2' := hN2 N (by simp; omega)

  -- 10. 计算：b N - a N > k/2
  have h_gap : b N - a N > k / 2 := by
    -- 从 c N ≥ k 和 |(b N - a N) - c N| < k/2 推出
    have h1 : |(b N - a N) - c N| < k / 2 := by
      specialize hN1 N ?_ ?_
      . simp
        omega
      . simp
        omega
      simp [Rat.Close] at hN1
      rw [if_pos, if_pos] at hN1
      linarith
      . omega
      . omega
    have h2 : c N ≥ k := hcN
    -- |X - c| < k/2 且 c ≥ k 意味着 X > k/2
    rw [abs_lt] at h1
    linarith

  -- 11. 构造有理数 q
  set q := a N + k / 4  -- 注意：这里用 k/4 更安全

  -- 12. 验证 q 在 a N 和 b N 之间
  have h1 : a N < q := by
    simp [q]
    linarith [hkpos]

  have h2 : q < b N := by
    simp [q]
    linarith [h_gap, hkpos]
  set a' := fun n ↦ if n ≥ N then a n - q else -k
  have ha'bounded_away_neg: (a: True) -> BoundedAwayNeg a' := by
    intro _
    rw [boundedAwayNeg_def]
    use (k/8)
    constructor
    . linarith
    intro n
    simp [a']
    split_ifs
    .
      simp [q]
      have close := hN2' n ?_
      rw [Rat.Close] at close
      simp only [Sequence.n0_coe, ge_iff_le, sup_le_iff, Nat.cast_nonneg, true_and,
        Sequence.eval_coe_at_int, ↓reduceIte, Int.toNat_natCast, dite_eq_ite] at close
      rw [if_pos, if_pos] at close
      have : -k/8 ≤ a N - a n := by
        rw [abs_sub_le_iff] at close
        linarith
      . linarith
      have : N2 ≤ N := by
        simp only [N]
        omega
      . linarith
      . dsimp [N]
        omega
      . dsimp [N]
        omega
    . linarith
  set b' := fun n ↦ if n ≥ N then q - b n else -(k / 8)
  have hb'bounded_away_neg: (_: True) -> BoundedAwayNeg b' := by
    intro _
    rw [boundedAwayNeg_def]
    use (k/8)
    constructor
    . linarith
    intro n
    dsimp [b']
    split_ifs
    .
      have close := hN3 N ?_ n ?_
      simp [Rat.Close] at close
      rw [if_pos, if_pos] at close
      have: q - b N < - k / 4:=by
        calc
            q - b N = a N + k / 4 - b N := by rfl
          _ = k / 4 - (b N - a N) := by ring_nf
          _ < k / 4 - k / 2 := by gcongr
          _ = -k / 4 := by ring_nf
      . rw [abs_sub_le_iff] at close
        have close_1: b N - b n ≤ k / 8 := close.1
        linarith
      . omega
      . omega
      . simp
        omega
      . simp
        omega
    . linarith

  -- 13. 关键：把序列位置的不等式提升到实数不等式
  use q
  constructor
  · rw [lt_iff]
    rw [isNeg_def]
    use (fun n ↦ if n ≥ N then a n - q else -k)
    constructor
    . change BoundedAwayNeg a'
      apply ha'bounded_away_neg
      trivial
    split_ands
    . apply Sequence.IsCauchy.ad_hoc_if
      exact hacauchy
    have : LIM (fun n ↦ if n ≥ N then a n - q else -k) = LIM (fun n ↦ a n - q) := by
      rw [LIM_eq_LIM]
      apply Sequence.equiv_if_eventually_eq N
      intro n hn
      rw [if_pos]
      . exact hn
      . apply Sequence.IsCauchy.ad_hoc_if hacauchy
      . apply Sequence.IsCauchy.sub
        exact hacauchy
        apply Sequence.IsCauchy.const
    rw [this]
    rw [hlima]
    change (LIM fun n ↦ a n) - ↑q = LIM fun n ↦ a n - q
    rw [ratCast_def, LIM_sub]
    rfl
    . exact hacauchy
    . apply Sequence.IsCauchy.const
  ·
    -- 证明 q < y
    rw [lt_iff]
    use (b')
    have hb'equiv: Sequence.Equiv b' (fun n ↦ q - b n) := by
      apply Sequence.equiv_if_eventually_eq N
      intro n hn
      dsimp [b']
      rw [if_pos]
      . exact hn
    have hb'cauchy: (b': Sequence).IsCauchy := by
      rw [Sequence.isCauchy_of_equiv hb'equiv]
      . apply Sequence.IsCauchy.sub
        apply Sequence.IsCauchy.const
        simpa
    split_ands
    . apply hb'bounded_away_neg
      trivial
    . exact hb'cauchy
    rw [hlimb, ratCast_def, LIM_sub]
    have : LIM b' = LIM ((fun x ↦ q) - b)  := by
      rw [LIM_eq_LIM]
      simpa
      simpa
      apply Sequence.IsCauchy.sub
      . apply Sequence.IsCauchy.const
      . exact hbcauchy
    symm
    exact this
    . apply Sequence.IsCauchy.const
    exact hbcauchy
  . apply Sequence.IsCauchy.sub
    exact hbcauchy
    exact hacauchy
  . simpa

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  obtain ⟨q, hq1, hq2⟩ := Real.rat_between (show x-1 < x by grind)
  sorry

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  set ε := (1:Real)
  have hpos : ε.IsPos := by
    simp [ε]
    change ((1:ℚ):Real).IsPos
    rw [Real.pos_of_coe]
    grind
  have h1 := Real.le_mul (ε:=ε) hpos (1/x)
  obtain ⟨N, Npos, hN⟩ := h1
  use N
  split_ands
  grind
  simp [ε] at hN
  norm_cast
  have hN : x⁻¹ * x * (N: Real)⁻¹ < ↑N * x * (N: Real)⁻¹ := by
    gcongr
    rw [isPos_iff] at hx
    exact hx
  have hN : x * x⁻¹ * (↑N)⁻¹ < ↑N * (↑N)⁻¹ * x := by
    grind
  repeat rw [Real.self_mul_inv] at hN
  grind
  . apply Real.nonzero_of_pos
    change ((N:ℚ): Real).IsPos
    rw [Real.pos_of_coe]
    simp
    simpa
  apply Real.nonzero_of_pos
  simpa

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rw [Real.abs_eq_abs, abs]
  rcases trichotomous (x-y) with h | h | h
  . have h: x = y:= by grind
    rw [h]
    simp_all
  . simp_all
    constructor
    .
      have hxy : x>y := by
        exact (gt_iff x y).mpr h
      intro h
      split_ands
      . have : y - x < ε := by
          grind
        grind
      grind
    intro ⟨_, h2⟩
    grind
  . simp_all
    rw [if_neg]
    . constructor
      . have hxy: y> x := by
          apply (gt_iff y x).mpr
          exact h
        intro h
        split_ands
        . grind
        . grind
      intro ⟨h1, h2⟩
      grind
    intro h1
    rw [<- neg_sub] at h
    rw [<- neg_iff_pos_of_neg] at h
    apply not_pos_neg (x-y)
    simp_all

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  constructor
  . intro h
    rw [le_iff] at h
    rcases h with hlt | heq
    . grind
    rcases trichotomous (x-y) with h | h | h
    . grind
    . grind
    split_ands
    . grind
    . grind
  intro ⟨h1, h2⟩
  grind

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor
  . intro h
    by_contra! h1
    rw [lt_iff] at h1
    rw [isNeg_def] at h1
    obtain ⟨a, hbound, hcauchy, hlim⟩ := h1
    rw [boundedAwayNeg_def] at hbound
    obtain ⟨c, hc, hbound⟩ := hbound
    have := Real.LIM_mono hcauchy (Sequence.IsCauchy.const (-c)) hbound
    have : LIM a ≤ -c := by
      rw [ratCast_def]
      convert this
      rw [<- LIM_neg]
      congr
      apply Sequence.IsCauchy.const
    specialize h (c/2) (by positivity)
    rw [<- hlim] at this
    have h: - ↑c / 2 ≤ y - x := by
      grind
    have : - (c / 2) ≤ - (c:Real) := by
      grind
    simp_all
    have : (c:Real) ≤ 0 := by
      grind
    have : 0 < (c:Real) := by
      exact_mod_cast hc
    grind
  intro h ε hε
  grind

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor
  . intro h
    have h1: x ≤ y := by
      rw [<- Real.le_add_eps_iff]
      peel h with ε hε h
      rw [Real.dist_le_iff] at h
      grind
    have h1: y ≤ x := by
      rw [<- Real.le_add_eps_iff]
      peel h with ε hε h
      rw [Real.dist_le_iff] at h
      grind
    grind
  intro h
  rw [h]
  intro ε hε
  grind

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by
      rw [← le_add_eps_iff]
      intro ε hε

      rw [← isPos_iff] at hε
      obtain ⟨N, Npos, hN⟩ := Real.exist_inv_nat_le (hε)
      lift N to ℕ using (by positivity)
      set e := (N:ℚ)⁻¹

      have : LIM a ≤ x + e := by
        suffices _: LIM a - x ≤ e by linarith
        have h1 := hcauchy e (by
          have : (N:ℚ)⁻¹ >0 := by
            simp
            exact_mod_cast Npos
          exact_mod_cast this
        )
        rcases h1 with ⟨N', Nle', hN'⟩
        lift N' to ℕ using Nle'
        rw [Rat.steady_def] at hN'
        set N2 := max N' N
        specialize hN' N2 (by simp [N2])
        set b := fun n ↦ (if n ≥ N2 then a N2 + e else a n)
        set b' := fun n ↦ a N2 + e
        have hbequiv: Sequence.Equiv b b' := by
          apply Sequence.equiv_if_eventually_eq N2
          intro n hn
          simp [b', b]
          intro _
          linarith
        have hbcauchy: (b: Sequence).IsCauchy := by
          rw [Sequence.isCauchy_of_equiv hbequiv]
          . apply Sequence.IsCauchy.const
        have hlimb' : LIM b' = ↑(a N2 + e) := by
          rw [ratCast_def]
        have hlimb: LIM b = LIM b' := by
          rw [LIM_eq_LIM]
          exact hbequiv
          . exact hbcauchy
          rw [← Sequence.isCauchy_of_equiv hbequiv]
          exact hbcauchy
        have : LIM a ≤ LIM b := by
          apply Real.LIM_mono
          exact hcauchy
          . exact hbcauchy
          intro n
          dsimp [b]
          split_ifs
          . specialize hN' n ?_
            . have: ((a: Sequence).from N').n₀ = N' := by
                simp
              rw [this]
              dsimp [N2] at *
              omega
            simp [Rat.Close] at hN'
            rw [if_pos, if_pos] at hN'
            rw [abs_sub_le_iff] at hN'
            dsimp [N2] at *
            . linarith
            . omega
            . omega
          . linarith
        have hlima_estimate: LIM a ≤ ↑(a N2 + e) := by
          rw [← hlimb']
          rw [← hlimb]
          linarith
        have hx_estimate: a N2 ≤ x := by
          specialize h N2
          linarith
        calc
          LIM a - x
          ≤ LIM a - ↑(a N2) := by gcongr
          _ ≤ e := ?_
        suffices _: LIM a  ≤ ↑e + ↑(a N2) by linarith
        convert hlima_estimate
        simp [ratCast_def]
        rw [LIM_add, LIM_add, add_comm]
        apply Sequence.IsCauchy.const
        apply Sequence.IsCauchy.const
        apply Sequence.IsCauchy.const
        apply Sequence.IsCauchy.const
      apply le_trans this
      gcongr
      . dsimp [e] at *
        simp_all
        linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
      have hneg_cauchy: ((fun n ↦ -a n): Sequence).IsCauchy := by
        apply Sequence.IsCauchy.neg
        exact hcauchy
      have h': ∀ n, (fun n ↦ -a n) n ≤ -x := by
        intro n
        simp
        apply h
      have h1 := Real.LIM_of_le hneg_cauchy (h')
      change LIM (- fun n ↦ a n) ≤ -x at h1
      rw [LIM_neg] at h1
      simp at h1
      gcongr
      exact hcauchy

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  rw [max_eq, min_eq]
  simp_all
  split_ifs
  . simp
  simp

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  rw [max_eq, min_eq]
  simp_all
  split_ifs
  . simp
  simp

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  simp [max_eq]
  split_ifs
  <;> grind

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  rw [max_eq]
  grind

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  rw [max_eq]
  grind

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  simp [max_eq]
  split_ifs
  <;> try grind
  . have hinvz: z⁻¹.IsPos := by
      exact inv_of_pos hz
    expose_names
    have h: y * z * z⁻¹ ≤ x * z * z⁻¹:= by
      gcongr
      have : z⁻¹>0:= by
        rw [gt_iff] at *
        grind
      grind
    ring_nf at h
    rw [mul_assoc] at h
    rw [Real.self_mul_inv] at h
    simp at h
    contradiction
    have : z > 0 := by
      exact (isPos_iff z).mp hz
    grind
  . expose_names
    have h1: y * z ≤ x * z := by
      gcongr
      have : z>0:= by
        exact (isPos_iff z).mp hz
      grind
    contradiction
/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  simp [min_eq]
  split_ifs
  <;> grind

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [min_eq]
  grind

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  rw [min_eq]
  grind

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  simp [min_eq]
  split_ifs
  . rfl
  . expose_names
    have h: x * z * z⁻¹ ≤ y * z * z⁻¹ := by
      gcongr
      have := Real.inv_of_pos hz
      have : z⁻¹>0:= by
        exact (isPos_iff z⁻¹).mp this
      grind
    simp [mul_assoc] at h
    rw [Real.self_mul_inv] at h
    simp at h
    grind
    exact Real.nonzero_of_pos hz
  . expose_names
    have h1: x * z  ≤ y * z  := by
      gcongr
      have := Real.inv_of_pos hz
      have : z>0:= by
        exact (isPos_iff z).mp hz
      grind
    contradiction
  . rfl

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  rw [max_eq, min_eq]
  split_ifs
  <;> try grind
  . expose_names
    rcases h with h | h
    . have := Real.inv_of_gt hx hy (by grind)
      simp at h_1
      grind
    grind
  . expose_names
    rcases h_1 with h_1 | h_1
    . simp at h
      have := Real.inv_of_gt hy hx (by grind)
      grind
    simp_all

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  rw [max_eq, min_eq]
  split_ifs
  <;> try grind
  . expose_names
    rcases h with h | h
    . have := Real.inv_of_gt hy hx (by grind)
      simp_all
      grind
    grind
  . expose_names
    rcases h_1 with h_1 | h_1
    . simp at h
      have := Real.inv_of_gt hx hy (by grind)
      grind
    simp_all

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by
    intro a b hab
    simp_all

end Chapter5
