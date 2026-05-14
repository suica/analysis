import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of {lean}`ℕ`.

- Equivalence with the Mathlib integers {name}`_root_.Int` (or {lean}`ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro x
      rfl
    symm := by
      intro x y h
      symm
      exact h
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    exact mul_congr (Quotient.eq.mpr h1) (Quotient.eq.mpr h2)
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor
  . intro h
    exact (natCast_inj n 0).mp h
  intro h
  simp_all

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp_all [eq]
    omega
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_all [add_eq]
    ring_nf
    ) (by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    rw [ofNat_eq]
    simp only [add_eq, zero_add]
    ) (by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp [ofNat_eq]
    rw [Int.neg_eq]
    simp [add_eq, eq]
    ring
    )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro x y
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    simp [add_eq, eq]
    ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro x y
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    simp [mul_eq, eq]
    ring
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp [ofNat_eq, mul_eq]
  mul_one := by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp [ofNat_eq, mul_eq]

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_all [add_eq, mul_eq, eq]
    ring
  right_distrib := by
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_all [add_eq, mul_eq, eq]
    ring
  zero_mul := by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp_all [ofNat_eq, mul_eq]
  mul_zero := by
    intro x
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    simp_all [ofNat_eq, mul_eq]

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  simp [sub_eq, natCast_eq, neg_eq, add_eq]

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  cases trichotomous a
  . simp_all
  . rename_i h1
    rcases h1 with h2 | h2
    . rcases h2 with ⟨k, hpos, hk⟩
      right
      obtain ⟨ e, f, rfl ⟩ := eq_diff b
      simp_all [ofNat_eq, natCast_eq, mul_eq, eq]
      cases h
      . simp_all
      simp_all
    right
    rcases h2 with ⟨k, hpos, hk⟩
    obtain ⟨ e, f, rfl ⟩ := eq_diff b
    simp_all [ofNat_eq, natCast_eq, neg_eq, eq, mul_eq]
    cases h
    . simp_all
    simp_all

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have h1: a * c - b*c = 0 := by simp_all
  have h2: (a + -b) *c = 0 := by
    rw [right_distrib]
    simp_all
  have h3 := mul_eq_zero h2
  obtain ⟨ a1, b1, rfl ⟩ := eq_diff a
  obtain ⟨ c1, d1, rfl ⟩ := eq_diff b
  rcases h3 with h | h
  . simp_all [neg_eq, add_eq, ofNat_eq, eq]
    ring
  contradiction

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor
  . intro h
    rcases h with ⟨⟨k, hk⟩, hneq⟩
    simp_all [natCast_eq, ofNat_eq, eq]
  intro h
  rcases h with ⟨k, hneq, hk⟩
  simp_all [natCast_eq]
  rw [lt_iff]
  constructor
  use k
  simp_all [natCast_eq]
  obtain ⟨ a1, b1, rfl ⟩ := eq_diff a
  intro h
  simp [ofNat_eq, eq] at h
  contradiction

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rcases h with ⟨⟨k, hk⟩, hneq⟩
  constructor
  . use k
    simp_all
    ring
  have cancel_right {a b c: Int}: a + b = c + b -> a = c := by
    intro h
    have h1: a + b + -b = c + b + -b:= by
      congr 1
    have h2: a + (b + -b) = c + (b + -b) := by
      ring_nf at *
      exact h1
    simp_all
  intro h
  have h3 := cancel_right h
  contradiction

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rcases hab with ⟨⟨k, hk⟩, hneq⟩
  rcases hc with ⟨⟨i, hi⟩, hneqi⟩
  -- simp_all [natCast_eq, ofNat_eq]
  constructor
  . use (k*i)
    simp [hk, hi]
    ring_nf
  intro h
  have : a = b := by
    apply mul_right_cancel₀ a b c
    exact h
    symm
    simpa
  contradiction

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rcases h with ⟨⟨k, hk⟩, hneq⟩
  rw [hk]
  constructor
  . use k
    ring
  simp_all

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rcases h with ⟨k, hk⟩
  use k
  simp_all

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rcases hab with ⟨⟨k, hk⟩, hneq⟩
  rcases hbc with ⟨⟨i, hi⟩, hneqi⟩
  rw [hk] at hi
  constructor
  . use (k+i)
    simp_all
    ring
  intro h
  rw [h] at hi
  have h: c + - c = c +  ↑k + ↑i -c := by
    congr
  have h2: (0: Int) = ↑k + ↑i := by
    ring_nf at h
    exact h
  have h2: 0 = k + i := by
    simp [natCast_eq, ofNat_eq, eq, add_eq] at h2
    exact h2
  rw [show ↑k = (0: Int) from by
    have := add_eq_zero.mp (symm h2)
    rw [this.left]
    ring ] at hk
  ring_nf at hk
  symm at hk
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rcases trichotomous (a-b) with h | h | h
  . right
    right
    have h1: a - b + b = 0 + b := by
      congr
    ring_nf at *
    exact h1
  . rcases h with ⟨k, kpos, hk⟩
    left
    constructor
    . use k
      rw [<- hk]
      ring
    intro h
    rw [h] at hk
    simp_all [ofNat_eq, natCast_eq, eq]
  rcases h with ⟨k, kpos, hk⟩
  have h: a - b + b = -↑k + b := by congr
  right
  left
  constructor
  . use k
    ring_nf at *
    simp_all
  intro h1
  simp at h
  rw [h1] at hk
  ring_nf at *
  have : 0 = (k: Int) := by simp_all
  simp_all [natCast_eq, ofNat_eq, eq]


/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  intro h
  rcases h with ⟨⟨⟨k, hk⟩, neq⟩, ⟨⟨k2, hk2⟩, neq2⟩⟩
  rw [hk2] at hk
  have h1: a + -a = a + ↑k2 + ↑k + -a := by congr
  have h2: (0: Int) = ↑k2 + ↑k := by
    ring_nf at h1
    exact h1
  simp [natCast_eq, eq, ofNat_eq, add_eq] at h2
  have h3: k2 = (0: Int) := by
    have h := add_eq_zero.mp (symm h2)
    congr
    exact h.left
  rw [h3] at hk2
  ring_nf at *
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  intro ⟨⟨a, hneq⟩, heq⟩
  symm at heq
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  intro ⟨⟨a, hneq⟩, heq⟩
  contradiction

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw [le_iff_exists_add] at h
        rcases h with ⟨k, hk⟩
        use k
        simp_all [natCast_eq, add_eq, eq]
        ring_nf at *
        simp_all
      | isFalse h =>
        apply isFalse
        rw [not_le] at h
        rw [lt_iff_exists_add] at h
        rcases h with ⟨w, ⟨wpos, h⟩⟩
        intro h'
        rcases h' with ⟨i, hi⟩
        simp_all [natCast_eq, add_eq, eq]
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor
  . intro h
    have h1 := h 0
    ring_nf at h1
    exact symm h1
  intro h
  simp_all


/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := fun x => by
    use 0
    simp_all
  le_trans := fun a b c => by
    intro h1 h2
    rcases h1 with ⟨k, hk⟩
    rcases h2 with ⟨k', hk'⟩
    use k+k'
    simp_all
    ring
  lt_iff_le_not_ge := fun a b => by
    constructor
    intro h
    rcases h with ⟨haleb, neq⟩
    constructor
    . exact haleb
    intro h
    rcases h with ⟨k, hk⟩
    by_cases h: k = 0
    . rw [h] at hk
      simp_all
    rcases haleb with ⟨i, hi⟩
    rw [hi] at hk
    have : ↑i + ↑k = (0: Int) := by
      have : a + - a = a + (i: Int) + (k: Int) + -a := by
        congr
      ring_nf at this
      exact symm this
    have : i = 0 := by
      simp [natCast_eq, ofNat_eq, add_eq, eq] at this
      exact this.left
    have : i = (0: Int) := by
      rw [this]
      ring
    rw [this] at hi
    ring_nf at hi
    symm at hi
    contradiction

    intro ⟨⟨i,hk⟩, hnle⟩
    constructor
    . use i
    intro h
    rw [h] at hnle
    have : b ≤ b := by
      use 0
      simp_all
    contradiction
  le_antisymm := fun a b => by
    intro h1 h2
    rcases h1 with ⟨i, hi⟩
    rcases h2 with ⟨j, hj⟩
    rw [hj] at hi
    have : b + - b = b + ↑j + ↑i + -b := by
      congr
    ring_nf at this

    have {a: Int} {k i : ℕ}: a = a + ↑i + ↑k -> i = 0 ∧ k = 0 := by
      intro h
      have : ↑i + ↑k = (0: Int) := by
        have : a + - a = a + (i: Int) + (k: Int) + -a := by
          congr
        ring_nf at this
        exact symm this
      have h1:i = 0 ∧ k = 0 := by
        simp [natCast_eq, ofNat_eq, add_eq, eq] at this
        exact this
      exact h1
    have j0: j = 0 := by
      have: j =0 ∧ i=0 := by
        apply this
        exact hi
      exact this.left
    rw [j0] at hj
    ring_nf at hj
    exact hj
  le_total := fun a b => by
    rcases trichotomous' a b with h | h | h
    . right
      rcases h with ⟨w, hw⟩
      exact w
    . left
      rcases h with ⟨w, hw⟩
      exact w
    . left
      use 0
      ring_nf
      simp_all
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  rw [neg_mul]
  congr
  rw [one_mul]

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  push_neg
  let P: Int -> Prop :=
    fun x => x ≥ 0
  use P
  constructor
  . constructor
    simp_all [P]
    intro i ih
    simp_all [P]
    apply le_trans ih
    use 1
    simp_all
  use -1
  simp_all [P]
  decide

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  rcases h with ⟨k, hk⟩
  use k*k
  rw [hk]
  ring_nf
  simp_all [natCast_eq]

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases le_total 0 n with h | h
  . apply sq_nonneg_of_pos
    exact h
  suffices h: 0 ≤ (-n) * (-n) from by
    have h1: -n * -n = n * n := by
      rw [neg_mul, mul_neg]
      ring
    rw [<- h1]
    exact h
  apply sq_nonneg_of_pos
  rcases h with ⟨w, h⟩
  use w
  ring_nf
  have h1: 0 + -n = n + ↑w + -n := by congr
  ring_nf at h1
  exact h1

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have h:= sq_nonneg n
  rcases h with ⟨w, h⟩
  rw [h]
  ring_nf
  use w

/--
  Not in textbook: create an equivalence between {name}`Int` and {lean}`ℤ`.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro a b h
    simp_all
    rw [PreInt.eq] at h
    omega)
  invFun: ℤ → Int := fun z =>
    match z with
    | Int.ofNat n => ↑n
    | Int.negSucc n => -↑(n+1)
  left_inv n := by
    simp_all
    refine Quotient.inductionOn n ?_
    intro p
    cases p with
    | mk a b =>
      simp
      by_cases h : b ≤ a
      · have : (a : ℤ) - b = Int.ofNat (a - b) := by
          ring_nf
          simp_all
        rw [this]
        simp
        -- 需要证明 ⟦(a-b,0)⟧ = ⟦(a,b)⟧
        apply Quotient.sound
        rw [PreInt.eq]
        omega
      · have : (a : ℤ) - b = Int.negSucc (b - a - 1) := by
          omega
        rw [this]
        simp
        -- 需要证明 ⟦(0,b-a)⟧ = ⟦(a,b)⟧
        apply Quotient.sound
        rw [PreInt.eq]
        ring_nf
        omega
  right_inv n := by
    cases n with
    | ofNat n =>
    
        simp
    | negSucc n =>
        simp

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

end Section_4_1
