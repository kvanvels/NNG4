-- EvenOdd World.
-- This entire world revolves around `∃ (t : ℕ), t + t = n` and `∃` is only
-- introduced in `≤ world` so this needs to go after `≤ world`
-- Furthermore this level is just *painful* (i.e. not actually fun) with no `decide` or `simp_add`
-- so it should also require algorithm world
-- Authors of levels: Kevin Buzzard and Ivan Farabella

import Game.MyNat.Even
import Game.MyNat.Odd
import Game.Levels.AdvMultiplication

namespace MyNat



-- level 1
theorem isEven_zero : IsEven 0 := by
  use 0
  decide

-- level 2
theorem isEven_two : IsEven 2 := by
  use 1
  decide

-- level 3
theorem isEven_add_isEven (a b : ℕ) (ha : IsEven a) (hb : IsEven b)
    : IsEven (a + b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2)
  rw [←ha2,←hb2]
  simp_add

-- level 4
theorem isOdd_one : IsOdd 1 := by
  use 0
  decide


-- level 5
theorem not_isOdd_zero : ¬ IsOdd 0 := by
  rintro ⟨w,hw⟩
  rw [←succ_eq_add_one] at hw
  have h1 := succ_ne_zero (w + w)
  exact h1 hw


-- level 6
theorem isOdd_add_isOdd {a b : ℕ} (ha : IsOdd a) (hb : IsOdd b)
    : IsEven (a + b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2 + 1)
  rw [←ha2,←hb2]
  simp_add

-- level 7
theorem isEven_add_isOdd {a b : ℕ} (ha : IsEven a) (hb : IsOdd b)
    : IsOdd (a + b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2)
  rw [←ha2,←hb2]
  simp_add

-- level 8
theorem IsOdd_add_IsEven (a b : ℕ) (ha : IsOdd a) (hb : IsEven b)
    : IsOdd (a + b) := by
  have h1 :=  isEven_add_isOdd hb ha
  rw [add_comm] at h1
  exact h1



-- level 9
@[simp]
theorem isOdd_succ_iff (a : ℕ) : IsOdd (succ a) ↔ IsEven a := by
  apply Iff.intro
  rintro ⟨w,hw⟩
  rw [←succ_eq_add_one] at hw
  have h1 := succ_inj (w + w) a hw
  use w
  exact h1
  rintro ⟨w,hw⟩
  use w
  rw [hw]
  rw [succ_eq_add_one]
  rfl


-- level 10
-- this is harder because there's a case split in the => direction
@[simp]
theorem isEven_succ_iff (a : ℕ) : IsEven (succ a) ↔ IsOdd a := by 
  apply Iff.intro
  rw [←isOdd_succ_iff]
  intro ⟨w,hw⟩
  rw [←succ_eq_add_one] at hw
  have h1 := succ_inj (w + w) (succ a) hw
  cases w with l
  exfalso
  rw [add_zero] at h1
  have h2 := zero_ne_succ a
  exact h2 h1
  use l
  rw [succ_add] at h1
  have h3 := succ_inj (l + succ l) a h1
  rw [←h3]
  rw [succ_eq_add_one,add_assoc]
  rfl
  intro ⟨w,hw⟩
  use w + 1
  rw [←hw,succ_eq_add_one]
  simp_add

-- Boss level comes in two parts: we have to prove that every number
-- is exactly one of even and odd!

-- level 11
theorem isEven_or_isOdd (n : ℕ) : IsEven n ∨ IsOdd n := by
  induction n with k hk
  left
  exact isEven_zero
  rcases hk with (hk | hk)
  right
  rw [←isOdd_succ_iff] at hk
  exact hk
  left
  rw [←isEven_succ_iff] at hk
  exact hk


theorem not_isEven_and_isOdd (n : ℕ) : ¬ (IsEven n ∧ IsOdd n) := by
  induction n with k hk
  intro h0
  exact not_isOdd_zero h0.right
  simp
  intro h0 h1
  exact hk (And.intro h1 h0)

theorem T0 (n : ℕ) : IsEven n ↔ ¬IsOdd n := by
  induction n with k hk
  apply Iff.intro
  intro _h0
  exact not_isOdd_zero
  intro _h0
  exact isEven_zero
  simp
  rw [hk,not_not]
  rfl

instance decIsOdd : DecidablePred IsOdd
| 0 => isFalse <| by
  exact not_isOdd_zero
| succ j =>
  match decIsOdd j with
  | isTrue (h : IsOdd j) => isFalse <| by
    simp
    intro h0
    exact (not_isEven_and_isOdd j) ⟨h0,h⟩
  | isFalse (h : ¬IsOdd j) => isTrue <| by
    simp
    exact Or.resolve_right (isEven_or_isOdd j) h

instance decIsEven : DecidablePred IsEven
| 0 => isTrue <| by
  exact isEven_zero
| succ j =>
  match decIsEven j with
  | isTrue (h : IsEven j) => isFalse <| by
    simp
    intro h0
    exact (not_isEven_and_isOdd j) (And.intro h h0)
  | isFalse (h : ¬IsEven j) => isTrue <| by
    simp
    exact Or.resolve_left (isEven_or_isOdd j)  h

-- level 13
theorem isOdd_mul_isOdd {a b : ℕ} (ha : IsOdd a) (hb : IsOdd b)
    : IsOdd (a * b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2 +  a2 * b2 + a2 * b2)
  rw [←ha2,←hb2]
  rw [mul_add,mul_add,mul_one,add_mul]
  rw [one_mul]
  rw [add_mul]
  simp_add

theorem isEven_mul_of_isEven_left {a b : ℕ} (ha : IsEven a)
    : IsEven (a * b) := by
  rcases ha with ⟨a2,ha2⟩
  rw [←ha2]
  use (a2 * b)
  rw [add_mul]
  rfl

theorem isEven_mul_of_isEven_right {a b : ℕ} (hb : IsEven b)
    : IsEven (a * b) := by
  rcases hb with ⟨b2,hb2⟩
  rw [←hb2]
  use (a * b2)
  rw [mul_add]
  rfl

theorem mul_isOdd_iff {a b : ℕ} : IsOdd (a * b) ↔ IsOdd a ∧ IsOdd b := by
  apply Iff.intro
  intro h0
  rcases (isEven_or_isOdd a) with (h|h)
  have h1 : IsEven (a * b) := isEven_mul_of_isEven_left h
  have h2 := not_isEven_and_isOdd (a * b)
  exfalso
  exact h2 ⟨h1,h0⟩
  rcases (isEven_or_isOdd b) with (h1|h1)
  exfalso
  have h2 : IsEven (a * b) := isEven_mul_of_isEven_right h1
  have h3 := not_isEven_and_isOdd (a * b)
  exact h3 ⟨h2,h0⟩
  apply And.intro h h1
  intro h0
  exact isOdd_mul_isOdd h0.left h0.right

theorem mul_isEveniff {a b : ℕ} : IsEven (a * b) ↔ IsEven a ∨ IsEven b := by
  apply Iff.intro
  intro h0
  rcases (isEven_or_isOdd a) with (ha|ha)
  left
  exact ha
  rcases (isEven_or_isOdd b) with (hb|hb)
  right
  exact hb
  exfalso
  have h1 : IsOdd a ∧ IsOdd b :=  ⟨ha,hb⟩
  rw [←mul_isOdd_iff] at h1
  have h2 := not_isEven_and_isOdd (a * b)
  apply h2
  apply And.intro h0 h1
  rintro (ha|hb)
  exact (isEven_mul_of_isEven_left ha)
  exact (isEven_mul_of_isEven_right hb)

#print mul_isEveniff

/-




After multiplication world (which we never used here) there are more
tedious levels e.g.

IsOdd_mul_IsOdd,
`IsEven a → IsEven (a * b)` etc

-/

end MyNat
