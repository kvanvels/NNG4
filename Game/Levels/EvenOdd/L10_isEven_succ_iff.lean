import Game.Levels.EvenOdd.L09_isOdd_succ_iff

World "EvenOdd"
Level 10
Title "The successor to a number is even iff the original number is odd."

namespace MyNat

Introduction"In this level we show that the successor to a number is
even if and only iff the original number is odd.  This is the obvious
partner to the previous level."


/-- `isEven_succ_iff a` is a proof of `IsEven (succ a) ↔ IsOdd a`.
-/
TheoremDoc MyNat.isEven_succ_iff as "isEven_succ" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
@[simp]
Statement isEven_succ_iff (a : ℕ) : IsEven (succ a) ↔ IsOdd a := by
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


Conclusion"We are ready to proceed to the boss level.  The boss level
comes in two parts, you have to prove that every number is even or odd
but not both."

end MyNat
