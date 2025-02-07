import Game.Levels.EvenOdd.L08_isOdd_add_isEven


World "EvenOdd"
Level 9
Title "The successor to a number is odd iff the original number is even"

namespace MyNat

Introduction"In this level we show that the successor to a number is odd if
and only iff the original number is even."


/-- `isOdd_succ_iff n` is a proof of of `IsOdd (succ a) ↔ IsEven a`.
-/
TheoremDoc MyNat.isOdd_succ_iff as "isOdd_succ_iff" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
@[simp]
Statement isOdd_succ_iff (a : ℕ) : IsOdd (succ a) ↔ IsEven a := by
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


Conclusion"We have notified the simplifier about this theorem so it
will perform these simplifications for you."

end MyNat
