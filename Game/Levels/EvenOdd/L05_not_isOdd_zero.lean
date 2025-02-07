import Game.Levels.EvenOdd.L04_isOdd_one


World "EvenOdd"
Level 5
Title "Zero is not odd"

namespace MyNat

Introduction"In this level we show that zero is not odd."


/-- `not_isOdd_zero` is a proof of `¬IsOdd 0`.
-/
TheoremDoc MyNat.not_isOdd_zero as "not_isOdd_zero" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement not_isOdd_zero : ¬ IsOdd 0 := by
  rintro ⟨w,hw⟩
  rw [←succ_eq_add_one] at hw
  have h1 := succ_ne_zero (w + w)
  exact h1 hw

Conclusion"CONCLUSION"

end MyNat
