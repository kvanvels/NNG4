import Game.Levels.EvenOdd.L04_isOdd_one


World "EvenOdd"
Level 5
Title "Zero is not odd"

namespace MyNat

Introduction"In this level we show that zero is not odd."


/-- `not_isOdd_zero` is a proof of `¬IsOdd 0`.
-/
TheoremDoc MyNat.not_isOdd_zero as "not_isOdd_zero" in "EvenOdd"

/-- Zero is not odd. -/
Statement not_isOdd_zero :  ¬(isOdd 0) := by
  intro h
  cases h with w hw
  rw [←succ_eq_add_one] at hw
  have h1 := succ_ne_zero (w + w)
  exact h1 hw



Conclusion"Nice job.  The next three levels are similar to
`isEven_add_isEven`.  Your task in the next level is to show that sum
of two odd number is even."


end MyNat
