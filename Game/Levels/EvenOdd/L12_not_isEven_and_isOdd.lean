import Game.Levels.EvenOdd.L11_isEven_or_isOdd

World "EvenOdd"
Level 12
Title "No number is both even and odd."

namespace MyNat

Introduction"In this level we show that no number is both even and odd."


/-- `not_isEven_and_isOdd n` is a proof of '¬(IsEven n ∧ IsOdd n)'.
-/
TheoremDoc MyNat.not_isEven_and_isOdd as "not_isEven_and_isOdd" in "EvenOdd"

/-- For every number `n`, it is not the cases that `n` is even and `n` is odd.
-/
Statement not_isEven_and_isOdd (n : ℕ) : ¬ (isEven n ∧ isOdd n) := by
  Hint (hidden := true) "try induction on `n`"
  induction n with k hk
  intro h0
  exact not_isOdd_zero h0.right
  simp
  intro h0 h1
  exact hk (And.intro h1 h0)

Conclusion"Congrats!"

end MyNat
