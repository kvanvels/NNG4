import Game.Levels.EvenOdd.L10_isEven_succ_iff

World "EvenOdd"
Level 11
Title "Every number is either even or odd."

namespace MyNat

Introduction"In this level we show that every number is either even or
odd."


/-- `isEven_or_isOdd n` is a proof of `IsEven n ∨ IsOdd n`.
-/
TheoremDoc MyNat.isEven_or_isOdd as "isEven_or_isOdd" in "EvenOdd"

/--
For every number `n`, `n` is even or `n` is odd.
-/
Statement isEven_or_isOdd (n : ℕ) : isEven n ∨ isOdd n := by
  Hint "There is a hidden hint if you get stuck."
  Hint (hidden := true) "Try induction on `n`."
  induction n with k hk
  left
  exact isEven_zero
  cases hk with hk  hk
  right
  rw [←isOdd_succ_iff] at hk
  exact hk
  left
  rw [←isEven_succ_iff] at hk
  exact hk


Conclusion"Congrats!  Your next task is to show that it is not
possible for a mumber to be both even and odd"

end MyNat
