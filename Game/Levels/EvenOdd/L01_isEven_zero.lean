import Game.MyNat.Even

namespace MyNat

World "EvenOdd"
Level 1
Title "Zero is Even"

/--
`isEven n` is a proof that `∃ (t : ℕ), t + t = n.
This means that if you have a goal of the form `isEven n`, you can make
progress with the `use` tactic, and if you have a hypothesis `h : isEven a`,
you can make progress with with `cases h with t ht`.
-/
DefinitionDoc isEven as "isEven"


Introduction"In this level we show that zero is even"


/-- `isEven_zero` is a proof of that zero is even.
-/
TheoremDoc MyNat.isEven_zero as "isEven_zero" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement isEven_zero : IsEven 0 := by
  Hint "0 is even because `t + t = 0`, for `t = 0`.  So you should write `use 0`."
  use 0
  simp

Conclusion"Nice.  Your next task is to show that two is even.  Click \"Next \" to continue."


end MyNat






