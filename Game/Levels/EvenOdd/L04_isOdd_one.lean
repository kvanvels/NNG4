import Game.Levels.EvenOdd.L03_isEven_add_isEven
import Game.MyNat.Odd

World "EvenOdd"
Level 4
Title "One is Odd"


/--`isOdd n` is a proof that `∃ (t : ℕ), t + t + 1 = n`.
This means that if you have a goal of the form `isOdd n`, you can make
progress with the `use` tactic, and if you have a hypothesis `h : isOdd a`,
you can make progress with with `cases h with t ht`.
-/
DefinitionDoc isOdd as "isOdd"

namespace MyNat

Introduction"In this level we"


/-- `isOdd_one` is a proof of `IsOdd 1`.
-/
TheoremDoc MyNat.isOdd_one as "isOdd_one" in "EvenOdd"

/-- One is odd. -/
theorem isOdd_one : IsOdd 1 := by
  use 0
  decide

Conclusion"CONCLUSION"

end MyNat
