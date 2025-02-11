import Game.Levels.EvenOdd.L03_isEven_add_isEven
import Game.MyNat.Odd

World "EvenOdd"
Level 4
Title "One is Odd"


/--`isOdd n` is a proof that `∃ (t : ℕ), t + t + 1 = n`.
This means that if you have a goal of the form `isOdd n`, you can make
progress with the `use` tactic, and if you have a hypothesis `h : isOdd a`,
you can make progress with `cases h with t ht`.
-/
DefinitionDoc isOdd as "isOdd"

namespace MyNat

Introduction"In this level we define `IsOdd`, a predicate on the natural numbers, and you will provide a proof of `IsOdd 1`.

For a natural number `n`, we have `isOdd n`, if (and only if) there exists a `t : ℕ, such that `t + t + 1 = n`.

So if `isOdd n` is the goal, you will need to employ a `use` tactic
and supply the correct `t`.  Alternatively, if you have a hypothesis
`h1 : isOdd n`, then you can employ the `cases` tactic as `cases h1
with t ht` to split the hypothesis into its parts."

/-- `isOdd_one` is a proof of `IsOdd 1`.
-/
TheoremDoc MyNat.isOdd_one as "isOdd_one" in "EvenOdd"

/-- One is odd. -/
theorem isOdd_one : isOdd 1 := by
  use 0
  decide

Conclusion
"My proof:
```
use 0
decide
```"



end MyNat
