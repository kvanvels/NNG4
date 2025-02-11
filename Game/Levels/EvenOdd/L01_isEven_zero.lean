import Game.MyNat.Even

namespace MyNat

World "EvenOdd"
Level 1
Title "Zero is Even"

/--
`IsEven n` is a proof that `∃ (t : ℕ), t + t = n.
This means that if you have a goal of the form `isEven n`, you can make
progress with the `use` tactic, and if you have a hypothesis `h : isEven a`,
you can make progress with with `cases h with t ht`.
-/
DefinitionDoc isEven as "isEven"


Introduction"In this level we show that we define `isEven`, a
predicate on the natural numbers, and then prove `isEven 0`.

For a natural number `n` we have `isEven n`,
if (and only if) there exists a `t : ℕ` such that `t + t = n`.

So if `isEven n` is the goal, you will need to employ a `use` tactic
and supply the correct `t`.  Alternatively, if you have a hypothesis
`h1 : isEven n`, then you can employ the `cases` tactic as `cases h1 with t
ht`, to split the hypothesis into its parts.

Your first task is to show that zero is even"


/-- `isEven_zero` is a proof of that zero is even.
-/
TheoremDoc MyNat.isEven_zero as "isEven_zero" in "EvenOdd"

/-- Zero is even. -/
Statement isEven_zero : isEven 0 := by
  Hint "0 is even because `t + t = 0`, for `t = 0`.
  So you should write `use 0`."
  use 0
  simp

Conclusion"My proof:
```
use 0
simp
```
Your next task is to show that two is even.  Click
\"Next \" to continue."

end MyNat






