import Game.Levels.EvenOdd.L01_isEven_zero

World "EvenOdd"
Level 2
Title "Two is Even"

namespace MyNat

Introduction"In this level we show that two is even."


/-- `isEven_two` is a proof of that `isEven 2`.
-/
TheoremDoc MyNat.isEven_two as "isEven_two" in "EvenOdd"

/--Two is even.-/
Statement isEven_two : isEven 2 := by
  use 1
  decide

Conclusion"
My Proof:
```
use 1
decide
```
"


