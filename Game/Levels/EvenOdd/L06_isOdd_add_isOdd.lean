import Game.Levels.EvenOdd.L05_not_isOdd_zero

World "EvenOdd"
Level 6
Title "The sum of two odd numbers is even"

namespace MyNat

Introduction"In this level we show that sum of two odd numbers is even"


/-- `isOdd_add_isOdd {a b : ℕ} (ha : isOdd a) (hb : isOdd b)` is a proof that
`isEven (a + b)`-/
TheoremDoc MyNat.isOdd_add_isOdd as "isOdd_add_isOdd" in "EvenOdd"

/-- If we have a proof that `a` is odd and a proof that `b` is odd, then
`a + b` is odd. -/
Statement isOdd_add_isOdd {a b : ℕ} (ha : isOdd a) (hb : isOdd b)
    : isEven (a + b) := by
  cases ha with a2 ha2
  cases hb with b2 hb2
  use (a2 + b2 + 1)
  rw [←ha2,←hb2]
  simp_add


Conclusion"
My Proof:
```
  cases ha with a2 ha2
  cases hb with b2 hb2
  use (a2 + b2 + 1)
  rw [←ha2,←hb2]
  simp_add
```
"
end MyNat
