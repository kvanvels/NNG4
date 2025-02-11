import Game.Levels.AdvMultiplication
import Game.Levels.EvenOdd

World "AdvEvenOdd"
Level 1
Title "TITLE"

namespace MyNat

Introduction"In this level we show that product of an natural number and an even
natural number is even"


/-- `isEven_mul_of_isEven_left (a b : ℕ) (ha : isEven a)` is a proof
of `isEven (a * b)`.  -/
TheoremDoc MyNat.isEven_mul_of_isEven_left as "isEven_mul_of_isEven_left"
  in "EvenOdd"

/-- The product of an even natural number and a natural number is even -/
Statement isEven_mul_of_isEven_left {a b : ℕ} (ha : isEven a)
    : isEven (a * b) := by
  cases ha with a2 ha2
  rw [←ha2]
  use (a2 * b)
  rw [add_mul]
  rfl


Conclusion"
My proof:
```
  cases ha with a2 ha2
  rw [←ha2]
  use (a2 * b)
  rw [add_mul]
  rfl
```
"

end MyNat
