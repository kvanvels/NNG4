import Game.Levels.AdvEvenOdd.L03_isEven_mul_of_isEven_left

World "AdvEvenOdd"
Level 4
Title "TITLE"

namespace MyNat

Introduction"In this level we show that product of a natural number and an even
natural number is even"


/-- `isEven_mul_of_isEven_right (a b : ℕ) (hb : isEven b)` is a proof
of `isEven (a * b)`.  -/
TheoremDoc MyNat.isEven_mul_of_isEven_right as "isEven_mul_of_isEven_right"
  in "EvenOdd"

/-- The product of an even natural number and a natural number is even -/
Statement isEven_mul_of_isEven_right {a b : ℕ} (hb : isEven b)
    : isEven (a * b) := by
  cases hb with b2 hb2
  rw [←hb2]
  use (a * b2)
  rw [mul_add]
  rfl


Conclusion"
My proof:
```
  cases hb with b2 hb2
  rw [←hb2]
  use (a * b2)
  rw [mul_add]
  rfl
```
"

end MyNat
