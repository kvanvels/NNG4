import Game.Levels.EvenOdd.L02_isEven_two

World "EvenOdd"
Level 3
Title "The sum of two even numbers is even"

namespace MyNat

Introduction"In this level we show that sum of two even numbers is even."


/-- `isEven_add_isEven (a b : ℕ) (ha : IsEven a) (hb : IsEven b)` is a proof for `isEven (a + b)`"
-/
TheoremDoc MyNat.isEven_add_isEven as "isEven_add_isEven" in "EvenOdd"

/-- The sum of two even numbers is even. -/
Statement isEven_add_isEven (a b : ℕ) (ha : isEven a) (hb : isEven b)
    : isEven (a + b) := by
  cases ha with a2 ha2
  cases hb with b2 hb2
  use (a2 + b2)
  rw [←ha2,←hb2]
  simp_add


Conclusion"
Nice! My Proof:
```
  cases ha with a2 ha2
  cases hb with b2 hb2
  use (a2 + b2)
  rw [←ha2,←hb2]
  simp_add
```
Next we introduce the partner of `isEven`, namely
`isOdd`.  Click \"Next\" to continue.
"

end MyNat
