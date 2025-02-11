import Game.Levels.EvenOdd.L06_isOdd_add_isOdd

World "EvenOdd"
Level 7
Title "The sum of an even number and an odd number is odd."

namespace MyNat

Introduction"In this level we show that the sum of an even number and
an odd number is odd.  The idea of the proof is a the same as the
previous proof so we won't give hints here."


/-- `isEven_add_isOdd {a b :ℕ) (ha : IsEven a) (hb : isOdd b)` is a proof of
`isOdd (a + b)`.-/
TheoremDoc MyNat.isEven_add_isOdd as "isEven_add_isOdd" in "EvenOdd"

/-- If we have a proof that `a` is even and a proof that `b` is odd, then
`a + b` is odd. -/
Statement isEven_add_isOdd {a b : ℕ} (ha : isEven a) (hb : isOdd b)
    : isOdd (a + b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2)
  rw [←ha2,←hb2]
  simp_add

Conclusion"
My proof looks shockingly similar to my previous proof,
```
cases ha with a2 ha2
cases hb with b2 hb2
use (a2 + b2)
rw [←ha2,←hb2]
simp_add
```
"

end MyNat
