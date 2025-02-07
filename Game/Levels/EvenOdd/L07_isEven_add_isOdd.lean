import Game.Levels.EvenOdd.L06_isOdd_add_isOdd

World "EvenOdd"
Level 7
Title "The sum of an even number and an odd number is odd."

namespace MyNat

Introduction"In this level we show that the sum of an even number
and an odd number is odd."


/-- `isEven_add_isOdd {a b :ℕ) (ha : IsEven a) (hb : IsOdd b)` is a proof of
`IsOdd (a + b)`.-/
TheoremDoc MyNat.isEven_add_isOdd as "isEven_add_isOdd" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement isEven_add_isOdd {a b : ℕ} (ha : IsEven a) (hb : IsOdd b)
    : IsOdd (a + b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2)
  rw [←ha2,←hb2]
  simp_add

Conclusion"CONCLUSION"

end MyNat
