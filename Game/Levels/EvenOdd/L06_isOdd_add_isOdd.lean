import Game.Levels.EvenOdd.L05_not_isOdd_zero

World "EvenOdd"
Level 6
Title "The sum of two odd numbers is even"

namespace MyNat

Introduction"In this level we show that sum of two odd numbers is even"


/-- `isOdd_add_isOdd {a b : ℕ} (ha : isOdd a) (hb : isOdd b)` is a proof that
`isEven (a + b)`-/
TheoremDoc MyNat.isOdd_add_isOdd as "isOdd_add_isOdd" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement isOdd_add_isOdd {a b : ℕ} (ha : IsOdd a) (hb : IsOdd b)
    : IsEven (a + b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩
  use (a2 + b2 + 1)
  rw [←ha2,←hb2]
  simp_add


Conclusion"CONCLUSION"

end MyNat
