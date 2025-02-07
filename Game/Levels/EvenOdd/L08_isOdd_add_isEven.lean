import Game.Levels.EvenOdd.L07_isEven_add_isOdd

World "EvenOdd"
Level 8
Title "The sum of an odd number and an even number is odd."

namespace MyNat

Introduction"In this level we show that the sum of an even number and
an odd number is odd.  This should be shockingly similiar to the previous
level, so you are encouraged to reuse that proof."


/-- `isOdd_add_isEven {a b : ℕ) (ha : IsOdd a) (hb : IsEven b)`` is a proof of
`isOdd (a + b)`.
-/
TheoremDoc MyNat.isOdd_add_isEven as "isOdd_add_isEven" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement isOdd_add_isEven {a b : ℕ} (ha : IsOdd a) (hb : IsEven b)
    : IsOdd (a + b) := by
  have h1 :=  isEven_add_isOdd hb ha
  rw [add_comm] at h1
  exact h1

Conclusion"CONCLUSION"

end MyNat
