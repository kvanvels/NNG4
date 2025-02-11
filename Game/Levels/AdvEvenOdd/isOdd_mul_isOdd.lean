import Game.Levels.AdvEvenOdd.L02_isEven_mul_of_isEven_right

World "AdvEvenOdd"
Level 3
Title "isOdd_mul_isOdd"

namespace MyNat

Introduction"In this level we show that the product of two odd natural numbers is odd."


/-- `isOdd_mul_isOdd (a b : ℕ) (ha : isOdd a) (hb : isOdd b)` is a proof of `isOdd (a * b)`.
-/
TheoremDoc MyNat.isOdd_mul_isOdd as "isOdd_mul_isOdd" in "EvenOdd"

/-- The product of two odd natural numbers is odd -/
Statement  isOdd_mul_isOdd (a b : ℕ) (ha : isOdd a) (hb : isOdd b) :
    isOdd (a * b) := by
  cases ha with a2 ha2
  cases hb with b2 hb2
  use (a2 + b2 +  a2 * b2 + a2 * b2)
  rw [←ha2,←hb2]
  rw [mul_add,mul_add,mul_one,add_mul]
  rw [one_mul]
  rw [add_mul]
  simp_add

Conclusion"CONCLUSION"

end MyNat
