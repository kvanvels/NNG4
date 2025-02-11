import Game.Levels.EvenOdd
import Game.Levels.AdvEvenOdd.L03_isOdd_mul_isOdd


World "AdvEvenOdd"
Level 4
Title "TITLE"

namespace MyNat

Introduction"In this level we"


/-- `mul_isOdd_iff a b  ` is a proof of `isOdd (a * b) ↔ isOdd a ∧ isOdd b`.
-/
TheoremDoc MyNat.mul_isOdd_iff as "mul_isOdd_iff" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement mul_isOdd_iff (a b : ℕ) : isOdd (a * b) ↔ isOdd a ∧ isOdd b := by
  apply Iff.intro
  intro h0
  rcases (MyNat.isEven_or_isOdd a) with (h| h)
  have h1 : isEven (a * b) := isEven_mul_of_isEven_left h
  have h2 := not_isEven_and_isOdd (a * b)
  exfalso
  exact h2 ⟨h1,h0⟩
  cases (isEven_or_isOdd b) with h1 h1
  exfalso
  have h2 : isEven (a * b) := isEven_mul_of_isEven_right h1
  have h3 := not_isEven_and_isOdd (a * b)
  exact h3 ⟨h2,h0⟩
  apply And.intro h h1
  intro h0
  exact isOdd_mul_isOdd a b h0.left h0.right

Conclusion"CONCLUSION"

end MyNat
