import Game.Levels.AdvEvenOdd.L06_mul_isOdd_iff


World "AdvEvenOdd"
Level 7
Title "TITLE"

namespace MyNat

IntroduCtion"In this level we"


/-- `mul_isEven_iff` is a proof of ``.
-/
TheoremDoc MyNat.mul_isEven_iff as "mul_isEven_iff" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement mul_isEven_iff (a b : ℕ) : isEven (a * b) ↔ isEven a ∨ isEven b := by
  apply Iff.intro
  intro h0
  rcases (isEven_or_isOdd a) with (ha|ha)
  left
  exact ha
  rcases (isEven_or_isOdd b) with (hb|hb)
  right
  exact hb
  exfalso
  have h1 : isOdd a ∧ isOdd b :=  ⟨ha,hb⟩
  rw [←mul_isOdd_iff] at h1
  have h2 := not_isEven_and_isOdd (a * b)
  apply h2
  apply And.intro h0 h1
  rintro (ha|hb)
  exact (isEven_mul_of_isEven_left ha)
  exact (isEven_mul_of_isEven_right hb)

Conclusion"CONCLUSION"

end MyNat
