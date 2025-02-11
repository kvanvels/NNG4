import Game.Levels.AdvEvenOdd.L01_isEven_iff


World "AdvEvenOdd"
Level 2
Title "TITLE"

namespace MyNat

Introduction"In this level we"


/-- `isOdd_iff` is a proof of ``.
-/
TheoremDoc MyNat.isOdd_iff as "isOdd_iff" in "EvenOdd"


/-- STATEMENT DOCUMENTATION -/
Statement isOdd_iff (a : ℕ) : isOdd a ↔ ∃ p : ℕ, 2 * p + 1 = a := by
  apply Iff.intro
  rintro ⟨w,hw⟩
  use w
  rw [two_eq_succ_one,succ_mul,one_mul]
  exact hw
  intro ⟨w,hw⟩
  use w
  rw [two_eq_succ_one,succ_mul,one_mul] at hw
  exact hw

Conclusion"CONCLUSION"

end MyNat
