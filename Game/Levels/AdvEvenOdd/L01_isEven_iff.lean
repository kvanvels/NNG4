import Game.Levels.AdvMultiplication
import Game.Levels.EvenOdd


World "AdvEvenOdd"
Level 1
Title "isEven_iff'"

namespace MyNat

Introduction"In this level we"


/-- `isEven_iff'` is a proof of ``.
-/
TheoremDoc MyNat.isEven_iff' as "isEven_iff'" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement isEven_iff' (a : ℕ) : isEven a ↔ ∃ k : ℕ, 2 * k = a := by 
  apply Iff.intro
  rintro ⟨w,hw⟩
  use w
  rw [two_eq_succ_one,succ_mul,one_mul]
  exact hw
  rintro ⟨w,hw⟩
  use w
  rw [two_eq_succ_one] at hw
  rw [succ_mul] at hw
  rw [one_mul] at hw
  exact hw

Conclusion"CONCLUSION"

end MyNat
