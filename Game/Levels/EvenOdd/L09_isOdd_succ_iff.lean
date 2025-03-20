import Game.Levels.EvenOdd.L08_isOdd_add_isEven


World "EvenOdd"
Level 9
Title "The successor to a number is odd iff the original number is even"

namespace MyNat

Introduction"In this level we show that the successor to a number is odd if
and only iff the original number is even."


/-- `isOdd_succ_iff n` is a proof of of `IsOdd (succ a) ↔ IsEven a`.
-/
TheoremDoc MyNat.isOdd_succ_iff as "isOdd_succ_iff" in "EvenOdd"

/-- A proof that that the successor of `a` is odd is equivalent to a
proof that `a` is even -/
@[simp]
Statement isOdd_succ_iff (a : ℕ) : isOdd (succ a) ↔ isEven a := by
  constructor
  intro hw
  cases hw with w hw
  rw [←succ_eq_add_one] at hw
  have h1 := succ_inj (w + w) a hw
  use w
  exact h1
  rintro ⟨w,hw⟩
  use w
  rw [hw]
  rw [succ_eq_add_one]
  rfl


Conclusion"We have notified the simplifier about this theorem so the
`simp` tactic will perform this transformation for you in subsequent levels."

end MyNat
