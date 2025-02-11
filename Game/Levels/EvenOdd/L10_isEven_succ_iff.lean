import Game.Levels.EvenOdd.L09_isOdd_succ_iff

World "EvenOdd"
Level 10
Title "The successor to a number is even iff the original number is odd."

namespace MyNat

Introduction"In this level we show that the successor to a number is
even if and only iff the original number is odd.  This is the obvious
partner to the previous level.  This proof is a little more involved
than the previous level.  "


/-- `isEven_succ_iff a` is a proof of `isEven (succ a) ↔ isOdd a`.
-/
TheoremDoc MyNat.isEven_succ_iff as "isEven_succ" in "EvenOdd"

/-- A proof that the successor to a number `a` is even is
equivalent to a proof that `a` is odd.
-/
@[simp]
Statement isEven_succ_iff (a : ℕ) : isEven (succ a) ↔ isOdd a := by
  apply Iff.intro
  rw [←isOdd_succ_iff]
  intro ⟨w,hw⟩
  rw [←succ_eq_add_one] at hw
  have h1 := succ_inj (w + w) (succ a) hw
  cases w with l
  exfalso
  rw [add_zero] at h1
  have h2 := zero_ne_succ a
  exact h2 h1
  use l
  rw [succ_add] at h1
  have h3 := succ_inj (l + succ l) a h1
  rw [←h3]
  rw [succ_eq_add_one,add_assoc]
  rfl
  intro ⟨w,hw⟩
  use w + 1
  rw [←hw,succ_eq_add_one]
  simp_add


Conclusion"
Note that we have imformed the simplifier about this equivalence.  As such,
the `simp` tactic will perform this transformation for you.

We are ready to proceed to the boss level.  The boss level
comes in two parts.  First you have to prove that every number is even or odd.  And then show that no number is both even and odd."

end MyNat
