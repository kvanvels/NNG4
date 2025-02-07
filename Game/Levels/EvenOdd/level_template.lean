import Game.Levels.EvenOdd.L0_

World "EvenOdd"
Level n
Title "TITLE"

namespace MyNat

Introduction"In this level we"


/-- `` is a proof of ``.
-/
TheoremDoc MyNat.foo as "foo" in "EvenOdd"

/-- STATEMENT DOCUMENTATION -/
Statement foo (a : ℕ) : a < a := by

Conclusion"CONCLUSION"

end MyNat
