import Game.MyNat.LE
import Game.MyNat.PeanoAxioms
import Game.Levels.Algorithm.L07succ_ne_succ -- succ_ne_succ
import Game.Tactic.Decide -- modified decide tactic


namespace MyNat

def lt (a b : ℕ) :=  succ a ≤ b

-- notation
instance : LT MyNat := ⟨MyNat.lt⟩

theorem lt_iff_succ_le (a b : ℕ) : a < b ↔ succ a ≤ b := by
  apply Iff.intro
  exact id
  exact id

instance instDecLT : DecidableRel ((· < · ) : ℕ → ℕ → Prop)
| a,b => leDec (succ a) b

end MyNat
