import Game.MyNat.PeanoAxioms
import Game.MyNat.Addition
import Game.Levels.Implication
import Game.Tactic.Decide
import Game.Levels.Algorithm



namespace MyNat

def le (a b : ℕ) :=  ∃ (c : ℕ), b = a + c

-- Another choice is to define it recursively:
-- (kb) note: I didn't choose this option because tests showed
-- that mathematicians found it a lot more confusing than
-- the existence definition.

-- | le 0 _
-- | le (succ a) (succ b) = le ab

-- notation
instance : LE MyNat := ⟨MyNat.le⟩

instance leDec : DecidableRel ((· ≤ ·) : ℕ  → ℕ → Prop) 
| 0, l => isTrue <| by
  use l
  rw [zero_add l]
  rfl
| succ j, 0 => isFalse <| by
  rintro ⟨n,hn⟩
  rw [succ_add] at hn
  have h1 := zero_ne_succ (j + n)
  exact h1 hn
| succ j, succ k =>
  match leDec j k with
  | isTrue (h : j ≤ k) => isTrue <| by
    cases h with θ hθ
    use θ
    rw [succ_add,hθ]
    rfl
  | isFalse (h : ¬(j ≤ k) ) => isFalse <| by
    intro ⟨θ,hθ⟩
    apply h
    use θ
    rw [succ_add] at hθ
    have h1 := succ_inj k (j + θ) hθ
    exact h1


end MyNat
