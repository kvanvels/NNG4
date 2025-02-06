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

instance instDecidableLt : DecidableRel MyNat.lt
| l,0 => isFalse <| by
  intro h0
  unfold lt at h0
  rcases h0 with ⟨aa,h1⟩
  rw [succ_add] at h1
  have h2 := succ_ne_zero (l + aa)
  exact h2 h1.symm

| 0, succ a => isTrue <| by
  use a
  rw [succ_add,zero_add]
  rfl
| succ a, succ b =>
  match instDecidableLt a b with
  | isTrue (h : a.succ ≤ b) => isTrue <| by
    rcases h with ⟨ll,h⟩
    use ll
    rw [h]
    rw [succ_add,succ_add,succ_add]
    rfl
  | isFalse (h : ¬(succ a ≤ b))  => isFalse <| by
    rintro ⟨ll,h0⟩
    apply h
    use ll
    rw [succ_add] at h0
    have h1 := succ_inj (b) (succ a + ll) h0
    exact h1

end MyNat
