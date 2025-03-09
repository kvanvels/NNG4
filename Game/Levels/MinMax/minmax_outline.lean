import Game.MyNat.MaxMin
import Game.Levels.LessOrEqual

namespace MyNat

theorem lt_iff_le_not_le (a b : ℕ) : a < b ↔ a ≤ b ∧ ¬(b ≤ a) := by
  apply Iff.intro
  intro ⟨n,hn⟩
  apply And.intro
  use (succ n)
  rw [hn]
  rw [succ_add,add_succ]
  rfl
  intro ⟨m,hm⟩
  rw [hm] at hn
  rw [succ_add,add_assoc,←add_succ] at hn
  have h1 := add_right_eq_self b (succ (m + n)) hn.symm
  have h2 := succ_ne_zero (m + n)
  exact h2 h1
  rintro ⟨⟨θ,hθab⟩,hab2⟩
  rw [hθab] at hab2 ⊢
  cases θ with l
  exfalso
  rw [add_zero] at hab2
  exact hab2 (le_refl a)
  use l
  rw [add_succ,succ_add]
  rfl

instance : Preorder ℕ :=
{
  le_refl := le_refl
  le_trans := le_trans
  lt_iff_le_not_le := lt_iff_le_not_le
}

instance : PartialOrder ℕ :=
{
  le_antisymm := le_antisymm
}

instance:  LinearOrder ℕ :=
{
  le_total := le_total
  decidableLE := leDec
  max_def := by
    intro a b
    unfold Max.max
    unfold instMaxMyNat
    unfold max
    dsimp
}

theorem min_le_left_and_right (a b : ℕ) : min a b ≤ a ∧ min a b ≤ b := by
  unfold min
  rcases (em (a ≤ b)) with (h1 | h1)
  · rw [if_pos h1]
    exact ⟨le_refl a, h1⟩
  rw [if_neg h1]
  apply And.intro (Or.resolve_left (le_total a b) h1) (le_refl b)

theorem min_le_left (a b : ℕ) :  min a b ≤ a :=
  (min_le_left_and_right a b).left

theorem min_le_right (a b : ℕ) : min a b ≤ b :=
  (min_le_left_and_right a b).right

theorem le_min (a b c : ℕ) : a ≤ b → a ≤ c → a ≤ min b c := by
  rintro ⟨l,hab⟩ ⟨m,hac⟩
  rw [hab,hac]
  unfold min
  rcases (em (a + l ≤ a +m)) with (h1 | h1)
  rw [if_pos h1]
  use l
  rfl
  rw [if_neg h1]
  use m
  rfl

theorem le_max_AND (a b : ℕ) : (a ≤ max a b) ∧ (b ≤ max a b) := by
  unfold max
  rcases (em (a ≤ b)) with (h1 | h1)
  rw [if_pos h1]
  apply And.intro h1 (le_refl b)
  rw [if_neg h1]
  apply And.intro (le_refl a)
  exact Or.resolve_left (le_total a b) h1


theorem le_max_left (a b : ℕ) : a ≤ max a b := by
  exact (le_max_AND a b).left

theorem le_max_right (a b : ℕ) : b ≤ max a b := by
  exact (le_max_AND a b).right

theorem max_le (a b c : ℕ) : a ≤ c → b ≤ c → max a b ≤ c := by
  intro hac hbc
  unfold max
  rcases (em (a ≤ b)) with (h0 | h0)
  rw [if_pos h0]
  exact hbc
  rw [if_neg h0]
  exact hac



instance : Lattice ℕ where
  sup := max
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le := max_le
  inf := min
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf := le_min

end MyNat
