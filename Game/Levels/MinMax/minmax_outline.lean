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
    rcases (em (b ≤ a)) with (h0 | h0)

    simp
    rw [if_pos h0]
    rcases h0 with ⟨θ,hθ⟩
    rw [hθ]
    cases θ with l
    rw [add_zero]
    rw [if_pos (le_refl b)]
    rfl
    have h1 : ¬(b + succ l ≤ b) := by
      rintro ⟨Γ,hΓ⟩
      rw [add_assoc] at hΓ
      have h2 := add_right_eq_self b (succ l + Γ) hΓ.symm
      rw [succ_add] at h2
      have h3 := succ_ne_zero (l + Γ)
      exact h3 h2
    rw [if_neg h1]
    rfl
    simp
    rw [if_neg h0]
    have h1 := Or.resolve_right (le_total a b) h0
    rw [if_pos h1]
    rfl
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
  rcases (em (b ≤ a)) with (h1 | h1)
  rw [if_pos h1]
  exact ⟨le_refl a, h1⟩
  rw [if_neg h1]
  exact ⟨Or.resolve_right (le_total a b) h1,le_refl b⟩

theorem le_max_left (a b : ℕ) : a ≤ max a b := by
  exact (le_max_AND a b).left

theorem le_max_right (a b : ℕ) : b ≤ max a b := by
  exact (le_max_AND a b).right

theorem max_le (a b c : ℕ) : a ≤ c → b ≤ c → max a b ≤ c := by
  intro hac hbc
  unfold max
  rcases (em (b ≤ a)) with (h0 | h0)
  rw [if_pos h0]
  exact hac
  rw [if_neg h0]
  exact hbc

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
