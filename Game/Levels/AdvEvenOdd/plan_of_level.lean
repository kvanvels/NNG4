-- AdvEvenOdd World.
-- This extends the concepts of even and odd to multiplication


namespace MyNat

-- instance decIsOdd : DecidablePred isOdd
-- | 0 => isFalse <| by
--   exact not_isOdd_zero
-- | succ j =>
--   match decIsOdd j with
--   | isTrue (h : isOdd j) => isFalse <| by
--     simp
--     intro h0
--     exact (not_isEven_and_isOdd j) ⟨h0,h⟩
--   | isFalse (h : ¬isOdd j) => isTrue <| by
--     simp
--     exact Or.resolve_right (isEven_or_isOdd j) h

-- instance decIsEven : DecidablePred isEven
-- | 0 => isTrue <| by
--   exact isEven_zero
-- | succ j =>
--   match decIsEven j with
--   | isTrue (h : isEven j) => isFalse <| by
--     simp
--     intro h0
--     exact (not_isEven_and_isOdd j) (And.intro h h0)
--   | isFalse (h : ¬isEven j) => isTrue <| by
--     simp
--     exact Or.resolve_left (isEven_or_isOdd j)  h



-- level 1
theorem isEven_mul_of_isEven_left {a b : ℕ} (ha : isEven a)
    : isEven (a * b) := by
  rcases ha with ⟨a2,ha2⟩
  rw [←ha2]
  use (a2 * b)
  rw [add_mul]
  rfl

--level 2
theorem isEven_mul_of_isEven_right {a b : ℕ} (hb : isEven b)
    : isEven (a * b) := by
  rcases hb with ⟨b2,hb2⟩
  rw [←hb2]
  use (a * b2)
  rw [mul_add]
  rfl

--level 3
theorem isOdd_mul_isOdd {a b : ℕ} (ha : isOdd a) (hb : isOdd b)
    : isOdd (a * b) := by
  rcases ha with ⟨a2,ha2⟩
  rcases hb with ⟨b2,hb2⟩  
  use (a2 + b2 +  a2 * b2 + a2 * b2)
  rw [←ha2,←hb2]
  rw [mul_add,mul_add,mul_one,add_mul]
  rw [one_mul]
  rw [add_mul]
  simp_add


--level 4
theorem mul_isOdd_iff {a b : ℕ} : isOdd (a * b) ↔ isOdd a ∧ isOdd b := by
  apply Iff.intro
  intro h0
  rcases (isEven_or_isOdd a) with (h|h)
  have h1 : isEven (a * b) := isEven_mul_of_isEven_left h
  have h2 := not_isEven_and_isOdd (a * b)
  exfalso
  exact h2 ⟨h1,h0⟩
  rcases (isEven_or_isOdd b) with (h1|h1)
  exfalso
  have h2 : isEven (a * b) := isEven_mul_of_isEven_right h1
  have h3 := not_isEven_and_isOdd (a * b)
  exact h3 ⟨h2,h0⟩
  apply And.intro h h1
  intro h0
  exact isOdd_mul_isOdd h0.left h0.right

--level 5
theorem mul_isEven_iff {a b : ℕ} : isEven (a * b) ↔ isEven a ∨ isEven b := by
  apply Iff.intro
  intro h0
  rcases (isEven_or_isOdd a) with (ha|ha)
  left
  exact ha
  rcases (isEven_or_isOdd b) with (hb|hb)
  right
  exact hb
  exfalso
  have h1 : isOdd a ∧ isOdd b :=  ⟨ha,hb⟩
  rw [←mul_isOdd_iff] at h1
  have h2 := not_isEven_and_isOdd (a * b)
  apply h2
  apply And.intro h0 h1
  rintro (ha|hb)
  exact (isEven_mul_of_isEven_left ha)
  exact (isEven_mul_of_isEven_right hb)

--level 6
theorem isEven_iff' (n : ℕ) : isEven n ↔ ∃ p : ℕ, 2 * p = n := by
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

--level 7
theorem isOdd_iff' (n : ℕ) : isOdd n ↔ ∃ p : ℕ, 2 * p + 1 = n := by
  apply Iff.intro
  rintro ⟨w,hw⟩
  use w
  rw [two_eq_succ_one,succ_mul,one_mul]
  exact hw
  intro ⟨w,hw⟩
  use w
  rw [two_eq_succ_one,succ_mul,one_mul] at hw
  exact hw


--level 8
theorem boss (n :ℕ ) : isEven (n * succ n) := by
  rw [mul_isEven_iff]
  cases (isEven_or_isOdd n) with hn hn
  · exact Or.inl hn
  apply Or.inr
  simp
  exact hn

end MyNat
