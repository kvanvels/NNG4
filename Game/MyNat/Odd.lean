import Game.Levels.LessOrEqual
import Game.Levels.Algorithm

namespace MyNat

def IsEven (n : ℕ) := ∃ (t : ℕ), t + t = n

--Question for Kevin, you don't want this, correct?
theorem isEven_def (n : ℕ) :  IsEven n ↔ ∃ t, t + t = n := Iff.rfl





-- Another choice is to define it recursively:
-- (kb) note: I didn't choose this option because tests showed
-- that mathematicians found it a lot more confusing than
-- the existence definition.

-- | le 0 _
-- | le (succ a) (succ b) = le ab

-- notation
instance : LE MyNat := ⟨MyNat.le⟩

-- We don't use this any more; I tell the users `≤` is *notation*
-- theorem le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl

end MyNat
