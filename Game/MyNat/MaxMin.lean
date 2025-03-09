import Game.MyNat.LT

namespace MyNat

open scoped Classical

def min (a b : ℕ) := if a ≤ b then a else b
def max (a b : ℕ) := if a ≤ b then b else a

instance : Min MyNat := ⟨MyNat.min⟩
instance : Max MyNat := ⟨MyNat.max⟩

end MyNat
