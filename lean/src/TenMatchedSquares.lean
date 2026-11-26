import Mathlib.Tactic

namespace QGI.TenMatchedSquares
def mult (a b c : Nat) := (if a=c then 1 else 0)+(if b=c then 1 else 0)
def Same (a b u w : Nat) := ∀ c, mult a b c=mult u w c
theorem same_iff (a b u w : Nat) : Same a b u w ↔ (a=u ∧ b=w) ∨ (a=w ∧ b=u) := by
  constructor
  · intro h
    have x := h a; have y := h b; have s := h u; have t := h w
    simp only [mult,if_pos rfl] at x y s t
    grind
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact fun _ => rfl
    · exact fun _ => Nat.add_comm _ _

def pick (u w : Nat) (sign s t : Bool) := if ((s==t)==sign) then u else w
theorem read (f : Bool → Bool → Nat) (u w : Nat) (rows : ∀ s, Same (f s false) (f s true) u w)
    (cols : ∀ t, Same (f false t) (f true t) u w) (s t : Bool) :
    f s t=pick u w (decide (f false false=u)) s t := by
  have a := (same_iff _ _ _ _).mp (rows false)
  have b := (same_iff _ _ _ _).mp (rows true)
  have c := (same_iff _ _ _ _).mp (cols false)
  have d := (same_iff _ _ _ _).mp (cols true)
  by_cases hit : f false false=u <;> cases s <;> cases t <;> simp only [pick,hit,decide_true,decide_false] <;> grind

theorem flip (u w : Nat) (g flip s t : Bool) : pick u w (xor flip g) s (xor flip t)=pick u w g s t := by
  cases g <;> cases flip <;> cases s <;> cases t <;> rfl

end QGI.TenMatchedSquares
