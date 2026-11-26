import EightFourteenPlacement
import FourHalfCore

namespace QGI.EightFourteenWitnesses
open EightFourteenWords EightFourteenPlacement Certificate
abbrev V := Fin 22
def value (s : Rep) (x y : V) : Nat :=
  let r (j : V) := Fin.ofNat' 14 j.val
  let l (i : V) := Fin.ofNat' 8 (i.val-14)
  if x.val<14 then
    if y.val<14 then rightName (key s) (r x) (r y) else 16+(inside s (l y) (r x)).toNat
  else if y.val<14 then 18+(inside s (l x) (r y)).toNat else 20+(decide (l x=l y)).toNat
def matrix (s : Rep) := FourHalfCatalog.fromFn 22 (fun k => value s (Fin.ofNat' 22 (k.val/22)) (Fin.ofNat' 22 k.val))
theorem read (s : Rep) (i j : V) : (matrix s).get i.val j.val=value s i j := by
  unfold matrix
  rw [FourHalfCatalog.fromFn_read _ i j (by omega)]
  have ar : ∀ i j : V, Fin.ofNat' 22 ((i.val*22+j.val)/22)=i ∧ Fin.ofNat' 22 (i.val*22+j.val)=j := by decide
  exact congrArg₂ (value s) (ar i j).1 (ar i j).2

abbrev Index := Fin EightFourteenInput.obstructions.size
def raw (i : Index) := EightFourteenInput.obstructions[i]
def src (i : Index) : Rep := Fin.ofNat' 10 (raw i).1
def dst (i : Index) : Rep := Fin.ofNat' 10 (raw i).2.1
def colors (i : Index) := [19,19,19,19,19,19,(raw i).2.2.1,(raw i).2.2.2.1,(raw i).2.2.2.2.1]
attribute [local irreducible] EightFourteenInput.obstructions EightFourteenInput.reps EightFourteenInput.families ZivAv.cores14
set_option maxRecDepth 20000 in
private theorem counts : ∀ i : Index, homCount (matrix (src i)) .nearClique (colors i)=(raw i).2.2.2.2.2.1 ∧
    homCount (matrix (dst i)) .nearClique (colors i)=(raw i).2.2.2.2.2.2 ∧ (raw i).2.2.2.2.2.1≠(raw i).2.2.2.2.2.2 := by native_decide
private theorem coverage : ∀ s t : Rep, key s=key t → s<t → ∃ i, src i=s ∧ dst i=t := by native_decide
theorem distinguish {s t : Rep} (eq : key s=key t) (ne : s≠t) : ∃ c, c.length=9 ∧
    homCount (matrix s) .nearClique c≠homCount (matrix t) .nearClique c := by
  have pick {a b : Rep} (same : key a=key b) (lt : a<b) : ∃ c, c.length=9 ∧ homCount (matrix a) .nearClique c≠homCount (matrix b) .nearClique c := by
    obtain ⟨i,rfl,rfl⟩ := coverage a b same lt
    have h := counts i
    refine ⟨colors i,rfl,?_⟩
    rw [h.1,h.2.1]; exact h.2.2
  rcases lt_or_gt_of_ne ne with h|h
  · exact pick eq h
  · obtain ⟨c,sz,m⟩ := pick eq.symm h; exact ⟨c,sz,Ne.symm m⟩
end QGI.EightFourteenWitnesses
