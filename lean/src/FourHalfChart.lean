import FourHalfPorts
import FourHalfModel
import FourDoubleEightCycle

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog (Key Eight Four Site base slot)
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private narrow from TwoAnchorUnionGlue

private theorem reverse_index : ∀ (sw : Bool) (i : Sum8),
    slot (!sw) (idx i)=slot sw (idx i.swap) := by decide

def Chart.flip {n l r} {c : Fin n → Fin n → Nat} (P : Chart c l r) : Chart c r l where
  key := P.key
  swap := !P.swap
  X := P.Y
  Y := P.X
  names i j a b := by
    have pt (z : Sum8) : vertex P.Y P.X z=vertex P.X P.Y z.swap := by cases z <;> rfl
    rw [pt,pt,pt,pt]
    have eq (i j : Sum8) : base P.key (!P.swap) (idx i) (idx j)=base P.key P.swap (idx i.swap) (idx j.swap) := by
      unfold base
      rw [reverse_index,reverse_index]
    rw [eq,eq]
    exact P.names _ _ _ _

def pts {n l r v : Nat} {c : Fin n → Fin n → Nat} (X : Shore c r Eight) (Y : Shore c v Eight)
    (F : Shore c l Four) : Site → Fin n := Sum.elim (vertex X Y) (atPoint F)

theorem pts_range {n l r v : Nat} {c : Fin n → Fin n → Nat} (X : Shore c r Eight)
    (Y : Shore c v Eight) (F : Shore c l Four) (z : Fin n) :
    (∃ u, pts X Y F u=z) ↔ c z z=l ∨ c z z=r ∨ c z z=v := by
  constructor
  · rintro ⟨((i|i)|i),rfl⟩
    · exact Or.inr (Or.inl (X i).property)
    · exact Or.inr (Or.inr (Y i).property)
    · exact Or.inl (F i).property
  · rintro (h|h|h)
    · exact ⟨.inr (F.symm ⟨z,h⟩),congrArg Subtype.val (F.apply_symm_apply _)⟩
    · exact ⟨.inl (.inl (X.symm ⟨z,h⟩)),congrArg Subtype.val (X.apply_symm_apply _)⟩
    · exact ⟨.inl (.inr (Y.symm ⟨z,h⟩)),congrArg Subtype.val (Y.apply_symm_apply _)⟩

theorem pts_inj {n l r v : Nat} {c : Fin n → Fin n → Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (X : Shore c r Eight) (Y : Shore c v Eight) (F : Shore c l Four) : Function.Injective (pts X Y F) := by
  have sep (u : Sum8) (i : Four) : vertex X Y u ≠ atPoint F i := by
    intro e
    have h := (congrArg (fun x => c x x) e).trans (F i).property
    cases u with
    | inl j => exact lr (h.symm.trans (X j).property)
    | inr j => exact lv (h.symm.trans (Y j).property)
  rintro (u|i) (w|j) e
  · exact congrArg Sum.inl (vertex_inj X Y rv e)
  · exact (sep u j e).elim
  · exact (sep w i e.symm).elim
  · exact congrArg Sum.inr (F.injective (Subtype.ext e))

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
   (p : PerfectStrategy G H K)

theorem targets (X : Shore (source G) r Eight) (Y : Shore (source G) v Eight)
    (old : Realizes p (fun t => t=r ∨ t=v)) :
    ∃ TX : Shore (targetName p) r Eight, ∃ TY : Shore (targetName p) v Eight,
      ∀ i j, source G (vertex X Y i) (vertex X Y j)=targetName p (vertex TX TY i) (vertex TX TY j) := by
  obtain ⟨e,he⟩ := old
  let TX := X.trans (narrow e he (Or.inl rfl))
  let TY := Y.trans (narrow e he (Or.inr rfl))
  let fromOld (i : Sum8) : Region (source G) (fun t => t=r ∨ t=v) :=
    ⟨vertex X Y i,(mem_vertices _ _ _).mpr (by cases i with
       | inl j => exact Or.inl (X j).property
       | inr j => exact Or.inr (Y j).property)⟩
  have loc (i : Sum8) : vertex TX TY i=(e (fromOld i)).val := by cases i <;> rfl
  exact ⟨TX,TY,fun i j => (he (fromOld i) (fromOld j)).trans (by rw [loc,loc])⟩

end QGI.Coherent.FourHalfModel
