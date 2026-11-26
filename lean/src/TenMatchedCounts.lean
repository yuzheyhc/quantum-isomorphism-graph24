import TenMatchedFrames
import TenMatchedSquares

namespace QGI.Coherent.TenPointMatched
open TenPointCross.MatchedCatalog SixTenCoordinates TenMatchedSquares
abbrev Rect := Slot → Slot → Nat
def rect {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Slot) (Y : Shore c r Slot) : Rect :=
  fun x y => c (atPoint F x) (atPoint Y y)
def rowCount (m : Rect) (i j : Q) (s : Bool) (h : Nat) := mult (m (i,s) (j,false)) (m (i,s) (j,true)) h
def colCount (m : Rect) (i j : Q) (s : Bool) (h : Nat) := mult (m (i,false) (j,s)) (m (i,true) (j,s)) h

private theorem collapse (k : Q) (f : Slot → Nat) :
    (∑ t : Slot, if t.1=k then f t else 0)=f (k,false)+f (k,true) := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool,Finset.sum_add_distrib,Nat.add_comm]

variable {n l r v : Nat} {c d : Fin n → Fin n → Nat}
    (A : Frames (l:=l) (r:=r) (c:=c) (d:=d) v) (law : Laws c d)

include law in
theorem counts (i j k z : Q) (ij : i≠j) (kz : k≠z) (s t : Bool) (h : Nat) :
    rowCount (rect A.F A.Y) i j s h=rowCount (rect A.T A.Z) k z t h ∧
    colCount (rect A.F A.Y) i j s h=colCount (rect A.T A.Z) k z t h := by
  let B (x y : Slot) := decide (x.1=y.1)
  have mark : Block A.F A.T A.Y A.Z B B := by
    intro x y u b eq; apply Bool.eq_iff_iff.mpr
    simp only [B,decide_eq_true_eq]
    exact (A.src x y).symm.trans ((by rw [eq] : (c (atPoint A.F x) (atPoint A.Y y)=v ↔ d (atPoint A.T u) (atPoint A.Z b)=v)).trans (A.tgt u b))
  have colors : Block A.F A.T A.Y A.Z (rect A.F A.Y) (rect A.T A.Z) := fun ⦃_ _ _ _⦄ eq => eq
  have eq1 := A.ll (i,s) (j,s) (k,t) (z,t) ⟨iff_of_false ij kz,iff_of_true rfl rfl⟩
  have eq2 := A.rr (j,s) (i,s) (z,t) (k,t) ⟨iff_of_false (Ne.symm ij) (Ne.symm kz),iff_of_true rfl rfl⟩
  have ra := Block.fold law colors (Block.flip law mark) (fun c b => if b=true then (if c=h then 1 else 0) else 0) eq1
  have ca := Block.fold law (Block.flip law colors) mark (fun c b => if b=true then (if c=h then 1 else 0) else 0) eq2
  constructor
  · simpa only [B,decide_eq_true_eq,eq_comm (a:=j),eq_comm (a:=z),collapse,rowCount,mult] using ra
  · simpa only [B,decide_eq_true_eq,collapse,colCount,mult] using ca

def matrixSign (m : Rect) (u : Nat) (i j : Q) := decide (m (i,false) (j,false)=u)

structure Outside (m : Rect) (v u w : Nat) : Prop where
  diag : ∀ i s t, m (i,s) (i,t)=v
  off : ∀ i j, i≠j → ∀ s t, m (i,s) (j,t)=pick u w (matrixSign m u i j) s t

include law in
theorem palettes : ∃ u w, u≠v ∧ w≠v ∧ Outside (rect A.F A.Y) v u w ∧ Outside (rect A.T A.Z) v u w := by
  let m := rect A.F A.Y
  let b := rect A.T A.Z
  let u := m (0,false) (1,false)
  let w := m (0,false) (1,true)
  have ne : (0:Q)≠1 := by decide
  have rowS (i j : Q) (diff : i≠j) (s : Bool) (h : Nat) : rowCount m i j s h=mult u w h :=
    ((counts A law i j 0 1 diff ne s false h).1).trans (counts A law 0 1 0 1 ne ne false false h).1.symm
  have rowT (i j : Q) (diff : i≠j) (s : Bool) (h : Nat) : rowCount b i j s h=mult u w h :=
    (counts A law 0 1 i j ne diff false s h).1.symm
  have colS (i j : Q) (diff : i≠j) (s : Bool) (h : Nat) : colCount m i j s h=colCount m 0 1 false h :=
    ((counts A law i j 0 1 diff ne s false h).2).trans (counts A law 0 1 0 1 ne ne false false h).2.symm
  have sum (h : Nat) : colCount m 0 1 false h=mult u w h := by
    have a := colS 0 1 ne true h
    have b := rowS 0 1 ne true h
    change mult _ _ h=mult _ _ h at a b ⊢
    dsimp only [u,w] at b ⊢
    unfold mult at a b ⊢
    omega
  have cs (i j : Q) (diff : i≠j) (t : Bool) (h : Nat) : colCount m i j t h=mult u w h :=
    (colS _ _ diff t h).trans (sum h)
  have ct (i j : Q) (diff : i≠j) (t : Bool) (h : Nat) : colCount b i j t h=mult u w h :=
    (counts A law 0 1 i j ne diff false t h).2.symm.trans (sum h)
  refine ⟨u,w,fun eq => ne ((A.src _ _).mp eq),fun eq => ne ((A.src _ _).mp eq),?_,?_⟩
  · exact ⟨fun i s t => (A.src (i,s) (i,t)).mpr rfl,fun i j ij => TenMatchedSquares.read _ u w (rowS i j ij) (cs i j ij)⟩
  · exact ⟨fun i s t => (A.tgt (i,s) (i,t)).mpr rfl,fun i j ij => TenMatchedSquares.read _ u w (rowT i j ij) (ct i j ij)⟩

end QGI.Coherent.TenPointMatched
