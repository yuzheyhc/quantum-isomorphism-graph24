import SmallCatalogModel
import SixShoreModels
import RegionalEightTwelveCatalog
import TenPointCrossCatalog

namespace QGI.SmallCatalog
open Coherent.SmallUnion CatalogComparison

/-- The homogeneous catalogs whose completeness already has a finite proof. -/
def KnownHomogeneous {n} (c : Table n) : Prop :=
  (n=6 ∨ n=8 ∨ n=10 ∨ n=12) ∧ ∀ i j, c i i=c j j

private def Matches {n r} (F : Frame n r) (cell : Table n) : Prop :=
  (∀ k, F.name (F.spot k).1 (F.spot k).2=k) ∧ ∀ i j, (F.name i j).val=cell i j
private instance {n r} (F : Frame n r) (cell : Table n) : Decidable (Matches F cell) := by
  unfold Matches
  infer_instance

private theorem place {n r} {F : Frame n r} {cell c : Table n} (checked : Matches F cell)
    (p : Equiv.Perm (Fin n))
    (iso : ∀ i j x y, c (p i) (p j)=c (p x) (p y) ↔ cell i j=cell x y) :
    Nonempty (Placement F c) := by
  let labels (k : Fin r) := c (p (F.spot k).1) (p (F.spot k).2)
  have key (k : Fin r) : cell (F.spot k).1 (F.spot k).2=k.val :=
    (checked.2 _ _).symm.trans (congrArg Fin.val (checked.1 k))
  have inj : Function.Injective labels := by
    intro k l eq
    exact Fin.ext ((key k).symm.trans (((iso _ _ _ _).mp eq).trans (key l)))
  exact ⟨⟨p,⟨labels,inj⟩,fun i j => (iso _ _ _ _).mpr ((checked.2 i j).symm.trans (key _).symm)⟩⟩

private def idx6 (a : Fin 8) : Index 6 :=
  ⟨15+a.val,by change 15+a.val < 38; omega⟩
private def cells6 : Fin 8 → Table 6 := SixShoreAtlas.cell
private theorem linked6 : ∀ a, Matches (frame (idx6 a)) (cells6 a) := by native_decide

private def idx8 (a : Fin 21) : Index 8 :=
  ⟨57+a.val,by change 57+a.val < 143; omega⟩
private def cells8 : Fin 21 → Table 8 := fun a i j => EightTwelveCatalog.cell (EightTwelveCatalog.row 8 a.val) i j
private theorem linked8 : ∀ a, Matches (frame (idx8 a)) (cells8 a) := by native_decide

private def idx10 (a : Fin 13) : Index 10 :=
  ⟨228+a.val,by change 228+a.val < 492; omega⟩
private def cells10 : Fin 13 → Table 10 := TenPointCross.cell
private theorem linked10 : ∀ a, Matches (frame (idx10 a)) (cells10 a) := by native_decide

private def idx12 (a : Fin 59) : Index 12 :=
  ⟨769+a.val,by change 769+a.val < 1845; omega⟩
private def cells12 : Fin 59 → Table 12 := fun a i j => EightTwelveCatalog.cell (EightTwelveCatalog.row 12 a.val) i j
private theorem linked12 : ∀ a, Matches (frame (idx12 a)) (cells12 a) := by native_decide

/-- Transport the separately proved classifications into the common 1–13 list. -/
theorem homogeneous_coverage {n} [NeZero n] {c : Table n} (hc : Configuration c)
    (known : KnownHomogeneous c) : ∃ a : Index n, Nonempty (Placement (frame a) c) := by
  obtain ⟨ord,uniform⟩ := known
  have localData : Coherent.SmallShore.Local c (c 0 0) :=
    ⟨fun i j => ⟨hc.diagonal i j 0,fun eq => by subst j; exact uniform i 0⟩,hc.reverse,hc.products⟩
  rcases ord with rfl|rfl|rfl|rfl
  · obtain ⟨a,p,h⟩ := Literature.zivAv_six_homogeneous_catalog c localData
    exact ⟨idx6 a,place (linked6 a) p h⟩
  · obtain ⟨a,p,h⟩ := Literature.eight_homogeneous_catalog c localData
    exact ⟨idx8 a,place (linked8 a) p h⟩
  · obtain ⟨a,p,h⟩ := Literature.zivAv_ten_homogeneous_catalog c localData
    exact ⟨idx10 a,place (linked10 a) p h⟩
  · obtain ⟨a,p,h⟩ := Literature.zivAv_twelve_homogeneous_catalog c localData
    exact ⟨idx12 a,place (linked12 a) p h⟩

end QGI.SmallCatalog

