import FourHalfCore
import RegionalDoubleEight
import SixEightGeometry
import RegionalFourSixEight

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog (base slot eight Key Eight)
open Relations SixTenCoordinates SmallUnion SmallFiberExtension LargeFourteenRegion
open FourTwelveFunctional (source)
open DoubleEight.MatchingExtension
open private models info from RegionalDoubleEightTables
open private induce from SmallUnionRealization

attribute [local irreducible] DoubleEight.Prepared.row DoubleEight.Prepared.scheme DoubleEight.Layers.matrices
set_option maxRecDepth 12000

abbrev Sum8 := Eight ⊕ Eight
def idx : Sum8 ≃ Fin 16 := finSumFinEquiv

theorem index_val : (∀ i : Eight, idx (.inl i)=eight false i) ∧ (∀ i : Eight, idx (.inr i)=eight true i) := by decide

def vertex {n l r : Nat} {c : Fin n → Fin n → Nat} (X : Shore c l Eight) (Y : Shore c r Eight) : Sum8 → Fin n :=
  Sum.elim (atPoint X) (atPoint Y)

theorem vertex_inj {n l r : Nat} {c : Fin n → Fin n → Nat} (X : Shore c l Eight) (Y : Shore c r Eight) (lr : l≠r) :
    Function.Injective (vertex X Y) := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (X.injective (Subtype.ext h))
  · exact (lr ((X i).property.symm.trans ((congrArg (fun z => c z z) h).trans (Y j).property))).elim
  · exact (lr ((X j).property.symm.trans ((congrArg (fun z => c z z) h.symm).trans (Y i).property))).elim
  · exact congrArg Sum.inr (Y.injective (Subtype.ext h))

private theorem catalog_diag : ∀ a : Key, ∀ sw : Bool,
    (∀ s i, base a sw (eight s i) (eight s i)=base a sw (eight s 0) (eight s 0)) ∧
    base a sw (eight false 0) (eight false 0)≠base a sw (eight true 0) (eight true 0) := by native_decide

structure Chart {n : Nat} (c : Fin n → Fin n → Nat) (l r : Nat) where
  key : Key
  swap : Bool
  X : Shore c l Eight
  Y : Shore c r Eight
  names : ∀ i j a b : Sum8, base key swap (idx i) (idx j)=base key swap (idx a) (idx b) ↔
    c (vertex X Y i) (vertex X Y j)=c (vertex X Y a) (vertex X Y b)

theorem represent {n l r : Nat} {G : Graph n} (X : Shore (source G) l Eight) (Y : Shore (source G) r Eight) (lr : l≠r) :
    (∃ i j, ∀ b, source G (atPoint X i) b=source G (atPoint X i) (atPoint Y j) → b=atPoint Y j) ∨
    Nonempty (Chart (source G) l r) := by
  classical
  let c := source G
  let f := vertex X Y ∘ idx.symm
  have fi : Function.Injective f := (vertex_inj X Y lr).comp idx.symm.injective
  let reg := fun t => t=l ∨ t=r
  have fr (z) : (∃ i, f i=z) ↔ reg (c z z) := by
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨u,rfl⟩ := idx.surjective i
      cases u with
      | inl x => simpa only [f,Function.comp_apply,Equiv.symm_apply_apply,vertex,Sum.elim_inl] using (Or.inl (X x).property : reg _)
      | inr x => simpa only [f,Function.comp_apply,Equiv.symm_apply_apply,vertex,Sum.elim_inr] using (Or.inr (Y x).property : reg _)
    · rintro (h|h)
      · exact ⟨idx (.inl (X.symm ⟨z,h⟩)),by simp [f,vertex,atPoint]⟩
      · exact ⟨idx (.inr (Y.symm ⟨z,h⟩)),by simp [f,vertex,atPoint]⟩
  let m := restricted c f
  have cc : Configuration c := ⟨fun _ _ _ h => diagonal _ h,fun _ _ _ _ h => transpose _ h,Relations.products _⟩
  have conf := induce cc (fun {_ _ _ _} h => (end_colors (closure G) h).2) f fi fr
  have named (i j) : m (idx i) (idx j)=c (vertex X Y i) (vertex X Y j) := by simp [m,restricted,SmallShore.restrict,f]
  have sides : RegionalDoubleEight.Sides m idx := by
    rintro (i|i) (j|j) <;> rw [named,named]
    · exact iff_of_true rfl ((X i).property.trans (X j).property.symm)
    · exact iff_of_false (by simp [DoubleEight.ShoreCensus.side]) (fun h => lr ((X i).property.symm.trans (h.trans (Y j).property)))
    · exact iff_of_false (by simp [DoubleEight.ShoreCensus.side]) (fun h => lr ((X j).property.symm.trans (h.symm.trans (Y i).property)))
    · exact iff_of_true rfl ((Y i).property.trans (Y j).property.symm)
  rcases models idx (info conf (fun _ _ _ _ h => end_colors (closure G) h) idx sides) with ⟨v,g,thin⟩|⟨a,⟨P⟩⟩
  · left
    have eq (w) : c (atPoint X 0) (vertex X Y w)=v ↔ w=Sum.inr (g 0) := by
      have h := thin 0 w
      change m (idx (Sum.inl 0)) (idx w)=v ↔ _ at h
      rwa [named] at h
    refine ⟨0,g 0,fun b h => ?_⟩
    obtain ⟨j,hj⟩ := (RegionalCycleExtension.range_emb Y b).mpr ((end_colors (closure G) h).2.trans (Y _).property)
    have h' : Sum.inr j=Sum.inr (g 0) := (eq _).mp (by change c (atPoint X 0) (atPoint Y j)=v; rw [show atPoint Y j=b from hj]; exact h.trans ((eq _).mpr rfl))
    exact hj.symm.trans (congrArg (atPoint Y) (Sum.inr.inj h'))
  · right
    let imagePt (sw : Bool) (i : Fin 16) := f (P.coordinates (slot sw i))
    have enc (sw) (i j x y : Fin 16) : base a sw i j=base a sw x y ↔ c (imagePt sw i) (imagePt sw j)=c (imagePt sw x) (imagePt sw y) :=
      by
        change (DoubleEight.Prepared.name a (slot sw i) (slot sw j)).val=(DoubleEight.Prepared.name a (slot sw x) (slot sw y)).val ↔ _
        rw [Fin.val_inj]
        exact P.same (slot sw i) (slot sw j) (slot sw x) (slot sw y)
    have tags (sw s) (i : Eight) := (enc sw _ _ _ _).mp ((catalog_diag a sw).1 s i)
    have diff (sw) : c (imagePt sw (eight false 0)) (imagePt sw (eight false 0))≠c (imagePt sw (eight true 0)) (imagePt sw (eight true 0)) :=
      fun h => (catalog_diag a sw).2 ((enc sw _ _ _ _).mpr h)
    have inReg (sw i) : reg (c (imagePt sw i) (imagePt sw i)) := (fr _).mp ⟨_,rfl⟩
    obtain ⟨sw,l0,r0⟩ : ∃ sw, c (imagePt sw (eight false 0)) (imagePt sw (eight false 0))=l ∧ c (imagePt sw (eight true 0)) (imagePt sw (eight true 0))=r := by
      rcases inReg false (eight false 0) with h|h
      · exact ⟨false,h,(inReg false (eight true 0)).resolve_left (fun e => diff false (h.trans e.symm))⟩
      · have hl := (inReg false (eight true 0)).resolve_right (fun e => diff false (h.trans e.symm))
        exact ⟨true,hl,h⟩
    have inj (s : Bool) : Function.Injective (fun i => imagePt sw (eight s i)) := by
      have hi : Function.Injective (eight s) := by intro i j eq; apply Fin.ext; have hh := congrArg Fin.val eq; change (if s then 8 else 0)+i.val=(if s then 8 else 0)+j.val at hh; omega
      have hj : Function.Injective (slot sw) := by cases sw <;> intro i j h <;> simp_all [slot]
      exact fi.comp (P.coordinates.injective.comp (hj.comp hi))
    have shore {v : Nat} (R : Shore c v Eight) (s : Bool) (tag : c (imagePt sw (eight s 0)) (imagePt sw (eight s 0))=v) :
        ∃ T : Shore c v Eight, ∀ i, atPoint T i=imagePt sw (eight s i) := by
      let t (i : Eight) := R.symm ⟨imagePt sw (eight s i),(tags sw s i).trans tag⟩
      have loc (i) : atPoint R (t i)=imagePt sw (eight s i) := congrArg Subtype.val (R.apply_symm_apply _)
      have ti : Function.Injective t := fun i j e => inj s ((loc i).symm.trans ((congrArg (atPoint R) e).trans (loc j)))
      exact ⟨(Equiv.ofBijective t (Finite.injective_iff_bijective.mp ti)).trans R,loc⟩
    obtain ⟨A,ax⟩ := shore X false l0
    obtain ⟨B,bx⟩ := shore Y true r0
    have loc (u : Sum8) : vertex A B u=imagePt sw (idx u) := by
      cases u with
      | inl i => rw [index_val.1]; exact ax i
      | inr i => rw [index_val.2]; exact bx i
    exact ⟨⟨a,sw,A,B,fun i j x y => by rw [loc,loc,loc,loc]; exact enc _ _ _ _ _⟩⟩

end QGI.Coherent.FourHalfModel
