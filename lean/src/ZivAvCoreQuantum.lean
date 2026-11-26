import CoreCatalogRows
import ZivAvCoreSound
import ZivAvCoreCensus
import RegionalPlanar
import LargeFourteenRegion

noncomputable section
namespace QGI.ZivAv
open Coherent.SmallUnion

structure Presentation (a : Index) (c : Table 14) where
  coordinates : Equiv.Perm Vertex
  labels : Fin (raw a).rank ↪ Nat
  cell : ∀ i j, c (coordinates i) (coordinates j) = labels (name a i j)

end QGI.ZivAv

namespace QGI.Literature
open ZivAv Coherent.SmallUnion Coherent.StrategyColorLaws

/-- Completeness of the 14-point catalog restricted to fibers of size at least four.
Only a presentation for a single input is assumed (Ziv-Av, §2.1). -/
axiom zivAv_fourteen_core_coverage {c : Table 14} (hc : Configuration c)
    (large : ∀ i, 4 ≤ (Finset.univ.filter (fun j => c j j=c i i)).card) :
    ∃ a : Index, Nonempty (Presentation a c)

/-- The intersection numbers determine which catalog row contains both inputs. -/
theorem zivAv_fourteen_common_catalog {c d : Table 14}
    (hc : Configuration c) (hd : Configuration d)
    (large : ∀ i, 4 ≤ (Finset.univ.filter (fun j => c j j = c i i)).card)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, d x y=s)
    (products : ∀ s t i j x y, c i j=d x y → count c s t i j=count d s t x y) :
    ∃ a : Index, Nonempty (Presentation a c) ∧ Nonempty (Presentation a d) := by
  let C : CatalogComparison.Common c d := ⟨used,products⟩
  obtain ⟨a,⟨A⟩⟩ := zivAv_fourteen_core_coverage hc large
  obtain ⟨b,⟨B⟩⟩ := zivAv_fourteen_core_coverage hd (CatalogComparison.large_target hc hd C large)
  let P : CatalogComparison.Placement (CatalogComparison.fourteen a) c := ⟨A.coordinates,A.labels,A.cell⟩
  let Q : CatalogComparison.Placement (CatalogComparison.fourteen b) d := ⟨B.coordinates,B.labels,B.cell⟩
  obtain ⟨e,he⟩ := CatalogComparison.compatible hc hd C P Q (fun k => (locations _ k).1) (fun k => (locations _ k).1)
  obtain rfl := CatalogComparison.fourteen_row he
  exact ⟨a,⟨A⟩,⟨B⟩⟩
end QGI.Literature

namespace QGI.ZivAv
open Coherent Coherent.SmallUnion Coherent.StrategyColorLaws Coherent.LargeFourteenRegion
open FourTwelveFunctional (source)

private theorem exceptional_rank : ∀ t : Index, (original t).1=249 → (raw t).rank=12 := by native_decide
attribute [local irreducible] raw color keyed cores14

private theorem match_names {a : Index} {c d : Table 14} (A : Presentation a c) (B : Presentation a d)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, d x y=s) :
    ∃ e : Equiv.Perm (Fin (raw a).rank), ∀ v, A.labels v = B.labels (e v) := by
  have hit (v : Fin (raw a).rank) : ∃ w, A.labels v = B.labels w := by
    obtain ⟨i,j,ij⟩ := onto a v
    obtain ⟨x,y,xy⟩ := (used _).mp ⟨A.coordinates i,A.coordinates j,(A.cell i j).trans (congrArg A.labels ij)⟩
    obtain ⟨x,rfl⟩ := B.coordinates.surjective x
    obtain ⟨y,rfl⟩ := B.coordinates.surjective y
    exact ⟨_,xy.symm.trans (B.cell x y)⟩
  choose f hf using hit
  have fi : Function.Injective f := fun x y h => A.labels.injective
    ((hf x).trans ((congrArg B.labels h).trans (hf y).symm))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi),hf⟩

private theorem count_named {a : Index} {c : Table 14} (A : Presentation a c)
    (i j : Fin (raw a).rank) (x y : Vertex) :
    count c (A.labels i) (A.labels j) (A.coordinates x) (A.coordinates y) =
    ∑ z : Vertex, if name a x z = i ∧ name a z y = j then 1 else 0 := by
  rw [←count_relabel c A.coordinates]
  simp only [count,A.cell,A.labels.injective.eq_iff]

private theorem range_comp {n} (f : Fin 14 → Fin n) (e : Equiv.Perm Vertex) (x : Fin n) :
    (∃ i, (f ∘ e) i = x) ↔ ∃ i, f i=x :=
  ⟨fun ⟨i,h⟩ => ⟨e i,h⟩,fun ⟨i,h⟩ => ⟨e.symm i,by simpa using h⟩⟩

private theorem named_or_exception {a : Index} {c d : Table 14} (A : Presentation a c)
    (B : Presentation a d) (e : Equiv.Perm (Fin (raw a).rank))
    (he : ∀ v, A.labels v = B.labels (e v))
    (reverse : ∀ {i j x y}, c i j = d x y → c j i = d y x)
    (products : ∀ s t i j x y, c i j = d x y → count c s t i j = count d s t x y) :
    (∃ h : Equiv.Perm Vertex, ∀ i j, c i j = d (h i) (h j)) ∨
      ((original a).1 = 249 ∧ (List.ofFn fun i => (e i).val) ∈ badMaps) := by
  classical
  have same (i j x y : Vertex) :
      e (name a i j) = name a x y ↔
      c (A.coordinates i) (A.coordinates j) = d (B.coordinates x) (B.coordinates y) := by
    rw [A.cell,B.cell,he,B.labels.injective.eq_iff]
  let pi := List.ofFn fun i => (e i).val
  have listed : pi ∈ SixteenMapSearch.enumeratedMaps (keyed a) (keyed a) := by
    apply eligible
    · intro x y u v h
      exact (same y x v u).mpr (reverse ((same x y u v).mp h))
    · intro x y u v h i j
      have num := products (A.labels i) (A.labels j) _ _ _ _ ((same x y u v).mp h)
      change count c _ _ _ _ = count d _ _ _ _ at num
      rw [count_named A,he i,he j,count_named B] at num
      exact num
  cases passed : pointCheck (keyed a) pi with
  | true =>
    obtain ⟨h,hh⟩ := points a e passed
    left
    refine ⟨A.coordinates.symm.trans (h.trans B.coordinates),?_⟩
    intro i j
    obtain ⟨i,rfl⟩ := A.coordinates.surjective i
    obtain ⟨j,rfl⟩ := A.coordinates.surjective j
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (hh i j)
  | false => exact Or.inr (obstruction listed passed)

/-- In the homogeneous case the two diagonal colors at positions 0 and 6
of the unique exceptional archive row already rule it out. -/
theorem named_of_homogeneous {c b : Table 14} {d : Nat}
    (hc : SmallShore.Local c d) (hb : SmallShore.Local b d)
    (used : ∀ s, (∃ i j, c i j = s) ↔ ∃ x y, b x y = s)
    (products : ∀ s t i j x y, c i j = b x y → count c s t i j = count b s t x y) :
    ∃ h : Equiv.Perm Vertex, ∀ i j, c i j = b (h i) (h j) := by
  classical
  have cd (i : Vertex) := (hc.diag i i).mpr rfl
  have bd (i : Vertex) := (hb.diag i i).mpr rfl
  have large (i : Vertex) : 4 ≤ (Finset.univ.filter (fun j => c j j = c i i)).card := by
    simp [cd]
  obtain ⟨a, ⟨A⟩, ⟨B⟩⟩ := Literature.zivAv_fourteen_common_catalog hc.configuration
    hb.configuration large used products
  obtain ⟨e, he⟩ := match_names A B used
  have rev {i j x y : Vertex} (eq : c i j = b x y) : c j i = b y x := by
    have num := products (c i j) (c j i) i i x x ((cd i).trans (bd x).symm)
    have present : 0 < count c (c i j) (c j i) i i := by
      simp only [count, Finset.sum_boole, Nat.cast_id, Finset.card_pos]
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩
    rw [num] at present
    simp only [count, Finset.sum_boole, Nat.cast_id, Finset.card_pos] at present
    obtain ⟨z, hz⟩ := present
    obtain ⟨_, first, second⟩ := Finset.mem_filter.mp hz
    exact second.symm.trans (hb.reverse _ _ _ _ (first.trans eq))
  rcases named_or_exception A B e he rev products with point | ⟨row, _⟩
  · exact point
  · have diag : name a 0 0 = name a 6 6 := by
      apply A.labels.injective
      rw [← A.cell, ← A.cell, cd, cd]
    have values : color a 0 0 = color a 6 6 := congrArg Fin.val diag
    rw [original_matches a row, original_matches a row] at values
    have distinct : Certificate.m_fourteen_249.get 0 0 ≠ Certificate.m_fourteen_249.get 6 6 := by
      native_decide
    exact (distinct values).elim

theorem solveRegion {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {region : Nat → Prop}
    (f g : Vertex → Fin n) (D : DataFor p region f g) :
    ∃ h : Equiv.Perm Vertex, ∀ i j, source G (f i) (f j) = targetName p (g (h i)) (g (h j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  obtain ⟨a,⟨A⟩,⟨B⟩⟩ := Literature.zivAv_fourteen_common_catalog (c:=c) (d:=d)
    D.srcConfig D.tgtConfig D.srcLarge D.used D.products
  obtain ⟨e,he⟩ := match_names A B D.used
  have same (i j x y : Vertex) :
      e (name a i j) = name a x y ↔
      c (A.coordinates i) (A.coordinates j) = d (B.coordinates x) (B.coordinates y) := by
    rw [A.cell,B.cell,he,B.labels.injective.eq_iff]
  let pi := List.ofFn fun i => (e i).val
  rcases named_or_exception A B e he (fun eq => common_transpose p eq) D.products with done_ | ⟨id249,bad⟩
  · exact done_
  · apply False.elim (Certificate.RegionalPlanar.exclude_fourteen p region
      (f ∘ A.coordinates) (g ∘ B.coordinates) (D.injF.comp A.coordinates.injective)
      (D.injG.comp B.coordinates.injective) (fun x => (range_comp _ _ x).trans (D.src x))
      (fun x => (range_comp _ _ x).trans (D.tgt x)) pi (checked bad) ?_)
    intro i j x y matchColor k member
    have colorMatch := (same i j x y).mpr matchColor
    rw [←original_matches a id249,←original_matches a id249]
    have valid : k < (raw a).rank := by
      rw [exceptional_rank a id249]
      have all : ∀ z ∈ Certificate.RegionalPlanar.fourteenColors, z < 12 := by decide
      exact all k member
    have read : pi[k]?.getD Certificate.m_fourteen_249.rank = (e ⟨k,valid⟩).val := by
      simp [pi,List.getElem?_ofFn,valid]
    rw [read]
    change (name a i j).val = k ↔ (name a x y).val = _
    rw [←colorMatch]
    exact (Fin.val_inj (a:=name a i j) (b:=⟨k,valid⟩)).trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm)

theorem solve {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (f g : Vertex → Fin n) (D : Data p f g) :
    ∃ h : Equiv.Perm Vertex, ∀ i j, source G (f i) (f j) = targetName p (g (h i)) (g (h j)) :=
  solveRegion p f g D

theorem isomorphic {n} {G H : Graph n} {xs : List Nat} (P : CoprimeProfiles.Profile G xs)
    (sum : (xs.filter (fun k => 3 < k)).sum=14) (q : QuantumIso G H) : Isomorphic G H :=
  isomorphic_via_core_fourteen P sum (fun p f g D => solve p f g D) q

end QGI.ZivAv
