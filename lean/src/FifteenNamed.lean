import CoreCatalogRows
import FifteenCatalog
import FifteenChainSound
import FifteenRegion
import RegionalPlanar
import SingletonSwitch

noncomputable section
namespace QGI.Fifteen
open Coherent.SmallUnion

structure Presentation (a : Index) (c : Table 15) where
  coordinates : Equiv.Perm Vertex
  labels : Color a ↪ Nat
  cell : ∀ i j, c (coordinates i) (coordinates j) = labels ((model a).name i j)
end QGI.Fifteen

namespace QGI.Literature
open Fifteen Coherent.SmallUnion Coherent.StrategyColorLaws

/-- Completeness of the 15-point catalog restricted to fibers of size at least four.
Only a presentation for a single input is assumed (Ziv-Av, §2.1). -/
axiom zivAv_fifteen_core_coverage {c : Table 15} (hc : Configuration c)
    (large : ∀ i, 4 ≤ (Finset.univ.filter (fun j => c j j=c i i)).card) :
    ∃ a : Index, Nonempty (Presentation a c)

/-- The intersection numbers determine which catalog row contains both inputs. -/
theorem zivAv_fifteen_common_catalog {c d : Table 15}
    (hc : Configuration c) (hd : Configuration d)
    (large : ∀ i, 4 ≤ (Finset.univ.filter (fun j => c j j = c i i)).card)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, d x y=s)
    (products : ∀ s t i j x y, c i j=d x y → count c s t i j=count d s t x y) :
    ∃ a : Index, Nonempty (Presentation a c) ∧ Nonempty (Presentation a d) := by
  let C : CatalogComparison.Common c d := ⟨used,products⟩
  obtain ⟨a,⟨A⟩⟩ := zivAv_fifteen_core_coverage hc large
  obtain ⟨b,⟨B⟩⟩ := zivAv_fifteen_core_coverage hd (CatalogComparison.large_target hc hd C large)
  let P : CatalogComparison.Placement (CatalogComparison.fifteen a) c := ⟨A.coordinates,A.labels,A.cell⟩
  let Q : CatalogComparison.Placement (CatalogComparison.fifteen b) d := ⟨B.coordinates,B.labels,B.cell⟩
  obtain ⟨e,he⟩ := CatalogComparison.compatible hc hd C P Q (positions _) (positions _)
  obtain rfl := CatalogComparison.fifteen_row he
  exact ⟨a,⟨A⟩,⟨B⟩⟩
end QGI.Literature

namespace QGI.Fifteen
open Coherent Coherent.SmallUnion Coherent.StrategyColorLaws Coherent.LargeFourteenRegion
open FourTwelveFunctional (source)
open private pair_middle from SingletonSwitch

attribute [local irreducible] model row rank rows15

private theorem match_names {a : Index} {c d : Table 15} (A : Presentation a c) (B : Presentation a d)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, d x y=s) :
    ∃ e : Equiv.Perm (Color a), ∀ v, A.labels v = B.labels (e v) := by
  have hit (v : Color a) : ∃ w, A.labels v = B.labels w := by
    let pair := (model a).spot v
    have ij := positions a v
    obtain ⟨x,y,xy⟩ := (used _).mp ⟨A.coordinates pair.1,A.coordinates pair.2,
      (A.cell pair.1 pair.2).trans (congrArg A.labels ij)⟩
    obtain ⟨x,rfl⟩ := B.coordinates.surjective x
    obtain ⟨y,rfl⟩ := B.coordinates.surjective y
    exact ⟨_,xy.symm.trans (B.cell x y)⟩
  choose f hf using hit
  have fi : Function.Injective f := fun x y h => A.labels.injective
    ((hf x).trans ((congrArg B.labels h).trans (hf y).symm))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi),hf⟩

private theorem range_comp {n} (f : Vertex → Fin n) (e : Equiv.Perm Vertex) (x : Fin n) :
    (∃ i, (f ∘ e) i = x) ↔ ∃ i, f i=x :=
  ⟨fun ⟨i,h⟩ => ⟨e i,h⟩,fun ⟨i,h⟩ => ⟨e.symm i,by simpa using h⟩⟩

theorem drawing_bipyramid : ∃ v : Array Certificate.PlanePoint, Certificate.Draws .bipyramid v := by
  refine ⟨#[(0,0),(395,501),(176,629),(1002,2),(131,502),(226,629),(23,1001),(322,375)],?_⟩
  unfold Certificate.Draws
  native_decide

private abbrev patternColors := List.replicate 18 1
private abbrev swap := [0,2,1]

/-- An arbitrary 15-point union of matched fibers, with every internal fiber
of size at least four. Both tables carry the perfect strategy's original names. -/
theorem solve {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (region : Nat → Prop)
    (f g : Vertex → Fin n) (D : DataFor p region f g) :
    ∃ h : Equiv.Perm Vertex, ∀ i j, source G (f i) (f j) = targetName p (g (h i)) (g (h j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  obtain ⟨a,⟨A⟩,⟨B⟩⟩ := Literature.zivAv_fifteen_common_catalog (c:=c) (d:=d)
    D.srcConfig D.tgtConfig D.srcLarge D.used D.products
  obtain ⟨e,he⟩ := match_names A B D.used
  have same (i j x y : Vertex) :
      e ((model a).name i j) = (model a).name x y ↔
      c (A.coordinates i) (A.coordinates j) = d (B.coordinates x) (B.coordinates y) := by
    rw [A.cell,B.cell,he,B.labels.injective.eq_iff]
  have laws : (model a).Laws e := by
    refine ⟨?_,?_,?_⟩
    · intro i j u v h
      have hit := (same _ _ _ _).mp h
      constructor
      · rintro rfl
        exact B.coordinates.injective (D.tgtConfig.diagonal _ _ _
          (hit.symm.trans (D.sameDiag (A.coordinates i))))
      · rintro rfl
        exact A.coordinates.injective (D.srcConfig.diagonal _ _ _
          (hit.trans (D.sameDiag (B.coordinates u)).symm))
    · intro i j u v h
      exact (same _ _ _ _).mpr (common_transpose p ((same _ _ _ _).mp h))
    · intro i j u v h
      obtain ⟨m,hm⟩ := pair_middle (c:=c) (d:=d)
        (fun l t => D.products l t _ _ _ _ ((same _ _ _ _).mp h))
      refine ⟨A.coordinates.trans (m.trans B.coordinates.symm),fun z => ⟨(same _ _ _ _).mpr ?_,
        (same _ _ _ _).mpr ?_⟩⟩
      · simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using (hm (A.coordinates z)).1
      · simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using (hm (A.coordinates z)).2
  have fixed : ∀ k ∈ base a, e k=k := by
    intro k hk
    by_cases id5 : (row a).id=5
    · have hk' : k=number a 1 := by simpa [base,id5] using hk
      subst k
      by_contra moved
      obtain ⟨literal,one,other⟩ := exceptional a id5
      let k := number a 1
      have tw := other (e k) (laws.diagonal _ _ _ _
        ((congrArg e (positions a k)).trans (positions a (e k)).symm)) moved
      have checked : Certificate.check Certificate.m_fifteen_5 Certificate.m_fifteen_5 .bipyramid
          swap patternColors 1239 1260 = true := Certificate.cert_fifteen_684
      apply Certificate.counts_differ_of_checked checked
      apply Certificate.RegionalPlanar.homCount_region p (by decide) region
        (f ∘ A.coordinates) (g ∘ B.coordinates) (D.injF.comp A.coordinates.injective)
        (D.injG.comp B.coordinates.injective) (fun z => (range_comp _ _ z).trans (D.src z))
        (fun z => (range_comp _ _ z).trans (D.tgt z)) _ _ rfl rfl .bipyramid drawing_bipyramid
        patternColors rfl (fun z => swap[z]?.getD Certificate.m_fifteen_5.rank)
      intro i j x y eq z hz
      have z1 : z=1 := (List.mem_replicate.mp hz).2
      subst z
      change Certificate.m_fifteen_5.get i.val j.val=1 ↔ Certificate.m_fifteen_5.get x.val y.val=2
      rw [←literal,←literal,←one,←tw,←(same i j x y).mpr eq]
      exact Fin.val_inj.trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm)
    · simp [base,id5] at hk
  obtain ⟨h,hh⟩ := System.check_sound (positions a) (chain a) (base a) (passes a) e laws fixed
  refine ⟨A.coordinates.symm.trans (h.trans B.coordinates),?_⟩
  intro i j
  obtain ⟨i,rfl⟩ := A.coordinates.surjective i
  obtain ⟨j,rfl⟩ := A.coordinates.surjective j
  simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (hh i j)

theorem isomorphic {n} {G H : Graph n} {xs : List Nat} (P : CoprimeProfiles.Profile G xs)
    (sum : (xs.filter (fun k => 3 < k)).sum=15) (q : QuantumIso G H) : Isomorphic G H :=
  LargeFifteenRegion.isomorphic_via_core_fifteen P sum (fun p f g D => solve p (large G) f g D) q

end QGI.Fifteen
