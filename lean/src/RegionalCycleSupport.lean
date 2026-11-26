import FourEightMixed
import RegionalBinaryChoice
import StrategyOrientation
import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.RegionalCycleSupport
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle
open FourEightMixed (Four)
open Intertwiner Synchrony LargeFourteenRegion
open FourTwelveFunctional (source)

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p₀ : PerfectStrategy G H K) {reg : Nat → Prop} {left right : Fin k → Fin n}
  (data : DataFor p₀ reg left right)

include data in
theorem solve_patterns {l v : Nat} (F : Shore (source G) l Four)
    (Y : Shore (source G) v Eight)
    (u : Nat) (b : Eight → Edge) (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=u ↔ i∈edge (b j))
    (C : RepeatedCycle b)
    (possible : ∀ j : Fin k, ∃ s t : Fin n, ∀ z, source G (left j) (left j)=source G z z →
      (∀ i, source G (left j) (atPoint F i)=source G z (atPoint F i)) → z=s ∨ z=t) :
    ∃ h : Equiv.Perm (Fin k), ∀ i j, source G (left i) (left j)=targetName p₀ (right (h i)) (right (h j)) := by
  classical
  let p := p₀.symm
  let c := color (closure G)
  let d := targetName p
  let tl : Four ↪ Fin n := F.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  have every (t : Four) : ∃ j, C.label j=t := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun j => C.label j=t)).card by rw [C.twice]; decide)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  obtain ⟨j₀,hj₀⟩ := every 0
  let i₀ := C.points 0
  have cell₀ : c (atPoint F i₀) (atPoint Y j₀)=u := (cells _ _).mpr (by
    rw [C.edges,hj₀]; exact Finset.mem_map.mpr ⟨0,by decide,rfl⟩)
  let mark := d (atPoint Y j₀) (tl i₀)
  have marked (i j) : d (atPoint Y j) (tl i)=mark ↔ i∈edge (b j) := by
    rw [←cells,←cell₀]
    exact (target_same p _ _ _ _).trans ⟨Relations.transpose _,Relations.transpose _⟩
  have rowSet (j) : FourTwelveCycle.neighbors d mark (atPoint Y j) = (edge (b j)).map tl := by
    ext z
    constructor
    · intro hz
      have h := (target_same p _ _ _ _).mp (Finset.mem_filter.mp hz).2
      have endz := (end_colors (closure G) h).2.trans (F i₀).property
      let i := F.symm ⟨z,endz⟩
      have loc : tl i=z := congrArg Subtype.val (F.apply_symm_apply _)
      exact Finset.mem_map.mpr ⟨i,(marked i j).mp (loc.symm ▸ (Finset.mem_filter.mp hz).2),loc⟩
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(marked i j).mpr hi⟩
  have cyclePairs : ∀ i : Four, ∃ t : Four, ∀ z, i≠z → z≠t → ∃ k, edge (cycle k)={i,z} := by native_decide
  obtain ⟨m,hm⟩ := SmallUnion.diagonal_names p
  let sl := tl.trans m.symm.toEmbedding
  obtain ⟨ξ,e,nz,fixed⟩ := FourCycleVectors.fixed_of_cycle p sl tl mark (by
    intro i a ξ h
    have name : color (closure H) (sl i) (sl i) = d (tl i) (tl i) := by
      simpa only [sl,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using hm (sl i)
    have tag := (target_same p _ _ _ _).mp (name.symm.trans (DoubledEdges.diag_of_nonzero p h))
    let e : {z // c z z=l} := ⟨a,tag.symm.trans (F i).property⟩
    exact ⟨F.symm e,congrArg Subtype.val (F.apply_symm_apply e)⟩
    ) (by
    intro i
    obtain ⟨i,rfl⟩ := C.points.surjective i
    obtain ⟨exc,hs⟩ := cyclePairs i
    refine ⟨C.points exc,fun z h₁ h₂ => ?_⟩
    obtain ⟨z,rfl⟩ := C.points.surjective z
    obtain ⟨k,hk⟩ := hs z (fun eq => h₁ (congrArg C.points eq)) (fun eq => h₂ (congrArg C.points eq))
    obtain ⟨j,hj⟩ := every k
    refine ⟨atPoint Y j,?_⟩
    change FourTwelveCycle.neighbors d mark (atPoint Y j) = _
    simp only [rowSet,C.edges,hj,hk,Finset.map_insert,Finset.map_singleton,Equiv.toEmbedding_apply]
    )
  have available (i : Fin k) (a : Fin n) (ha : U p (right i) a ξ≠0) : ∃ j, left j=a := by
    have diag := DoubledEdges.diag_of_nonzero p ha
    have back := StrategyOrientation.reverse p p₀ diag
    apply (data.src _).mpr
    change reg (color (closure G) a a)
    rw [back]
    exact (data.tgt _).mp ⟨_,rfl⟩
  have entry (i : Fin k) (a : Fin n) (ha : U p (right i) a ξ≠0) (j : Four) :
      source H (right i) (sl j)=d a (tl (e j)) := by
    apply (associated p).mpr (StrategyColors.maps_support p ?_)
    intro zero
    have eq := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ξ) zero
    change U p (right i) a (U p (sl j) (tl (e j)) ξ)=0 at eq
    exact ha ((congrArg (U p (right i) a) (fixed j)).symm.trans eq)
  obtain ⟨h,hh⟩ := RegionalBinaryChoice.solve p right left data.injG data.injF ξ nz (by
    intro i
    obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ξ nz (right i)
    obtain ⟨j,rfl⟩ := available i a ha
    obtain ⟨s,t,lim⟩ := possible j
    let coord (z : Fin n) := if ok : ∃ x, left x=z then ok.choose else j
    have ret (z : Fin n) (ok : ∃ x, left x=z) : left (coord z)=z := by
      simpa only [coord,dif_pos ok] using ok.choose_spec
    refine ⟨coord s,coord t,fun z hz => ?_⟩
    have dx := (DoubledEdges.diag_of_nonzero p ha).symm.trans (DoubledEdges.diag_of_nonzero p hz)
    rcases lim z ((target_same p _ _ _ _).mp dx) (fun idx => by
      obtain ⟨idx,rfl⟩ := e.surjective idx
      exact (target_same p _ _ _ _).mp ((entry i _ ha idx).symm.trans (entry i _ hz idx))) with eq|eq
    · exact Or.inl (eq ▸ (ret z (available i z hz)).symm)
    · exact Or.inr (eq ▸ (ret z (available i z hz)).symm))
  refine ⟨h.symm,fun i j => ?_⟩
  have h' := StrategyOrientation.reverse p p₀ (hh (h.symm i) (h.symm j))
  simpa only [Equiv.apply_symm_apply] using h'

include data in
theorem solve {l r v : Nat} (F : Shore (source G) l Four) (S : Shore (source G) r Four)
    (Y : Shore (source G) v Eight)
    (inside : ∀ i, source G (left i) (left i)=l ∨ source G (left i) (left i)=r ∨ source G (left i) (left i)=v)
    (mixed : ∃ i j, source G (atPoint F i) (atPoint S j) ≠ source G (atPoint F 0) (atPoint S 0))
    (u : Nat) (b : Eight → Edge) (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=u ↔ i∈edge (b j))
    (C : RepeatedCycle b) :
    ∃ h : Equiv.Perm (Fin k), ∀ i j, source G (left i) (left j)=targetName p₀ (right (h i)) (right (h j)) := by
  exact solve_patterns p₀ data F Y u b cells C (fun j => FourEightMixed.patterns_at F S Y (left j)
    ((inside j).imp_right (Or.imp_right Or.inl)) mixed u b cells C)

end QGI.Coherent.RegionalCycleSupport
