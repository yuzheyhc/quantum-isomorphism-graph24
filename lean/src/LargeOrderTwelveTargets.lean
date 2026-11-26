import LargeOrderTwelveCycle
import FourCycleVectors

noncomputable section
namespace QGI.Coherent.LargeOrderTwelveTargets
open SixTenCoordinates LargeOrderFourFourTwelveGeometry LargeOrderSquareInterface FourTwelveCycle FourTwelveTypes
open SmallUnion SmallFiberExtension StrategyColorLaws Synchrony Intertwiner
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)

variable {n l v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G
local notation "d₀" => targetName p

structure Model (F : Shore c₀ l I) (Y : Shore c₀ v Twelve) where
  four : Shore d₀ l I
  twelve : Shore d₀ v Twelve
  cross : ∀ j i, c₀ (atPoint Y j) (atPoint F i)=d₀ (atPoint twelve j) (atPoint four i)
  internal : ∀ i j, c₀ (atPoint Y i) (atPoint Y j)=d₀ (atPoint twelve i) (atPoint twelve j)

theorem model (F : Shore c₀ l I) (Y : Shore c₀ v Twelve) (lv : l≠v) : Nonempty (Model p F Y) := by
  let keep := fun t => t=l ∨ t=v
  obtain ⟨e,he⟩ := LargeOrderTwelveCycle.pair p F Y lv
  let put (z : Fin n) (h : keep (c₀ z z)) : Region c₀ keep := ⟨z,(mem_vertices _ _ _).mpr h⟩
  have transport {k s : Nat} (A : Shore c₀ s (Fin k)) (inside : keep s) : ∃ T : Shore d₀ s (Fin k),
      ∀ i, atPoint T i=(e (put (atPoint A i) ((A i).property.symm ▸ inside))).val := by
    obtain ⟨m,hm⟩ := diagonal_names p
    let Z : Shore d₀ s (Fin k) := A.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
    let z (i : Fin k) := put (atPoint A i) ((A i).property.symm ▸ inside)
    let send (i : Fin k) : {a : Fin n // d₀ a a=s} := ⟨(e (z i)).val,(he (z i) (z i)).symm.trans (A i).property⟩
    have inj : Function.Injective send := by
      intro i j eq
      apply (emb A).injective
      have values : (send i).val=(send j).val := congrArg Subtype.val eq
      have same : e (z i)=e (z j) := Subtype.ext values
      exact congrArg (fun q : Region c₀ keep => q.val) (e.injective same)
    let perm := Equiv.ofBijective (fun i => Z.symm (send i)) (Finite.injective_iff_bijective.mp (Z.symm.injective.comp inj))
    refine ⟨perm.trans Z,fun i => ?_⟩
    exact congrArg Subtype.val (Z.apply_symm_apply (send i))
  obtain ⟨T,tt⟩ := transport F (Or.inl rfl)
  obtain ⟨Z,zz⟩ := transport Y (Or.inr rfl)
  refine ⟨⟨T,Z,fun j i => ?_,fun i j => ?_⟩⟩
  · rw [zz,tt]
    exact he (put _ (Or.inr (Y j).property)) (put _ (Or.inl (F i).property))
  · rw [zz,zz]
    exact he (put _ (Or.inr (Y i).property)) (put _ (Or.inr (Y j).property))

variable {F : Shore (source G) l I} {Y : Shore (source G) v Twelve}

theorem target_columns (B : Layout F Y) (M : Model p F Y) (j) :
    neighbors d₀ B.mark (atPoint M.twelve j)=(edge (B.col j)).map (emb M.four) := by
  let i₀ := (FourTwelveCycle.ends (B.col j)).1
  have initial : d₀ (atPoint M.twelve j) (atPoint M.four i₀)=B.mark := (M.cross j i₀).symm.trans
    ((B.cells j i₀).mpr (by simp [i₀,edge]))
  ext z
  constructor
  · intro hz
    have raw := (Finset.mem_filter.mp hz).2
    obtain ⟨i,rfl⟩ := (range_emb M.four z).mpr (((target_same p _ _ _ _).mpr
      (Relations.end_colors (closure H) ((target_same p _ _ _ _).mp (raw.trans initial.symm))).2).trans (M.four i₀).property)
    exact Finset.mem_map.mpr ⟨i,(B.cells j i).mp ((M.cross j i).trans raw),rfl⟩
  · intro hz; obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(M.cross j i).symm.trans ((B.cells j i).mpr hi)⟩

theorem fixed (B : Layout F Y) (M : Model p F Y) (strong : Nonempty (Around B) ∨ ∀ e, mult B.col e=2) :
    ∃ (ξ : cyclic p) (e : Equiv.Perm I), ξ≠0 ∧ ∀ i, U p (atPoint F i) (atPoint M.four (e i)) ξ=ξ := by
  have pairs (i : I) : ∃ t : I, ∀ z, i≠z → z≠t → ∃ j, edge (B.col j)={i,z} := by
    rcases strong with cycleCase|full
    · obtain ⟨C⟩ := cycleCase
      obtain ⟨i,rfl⟩ := C.points.surjective i
      have existsPair : ∀ i : I, ∃ t : I, ∀ z, i≠z → z≠t → ∃ k, edge (cycle k)={i,z} := by native_decide
      obtain ⟨t,all⟩ := existsPair i
      refine ⟨C.points t,fun z iz zt => ?_⟩
      obtain ⟨z,rfl⟩ := C.points.surjective z
      obtain ⟨k,hk⟩ := all z (fun h => iz (congrArg C.points h)) (fun h => zt (congrArg C.points h))
      obtain ⟨j,hj⟩ := C.onto k
      exact ⟨j,by rw [C.pattern,hj,hk,Finset.map_insert,Finset.map_singleton]; rfl⟩
    · refine ⟨i,fun z ne _ => ?_⟩
      obtain ⟨e,he⟩ := (by native_decide : ∀ i z : I, i≠z → ∃ e, edge e={i,z}) i z ne
      obtain ⟨j,hj⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (full e).symm)
      exact ⟨j,by rw [(Finset.mem_filter.mp hj).2,he]⟩
  apply FourCycleVectors.fixed_of_cycle p (emb F) (emb M.four) B.mark
  · intro i z ξ h
    exact (range_emb M.four z).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (F i).property)
  · intro i
    obtain ⟨t,all⟩ := pairs i
    refine ⟨t,fun z iz zt => ?_⟩
    obtain ⟨j,hj⟩ := all z iz zt
    exact ⟨atPoint M.twelve j,by rw [target_columns p B M j,hj,Finset.map_insert,Finset.map_singleton]⟩

end QGI.Coherent.LargeOrderTwelveTargets
