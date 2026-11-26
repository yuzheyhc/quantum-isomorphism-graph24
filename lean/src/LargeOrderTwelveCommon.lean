import LargeOrderTwelveVector
import LargeOrderTwelvePairs

noncomputable section
namespace QGI.Coherent.LargeOrderTwelveCommon
open SixTenCoordinates LargeOrderFourFourTwelveGeometry LargeOrderTwelveTargets LargeOrderTwelvePairs LargeOrderSquareInterface
open FourTwelveCycle FourTwelveTypes SmallUnion SmallFiberExtension StrategyColorLaws Synchrony Intertwiner
open LargeFourteenRegion
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)
open Classical

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G
local notation "d₀" => targetName p

private theorem row_partner (ξ : cyclic p) {i a : Fin n} (ha : U p i a ξ≠0) (j : Fin n) :
    ∃ b, U p j b ξ≠0 ∧ c₀ i j=d₀ a b := by
  have row : ∑ b, U p j b ξ=ξ := by
    apply Subtype.ext
    change (cyclic p).subtype (∑ b, U p j b ξ)=_
    rw [map_sum]; exact (magic_sums p j ξ).1
  have some' : ∃ b, U p i a (U p j b ξ)≠0 := by
    by_contra! none
    apply ha
    rw [←row,map_sum]
    simp [none]
  obtain ⟨b,h⟩ := some'
  refine ⟨b,fun zero => h (by rw [zero,map_zero]),(associated p).mpr (StrategyColors.maps_support p ?_)⟩
  intro zero
  exact h (congrArg (fun T : Module.End ℂ (cyclic p) => T ξ) zero)

private theorem pinned_name {ξ : cyclic p} {i j a b} (ha : U p i a ξ≠0) (hb : U p j b ξ=ξ) :
    c₀ i j=d₀ a b := by
  apply (associated p).mpr (StrategyColors.maps_support p ?_)
  intro zero
  have h := congrArg (fun T : Module.End ℂ (cyclic p) => T ξ) zero
  change U p i a (U p j b ξ)=0 at h
  exact ha (hb ▸ h)

attribute [local instance 2000] Classical.propDecidable

theorem realize (F : Shore c₀ l I) (S : Shore c₀ r I) (Y : Shore c₀ v Twelve)
    (lv : l≠v) (rv : r≠v) (B : Layout F Y) (C : Layout S Y)
    (twoB : ∀ e, mult B.col e=2)
    (j k : Twelve) (ne : j≠k) (BC : B.col j=B.col k) (CC : C.col j=C.col k)
    (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (cover : ∀ z, reg (c₀ z z) → c₀ z z=l ∨ c₀ z z=r ∨ c₀ z z=v) : Realizes p reg := by
  classical
  obtain ⟨M⟩ := model p F Y lv
  obtain ⟨N⟩ := model p S Y rv
  obtain ⟨ξ,e,nz,fix⟩ := fixed p B M (Or.inr twoB)
  let z₀ := atPoint N.twelve j
  let z₁ := atPoint N.twelve k
  have zn : z₀≠z₁ := (emb N.twelve).injective.ne ne
  obtain ⟨a,za⟩ := (range_emb M.twelve z₀).mpr (N.twelve j).property
  obtain ⟨b,zb⟩ := (range_emb M.twelve z₁).mpr (N.twelve k).property
  have inB : B.col a=B.col b := by
    have matchY : c₀ (atPoint Y a) (atPoint Y b)=c₀ (atPoint Y j) (atPoint Y k) := by
      calc _ = d₀ (atPoint M.twelve a) (atPoint M.twelve b) := M.internal a b
           _ = _ := (congrArg₂ (targetName p) za zb).trans (N.internal j k).symm
    exact (edge_overlap _ _).mp ((B.gram matchY).trans ((edge_overlap _ _).mpr BC))
  have ab : a≠b := fun h => zn (za.symm.trans ((congrArg (atPoint M.twelve) h).trans zb))
  obtain ⟨P⟩ := matching B.col twoB
  have mate := (P.unique a b).mp ⟨Ne.symm ab,inB.symm⟩
  have column : ∑ i, U p i z₀ ξ=ξ := by
    apply Subtype.ext
    change (cyclic p).subtype (∑ i, U p i z₀ ξ)=_
    rw [map_sum]; exact (magic_sums p z₀ ξ).2
  obtain ⟨x,hx⟩ : ∃ x, U p x z₀ ξ≠0 := by by_contra! none; exact nz (column.symm.trans (by simp [none]))
  obtain ⟨y,hy⟩ := (range_emb Y x).mpr ((DoubledEdges.diag_of_nonzero p hx).trans (N.twelve j).property)
  have choices (z) (hz : U p x z ξ≠0) : z=z₀ ∨ z=z₁ := by
    obtain ⟨t,ht⟩ := (range_emb M.twelve z).mpr (((DoubledEdges.diag_of_nonzero p hz).symm.trans
      (DoubledEdges.diag_of_nonzero p hx)).trans (N.twelve j).property)
    have same (s : I) : c₀ (atPoint Y t) (atPoint F s)=c₀ (atPoint Y a) (atPoint F s) := by
      have pin : RegionalPins.Pinned p ξ (atPoint M.four s) := by
        obtain ⟨i,rfl⟩ := e.surjective s
        exact ⟨atPoint F i,fix i⟩
      calc _ = d₀ (atPoint M.twelve t) (atPoint M.four s) := M.cross t s
           _ = d₀ (atPoint M.twelve a) (atPoint M.four s) := by change d₀ (emb M.twelve t) _=d₀ (emb M.twelve a) _; rw [ht,za]; exact RegionalPins.equal p ξ hz hx pin
           _ = _ := (M.cross a s).symm
    have edgeEq : B.col t=B.col a := by
      apply edge_inj; ext i; rw [←B.cells,←B.cells,same]
    by_cases ta : t=a
    · exact Or.inl (ht.symm.trans ((congrArg (atPoint M.twelve) ta).trans za))
    · exact Or.inr (ht.symm.trans ((congrArg (atPoint M.twelve) (((P.unique a t).mp ⟨ta,edgeEq⟩).trans mate.symm)).trans zb))
  have across (i z) (hi : c₀ i i=r) (hz : U p i z ξ≠0) : c₀ i x=d₀ z z₀ := by
    obtain ⟨t,nonzero,raw⟩ := row_partner p ξ hz x
    rcases choices t nonzero with atZero|atOne
    · exact raw.trans (congrArg (d₀ z) atZero)
    obtain ⟨q,hq⟩ := (range_emb N.four z).mpr ((DoubledEdges.diag_of_nonzero p hz).symm.trans hi)
    have cEq : c₀ (atPoint Y k) (atPoint S q)=c₀ (atPoint Y j) (atPoint S q) := by
      by_cases h : q∈edge (C.col j)
      · exact ((C.cells k q).mpr (CC ▸ h)).trans ((C.cells j q).mpr h).symm
      · exact ((C.palette k q).resolve_left (fun eq => h (CC.symm ▸ (C.cells k q).mp eq))).trans
          ((C.palette j q).resolve_left (mt (C.cells j q).mp h)).symm
    have eq : d₀ z₁ (atPoint N.four q)=d₀ z₀ (atPoint N.four q) := (N.cross k q).symm.trans (cEq.trans (N.cross j q))
    have reverse : d₀ (atPoint N.four q) z₁=d₀ (atPoint N.four q) z₀ :=
      (target_same p _ _ _ _).mpr (Relations.transpose _ ((target_same p _ _ _ _).mp eq))
    exact (raw.trans (congrArg (d₀ z) atOne)).trans (by rw [←hq]; exact reverse)
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g D
  let sh (i) := (c₀ (f i) (f i),fun j => c₀ (f i) (atPoint F j),if c₀ (f i) (f i)=r then c₀ (f i) x else 0)
  let th (a) := (d₀ (g a) (g a),fun j => d₀ (g a) (atPoint M.four (e j)),if d₀ (g a) (g a)=r then d₀ (g a) z₀ else 0)
  apply SmallVectorCells.of_partition (RegionalTernaryChoice.vector_data p D ξ nz) sh th
  · intro i a ha
    have diag := DoubledEdges.diag_of_nonzero p ha
    apply Prod.ext diag
    apply Prod.ext (funext (fun j => pinned_name p ha (fix j)))
    by_cases h : c₀ (f i) (f i)=r
    · exact (if_pos h).trans ((across (f i) (g a) h ha).trans (if_pos (diag.symm.trans h)).symm)
    · exact (if_neg h).trans (if_neg (fun eq => h (diag.trans eq))).symm
  · intro s
    by_cases used : ∃ i, sh i=s
    · obtain ⟨i,rfl⟩ := used
      apply LargeOrderTwelveVector.based p D F S Y B (Or.inr twoB) cover (fun u q => sh u=sh q) i
        (fun b eq => ⟨congrArg Prod.fst eq,congrFun (congrArg (fun t => t.2.1) eq)⟩)
      intro q hq
      let E := edge (C.col y)
      let J := if q∈E then E else Eᶜ
      have small : J.card≤3 := by
        have H : ∀ e : Edge, (edge e).card≤3 ∧ (edge e)ᶜ.card≤3 := by native_decide
        by_cases h : q∈E <;> simp only [J,h,if_true,if_false] <;> first | exact (H _).1 | exact (H _).2
      refine ⟨J,small,fun b eq t ht => ?_⟩
      have qi : c₀ (f i) (f i)=r := hq ▸ (S q).property
      have ti : c₀ (f b) (f b)=r := ht ▸ (S t).property
      have raw := congrArg (fun w => w.2.2) eq
      change (if c₀ (f b) (f b)=r then c₀ (f b) x else 0)=(if c₀ (f i) (f i)=r then c₀ (f i) x else 0) at raw
      rw [if_pos qi,if_pos ti,←hy,←ht,←hq] at raw
      have twin : t∈E ↔ q∈E := (C.cells y t).symm.trans ((Iff.of_eq (congrArg (·=C.mark) (Relations.transpose _ raw))).trans (C.cells y q))
      by_cases h : q∈E
      · simpa only [J,if_pos h] using twin.mpr h
      · simpa only [J,if_neg h,Finset.mem_compl] using mt twin.mp h
    · apply (Finset.card_eq_zero.mpr ?_).le.trans (by decide : 0≤3)
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i hi
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi
      exact used ⟨i,hi⟩

end QGI.Coherent.LargeOrderTwelveCommon
