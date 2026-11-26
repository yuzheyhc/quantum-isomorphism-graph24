import SmallUnionRealization
import SixTenCoordinates
import SplitRectangleGluing

noncomputable section
namespace QGI.Coherent.ThreeFiberTwins

open SixTenCoordinates StrategyColorLaws

abbrev Points (c : Coloring) (l : Nat) := {x : V // c x x = l}
abbrev Outside (c : Coloring) (l : Nat) := {x : V // c x x ≠ l}

def twinBlock (c : Coloring) (l k : Nat) : Prop :=
  SplitRectangle.Twins (fun (x : Points c l) (y : Points c k) => c x.val y.val)

variable {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem back : Laws (targetName p) (Relations.color (closure G)) :=
  ⟨fun h => (common_transpose p h.symm).symm,fun h => (SmallShore.endpoints p h.symm).2.symm,
   fun a b _ _ _ _ h => (common_products p a b h.symm).symm⟩

private theorem rectangle {l k : Nat}
    (f : Points (Relations.color (closure G)) l ≃ Points (targetName p) l)
    (r : Outside (Relations.color (closure G)) l ≃ Outside (targetName p) l)
    (hf : ∀ i j, Relations.color (closure G) i.val j.val = targetName p (f i).val (f j).val)
    (hr : ∀ i j, Relations.color (closure G) i.val j.val = targetName p (r i).val (r j).val)
    (i₀ : Points (Relations.color (closure G)) l) (j₀ : Outside (Relations.color (closure G)) l)
    (hj : Relations.color (closure G) j₀.val j₀.val = k)
    (base : Relations.color (closure G) i₀.val j₀.val = targetName p (f i₀).val (r j₀).val)
    (twins : twinBlock (Relations.color (closure G)) l k)
    (i : Points (Relations.color (closure G)) l) (j : Outside (Relations.color (closure G)) l)
    (name : Relations.color (closure G) j.val j.val = k) :
    Relations.color (closure G) i.val j.val = targetName p (f i).val (r j).val := by
  let c := Relations.color (closure G)
  let d := targetName p
  let j0 : Points c k := ⟨j₀.val,hj⟩
  let j' : Points c k := ⟨j.val,name⟩
  have column : c i.val j₀.val = d (f i).val (r j₀).val := by
    obtain ⟨e,he⟩ := (back p).middle (hf i₀ i).symm
    obtain ⟨h₁,h₂⟩ := he (r j₀).val
    have match' := base.trans h₁
    let mid : Points c k := ⟨_,(Relations.end_colors _ match').2.symm.trans hj⟩
    have eq := twins.2 i₀ j0 mid match' i
    exact common_transpose p ((Relations.transpose _ eq).trans h₂.symm)
  obtain ⟨e,he⟩ := (back p).middle (hr j₀ j).symm
  obtain ⟨h₁,h₂⟩ := he (f i).val
  have same := (common_transpose p column).trans h₁
  let mid : Points c l := ⟨_,(Relations.end_colors _ same).2.symm.trans i.property⟩
  exact (twins.1 i mid j0 (Relations.transpose _ same) j').trans h₂.symm

include p in
/-- A single homogeneous fiber meets at most two other fibers. A named
isomorphism of the exterior extends whenever each incident rectangle has
the twin property. One exterior point in each fiber fixes both orientations. -/
theorem isomorphic {l : Nat} {k : Nat} (F : Shore (Relations.color (closure G)) l (Fin k))
    (a : Fin k) (small : k ≤ 13) (y z : Outside (Relations.color (closure G)) l)
    (restSmall : (SmallUnion.vertices (Relations.color (closure G)) (fun v => v ≠ l)).card ≤ 13)
    (cover : ∀ j : Outside (Relations.color (closure G)) l,
      Relations.color (closure G) j.val j.val = Relations.color (closure G) y.val y.val ∨
      Relations.color (closure G) j.val j.val = Relations.color (closure G) z.val z.val)
    (first : twinBlock (Relations.color (closure G)) l (Relations.color (closure G) y.val y.val))
    (second : twinBlock (Relations.color (closure G)) l (Relations.color (closure G) z.val z.val)) :
    Isomorphic G H := by
  classical
  let c := Relations.color (closure G)
  let d := targetName p
  let neg := fun v : Nat => v ≠ l
  have reg (m : Coloring) (x : V) : m x x ≠ l ↔ x ∈ SmallUnion.vertices m neg := (SmallUnion.mem_vertices m neg x).symm
  have positive : 0 < (SmallUnion.vertices c neg).card := Finset.card_pos.mpr ⟨y.val,(reg c y.val).mp y.property⟩
  obtain ⟨r0,hr0⟩ := SmallUnion.realize_region p neg positive restSmall
  let r : Outside c l ≃ Outside d l :=
    ((Equiv.subtypeEquivRight (reg c)).trans r0).trans (Equiv.subtypeEquivRight (reg d)).symm
  have hr (i j : Outside c l) : c i.val j.val = d (r i).val (r j).val :=
    hr0 ((Equiv.subtypeEquivRight (reg c)) i) ((Equiv.subtypeEquivRight (reg c)) j)
  obtain ⟨m,hm⟩ := SmallUnion.diagonal_names p
  let T : Shore d l (Fin k) := F.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
  let i₀ := F a
  obtain ⟨e,he⟩ := (commonLaws p).middle (hr y z)
  obtain ⟨incY,incZ⟩ := he i₀.val
  let s : Points d l := ⟨e i₀.val,(SmallShore.endpoints p incY).2.symm.trans i₀.property⟩
  have onto {h : Coloring} (S : Shore h l (Fin k)) (x : V) :
      (∃ j, atPoint S j = x) ↔ h x x = l := by
    refine ⟨fun ⟨j,eq⟩ => eq ▸ (S j).property,fun h => ?_⟩
    exact ⟨S.symm ⟨x,h⟩,congrArg Subtype.val (S.apply_symm_apply _)⟩
  have inj {h : Coloring} (S : Shore h l (Fin k)) : Function.Injective (atPoint S) :=
    fun _ _ eq => S.injective (Subtype.ext eq)
  obtain ⟨u,atA,hu⟩ := SmallShore.realize_at p (Nat.zero_lt_of_lt a.isLt) small
    (atPoint F) (atPoint T) l (inj F) (inj T) (onto F) (onto T) a (T.symm s)
  let f : Points c l ≃ Points d l := (F.symm.trans u).trans T
  have hf (i j : Points c l) : c i.val j.val = d (f i).val (f j).val := by
    simpa only [atPoint,Equiv.apply_symm_apply] using hu (F.symm i) (F.symm j)
  have anchor : f i₀ = s := by
    exact (congrArg (fun j => T (u j)) (F.symm_apply_apply a)).trans ((congrArg T atA).trans (T.apply_symm_apply s))
  have mixed (i : Points c l) (j : Outside c l) : c i.val j.val = d (f i).val (r j).val := by
    rcases cover j with h | h
    · apply rectangle p f r hf hr i₀ y rfl _ first i j h
      rw [anchor]; exact common_transpose p incY
    · apply rectangle p f r hf hr i₀ z rfl _ second i j h
      rw [anchor]; exact incZ
  let E := ((Equiv.sumCompl (fun i : V => c i i=l)).symm.trans (Equiv.sumCongr f r)).trans
    (Equiv.sumCompl (fun i : V => d i i=l))
  refine ⟨⟨E,E.symm,E.symm_apply_apply,E.apply_symm_apply,?_⟩⟩
  intro x y
  obtain ⟨x,rfl⟩ := (Equiv.sumCompl (fun i : V => c i i=l)).surjective x
  obtain ⟨y,rfl⟩ := (Equiv.sumCompl (fun i : V => c i i=l)).surjective y
  simp only [E,Equiv.trans_apply,Equiv.symm_apply_apply]
  cases x with
  | inl x =>
    cases y with
    | inl y => exact common_edge p (hf x y)
    | inr y => exact common_edge p (mixed x y)
  | inr x =>
    cases y with
    | inl y => exact common_edge p (common_transpose p (mixed y x))
    | inr y => exact common_edge p (hr x y)

end QGI.Coherent.ThreeFiberTwins
