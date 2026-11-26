import ThreeFiberOverlap
import ThreeFiberTwins
import SingletonSwitch

noncomputable section
namespace QGI.Coherent.SeventeenHardGlue
open StrategyColorLaws SmallUnion
open FourTwelveFunctional (source)
open private pair_middle from SingletonSwitch
variable {n : Nat}
local notation "V" => Fin n
local notation "Coloring" => V → V → Nat
abbrev Shore {n : Nat} (c : Fin n → Fin n → Nat) (l : Nat) (X : Type) := X ≃ {z // c z z=l}
abbrev atPoint {n l X} {c : Fin n → Fin n → Nat} (s : Shore c l X) (i : X) := (s i).val

namespace Overlap
private def member (c : V → V → Nat) (v : Nat) (x : V) (h : c x x ≠ v) :
    {x // x ∈ vertices c (fun k => k≠v)} := ⟨x,(mem_vertices _ _ _).mpr h⟩

/-- Two named maps on intersecting unions of fibers glue after prescribing
two vertices in their overlap. On the overlap, the two anchor colors need
only determine the row of the graph on the last fiber. -/
theorem isomorphic {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (front : (vertices (source G) (fun k => k≠v)).card ≤ 13)
    (rear : (vertices (source G) (fun k => k≠l)).card ≤ 13)
    (a b : V) (da : source G a a=u) (db : source G b b=u)
    (uniform : ∀ i j x y, source G i i≠u → source G i i≠v → source G j j=v → source G x x=source G i i →
      source G y y=v → G.edge i j = G.edge x y)
    (rows : ∀ i x j, source G i i=u → source G x x=u → source G j j=v →
      source G a i = source G a x → source G b i = source G b x → G.edge i j = G.edge x j) :
    Isomorphic G H := by
  classical
  let c := source G
  let d := targetName p
  have frontPos : 0 < (vertices c (fun k => k≠v)).card :=
    Finset.card_pos.mpr ⟨a,(member c v a (fun h => uv (da.symm.trans h))).property⟩
  have rearPos : 0 < (vertices c (fun k => k≠l)).card :=
    Finset.card_pos.mpr ⟨a,(member c l a (fun h => lu (h.symm.trans da))).property⟩
  obtain ⟨r,hr⟩ := realize_region p (fun k => k≠l) rearPos rear
  let ra := member c l a (fun h => lu (h.symm.trans da))
  let rb := member c l b (fun h => lu (h.symm.trans db))
  let fa := member c v a (fun h => uv (da.symm.trans h))
  let fb := member c v b (fun h => uv (db.symm.trans h))
  have raDiag : d (r ra).val (r ra).val = u := (hr ra ra).symm.trans da
  have rbDiag : d (r rb).val (r rb).val = u := (hr rb rb).symm.trans db
  obtain ⟨f,hfa,hfb,hf⟩ := realize_region_pair p (fun k => k≠v) frontPos front fa fb
    (member d v (r ra).val (raDiag ▸ uv)) (member d v (r rb).val (rbDiag ▸ uv)) (hr ra rb)
  have aEq : (f fa).val = (r ra).val := congrArg Subtype.val hfa
  have bEq : (f fb).val = (r rb).val := congrArg Subtype.val hfb
  let T (i : V) := if hi : c i i = v then (r (member c l i (hi ▸ Ne.symm lv))).val
    else (f (member c v i hi)).val
  have useZ (i : V) (hi : c i i=v) : T i = (r (member c l i (hi ▸ Ne.symm lv))).val := dif_pos hi
  have useF (i : V) (hi : c i i≠v) : T i = (f (member c v i hi)).val := dif_neg hi
  have diag (i : V) : c i i = d (T i) (T i) := by
    by_cases h : c i i=v
    · rw [useZ i h]; exact hr (member c l i (h ▸ Ne.symm lv)) (member c l i (h ▸ Ne.symm lv))
    · rw [useF i h]; exact hf (member c v i h) (member c v i h)
  have inj : Function.Injective T := by
    intro i j eq
    have same : c i i=c j j := (diag i).trans ((congrArg (fun x => d x x) eq).trans (diag j).symm)
    by_cases hi : c i i=v
    · have hj := same.symm.trans hi
      rw [useZ _ hi,useZ _ hj] at eq
      exact congrArg Subtype.val (r.injective (Subtype.ext eq))
    · have hj : c j j ≠ v := fun h => hi (same.trans h)
      rw [useF _ hi,useF _ hj] at eq
      exact congrArg Subtype.val (f.injective (Subtype.ext eq))
  have mixed (i j : V) (hi : c i i≠v) (hj : c j j=v) : G.edge i j = H.edge (T i) (T j) := by
    by_cases h : c i i≠u
    · obtain ⟨x,y,hxy⟩ := StrategyColors.exists_source p (T i) (T j)
      have eq := (associated p).mpr (StrategyColors.maps_support p hxy)
      obtain ⟨dx,dy⟩ := SmallShore.endpoints p eq
      exact (uniform i j x y h hi hj (dx.trans (diag i).symm)
        (dy.trans ((diag j).symm.trans hj))).trans (common_edge p eq)
    · have h := not_not.mp h
      have dt : d (T i) (T i) = u := (diag i).symm.trans h
      let y := member d l (T i) (dt ▸ Ne.symm lu)
      let x := r.symm y
      have ex : (r x).val=T i := congrArg Subtype.val (r.apply_symm_apply y)
      have exF : (r x).val = (f (member c v i hi)).val := ex.trans (useF _ hi)
      have eqA : c a i = c a x.val := (hf fa (member c v i hi)).trans (by
        rw [aEq,←exF]; exact (hr ra x).symm)
      have eqB : c b i = c b x.val := (hf fb (member c v i hi)).trans (by
        rw [bEq,←exF]; exact (hr rb x).symm)
      have dx : c x.val x.val=u := (hr x x).trans (by rw [ex]; exact dt)
      refine (rows i x.val j h dx hj eqA eqB).trans (common_edge p ?_)
      rw [useZ _ hj,←ex]
      exact hr x (member c l j (hj ▸ Ne.symm lv))
  let e := Equiv.ofBijective T (Finite.injective_iff_bijective.mp inj)
  refine ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,?_⟩⟩
  intro x y
  change G.edge x y = H.edge (T x) (T y)
  by_cases hx : c x x=v <;> by_cases hy : c y y=v
  · rw [useZ _ hx,useZ _ hy]
    exact common_edge p (hr (member c l x (hx ▸ Ne.symm lv)) (member c l y (hy ▸ Ne.symm lv)))
  · exact (G.symm _ _).trans ((mixed y x hy hx).trans (H.symm _ _))
  · exact mixed x y hx hy
  · rw [useF _ hx,useF _ hy]
    exact common_edge p (hf (member c v x hx) (member c v y hy))
end Overlap

namespace Twins
abbrev Points (c : Coloring) (l : Nat) := {x : V // c x x = l}
abbrev Outside (c : Coloring) (l : Nat) := {x : V // c x x ≠ l}

def twinBlock (c : Coloring) (l k : Nat) : Prop :=
  SplitRectangle.Twins (fun (x : Points c l) (y : Points c k) => c x.val y.val)

variable {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

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
    obtain ⟨e,he⟩ := pair_middle (fun a b => (common_products p a b (hf i₀ i)).symm)
    obtain ⟨h₁,h₂⟩ := he (r j₀).val
    have match' := base.trans h₁
    let mid : Points c k := ⟨_,(Relations.end_colors _ match').2.symm.trans hj⟩
    have eq := twins.2 i₀ j0 mid match' i
    exact common_transpose p ((Relations.transpose _ eq).trans h₂.symm)
  obtain ⟨e,he⟩ := pair_middle (fun a b => (common_products p a b (hr j₀ j)).symm)
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
      Relations.color (closure G) j.val j.val = Relations.color (closure G) z.val z.val ∨
      ∀ i x : Points (Relations.color (closure G)) l, ∀ w : Fin n,
        Relations.color (closure G) w w = Relations.color (closure G) j.val j.val →
        Relations.color (closure G) i.val j.val = Relations.color (closure G) x.val w)
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
  obtain ⟨e,he⟩ := pair_middle (fun a b => common_products p a b (hr y z))
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
    rcases cover j with h | h | h
    · apply rectangle p f r hf hr i₀ y rfl _ first i j h
      rw [anchor]; exact common_transpose p incY
    · apply rectangle p f r hf hr i₀ z rfl _ second i j h
      rw [anchor]; exact incZ
    · obtain ⟨w,t,hit⟩ := StrategyColors.exists_source p (f i).val (r j).val
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨dw,dt⟩ := SmallShore.endpoints p eq
      let x : Points c l := ⟨w,dw.trans (f i).property⟩
      exact (h i x t (dt.trans (hr j j).symm)).trans eq
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
end Twins
end QGI.Coherent.SeventeenHardGlue
