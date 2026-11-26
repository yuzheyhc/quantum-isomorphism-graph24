import LargeOrderSubregions
import FourSixSixComplete

noncomputable section
namespace QGI.Coherent.LargeOrderFourSixGlue
open SmallUnion StrategyColorLaws LargeFourteenRegion SixTenCoordinates
open FourTwelveFunctional (source)
open ThreeFiberTwins (Outside)
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {reg : Nat → Prop} {F Tgt : V → Fin n} (D : DataFor p reg F Tgt)
local notation "c₀" => restricted (source G) F
local notation "d₀" => restricted (targetName p) Tgt
private def member (c : Coloring) (l : Nat) (i : V) (h : c i i≠l) : Outside c l := ⟨i,h⟩
include D

theorem overlap {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (all : ∀ i, c₀ i i=l ∨ c₀ i i=u ∨ c₀ i i=v)
    (front : (vertices c₀ (fun k => k≠v)).card ≤ 13)
    (rear : (vertices c₀ (fun k => k≠l)).card ≤ 13)
    (a b : V) (da : c₀ a a=u) (db : c₀ b b=u)
    (uniform : ∀ i j x y, c₀ i i=l → c₀ j j=v → c₀ x x=l → c₀ y y=v → c₀ i j = c₀ x y)
    (rows : ∀ i x j, c₀ i i=u → c₀ x x=u → c₀ j j=v →
      c₀ a i = c₀ a x → c₀ b i = c₀ b x → c₀ i j = c₀ x j) :
    ∃ e : Equiv.Perm V, ∀ i j, c₀ i j = d₀ (e i) (e j) := by
  classical
  let c := c₀
  let d := d₀
  obtain ⟨r,hr⟩ := LargeOrderSubregions.small p D (fun k => k≠l) rear
  let ra := member c l a (fun h => lu (h.symm.trans da))
  let rb := member c l b (fun h => lu (h.symm.trans db))
  let fa := member c v a (fun h => uv (da.symm.trans h))
  let fb := member c v b (fun h => uv (db.symm.trans h))
  have raDiag : d (r ra).val (r ra).val = u := (hr ra ra).symm.trans da
  have rbDiag : d (r rb).val (r rb).val = u := (hr rb rb).symm.trans db
  obtain ⟨f,hfa,hfb,hf⟩ := LargeOrderSubregions.pair p D (fun k => k≠v) front fa fb
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
  have mixed (i j : V) (hi : c i i≠v) (hj : c j j=v) : c i j = d (T i) (T j) := by
    rcases all i with h | h | h
    · obtain ⟨x,y,eq⟩ := (D.used _).mpr ⟨T i,T j,rfl⟩
      obtain ⟨dx,dy⟩ := SmallShore.endpoints p eq
      exact (uniform i j x y h hj (dx.trans ((diag i).symm.trans h))
        (dy.trans ((diag j).symm.trans hj))).trans eq
    · have dt : d (T i) (T i) = u := (diag i).symm.trans h
      let y := member d l (T i) (dt ▸ Ne.symm lu)
      let x := r.symm y
      have ex : (r x).val=T i := congrArg Subtype.val (r.apply_symm_apply y)
      have exF : (r x).val = (f (member c v i hi)).val := ex.trans (useF _ hi)
      have eqA : c a i = c a x.val := (hf fa (member c v i hi)).trans (by
        rw [aEq,←exF]; exact (hr ra x).symm)
      have eqB : c b i = c b x.val := (hf fb (member c v i hi)).trans (by
        rw [bEq,←exF]; exact (hr rb x).symm)
      have dx : c x.val x.val=u := (hr x x).trans (by rw [ex]; exact dt)
      refine (rows i x.val j h dx hj eqA eqB).trans ?_
      rw [useZ _ hj,←ex]
      exact hr x (member c l j (hj ▸ Ne.symm lv))
    · exact (hi h).elim
  let e := Equiv.ofBijective T (Finite.injective_iff_bijective.mp inj)
  refine ⟨e,?_⟩
  intro x y
  change c x y = d (T x) (T y)
  by_cases hx : c x x=v <;> by_cases hy : c y y=v
  · rw [useZ _ hx,useZ _ hy]
    exact hr (member c l x (hx ▸ Ne.symm lv)) (member c l y (hy ▸ Ne.symm lv))
  · exact common_transpose p (mixed y x hy hx)
  · exact mixed x y hx hy
  · rw [useF _ hx,useF _ hy]
    exact hf (member c v x hx) (member c v y hy)

private theorem back : Laws d₀ c₀ :=
  ⟨fun h => (common_transpose p h.symm).symm,fun h => (SmallShore.endpoints p h.symm).2.symm,
    fun a b _ _ _ _ h => (D.products a b _ _ _ _ h.symm).symm⟩

private theorem rectangle {l k : Nat}
    (f : ThreeFiberTwins.Points (c₀) l ≃ ThreeFiberTwins.Points (d₀) l)
    (r : Outside (c₀) l ≃ Outside (d₀) l)
    (hf : ∀ i j, c₀ i.val j.val = d₀ (f i).val (f j).val)
    (hr : ∀ i j, c₀ i.val j.val = d₀ (r i).val (r j).val)
    (i₀ : ThreeFiberTwins.Points (c₀) l) (j₀ : Outside (c₀) l)
    (hj : c₀ j₀.val j₀.val = k)
    (base : c₀ i₀.val j₀.val = d₀ (f i₀).val (r j₀).val)
    (twins : ThreeFiberTwins.twinBlock (c₀) l k)
    (i : ThreeFiberTwins.Points (c₀) l) (j : Outside (c₀) l)
    (name : c₀ j.val j.val = k) :
    c₀ i.val j.val = d₀ (f i).val (r j).val := by
  let c := c₀
  let d := d₀
  let j0 : ThreeFiberTwins.Points c k := ⟨j₀.val,hj⟩
  let j' : ThreeFiberTwins.Points c k := ⟨j.val,name⟩
  have column : c i.val j₀.val = d (f i).val (r j₀).val := by
    obtain ⟨e,he⟩ := (back p D).middle (hf i₀ i).symm
    obtain ⟨h₁,h₂⟩ := he (r j₀).val
    have match' := base.trans h₁
    let mid : ThreeFiberTwins.Points c k := ⟨_,(Relations.end_colors _ match').2.symm.trans hj⟩
    have eq := twins.2 i₀ j0 mid match' i
    exact common_transpose p ((Relations.transpose _ eq).trans h₂.symm)
  obtain ⟨e,he⟩ := (back p D).middle (hr j₀ j).symm
  obtain ⟨h₁,h₂⟩ := he (f i).val
  have same := (common_transpose p column).trans h₁
  let mid : ThreeFiberTwins.Points c l := ⟨_,(Relations.end_colors _ same).2.symm.trans i.property⟩
  exact (twins.1 i mid j0 (Relations.transpose _ same) j').trans h₂.symm

theorem twins {l : Nat} (i₀ : ThreeFiberTwins.Points c₀ l) (y z : Outside c₀ l)
    (small : (vertices c₀ (·=l)).card ≤ 13) (rear : (vertices c₀ (·≠l)).card ≤ 13)
    (cover : ∀ j : Outside c₀ l, c₀ j.val j.val=c₀ y.val y.val ∨ c₀ j.val j.val=c₀ z.val z.val)
    (first : ThreeFiberTwins.twinBlock c₀ l (c₀ y.val y.val))
    (second : ThreeFiberTwins.twinBlock c₀ l (c₀ z.val z.val)) :
    ∃ e : Equiv.Perm V, ∀ i j, c₀ i j = d₀ (e i) (e j) := by
  classical
  let c := c₀
  let d := d₀
  obtain ⟨r,hr⟩ := LargeOrderSubregions.small p D (fun k => k≠l) rear
  have law : Laws c d := ⟨fun h => common_transpose p h,fun h => (SmallShore.endpoints p h).2,
    fun a b i j x y h => D.products a b i j x y h⟩
  obtain ⟨e,he⟩ := law.middle (hr y z)
  obtain ⟨incY,incZ⟩ := he i₀.val
  let s : ThreeFiberTwins.Points d l := ⟨e i₀.val,(SmallShore.endpoints p incY).2.symm.trans i₀.property⟩
  obtain ⟨f,anchor,_,hf⟩ := LargeOrderSubregions.pair p D (fun k => k=l) small i₀ i₀ s s
    (i₀.property.trans s.property.symm)
  have mixed (i : ThreeFiberTwins.Points c l) (j : Outside c l) : c i.val j.val = d (f i).val (r j).val := by
    rcases cover j with h | h
    · apply rectangle p D f r hf hr i₀ y rfl _ first i j h
      rw [anchor]; exact common_transpose p incY
    · apply rectangle p D f r hf hr i₀ z rfl _ second i j h
      rw [anchor]; exact incZ
  let E := ((Equiv.sumCompl (fun i : V => c i i=l)).symm.trans (Equiv.sumCongr f r)).trans
    (Equiv.sumCompl (fun i : V => d i i=l))
  refine ⟨E,?_⟩
  intro x y
  obtain ⟨x,rfl⟩ := (Equiv.sumCompl (fun i : V => c i i=l)).surjective x
  obtain ⟨y,rfl⟩ := (Equiv.sumCompl (fun i : V => c i i=l)).surjective y
  simp only [E,Equiv.trans_apply,Equiv.symm_apply_apply]
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hf x y
    | inr y => exact mixed x y
  | inr x =>
    cases y with
    | inl y => exact common_transpose p (mixed y x)
    | inr y => exact hr x y

end QGI.Coherent.LargeOrderFourSixGlue
