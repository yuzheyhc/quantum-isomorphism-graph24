import SmallUnionRealization

noncomputable section
namespace QGI.Coherent.ThreeFiberOverlap

open StrategyColorLaws SmallUnion
abbrev V := Fin 16
abbrev source (G : Graph 16) := Relations.color (closure G)

private def member (c : V → V → Nat) (v : Nat) (x : V) (h : c x x ≠ v) :
    {x // x ∈ vertices c (fun k => k≠v)} := ⟨x,(mem_vertices _ _ _).mpr h⟩

/-- Two named maps on intersecting unions of fibers glue after prescribing
two vertices in their overlap. On the overlap, the two anchor colors need
only determine the row of the graph on the last fiber. -/
theorem isomorphic {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (all : ∀ i, source G i i=l ∨ source G i i=u ∨ source G i i=v)
    (front : (vertices (source G) (fun k => k≠v)).card ≤ 13)
    (rear : (vertices (source G) (fun k => k≠l)).card ≤ 13)
    (a b : V) (da : source G a a=u) (db : source G b b=u)
    (uniform : ∀ i j x y, source G i i=l → source G j j=v → source G x x=l →
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
    rcases all i with h | h | h
    · obtain ⟨x,y,hxy⟩ := StrategyColors.exists_source p (T i) (T j)
      have eq := (associated p).mpr (StrategyColors.maps_support p hxy)
      obtain ⟨dx,dy⟩ := SmallShore.endpoints p eq
      exact (uniform i j x y h hj (dx.trans ((diag i).symm.trans h))
        (dy.trans ((diag j).symm.trans hj))).trans (common_edge p eq)
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
      refine (rows i x.val j h dx hj eqA eqB).trans (common_edge p ?_)
      rw [useZ _ hj,←ex]
      exact hr x (member c l j (hj ▸ Ne.symm lv))
    · exact (hi h).elim
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

end QGI.Coherent.ThreeFiberOverlap

