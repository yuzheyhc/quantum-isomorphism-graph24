import SmallFiberElimination
import PartialFunctional

noncomputable section
namespace QGI.Coherent.SmallFiberExtension

open StrategyColorLaws SmallUnion
open FourTwelveFunctional (source fiber_eq transport_thin)

abbrev Region {n : Nat} (c : Fin n → Fin n → Nat) (reg : Nat → Prop) :=
    {x : Fin n // x ∈ vertices c reg}

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

def Realizes (reg : Nat → Prop) : Prop := ∃ e : Region (source G) reg ≃ Region (targetName p) reg,
  ∀ i j, source G i.val j.val = targetName p (e i).val (e j).val

def includeRegion {reg : Nat → Prop} (s : Nat) (x : Region (source G) reg) :
    Region (source G) (fun v => reg v ∨ v=s) := ⟨x.val,(mem_vertices _ _ _).mpr (Or.inl ((mem_vertices _ _ _).mp x.property))⟩

private theorem size_named (b : Fin n) {s : Nat} (eq : source G b b=s) :
    vertices (source G) (fun v => v=s) = fiber G b := by
  ext x
  simp only [mem_vertices,fiber_eq,eq]

private theorem small_map (reg : Nat → Prop) (bound : (vertices (source G) reg).card ≤ 13) : Realizes p reg := by
  classical
  by_cases pos : 0 < (vertices (source G) reg).card
  · exact realize_region p reg pos bound
  · obtain ⟨e,he⟩ := diagonal_names p
    let f := Equiv.subtypeEquiv (p := fun x => x ∈ vertices (source G) reg)
      (q := fun x => x ∈ vertices (targetName p) reg) e (fun x => by simp only [mem_vertices,source,he x])
    exact ⟨f,fun x _ => (pos (Finset.card_pos.mpr ⟨_,x.property⟩)).elim⟩

private theorem bundle (reg : Nat → Prop) (f : Region (source G) reg → Fin n)
    (pairs : ∀ i j, source G i.val j.val = targetName p (f i) (f j)) :
    ∃ e : Region (source G) reg ≃ Region (targetName p) reg, ∀ i, (e i).val = f i := by
  classical
  let g (i : Region (source G) reg) : Region (targetName p) reg := ⟨f i,
    (mem_vertices _ _ _).mpr (pairs i i ▸ (mem_vertices _ _ _).mp i.property)⟩
  have inj : Function.Injective g := by
    intro x y h
    have eq : f x=f y := congrArg Subtype.val h
    have id := entries p (pairs x y) (closure H).one_mem (Intertwiner.initial_diagonal p)
    apply Subtype.ext
    by_contra ne
    simp [Matrix.one_apply,ne,eq] at id
  obtain ⟨u,hu⟩ := diagonal_names p
  let size := Equiv.subtypeEquiv (p := fun x => x ∈ vertices (source G) reg)
    (q := fun x => x ∈ vertices (targetName p) reg) u (fun x => by simp only [mem_vertices,source,hu x])
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨inj,Fintype.card_congr size⟩),fun _ => rfl⟩

private theorem uniform_merge (reg : Nat → Prop) (s : Nat)
    (e : Region (source G) reg ≃ Region (targetName p) reg)
    (he : ∀ i j, source G i.val j.val = targetName p (e i).val (e j).val)
    (q : Region (source G) (fun v => v=s) ≃ Region (targetName p) (fun v => v=s))
    (hq : ∀ i j, source G i.val j.val = targetName p (q i).val (q j).val)
    (uniform : ∀ a b i j, reg (source G a a) → source G b b=s →
      source G i i=source G a a → source G j j=s → source G a b=source G i j) :
    ∃ f : Region (source G) (fun v => reg v ∨ v=s) → Fin n,
      (∀ i j, source G i.val j.val=targetName p (f i) (f j)) ∧
      ∀ i, f (includeRegion s i)=(e i).val := by
  classical
  let c := source G
  let U := Region c (fun v => reg v ∨ v=s)
  let old (x : U) (h : reg (c x.val x.val)) : Region c reg := ⟨x.val,(mem_vertices _ _ _).mpr h⟩
  let new' (x : U) (h : ¬reg (c x.val x.val)) : Region c (fun v => v=s) :=
    ⟨x.val,(mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp x.property).resolve_left h)⟩
  let f (x : U) := if h : reg (c x.val x.val) then (e (old x h)).val else (q (new' x h)).val
  have diag (x : U) : c x.val x.val = targetName p (f x) (f x) := by
    by_cases h : reg (c x.val x.val)
    · rw [show f x=(e (old x h)).val from dif_pos h]; exact he (old x h) (old x h)
    · rw [show f x=(q (new' x h)).val from dif_neg h]; exact hq (new' x h) (new' x h)
  have mixed (x y : U) (hx : reg (c x.val x.val)) (hy : ¬reg (c y.val y.val)) :
      c x.val y.val = targetName p (f x) (f y) := by
    have sy : c y.val y.val=s := ((mem_vertices _ _ _).mp y.property).resolve_left hy
    obtain ⟨i,j,sup⟩ := StrategyColors.exists_source p (f x) (f y)
    have hit := (associated p).mpr (StrategyColors.maps_support p sup)
    obtain ⟨a,b⟩ := SmallShore.endpoints p hit
    exact (uniform x.val y.val i j hx sy (a.trans (diag x).symm) (b.trans ((diag y).symm.trans sy))).trans hit
  refine ⟨f,fun x y => ?_,fun i => ?_⟩
  · by_cases hx : reg (c x.val x.val) <;> by_cases hy : reg (c y.val y.val)
    · simpa only [f,dif_pos hx,dif_pos hy] using he (old x hx) (old y hy)
    · exact mixed x y hx hy
    · exact common_transpose p (mixed y x hy hx)
    · simpa only [f,dif_neg hx,dif_neg hy] using hq (new' x hx) (new' y hy)
  · exact dif_pos ((mem_vertices _ _ _).mp i.property)

/-- An already chosen named realization extends over any fiber of size at
most three. The isomorphism agrees at every previously placed point. -/
theorem extend_map (reg : Nat → Prop) (s : Nat) (bound : (vertices (source G) (fun v => v=s)).card ≤ 3)
    (e : Region (source G) reg ≃ Region (targetName p) reg)
    (he : ∀ i j, source G i.val j.val = targetName p (e i).val (e j).val) :
    ∃ h : Region (source G) (fun v => reg v ∨ v=s) ≃ Region (targetName p) (fun v => reg v ∨ v=s),
      (∀ i j, source G i.val j.val = targetName p (h i).val (h j).val) ∧
      ∀ i, (h (includeRegion s i)).val = (e i).val := by
  classical
  let c := source G
  let reg' := fun v => reg v ∨ v=s
  have obtainMap : ∃ f : Region c reg' → Fin n,
      (∀ i j, c i.val j.val=targetName p (f i) (f j)) ∧ ∀ i, f (includeRegion s i)=(e i).val := by
    by_cases uniform : ∀ a b i j, reg (c a a) → c b b=s → c i i=c a a → c j j=s → c a b=c i j
    · obtain ⟨q,hq⟩ := small_map p (fun v => v=s) (by omega)
      exact uniform_merge p reg s e he q hq uniform
    · push_neg at uniform
      obtain ⟨a,b,i,j,ra,bs,is,js,ne⟩ := uniform
      have size : (fiber G b).card ≤ 3 := (size_named b bs) ▸ bound
      obtain ⟨x,hx,y,hy,one⟩ := SmallFiberElimination.single_row G a b size
        ⟨i,(fiber_eq _ _).mpr is,j,(fiber_eq _ _).mpr (js.trans bs.symm),Ne.symm ne⟩
      have insideX : reg (c x x) := (congrArg reg ((fiber_eq _ _).mp hx)).mpr ra
      have sameY : c y y=s := ((fiber_eq _ _).mp hy).trans bs
      let U := Region c reg'
      have covered (k : U) : ∃ i : Region c reg, ∀ z, c i.val z=c i.val k.val → z=k.val := by
        by_cases h : reg (c k.val k.val)
        · exact ⟨⟨k.val,(mem_vertices _ _ _).mpr h⟩,fun z eq => (Relations.diagonal _ eq).symm⟩
        have ks : c k.val k.val=s := ((mem_vertices _ _ _).mp k.property).resolve_left h
        have diag := sameY.trans ks.symm
        obtain ⟨w,_,hit⟩ := PartialFunctional.middle c c (fun a b => Relations.products (closure G) a b _ _ _ _ diag) x
        have row := (Relations.end_colors (closure G) hit).1
        refine ⟨⟨w,(mem_vertices _ _ _).mpr ((congrArg reg row).mp insideX)⟩,fun z hz => ?_⟩
        exact transport_thin row one z k.val (hz.trans hit.symm) hit.symm
      obtain ⟨f,_,name,stay⟩ := PartialFunctional.extend p (fun x : U => x.val) Subtype.val_injective
        (fun i : Region c reg => i.val) (fun i => (e i).val) he covered
      exact ⟨f,name,fun i => stay i (includeRegion s i) rfl⟩
  obtain ⟨f,pairs,stay⟩ := obtainMap
  obtain ⟨h,same⟩ := bundle p reg' f pairs
  exact ⟨h,fun i j => (pairs i j).trans (congrArg₂ (targetName p) (same i).symm (same j).symm),
    fun i => (same _).trans (stay i)⟩

theorem extend (reg : Nat → Prop) (s : Nat) (bound : (vertices (source G) (fun v => v=s)).card ≤ 3)
    (real : Realizes p reg) : Realizes p (fun v => reg v ∨ v=s) := by
  obtain ⟨e,he⟩ := real
  obtain ⟨h,hh,_⟩ := extend_map p reg s bound e he
  exact ⟨h,hh⟩

private theorem convert_real {reg next : Nat → Prop} (iff : ∀ v, reg v ↔ next v)
    (h : Realizes p reg) : Realizes p next := by
  obtain ⟨e,he⟩ := h
  have hmem (m : Fin n → Fin n → Nat) (x : Fin n) : x ∈ vertices m reg ↔ x ∈ vertices m next := by
    simpa only [mem_vertices] using iff (m x x)
  let s := Equiv.subtypeEquivRight (hmem (source G))
  let t := Equiv.subtypeEquivRight (hmem (targetName p))
  exact ⟨(s.symm.trans e).trans t,fun x y => he (s.symm x) (s.symm y)⟩

theorem extend_names (reg : Nat → Prop) (names : Finset Nat)
    (bound : ∀ v ∈ names, (vertices (source G) (fun w => w=v)).card ≤ 3) (h : Realizes p reg) :
    Realizes p (fun v => reg v ∨ v∈names) := by
  induction names using Finset.induction_on with
  | empty =>
    exact convert_real p (fun _ => by simp) h
  | @insert v names hv ih =>
    have smaller := ih (fun t ht => bound t (Finset.mem_insert_of_mem ht))
    have add := extend p _ v (bound v (Finset.mem_insert_self _ _)) smaller
    exact convert_real p (fun t => by simp only [Finset.mem_insert]; tauto) add

private theorem full {reg : Nat → Prop} (h : Realizes p reg) (contains : ∀ i, reg (source G i i)) :
    ∃ e : Equiv.Perm (Fin n), ∀ x y, source G x y = targetName p (e x) (e y) := by
  obtain ⟨f,hf⟩ := h
  let i (x : Fin n) : Region (source G) reg := ⟨x,(mem_vertices _ _ _).mpr (contains x)⟩
  let g := fun x => (f (i x)).val
  have inj : Function.Injective g := by
    intro x y eq
    exact congrArg Subtype.val (f.injective (Subtype.ext eq))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp inj),fun x y => hf (i x) (i y)⟩

/-- Realizing the union of the fibers of cardinality greater than three
suffices for realizing every named color of the graph. -/
theorem of_large_region
    (real : Realizes p (fun v => 3 < (vertices (source G) (fun w => w=v)).card)) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, source G i j = targetName p (e i) (e j) := by
  classical
  let large := fun v => 3 < (vertices (source G) (fun w => w=v)).card
  let all := Finset.univ.image (fun i : Fin n => source G i i)
  let small := all.filter (fun v => ¬large v)
  have bound (v : Nat) (h : v∈small) : (vertices (source G) (fun w => w=v)).card ≤ 3 :=
    Nat.le_of_not_gt (Finset.mem_filter.mp h).2
  apply full p (extend_names p large small bound real)
  intro i
  by_cases h : large (source G i i)
  · exact Or.inl h
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,h⟩)

include p in
theorem isomorphic_of_small_core
    (size : (vertices (source G) (fun v => 3 < (vertices (source G) (fun w => w=v)).card)).card ≤ 13) :
    Isomorphic G H := by
  obtain ⟨e,h⟩ := of_large_region p (small_map p _ size)
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun x y => common_edge p (h x y)⟩

/-- In particular, two distinct two-point fibers on 16 vertices leave a
twelve-point core. This form also applies to unequal sizes and other orders. -/
theorem isomorphic_of_two_small {G H : Graph n} (a b : Fin n) (ab : a ∉ fiber G b)
    (sa : (fiber G a).card ≤ 3) (sb : (fiber G b).card ≤ 3)
    (remaining : n-(fiber G a).card-(fiber G b).card ≤ 13) (qc : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,ng,ip,_,⟨p⟩⟩ := qc
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  let large := fun v => 3 < (vertices (source G) (fun w => w=v)).card
  have excludes (i x : Fin n) (size : (fiber G i).card ≤ 3) (hx : x ∈ fiber G i) : ¬large (source G x x) := by
    have same := (fiber_eq i x).mp hx
    have sz := size_named (G := G) i same.symm
    simpa only [large,sz,not_lt] using size
  have sub : vertices (source G) large ⊆ (fiber G a ∪ fiber G b)ᶜ := by
    intro x hx
    exact Finset.mem_compl.mpr (fun h => (Finset.mem_union.mp h).elim
      (fun ha => excludes a x sa ha ((mem_vertices _ _ _).mp hx))
      (fun hb => excludes b x sb hb ((mem_vertices _ _ _).mp hx)))
  have dj : Disjoint (fiber G a) (fiber G b) := by
    refine Finset.disjoint_left.mpr fun x ha hb => ab ((fiber_eq _ _).mpr ?_)
    exact ((fiber_eq _ _).mp ha).symm.trans ((fiber_eq _ _).mp hb)
  apply isomorphic_of_small_core p
  change (vertices (source G) large).card ≤ 13
  have bound := Finset.card_le_card sub
  rw [Finset.card_compl,Finset.card_union_of_disjoint dj,Fintype.card_fin] at bound
  omega

end QGI.Coherent.SmallFiberExtension
