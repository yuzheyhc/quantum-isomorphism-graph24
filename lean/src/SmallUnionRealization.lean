import FourTwelveFunctional

noncomputable section
open scoped BigOperators

namespace QGI.Coherent.SmallUnion
open Relations StrategyColorLaws

private theorem restrict_count {n k} {c : Table n} {keep : Nat → Prop} {f : Fin k → Fin n}
    (inj : Function.Injective f) (range : ∀ z, (∃ i, f i=z) ↔ keep (c z z))
    (ends : ∀ {i j x y}, c i j = c x y → c j j = c y y)
    {s : Nat} (occurs : ∃ i j, c (f i) (f j) = s) (t : Nat) (i j : Fin k) :
    count (SmallShore.restrict c f) s t i j = count c s t (f i) (f j) := by
  obtain ⟨a,b,rfl⟩ := occurs
  let value := fun z => if c (f i) z = c (f a) (f b) ∧ c z (f j) = t then 1 else 0
  change (∑ z, value (f z)) = ∑ z, value z
  apply Fintype.sum_of_injective f inj _ value _ (fun _ => rfl)
  intro z outside
  have forbid : c (f i) z ≠ c (f a) (f b) := by
    intro h
    exact outside ((range z).mpr ((ends h).symm ▸ ((range (f b)).mp ⟨b,rfl⟩)))
  simp [value,forbid]

private theorem induce {n k} {c : Table n} (cc : Configuration c)
    (ends : ∀ {i j x y}, c i j = c x y → c j j = c y y)
    {keep : Nat → Prop} (f : Fin k → Fin n)
    (hf : Function.Injective f) (region : ∀ z, (∃ i, f i=z) ↔ keep (c z z)) :
    Configuration (SmallShore.restrict c f) := by
  refine ⟨fun _ _ _ h => hf (cc.diagonal _ _ _ h),fun _ _ _ _ h => cc.reverse _ _ _ _ h,?_⟩
  intro a b i j x y eq
  change count (SmallShore.restrict c f) a b i j = count (SmallShore.restrict c f) a b x y
  by_cases occ : ∃ i j, c (f i) (f j) = a
  · rw [restrict_count hf region ends occ,restrict_count hf region ends occ]
    exact cc.products a b _ _ _ _ eq
  · push_neg at occ
    simp [count, SmallShore.restrict,occ]

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem target_config : Configuration (targetName p) :=
  ⟨fun _ _ _ h => diagonal _ ((target_same p _ _ _ _).mp h),
    fun _ _ _ _ h => (target_same p _ _ _ _).mpr (transpose _ ((target_same p _ _ _ _).mp h)),
    DoubleEight.FixedInterface.rename_products (fun i j x y => (target_same p i j x y).symm) (Relations.products _)⟩

/-- Restricting to the same union of fiber names leaves two coherent
configurations with the same used colors and intersection numbers. -/
theorem correspondence {k : Nat} (region : Nat → Prop)
    (f g : Fin k → Fin n) (hf : Function.Injective f) (hg : Function.Injective g)
    (src : ∀ z, (∃ i, f i=z) ↔ region (color (closure G) z z))
    (tgt : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z)) :
    let c := SmallShore.restrict (color (closure G)) f
    let d := SmallShore.restrict (targetName p) g
    Configuration c ∧ Configuration d ∧
      (∀ a, (∃ i j, c i j=a) ↔ ∃ x y, d x y=a) ∧
      ∀ a b i j x y, c i j=d x y → count c a b i j = count d a b x y := by
  let c := color (closure G)
  let d := targetName p
  have ends {i j x y : Fin n} (h : c i j = c x y) := (end_colors (closure G) h).2
  have endd {i j x y : Fin n} (h : d i j = d x y) :=
    (target_same p _ _ _ _).mpr (end_colors (closure H) ((target_same p _ _ _ _).mp h)).2
  have first : Configuration c :=
    ⟨fun _ _ _ h => diagonal _ h,fun _ _ _ _ h => transpose _ h,Relations.products _⟩
  have second : Configuration d := target_config p
  have used (a : Nat) : (∃ i j, c (f i) (f j) = a) ↔ ∃ x y, d (g x) (g y) = a := by
    constructor
    · rintro ⟨i,j,rfl⟩
      obtain ⟨s,t,hit⟩ := StrategyColors.exists_target p (f i) (f j)
      have h := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨l,r⟩ := SmallShore.endpoints p h
      obtain ⟨x,rfl⟩ := (tgt s).mpr (l ▸ ((src _).mp ⟨i,rfl⟩))
      obtain ⟨y,rfl⟩ := (tgt t).mpr (r ▸ ((src _).mp ⟨j,rfl⟩))
      exact ⟨x,y,h.symm⟩
    · rintro ⟨x,y,rfl⟩
      obtain ⟨s,t,hit⟩ := StrategyColors.exists_source p (g x) (g y)
      have h := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨l,r⟩ := SmallShore.endpoints p h
      obtain ⟨i,rfl⟩ := (src s).mpr (l.symm ▸ ((tgt _).mp ⟨x,rfl⟩))
      obtain ⟨j,rfl⟩ := (src t).mpr (r.symm ▸ ((tgt _).mp ⟨y,rfl⟩))
      exact ⟨i,j,h⟩
  refine ⟨induce first ends f hf src,induce second endd g hg tgt,used,?_⟩
  intro a b i j x y eq
  by_cases hits : ∃ i j, c (f i) (f j) = a
  · rw [restrict_count hf src ends hits,restrict_count hg tgt endd ((used _).mp hits)]
    exact common_products p _ _ eq
  · have absent := mt (used _).mpr hits
    push_neg at hits absent
    simp [count,SmallShore.restrict,c,d] at hits absent ⊢
    simp [hits,absent]

/-- Realize the strategy's color names on any union of diagonal classes of
size at most thirteen, in any chosen source and target coordinates. -/
theorem realize {k : Nat} (positive : 0 < k) (small : k ≤ 13) (region : Nat → Prop)
    (f g : Fin k → Fin n) (hf : Function.Injective f) (hg : Function.Injective g)
    (src : ∀ z, (∃ i, f i=z) ↔ region (color (closure G) z z))
    (tgt : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z)) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, color (closure G) (f i) (f j) = targetName p (g (e i)) (g (e j)) := by
  obtain ⟨first,second,used,products⟩ := correspondence p region f g hf hg src tgt
  exact Literature.zivAv_named_small_configuration positive small first second used products

def vertices {n : Nat} (c : Table n) (region : Nat → Prop) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => region (c i i))

@[simp] theorem mem_vertices {n : Nat} (c : Table n) (region : Nat → Prop) (x : Fin n) :
    x ∈ vertices c region ↔ region (c x x) := by classical simp [vertices]

/-- Equality of the trace of every diagonal-name indicator matches all
diagonal classes at once, without choosing internal point realizations. -/
theorem diagonal_names : ∃ e : Equiv.Perm (Fin n), ∀ x, color (closure G) x x = targetName p (e x) (e x) := by
  classical
  let c := fun x => color (closure G) x x
  let d := fun y => targetName p y y
  have sized (v : Nat) : Fintype.card {x // c x = v} = Fintype.card {x // d x = v} := by
    simpa [Matrix.trace,Matrix.diag_apply,mark,c,d,Fintype.card_subtype]
      using Intertwiner.trace_eq p (mark_intertwines p v)
  let family := fun v => Fintype.equivOfCardEq (sized v)
  exact ⟨Equiv.ofFiberEquiv family,fun x => (Equiv.ofFiberEquiv_map family x).symm⟩

/-- Coordinate-free realization on the induced union of named fibers. -/
theorem realize_region (region : Nat → Prop)
    (positive : 0 < (vertices (color (closure G)) region).card)
    (small : (vertices (color (closure G)) region).card ≤ 13) :
    ∃ e : {x // x ∈ vertices (color (closure G)) region} ≃ {x // x ∈ vertices (targetName p) region},
      ∀ i j, color (closure G) i.val j.val = targetName p (e i).val (e j).val := by
  classical
  let c := color (closure G)
  let d := targetName p
  let s := vertices c region
  let t := vertices d region
  obtain ⟨m,h⟩ := diagonal_names p
  let corr := Equiv.subtypeEquiv (p := fun x => x ∈ s) (q := fun y => y ∈ t) m
    (fun x => by simp only [s,t,mem_vertices,c,d,h x])
  let a := Fintype.equivOfCardEq (show Fintype.card (Fin s.card) = Fintype.card {x // x ∈ s} by simp)
  let b := a.trans corr
  let f := fun i => (a i).val
  let g := fun i => (b i).val
  have sf (x : Fin n) : (∃ i, f i = x) ↔ region (c x x) := by
    refine ⟨?_,fun hx => ?_⟩
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (a i).property
    · let z : {x // x ∈ s} := ⟨x,(mem_vertices _ _ _).mpr hx⟩
      exact ⟨a.symm z,congrArg Subtype.val (a.apply_symm_apply z)⟩
  have sg (x : Fin n) : (∃ i, g i = x) ↔ region (d x x) := by
    refine ⟨?_,fun hx => ?_⟩
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (b i).property
    · let z : {x // x ∈ t} := ⟨x,(mem_vertices _ _ _).mpr hx⟩
      exact ⟨b.symm z,congrArg Subtype.val (b.apply_symm_apply z)⟩
  obtain ⟨e,he⟩ := realize p positive small region f g
    (fun _ _ eq => a.injective (Subtype.ext eq)) (fun _ _ eq => b.injective (Subtype.ext eq)) sf sg
  exact ⟨a.symm.trans (e.trans b),fun i j => by
    simpa only [f,g,Equiv.apply_symm_apply,Equiv.trans_apply] using he (a.symm i) (a.symm j)⟩

/-- Realize the union with the images of two source points prescribed,
provided the ordered pairs have corresponding names. -/
theorem realize_region_pair (region : Nat → Prop)
    (positive : 0 < (vertices (color (closure G)) region).card)
    (small : (vertices (color (closure G)) region).card ≤ 13)
    (i j : {z // z ∈ vertices (color (closure G)) region})
    (x y : {z // z ∈ vertices (targetName p) region})
    (hit : color (closure G) i.val j.val = targetName p x.val y.val) :
    ∃ e : {z // z ∈ vertices (color (closure G)) region} ≃ {z // z ∈ vertices (targetName p) region},
      e i=x ∧ e j=y ∧ ∀ u v, color (closure G) u.val v.val = targetName p (e u).val (e v).val := by
  classical
  obtain ⟨e,he⟩ := realize_region p region positive small
  let c := color (closure G)
  let d := targetName p
  let s := vertices c region
  let t := vertices d region
  have card : s.card=t.card := by simpa only [Fintype.card_coe] using Fintype.card_congr e
  let q := Fintype.equivOfCardEq (show Fintype.card (Fin s.card)=Fintype.card {z // z∈t} by simp [card])
  let f := fun u => (q u).val
  have rg (z : Fin n) : (∃ u, f u=z) ↔ region (d z z) := by
    refine ⟨?_,fun hz => ?_⟩
    · rintro ⟨u,rfl⟩; exact (mem_vertices _ _ _).mp (q u).property
    · let w : {z // z∈t} := ⟨z,(mem_vertices _ _ _).mpr hz⟩
      exact ⟨q.symm w,congrArg Subtype.val (q.apply_symm_apply w)⟩
  have cfg := induce (target_config p) (fun h =>
    (target_same p _ _ _ _).mpr (end_colors _ ((target_same p _ _ _ _).mp h)).2)
    f (fun _ _ h => q.injective (Subtype.ext h)) rg
  have pair := (he i j).symm.trans hit
  obtain ⟨perm,hx,hy,pres⟩ := Literature.zivAv_small_relation_transitive positive small cfg
    (q.symm (e i)) (q.symm (e j)) (q.symm x) (q.symm y)
    (by simpa only [SmallShore.restrict,f,Equiv.apply_symm_apply] using pair)
  let h := e.trans (q.symm.trans (perm.trans q))
  refine ⟨h,?_,?_,fun u v => (he u v).trans ?_⟩
  · exact (congrArg q hx).trans (q.apply_symm_apply x)
  · exact (congrArg q hy).trans (q.apply_symm_apply y)
  · simpa only [h,Equiv.trans_apply,SmallShore.restrict,f,Equiv.apply_symm_apply] using pres (q.symm (e u)) (q.symm (e v))

/-- If a union of at most thirteen points determines every omitted point
by an outgoing singleton color, its named realization extends over the graph. -/
theorem extend_region (region : Nat → Prop)
    (positive : 0 < (vertices (color (closure G)) region).card)
    (small : (vertices (color (closure G)) region).card ≤ 13)
    (cover : ∀ x, ¬region (color (closure G) x x) → ∃ i, region (color (closure G) i i) ∧
      ∀ z, color (closure G) i z = color (closure G) i x → z=x) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, color (closure G) i j = targetName p (e i) (e j) := by
  obtain ⟨e,he⟩ := realize_region p region positive small
  apply FourTwelveFunctional.extend p Subtype.val (fun i => (e i).val) he
  intro x
  by_cases inside : region (color (closure G) x x)
  · exact ⟨⟨x,(mem_vertices _ _ _).mpr inside⟩,fun z eq => (Relations.diagonal _ eq).symm⟩
  · obtain ⟨i,hi,single⟩ := cover x inside
    exact ⟨⟨i,(mem_vertices _ _ _).mpr hi⟩,single⟩

/-- Delete a fiber when the complement has at most thirteen points and
each deleted point is selected by a singleton color from that complement. -/
theorem erase (b : Fin n) (positive : 0 < n-(fiber G b).card) (small : n-(fiber G b).card ≤ 13)
    (cover : ∀ x ∈ fiber G b, ∃ i, i ∉ fiber G b ∧ ∀ z,
      color (closure G) i z = color (closure G) i x → z=x) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, color (closure G) i j = targetName p (e i) (e j) := by
  classical
  let c := color (closure G)
  let region := fun v => v ≠ c b b
  have belongs (x : Fin n) : x ∈ fiber G b ↔ c x x = c b b :=
    mem_fiber.trans (same _ _ _ _ _).symm
  have setEq : vertices c region = (fiber G b)ᶜ := by
    ext x; simp only [mem_vertices,Finset.mem_compl,belongs,region]
  have num : (vertices c region).card = n-(fiber G b).card := by simp [setEq,Finset.card_compl]
  apply extend_region p region (num.symm ▸ positive) (num.symm ▸ small)
  intro x outside
  obtain ⟨i,hi,hs⟩ := cover x ((belongs x).mpr (not_not.mp outside))
  exact ⟨i,fun eq => hi ((belongs i).mpr eq),hs⟩

open private middle from FourTwelveFunctional

/-- A single tested entry of valency one at any exterior fiber suffices to
delete its entire target fiber; the other retained fibers are arbitrary. -/
theorem erase_of_column_one (a b : Fin n) (outside : a ∉ fiber G b)
    (positive : 0 < n-(fiber G b).card) (small : n-(fiber G b).card ≤ 13)
    (single : ∀ z, color (closure G) a z = color (closure G) a b → z=b) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, color (closure G) i j = targetName p (e i) (e j) := by
  let c := color (closure G)
  have belongs (i x : Fin n) : x ∈ fiber G i ↔ c x x = c i i :=
    mem_fiber.trans (same _ _ _ _ _).symm
  apply erase p b positive small
  intro y hy
  have diag := ((belongs b y).mp hy).symm
  obtain ⟨i,_,hi⟩ := middle c c (fun s t => Relations.products (closure G) s t _ _ _ _ diag) a
  have row := (end_colors (closure G) hi).1
  exact ⟨i,fun bad => outside ((belongs b a).mpr (row.trans ((belongs b i).mp bad))),
    fun z h => FourTwelveFunctional.transport_thin row single z y (h.trans hi.symm) hi.symm⟩

/-- In particular, this handles any 4+4+8 graph as soon as a retained
vertex has a valency-one color pointing into either four-point cell. -/
theorem isomorphic_of_four_column_one {G H : Graph 16} (a b : Fin 16)
    (outside : a ∉ fiber G b) (size : (fiber G b).card = 4)
    (single : ∀ z, color (closure G) a z = color (closure G) a b → z=b)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨e,h⟩ := erase_of_column_one p a b outside (by omega) (by omega) single
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (h i j)⟩

end QGI.Coherent.SmallUnion
