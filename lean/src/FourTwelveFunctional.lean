import SmallShoreRealization

noncomputable section
namespace QGI.Coherent.FourTwelveFunctional
open StrategyColorLaws

private theorem middle {X Y : Type} [Fintype X] [Fintype Y]
    (c : X → X → Nat) (d : Y → Y → Nat) {i j : X} {x y : Y}
    (law : ∀ a b, count c a b i j = count d a b x y) (k : X) :
    ∃ z, c i k = d x z ∧ c k j = d z y := by
  classical
  have eq := law (c i k) (c k j)
  simp only [count,Finset.sum_boole] at eq
  have pos := Finset.card_pos.mpr (show (Finset.univ.filter
    (fun z => c i z = c i k ∧ c z j = c k j)).Nonempty from
    ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩⟩)
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (pos.trans_eq eq)
  exact ⟨z,(Finset.mem_filter.mp hz).2.1.symm,(Finset.mem_filter.mp hz).2.2.symm⟩

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

abbrev source (G : Graph n) := Relations.color (closure G)

/-- A named realization of the reference points determines a realization
of the entire configuration when every vertex has a singleton color from
one reference point. Neither the choice of reference nor its cardinality
is constrained. -/
theorem extend {I : Type} (a b : I → Fin n)
    (named : ∀ i j, source G (a i) (a j) = targetName p (b i) (b j))
    (cover : ∀ x, ∃ i, ∀ z, source G (a i) z = source G (a i) x → z = x) :
    ∃ e : Equiv.Perm (Fin n), ∀ x y, source G x y = targetName p (e x) (e y) := by
  let c := source G
  let d := targetName p
  have forward {i j x y} (eq : c i j = d x y) (k : Fin n) :=
    middle c d (fun s t => common_products p s t eq) k
  have backward {i j x y} (eq : c i j = d x y) (k : Fin n) :=
    middle d c (fun s t => (common_products p s t eq).symm) k
  choose index unique using cover
  have pick (x : Fin n) : ∃ v, c (a (index x)) x = d (b (index x)) v := by
    obtain ⟨v,h,_⟩ := forward (named (index x) (index x)) x
    exact ⟨v,h⟩
  choose f hf using pick
  have toAnchor (x : Fin n) (j : I) : c x (a j) = d (f x) (b j) := by
    obtain ⟨z,h,k⟩ := backward (named (index x) j) (f x)
    have zx := unique x z (h.symm.trans (hf x).symm)
    exact zx ▸ k.symm
  have allPairs (x y : Fin n) : c x y = d (f x) (f y) := by
    obtain ⟨z,h,k⟩ := backward (toAnchor x (index y)) (f y)
    have zy := unique y z ((common_transpose p k.symm).trans (hf y).symm)
    exact zy ▸ h.symm
  have inj : Function.Injective f := by
    intro x y same
    have identity := entries p (allPairs x y) (closure H).one_mem (Intertwiner.initial_diagonal p)
    by_contra ne
    simp [Matrix.one_apply,ne,same] at identity
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),allPairs⟩

theorem fiber_eq (x z : Fin n) :
    z ∈ fiber G x ↔ source G z z = source G x x :=
  mem_fiber.trans (Relations.same _ _ _ _ _).symm

/-- A homogeneous fiber of at most thirteen points with singleton colors
reaching every outside vertex determines the whole graph. -/
theorem named_of_functional_cover (x : Fin n) (small : (fiber G x).card ≤ 13)
    (cover : ∀ y, y ∉ fiber G x → ∃ i ∈ fiber G x,
      ∀ z, source G i z = source G i y → z = y) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, source G i j = targetName p (e i) (e j) := by
  classical
  let s := fiber G x
  let k := s.card
  let d := source G x x
  let t := Finset.univ.filter (fun z : Fin n => targetName p z z = d)
  have s_mem (z : Fin n) : z ∈ s ↔ source G z z = d := fiber_eq x z
  have t_mem (z : Fin n) : z ∈ t ↔ targetName p z z = d := by simp [t]
  have trace := Intertwiner.trace_eq p (mark_intertwines p d)
  have card : s.card = t.card := by
    simpa [Matrix.trace, Matrix.diag_apply,mark,←s_mem,←t_mem] using trace
  let l := (Fintype.equivOfCardEq (show Fintype.card (Fin k) = Fintype.card {z // z ∈ s} by simp [k]))
  let r := (Fintype.equivOfCardEq (show Fintype.card (Fin k) = Fintype.card {z // z ∈ t} by simp [k,card]))
  let a := fun i : Fin k => (l i).val
  let b := fun i : Fin k => (r i).val
  have apos : 0 < k := Finset.card_pos.mpr ⟨x,(s_mem x).mpr rfl⟩
  have sa (z : Fin n) : (∃ i, a i = z) ↔ source G z z = d := by
    rw [←s_mem]
    exact ⟨by rintro ⟨i,rfl⟩; exact (l i).property,fun h => ⟨l.symm ⟨z,h⟩,congrArg Subtype.val (l.apply_symm_apply _)⟩⟩
  have tb (z : Fin n) : (∃ i, b i = z) ↔ targetName p z z = d := by
    rw [←t_mem]
    exact ⟨by rintro ⟨i,rfl⟩; exact (r i).property,fun h => ⟨r.symm ⟨z,h⟩,congrArg Subtype.val (r.apply_symm_apply _)⟩⟩
  let first : Fin k := ⟨0,apos⟩
  obtain ⟨e,_,he⟩ := SmallShore.realize_at p apos small a b d
    (fun _ _ h => l.injective (Subtype.ext h)) (fun _ _ h => r.injective (Subtype.ext h))
    sa tb first first
  apply extend p a (fun j => b (e j)) he
  intro y
  by_cases inside : y ∈ s
  · obtain ⟨i,hi⟩ := (sa y).mpr ((s_mem y).mp inside)
    exact ⟨i,fun z h => (Relations.diagonal (closure G) (hi ▸ h)).symm⟩
  · obtain ⟨i,hi,only⟩ := cover y inside
    obtain ⟨j,hj⟩ := (sa i).mpr ((s_mem i).mp hi)
    exact ⟨j,hj.symm ▸ only⟩

include p in
theorem isomorphic_of_functional_cover (x : Fin n) (small : (fiber G x).card ≤ 13)
    (cover : ∀ y, y ∉ fiber G x → ∃ i ∈ fiber G x,
      ∀ z, source G i z = source G i y → z = y) : Isomorphic G H := by
  obtain ⟨e,h⟩ := named_of_functional_cover p x small cover
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (h i j)⟩

end QGI.Coherent.FourTwelveFunctional

namespace QGI.Coherent.FourTwelveFunctional
open StrategyColorLaws

theorem transport_thin {n : Nat} {G : Graph n} {a b i : Fin n}
    (same : source G a a = source G i i)
    (single : ∀ w, source G a w = source G a b → w = b) :
    ∀ u v, source G i u = source G a b → source G i v = source G a b → u = v := by
  classical
  let c := source G
  let row := fun x => Finset.univ.filter (fun z => c x z = c a b)
  have card (x : Fin n) : count c (c a b) (c b a) x x = (row x).card := by
    simp only [count,Finset.sum_boole]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro z _
    exact ⟨And.left,fun h => ⟨h,Relations.transpose (closure G) h⟩⟩
  have one : row a = {b} := by
    ext w
    simp only [row,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨single w,fun h => h ▸ rfl⟩
  have balance : count c (c a b) (c b a) a a = count c (c a b) (c b a) i i :=
    Relations.products (closure G) _ _ _ _ _ _ same
  rw [card,card,one,Finset.card_singleton] at balance
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp balance.symm
  have eq (w : Fin n) (hit : c i w = c a b) : w = j := by
    have mem : w ∈ row i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    simpa [hj] using mem
  exact fun u v hu hv => (eq u hu).trans (eq v hv).symm

/-- For the 4+12 partition a single color of column valency one suffices.
It is enough to test its row at one large-fiber vertex and to exhibit one
small-fiber endpoint. Both fiber membership and all further column degrees
are consequences of the coherent intersection numbers. -/
theorem isomorphic_of_column_one {G H : Graph 16} (a b : Fin 16)
    (large : (fiber G a).card = 12) (four : (fiber G b).card = 4)
    (single : ∀ z, source G a z = source G a b → z = b)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  classical
  let c := source G
  have diff : c a a ≠ c b b := by
    intro h
    have hset : fiber G a = fiber G b := by
      ext z
      simp only [fiber_eq]
      change c z z = c a a ↔ c z z = c b b
      rw [h]
    have := congrArg Finset.card hset
    omega
  have complement : fiber G b = (fiber G a)ᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      apply Finset.mem_compl.mpr
      intro ha
      exact diff (((fiber_eq a z).mp ha).symm.trans ((fiber_eq b z).mp hz))
    · simp [Finset.card_compl,large,four]
  obtain ⟨K,g,ip,_,⟨p⟩⟩ := quantum
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  apply isomorphic_of_functional_cover p a (by omega)
  intro y outside
  have hy : y ∈ fiber G b := complement ▸ Finset.mem_compl.mpr outside
  have diag := ((fiber_eq b y).mp hy).symm
  obtain ⟨i,_,hi⟩ := middle c c (fun s t => Relations.products (closure G) s t _ _ _ _ diag) a
  have rowEq := (Relations.end_colors (closure G) hi).1
  exact ⟨i,(fiber_eq a i).mpr rowEq.symm,fun z h =>
    transport_thin rowEq single z y (h.trans hi.symm) hi.symm⟩

end QGI.Coherent.FourTwelveFunctional



