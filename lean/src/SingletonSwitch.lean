import RecoloredStrategy
import FourTwelveFunctional

noncomputable section
namespace QGI.Coherent.SingletonSwitch

open StrategyColorLaws SixTenCoordinates
abbrev ColoringAt (n : Nat) := Fin n → Fin n → Nat
abbrev Coloring := ColoringAt 16

variable {n : Nat}
abbrev Col (G : Graph n) := Relations.color (closure G)

private def bit (root left : Nat) (flip : Bool) (a b : Nat) (neq adj : Bool) : Bool :=
  if a = root ∨ b = root then false else if flip = true ∧ a = left ∧ b = left then neq && !adj else adj

private def graph (G : Graph n) (c : ColoringAt n) (root left : Nat) (flip : Bool) : Graph n where
  edge i j := bit root left flip (c i i) (c j j) (decide (i≠j)) (G.edge i j)
  symm i j := by simp [bit,or_comm,and_left_comm,and_comm,G.symm i j,ne_comm]
  loopless i := by simp [bit,G.loopless]

private theorem pair_middle {c d : ColoringAt n} {i j x y : Fin n}
    (law : ∀ a b, count c a b i j = count d a b x y) :
    ∃ e : Equiv.Perm (Fin n), ∀ z, c i z = d x (e z) ∧ c z j = d (e z) y := by
  classical
  let f := fun z => (c i z,c z j)
  let g := fun z => (d x z,d z y)
  have card (k : Nat × Nat) : Fintype.card {z // f z = k} = Fintype.card {z // g z = k} := by
    rcases k with ⟨a,b⟩
    simpa [f,g,Fintype.card_subtype,Prod.mk.injEq,count] using law a b
  let family := fun k => Fintype.equivOfCardEq (card k)
  exact ⟨Equiv.ofFiberEquiv family,fun z => Prod.mk.inj (Equiv.ofFiberEquiv_map family z).symm⟩

private theorem degree_of_products {c d : ColoringAt n} (A B : Graph n)
    (compatible : ∀ i j x y, c i j = d x y → A.edge i j = B.edge x y)
    {i x : Fin n} (products : ∀ s t, count c s t i i = count d s t x x) :
    DegreeSpectrum.degree A i = DegreeSpectrum.degree B x := by
  obtain ⟨e,he⟩ := pair_middle products
  change (∑ j, if A.edge i j = true then 1 else 0) = ∑ j, if B.edge x j = true then 1 else 0
  calc
    _ = ∑ j, (if B.edge x (e j) = true then 1 else (0:Nat)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [compatible i j x (e j) (he j).1]
    _ = _ := Equiv.sum_comp e (fun j => if B.edge x j = true then 1 else (0:Nat))

theorem degree_at {c d : Coloring} (law : Laws c d) (A B : Graph 16)
    (compatible : ∀ i j x y, c i j = d x y → A.edge i j = B.edge x y)
    {i x : Fin 16} (eq : c i i = d x x) : DegreeSpectrum.degree A i = DegreeSpectrum.degree B x :=
  degree_of_products A B compatible (fun s t => law.products s t eq)

private theorem root_unique {G : Graph n} (x : Fin n) (one : (fiber G x).card = 1) (z : Fin n)
    (eq : Col G z z = Col G x x) : z=x := by
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp one
  have unique (t : Fin n) (h : Col G t t = Col G x x) : t=w := by
    have mem := (FourTwelveFunctional.fiber_eq x t).mpr h
    simpa [hw] using mem
  exact (unique z eq).trans (unique x rfl).symm

/-- Complementing only the internal edges of an even-sized fiber changes
each degree on that fiber. Its own vertex is excluded from the toggle. -/
private theorem different_degree {G : Graph n} (x a : Fin n)
    (away : Col G a a ≠ Col G x x) (even : Even (fiber G a).card) :
    DegreeSpectrum.degree (graph G (Col G) (Col G x x) (Col G a a) true) a ≠
    DegreeSpectrum.degree (graph G (Col G) (Col G x x) (Col G a a) false) a := by
  classical
  let c := Col G
  change c a a ≠ c x x at away
  let flip := graph G c (c x x) (c a a)
  let s := Finset.univ.filter (fun z => c z z = c a a ∧ a ≠ z)
  let ext := Finset.univ.filter fun z => c z z ≠ c x x ∧ c z z ≠ c a a ∧ G.edge a z = true
  have eq : DegreeSpectrum.degree (flip true) a + DegreeSpectrum.degree (flip false) a = s.card + 2 * ext.card := by
    have sc : (∑ j : Fin n, if c j j = c a a ∧ a ≠ j then 1 else (0:Nat)) = s.card := by simp [s]
    have ec : (∑ j : Fin n, if c j j ≠ c x x ∧ c j j ≠ c a a ∧ G.edge a j = true then 1 else (0:Nat)) = ext.card := by simp [ext]
    rw [←sc,←ec,Finset.mul_sum,←Finset.sum_add_distrib]
    simp only [DegreeSpectrum.degree]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases self : a=j
    · subst j; simp [flip,graph,bit,away,G.loopless]
    by_cases hr : c j j = c x x
    · have h : c j j ≠ c a a := fun e => away (e.symm.trans hr)
      simp [flip,graph,bit,away,Ne.symm away,hr,h]
    by_cases ha : c j j = c a a
    · cases edge : G.edge a j <;> simp [flip,graph,bit,away,hr,ha,self,edge]
    · cases edge : G.edge a j <;> simp [flip,graph,bit,away,hr,ha,self,edge]
  have er : s = (fiber G a).erase a := by
    ext j
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,FourTwelveFunctional.fiber_eq]
    exact ⟨fun h => ⟨Ne.symm h.2,h.1⟩,fun h => ⟨h.2,Ne.symm h.1⟩⟩
  have one : ((fiber G a).erase a).card + 1 = (fiber G a).card := Finset.card_erase_add_one ((FourTwelveFunctional.fiber_eq a a).mpr rfl)
  obtain ⟨k,hk⟩ := even
  rw [←er] at one
  change DegreeSpectrum.degree (flip true) a ≠ DegreeSpectrum.degree (flip false) a
  omega

variable {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] (p : PerfectStrategy G H K)

omit [CompleteSpace K] in
theorem diagonal_iff {i j x y : Fin n} (eq : Col G i j = targetName p x y) : i=j ↔ x=y := by
  have h := entries p eq (closure H).one_mem (Intertwiner.initial_diagonal p)
  by_cases ij : i=j <;> by_cases xy : x=y <;> simp_all [Matrix.one_apply]

include p in
/-- The singleton, the even-sized fiber, and the third fiber exhaust the
vertices. No structural assumptions on internal or cross colors
are required. -/
theorem isomorphic_with_lower (lower : Through (n-1)) (x a b : Fin n) (single : (fiber G x).card = 1) (even : Even (fiber G a).card)
    (ar : Col G a a ≠ Col G x x) (br : Col G b b ≠ Col G x x) (ba : Col G b b ≠ Col G a a)
    (cover : ∀ j, Col G j j=Col G x x ∨ Col G j j=Col G a a ∨ Col G j j=Col G b b) : Isomorphic G H := by
  classical
  let c := Col G
  let d := targetName p
  let root := c x x
  let left := c a a
  let flip := graph G c root left
  have bFixed : DegreeSpectrum.degree (flip true) b = DegreeSpectrum.degree (flip false) b := by
    simp [DegreeSpectrum.degree,flip,graph,bit,left,ba,c]
  obtain ⟨t,separate⟩ : ∃ t : Bool, DegreeSpectrum.degree (flip t) a ≠ DegreeSpectrum.degree (flip t) b := by
    by_cases eq : DegreeSpectrum.degree (flip false) a = DegreeSpectrum.degree (flip false) b
    · exact ⟨true,fun same => different_degree x a ar even (same.trans (bFixed.trans eq.symm))⟩
    · exact ⟨false,eq⟩
  let A := flip t
  let B := graph H d root left t
  have comp (i j s u : Fin n) (eq : c i j=d s u) : A.edge i j = B.edge s u := by
    obtain ⟨h₁,h₂⟩ := SmallShore.endpoints p eq
    change bit _ _ _ _ _ _ _ = bit _ _ _ _ _ _ _
    change c i i=d s s at h₁
    change c j j=d u u at h₂
    rw [h₁,h₂,common_edge p eq,Bool.decide_congr (not_congr (diagonal_iff p eq))]
  have selfLaw (i j s u : Fin n) (eq : c i j = c s u) : A.edge i j = A.edge s u := by
    obtain ⟨k,l,hit⟩ := StrategyColors.exists_target p s u
    have name := (associated p).mpr (StrategyColors.maps_support p hit)
    exact (comp _ _ _ _ (eq.trans name)).trans (comp _ _ _ _ name).symm
  have degS {i j : Fin n} (eq : c i i=c j j) := degree_of_products A A selfLaw
    (fun s t => Relations.products (closure G) s t i i j j eq)
  have degT {i j : Fin n} (eq : c i i=d j j) := degree_of_products A B comp
    (fun s t => common_products p s t eq)
  obtain ⟨w,z,hit⟩ := StrategyColors.exists_target p x x
  have base := (associated p).mpr (StrategyColors.maps_support p hit)
  obtain rfl : w=z := (diagonal_iff p base).mp rfl
  obtain ⟨E,hE⟩ := pair_middle (fun s t => common_products p s t base)
  have transport (i : Fin n) : c i i = d (E i) (E i) := (SmallShore.endpoints p (hE i).1).2
  have uniqueT (j : Fin n) (eq : d j j=root) : j=E x := by
    obtain ⟨i,rfl⟩ := E.surjective j
    exact congrArg E (root_unique x single i ((transport i).trans eq))
  obtain ⟨e,ex,newEdge⟩ := RecoloredStrategy.isolated_via_smaller p lower A B comp x (E x)
    ⟨a,fun eq => ar (congrArg (fun v => c v v) eq)⟩
    (fun j => by simp [A,flip,graph,bit,root])
    (fun j => by simp [B,graph,bit,←transport x,root])
  have degrees (i : Fin n) := RecoloredStrategy.preserves_degree e newEdge i
  have names (i : Fin n) : c i i = d (e i) (e i) := by
    obtain ⟨k,hk⟩ := E.surjective (e i)
    have eqdeg : DegreeSpectrum.degree A i = DegreeSpectrum.degree A k :=
      (degrees i).trans (degT ((transport k).trans (by rw [hk]))).symm
    have roots : i=x ↔ k=x := by
      constructor
      · intro ix; exact E.injective (hk.trans ((congrArg e ix).trans ex))
      · intro kx; exact e.injective (hk.symm.trans ((congrArg E kx).trans ex.symm))
    have same : c i i=c k k := by
      rcases cover i with h|h|h
      · exact (roots.mp (root_unique x single i h)) ▸ h
      · rcases cover k with g|g|g
        · exact (ar (h.symm.trans (congrArg (fun z => c z z) (roots.mpr (root_unique x single k g))))).elim
        · exact h.trans g.symm
        · exact (separate ((degS h).symm.trans (eqdeg.trans (degS g)))).elim
      · rcases cover k with g|g|g
        · exact (br (h.symm.trans (congrArg (fun z => c z z) (roots.mpr (root_unique x single k g))))).elim
        · exact (separate ((degS g).symm.trans (eqdeg.symm.trans (degS h)))).elim
        · exact h.trans g.symm
    exact same.trans ((transport k).trans (by rw [hk]))
  have rooted (j : Fin n) : G.edge x j=H.edge (e x) (e j) := by
    obtain ⟨s,hs⟩ := pair_middle (fun u v => common_products p u v (names j))
    have hx := uniqueT (s x) ((SmallShore.endpoints p (hs x).1).2.symm)
    rw [ex,←hx]
    exact common_edge p (hs x).2
  refine ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,?_⟩⟩
  intro i j
  by_cases h : c i i = root
  · exact root_unique x single i h ▸ rooted j
  by_cases k : c j j = root
  · have jx := root_unique x single j k
    exact (G.symm _ _).trans ((jx ▸ rooted i).trans (H.symm _ _))
  have eq := newEdge i j
  change bit _ _ _ _ _ _ _ = bit _ _ _ _ _ _ _ at eq
  rw [←names,←names] at eq
  by_cases ij : i=j
  · subst j; simp [G.loopless,H.loopless]
  have ne := e.injective.ne ij
  have leftNotRoot : left ≠ root := ar
  by_cases flipBit : t=true ∧ c i i=left ∧ c j j=left <;> simpa [bit,h,k,ij,ne,flipBit,leftNotRoot] using eq

end QGI.Coherent.SingletonSwitch

namespace QGI.Coherent.SingletonSwitch

private theorem diagonal_ne {G : Graph 16} {i j : Fin 16} (ne : (fiber G i).card ≠ (fiber G j).card) :
    Col G i i ≠ Col G j j := by
  intro h
  have same : fiber G i = fiber G j := by
    ext z
    rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq]
    change Col G z z = Col G i i ↔ Col G z z = Col G j j
    rw [h]
  exact ne (congrArg Finset.card same)

/-- Cardinality-only entry point for 1+5+10, 1+6+9 and all other
three-fiber partitions with exactly one singleton. The even-sized
nonsingleton fiber may be placed in either order. -/
theorem isomorphic_of_three_sizes {G H : Graph 16} (x a b : Fin 16)
    (one : (fiber G x).card=1) (bigA : 1 < (fiber G a).card) (bigB : 1 < (fiber G b).card)
    (total : (fiber G a).card + (fiber G b).card = 15) (q : QuantumIso G H) : Isomorphic G H := by
  classical
  have na : Col G a a ≠ Col G x x := diagonal_ne (by omega)
  have nb : Col G b b ≠ Col G x x := diagonal_ne (by omega)
  have ba : Col G b b ≠ Col G a a := diagonal_ne (by omega)
  have disj {i j : Fin 16} (h : Col G i i ≠ Col G j j) : Disjoint (fiber G i) (fiber G j) :=
    Finset.disjoint_left.mpr fun z zi zj => h (((FourTwelveFunctional.fiber_eq i z).mp zi).symm.trans
      ((FourTwelveFunctional.fiber_eq j z).mp zj))
  have union : fiber G x ∪ fiber G a ∪ fiber G b = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disj nb.symm,disj ba.symm⟩),
      Finset.card_union_of_disjoint (disj na.symm),one]
    change 1+_+_ = 16
    omega)
  have cover (i : Fin 16) : Col G i i=Col G x x ∨ Col G i i=Col G a a ∨ Col G i i=Col G b b := by
    have mem : i ∈ fiber G x ∪ fiber G a ∪ fiber G b := union ▸ Finset.mem_univ _
    simpa only [Finset.mem_union,FourTwelveFunctional.fiber_eq,or_assoc] using mem
  obtain ⟨K,g,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  by_cases ev : Even (fiber G a).card
  · exact isomorphic_with_lower p through15 x a b one ev na nb ba cover
  · have evb : Even (fiber G b).card := by rw [Nat.even_iff] at *; omega
    exact isomorphic_with_lower p through15 x b a one evb nb na ba.symm (fun j => (cover j).imp_right Or.symm)

end QGI.Coherent.SingletonSwitch



