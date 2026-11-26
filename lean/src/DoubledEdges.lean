import FourTwelveCycleGraph
import BinaryVectorChoice

noncomputable section
namespace QGI.Coherent.DoubledEdges
open Intertwiner Synchrony StrategyColorLaws FourTwelveCycle FourTwelveCycleGraph
open scoped BigOperators

private theorem commute_cell {T : Type} [Ring T] {A B C D : T}
    (aa : A*A=A) (ab : A*B=0) (ba : B*A=0) (ac : A*C=0) (ca : C*A=0)
    (bd : B*D=0) (db : D*B=0) (s : Commute (A+B) (C+D)) : Commute A D := by
  have balance : A*D+B*C = D*A+C*B := by
    simpa only [mul_add,add_mul,ac,bd,ca,db,zero_add,add_zero,add_comm (B*C)] using s.eq
  have left := congrArg (fun q => A*q) balance
  have right := congrArg (fun q => q*A) balance
  simp only [mul_add,←mul_assoc,aa,ab,ac,zero_mul,zero_add,add_zero] at left
  simp only [add_mul,mul_assoc,aa,ba,ca,mul_zero,zero_add,add_zero] at right
  exact left.trans ((mul_assoc _ _ _).trans right)

section
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

abbrev Src {n} (G : Graph n) := Relations.color (closure G)
abbrev Dst := targetName p

theorem diag_of_nonzero {i a : Fin n} {ξ : cyclic p} (hne : U p i a ξ ≠ 0) :
    Src G i i = Dst p a a := by
  apply (associated p).mpr
  apply StrategyColors.maps_support
  intro h
  exact hne (congrArg (fun F : Module.End ℂ (cyclic p) => F ξ)
    ((restricted_projection p (false,i) a).1.symm.trans h))

theorem nonzero_row (ξ : cyclic p) (hne : ξ ≠ 0) (i : Fin n) :
    ∃ a, U p i a ξ ≠ 0 := by
  by_contra! no
  have total := (magic_sums p i ξ).1
  simp only [←show ∀ a, U p i a = restricted p (false,i) a from fun _ => rfl,no,
    Submodule.coe_zero,Finset.sum_const_zero] at total
  exact hne (Subtype.ext total.symm)

private theorem column_sums_commute (y : Fin n) (s t : Finset (Fin n)) :
    Commute (∑ i ∈ s, U p i y) (∑ j ∈ t, U p j y) := by
  change _ * _ = _ * _
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i = j
  · rw [h]
  · exact (magic_orthogonal p y j i (Ne.symm h)).2.trans (magic_orthogonal p y i j h).2.symm

private theorem pair_sum (v : Nat) (x y a b : Fin n) (ne : a ≠ b)
    (shape : neighbors (Dst p) v y = {a,b}) :
    U p x a + U p x b = ∑ z ∈ Finset.univ.filter (fun z => Src G z x = v), U p z y := by
  have tr := conjugate_transpose p (mark_intertwines p v)
  apply LinearMap.ext
  intro ξ
  have eq := tr x y ξ
  have entry (c : Fin n → Fin n → Nat) (u w : Fin n) :
      (mark c v).conjTranspose u w = (if c w u = v then 1 else 0 : ℂ) := by
    by_cases h : c w u = v <;> simp [mark,Matrix.conjTranspose_apply,h]
  simp only [entry,ite_smul,one_smul,zero_smul,←Finset.sum_filter] at eq
  change _ = ∑ z ∈ neighbors (Dst p) v y, U p x z ξ at eq
  rw [shape,Finset.sum_pair ne] at eq
  simpa only [LinearMap.add_apply,LinearMap.sum_apply] using eq.symm

/-- Entries with two target labels commute when that label pair is one neighborhood. -/
theorem pair_commute (v : Nat) (x z a b : Fin n)
    (pairs : a ≠ b → ∃ y, neighbors (Dst p) v y = {a,b}) : Commute (U p x a) (U p z b) := by
  by_cases h : x = z
  · subst z
    by_cases eq : a=b
    · subst b; exact Commute.refl _
    · exact (magic_orthogonal p x _ _ eq).1.trans (magic_orthogonal p x _ _ (Ne.symm eq)).1.symm
  by_cases ne : a = b
  · subst b
    exact (magic_orthogonal p _ _ _ h).2.trans (magic_orthogonal p _ _ _ (Ne.symm h)).2.symm
  obtain ⟨y,hy⟩ := pairs ne
  apply commute_cell (restricted_projection p _ _).1 (magic_orthogonal p x _ _ ne).1
    (magic_orthogonal p x _ _ (Ne.symm ne)).1 (magic_orthogonal p _ _ _ h).2
    (magic_orthogonal p _ _ _ (Ne.symm h)).2 (magic_orthogonal p _ _ _ h).2
    (magic_orthogonal p _ _ _ (Ne.symm h)).2
  rw [pair_sum p v x y _ _ ne hy,pair_sum p v z y _ _ ne hy]
  exact column_sums_commute p y _ _

/-- Commuting entries of a four-point block have a nonzero simultaneous fixed vector. -/
theorem fixed_block (sl tl : Fin 4 ↪ Fin n)
    (supported : ∀ i a (ξ : cyclic p), U p (sl i) a ξ ≠ 0 → ∃ j, tl j=a)
    (commutes : ∀ i j a b, Commute (U p (sl i) (tl a)) (U p (sl j) (tl b))) :
    ∃ (ξ : cyclic p) (e : Equiv.Perm (Fin 4)), ξ ≠ 0 ∧ ∀ i, U p (sl i) (tl (e i)) ξ = ξ := by
  classical
  have localFix (s : Finset (Fin 4)) : ∃ ξ : cyclic p, ξ ≠ 0 ∧
      ∀ i ∈ s, ∃ a : Fin 4, U p (sl i) (tl a) ξ = ξ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨⟨p.psi,psi_mem p⟩,fun h => psi_ne_zero p (congrArg Subtype.val h),by simp⟩
    | @insert i s _ ih =>
      obtain ⟨ξ,nz,keep⟩ := ih
      obtain ⟨a,nonzero⟩ := nonzero_row p ξ nz (sl i)
      obtain ⟨a,rfl⟩ := supported i a ξ nonzero
      refine ⟨_,nonzero,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | old
      · exact ⟨a,congrArg (fun F : Module.End ℂ (cyclic p) => F ξ) (restricted_projection p _ _).1⟩
      · obtain ⟨b,hb⟩ := keep j old
        have comm := congrArg (fun F : Module.End ℂ (cyclic p) => F ξ)
          (commutes j i b a).eq
        exact ⟨b,comm.trans (congrArg (U p (sl i) (tl a)) hb)⟩
  obtain ⟨ξ,nz,h⟩ := localFix Finset.univ
  choose f hf using fun i => h i (Finset.mem_univ _)
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    have zero := congrArg (fun F : Module.End ℂ (cyclic p) => F ξ)
      (magic_orthogonal p (tl (f i)) _ _ (sl.injective.ne ne)).2
    change U p (sl i) (tl (f i)) (U p (sl j) (tl (f i)) ξ) = 0 at zero
    rw [show U p (sl j) (tl (f i)) ξ = ξ by rw [eq,hf],hf] at zero
    exact nz zero
  exact ⟨ξ,Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),nz,hf⟩

end

variable {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

private theorem all_pairs : ∀ a b : Fin 4, a ≠ b → ∃ k : Edge, edge k = {a,b} := by native_decide
private theorem edge_inj : Function.Injective edge := by
  change ∀ a b : Edge, edge a = edge b → a=b
  native_decide

/-- The target has two copies of each edge of the four-point complete
graph as neighborhoods of a single named cross color. No commutativity
is assumed of any of the twelve-point measurement operators. -/
theorem isomorphic (S : Frame (Src G)) (T : Frame (Dst p)) (hl : S.l = T.l) (hr : S.r = T.r)
    (v : Nat) (column : Fin 12 → Edge)
    (cells : ∀ j, neighbors (Dst p) v (T.right j) = (edge (column j)).map T.left)
    (twice : ∀ k, (Finset.univ.filter (fun j => column j = k)).card = 2) : Isomorphic G H := by
  classical
  have pairs (a b : Fin 4) (ne : a ≠ b) : ∃ y, neighbors (Dst p) v y = {T.left a,T.left b} := by
    obtain ⟨k,hk⟩ := all_pairs a b ne
    have pos : 0 < (Finset.univ.filter (fun j => column j = k)).card := by rw [twice]; decide
    obtain ⟨j,hj⟩ := Finset.card_pos.mp pos
    refine ⟨T.right j,?_⟩
    simp only [cells,(Finset.mem_filter.mp hj).2,hk,Finset.map_insert,Finset.map_singleton]
  obtain ⟨ξ,e,nz,fixed⟩ := fixed_block p S.left T.left (fun i a ξ h =>
    (T.left_iff a).mpr ((diag_of_nonzero p h).symm.trans ((S.leftDiag i).trans hl))) (fun i j a b =>
      pair_commute p v _ _ _ _ (fun ne => pairs a b (fun eq => ne (congrArg T.left eq))))
  have named {x a : Fin 16} (active : U p x a ξ ≠ 0) (i : Fin 4) :
      Src G x (S.left i) = Dst p a (T.left (e i)) := by
    apply (associated p).mpr
    apply StrategyColors.maps_support
    intro zero
    have eq := congrArg (fun F : Module.End ℂ (cyclic p) => F ξ) zero
    change U p x a (U p (S.left i) (T.left (e i)) ξ) = 0 at eq
    exact active ((congrArg (U p x a) (fixed i)).symm.trans eq)
  apply BinaryVectorChoice.isomorphic_on_cyclic p ξ nz
  intro x
  obtain ⟨z,rfl⟩ := S.points.surjective x
  cases z with
  | inl i =>
    refine ⟨T.left (e i),T.left (e i),fun a active => Or.inl ?_⟩
    by_contra ne
    have eq := congrArg (fun F : Module.End ℂ (cyclic p) => F ξ)
      (magic_orthogonal p (S.left i) a _ ne).1
    change U p (S.left i) a (U p (S.left i) (T.left (e i)) ξ) = 0 at eq
    rw [fixed] at eq
    exact active eq
  | inr j =>
    have onRight {a} (active : U p (S.right j) a ξ ≠ 0) : ∃ t, T.right t = a :=
      (T.right_iff _).mpr ((diag_of_nonzero p active).symm.trans ((S.rightDiag j).trans hr))
    obtain ⟨a,ha⟩ := nonzero_row p ξ nz (S.right j)
    obtain ⟨j₀,rfl⟩ := onRight ha
    obtain ⟨u,w,_,classes⟩ := Finset.card_eq_two.mp (twice (column j₀))
    refine ⟨T.right u,T.right w,?_⟩
    intro a active
    obtain ⟨t,rfl⟩ := onRight active
    have equal (i : Fin 4) : Dst p (T.right t) (T.left i) = Dst p (T.right j₀) (T.left i) := by
      obtain ⟨i,rfl⟩ := e.surjective i
      exact (named active i).symm.trans (named ha i)
    have eq : edge (column t) = edge (column j₀) := by
      ext i
      have member (j : Fin 12) : i ∈ edge (column j) ↔ Dst p (T.right j) (T.left i) = v := by
        change i ∈ edge (column j) ↔ _
        rw [← Finset.mem_map' T.left,←cells]
        simp [neighbors]
      rw [member,member,equal]
    have ht : t ∈ ({u,w} : Finset (Fin 12)) :=
      classes ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,edge_inj eq⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton,T.right.injective.eq_iff] using ht

end QGI.Coherent.DoubledEdges
