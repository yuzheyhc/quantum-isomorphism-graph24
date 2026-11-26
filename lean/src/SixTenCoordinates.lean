import StrategyColorLaws
import SmallShoreRealization
import FiberRectangles

noncomputable section
open scoped BigOperators

namespace QGI.Coherent.SixTenCoordinates
open Relations StrategyColorLaws

abbrev V := Fin 16
abbrev A := Fin 6
abbrev B := Fin 10
abbrev Coloring := V → V → Nat

/-- Coordinates for the two named diagonal classes. -/
structure Frame (c : Coloring) (l r : Nat) where
  e : A ⊕ B ≃ V
  left : ∀ i, c (e (.inl i)) (e (.inl i)) = l
  right : ∀ j, c (e (.inr j)) (e (.inr j)) = r
  distinct : l ≠ r

namespace Frame
variable {c : Coloring} {l r : Nat} (f : Frame c l r)

theorem left_iff (x : V) : (∃ i, f.e (.inl i) = x) ↔ c x x = l := by
  obtain ⟨i,rfl⟩ := f.e.surjective x
  cases i with
  | inl i => exact iff_of_true ⟨i,rfl⟩ (f.left i)
  | inr i =>
    exact iff_of_false (by rintro ⟨_,h⟩; cases f.e.injective h)
      (fun h => f.distinct (h.symm.trans (f.right i)))

theorem right_iff (x : V) : (∃ i, f.e (.inr i) = x) ↔ c x x = r := by
  obtain ⟨i,rfl⟩ := f.e.surjective x
  cases i with
  | inr i => exact iff_of_true ⟨i,rfl⟩ (f.right i)
  | inl i =>
    exact iff_of_false (by rintro ⟨_,h⟩; cases f.e.injective h)
      (fun h => f.distinct ((f.left i).symm.trans h))
end Frame

def named (c : Coloring) (u : Nat) := Finset.univ.filter (fun x => c x x = u)

private theorem frame_of_cards (c : Coloring) (l r : Nat)
    (hc : (named c l).card = 6) (hd : (named c r).card = 10) : Nonempty (Frame c l r) := by
  classical
  have ne : l ≠ r := by rintro rfl; omega
  let s := named c l
  have cover : named c r = sᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      apply Finset.mem_compl.mpr
      simp only [s,named,Finset.mem_filter,Finset.mem_univ,true_and] at *
      exact fun h => ne (h.symm.trans hx)
    · simp [s,Finset.card_compl,hc,hd]
  have cardS : Fintype.card {x // x ∈ s} = 6 := (Fintype.card_coe s).trans hc
  have cardT : Fintype.card {x : V // x ∉ s} = 10 := by
    rw [Fintype.card_subtype_compl,cardS]; decide
  let p := Fintype.equivOfCardEq (show Fintype.card A = Fintype.card {x // x ∈ s} by simp [cardS])
  let q := Fintype.equivOfCardEq (show Fintype.card B = Fintype.card {x : V // x ∉ s} by simp [cardT])
  let e := (Equiv.sumCongr p q).trans (Equiv.sumCompl (fun x => x ∈ s))
  refine ⟨⟨e, fun i => ?_, fun j => ?_, ne⟩⟩
  · exact (Finset.mem_filter.mp (p i).property).2
  · have h : (q j).val ∈ named c r := cover ▸ Finset.mem_compl.mpr (q j).property
    exact (Finset.mem_filter.mp h).2

private theorem corresponding_card {G H : Graph 16} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (p : PerfectStrategy G H K) (v : Nat) :
    (named (color (closure G)) v).card = (named (targetName p) v).card := by
  have h := Intertwiner.trace_eq p (mark_intertwines p v)
  simpa [Matrix.trace,Matrix.diag_apply,mark,named] using h

theorem paired {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (six : ∃ x, (fiber G x).card = 6)
    (ten : ∃ x, (fiber G x).card = 10) :
    ∃ l r, Nonempty (Frame (color (closure G)) l r) ∧ Nonempty (Frame (targetName p) l r) := by
  obtain ⟨x,hx⟩ := six
  obtain ⟨y,hy⟩ := ten
  have eq (i : V) : named (color (closure G)) (color (closure G) i i) = fiber G i := by
    ext j
    simp [named,mem_fiber,Relations.same]
  let l := color (closure G) x x
  let r := color (closure G) y y
  have hc : (named (color (closure G)) l).card = 6 := (congrArg Finset.card (eq x)).trans hx
  have hd : (named (color (closure G)) r).card = 10 := (congrArg Finset.card (eq y)).trans hy
  exact ⟨l,r,frame_of_cards _ _ _ hc hd,frame_of_cards _ _ _
    ((corresponding_card p l).symm.trans hc) ((corresponding_card p r).symm.trans hd)⟩

structure Laws {n : Nat} (c d : Fin n → Fin n → Nat) : Prop where
  rev : ∀ {i j x y}, c i j = d x y → c j i = d y x
  last : ∀ {i j x y}, c i j = d x y → c j j = d y y
  products : ∀ a b {i j x y}, c i j = d x y → count c a b i j = count d a b x y

theorem sourceLaws {n} (C : CoherentAlgebra n) : Laws (color C) (color C) :=
  ⟨transpose C,fun h => (end_colors C h).2,fun a b i j x y h => Relations.products C a b i j x y h⟩

theorem commonLaws {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) : Laws (color (closure G)) (targetName p) :=
  ⟨common_transpose p,fun h => (SmallShore.endpoints p h).2,common_products p⟩

theorem targetLaws {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) : Laws (targetName p) (targetName p) := by
  refine ⟨fun h => (target_same p _ _ _ _).mpr (transpose _ ((target_same p _ _ _ _).mp h)),
    fun h => (target_same p _ _ _ _).mpr (end_colors _ ((target_same p _ _ _ _).mp h)).2,?_⟩
  intro a b i j x y h
  obtain ⟨s,t,hst⟩ := StrategyColors.exists_source p i j
  have match' := (associated p).mpr (StrategyColors.maps_support p hst)
  exact (common_products p a b match').symm.trans (common_products p a b (match'.trans h))

/-- Intersection numbers give a bijection of middle vertices preserving both relation names. -/
theorem Laws.middle {n} {c d : Fin n → Fin n → Nat} (law : Laws c d) {i j x y : Fin n} (h : c i j = d x y) :
    ∃ e : Equiv.Perm (Fin n), ∀ z, c i z = d x (e z) ∧ c z j = d (e z) y := by
  classical
  let f := fun z : Fin n => (c i z,c z j)
  let g := fun z : Fin n => (d x z,d z y)
  have card (k : Nat × Nat) : Fintype.card {z // f z = k} = Fintype.card {z // g z = k} := by
    rcases k with ⟨a,b⟩
    simpa [f,g,Fintype.card_subtype,Prod.mk.injEq,count] using law.products a b h
  let family := fun k => Fintype.equivOfCardEq (card k)
  refine ⟨Equiv.ofFiberEquiv family,fun z => ?_⟩
  exact Prod.mk.inj (Equiv.ofFiberEquiv_map family z).symm

abbrev Shore {n} (c : Fin n → Fin n → Nat) (v : Nat) (X : Type) := X ≃ {z : Fin n // c z z = v}

def Frame.leftShore {c l r} (f : Frame c l r) : Shore c l A := by
  let m (i : A) : {z // c z z = l} := ⟨f.e (.inl i),f.left i⟩
  exact Equiv.ofBijective m ⟨fun _ _ h => Sum.inl.inj (f.e.injective (congrArg Subtype.val h)),
    fun z => by obtain ⟨i,hi⟩ := (f.left_iff z.val).mpr z.property; exact ⟨i,Subtype.ext hi⟩⟩

def Frame.rightShore {c l r} (f : Frame c l r) : Shore c r B := by
  let m (j : B) : {z // c z z = r} := ⟨f.e (.inr j),f.right j⟩
  exact Equiv.ofBijective m ⟨fun _ _ h => Sum.inr.inj (f.e.injective (congrArg Subtype.val h)),
    fun z => by obtain ⟨i,hi⟩ := (f.right_iff z.val).mpr z.property; exact ⟨i,Subtype.ext hi⟩⟩

abbrev atPoint {n} {c : Fin n → Fin n → Nat} {v X} (s : Shore c v X) (i : X) : Fin n := (s i).val

/-- The expression takes equal values on pairs with the same basic relation name. -/
def Block {n : Nat} {c d : Fin n → Fin n → Nat} {u v : Nat} {X Y : Type} {α : Type}
    (L : Shore c u X) (L' : Shore d u X) (R : Shore c v Y) (R' : Shore d v Y)
    (T U : X → Y → α) : Prop :=
  ∀ ⦃i j x y⦄, c (atPoint L i) (atPoint R j) = d (atPoint L' x) (atPoint R' y) → T i j = U x y

namespace Block
variable {n : Nat} {c d : Fin n → Fin n → Nat} {u v w : Nat} {X Y Z α β γ : Type}
  {L : Shore c u X} {L' : Shore d u X} {M : Shore c v Y} {M' : Shore d v Y}
  {R : Shore c w Z} {R' : Shore d w Z}

theorem names : Block L L' R R' (fun i j => c (atPoint L i) (atPoint R j))
    (fun x y => d (atPoint L' x) (atPoint R' y)) := fun ⦃_ _ _ _⦄ h => h

theorem edges {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (L : Shore (color (closure G)) u X) (L' : Shore (targetName p) u X)
    (R : Shore (color (closure G)) w Z) (R' : Shore (targetName p) w Z) :
    Block L L' R R' (fun i j => G.edge (atPoint L i) (atPoint R j))
      (fun x y => H.edge (atPoint L' x) (atPoint R' y)) := fun ⦃_ _ _ _⦄ h => common_edge p h

theorem edges_self {n} (G : Graph n) (L : Shore (color (closure G)) u X) (R : Shore (color (closure G)) w Z) :
    Block L L R R (fun i j => G.edge (atPoint L i) (atPoint R j))
      (fun x y => G.edge (atPoint L x) (atPoint R y)) := by
  intro i j x y h
  have eq := (same _ _ _ _ _).mp h _ (adjacency_mem G)
  change G.edge (atPoint L i) (atPoint R j) = G.edge (atPoint L x) (atPoint R y)
  cases s : G.edge (atPoint L i) (atPoint R j) <;> cases t : G.edge (atPoint L x) (atPoint R y)
    <;> first | rfl | simp [Intertwiner.adjacency,s,t] at eq

theorem const (v : α) : Block L L' R R' (fun _ _ => v) (fun _ _ => v) := fun ⦃_ _ _ _⦄ _ => rfl

theorem map {T U : X → Z → α} (h : Block L L' R R' T U) (f : α → β) :
    Block L L' R R' (fun i j => f (T i j)) (fun x y => f (U x y)) := fun ⦃_ _ _ _⦄ e => congrArg f (h e)

theorem map₂ {T U : X → Z → α} {P Q : X → Z → β}
    (h : Block L L' R R' T U) (k : Block L L' R R' P Q) (f : α → β → γ) :
    Block L L' R R' (fun i j => f (T i j) (P i j)) (fun x y => f (U x y) (Q x y)) :=
  fun ⦃_ _ _ _⦄ e => congrArg₂ f (h e) (k e)

theorem flip {T U : X → Z → α} (law : Laws c d) (h : Block L L' R R' T U) :
    Block R R' L L' (fun j i => T i j) (fun y x => U x y) := fun ⦃_ _ _ _⦄ eq => h (law.rev eq)

theorem fold [Fintype Y] {T U : X → Y → α} {P Q : Y → Z → β} (law : Laws c d)
    (h : Block L L' M M' T U) (k : Block M M' R R' P Q) (term : α → β → Nat) :
    Block L L' R R' (fun i j => ∑ t, term (T i t) (P t j))
      (fun x y => ∑ t, term (U x t) (Q t y)) := by
  intro i j x y eq
  obtain ⟨e,pres⟩ := law.middle eq
  let mid := Equiv.subtypeEquiv (p := fun z => c z z = v) (q := fun z => d z z = v) e
    (fun z => by change c z z = v ↔ d (e z) (e z) = v; rw [law.last (pres z).1])
  let perm := (M.trans mid).trans M'.symm
  have atMid (z : Y) : atPoint M' (perm z) = e (atPoint M z) := by
    change (M' (M'.symm _)).val = _
    rw [Equiv.apply_symm_apply]; rfl
  calc
    _ = ∑ z, term (U x (perm z)) (Q (perm z) y) := by
      apply Finset.sum_congr rfl
      intro z _
      have links := pres (atPoint M z)
      rw [←atMid] at links
      exact congrArg₂ term (h links.1) (k links.2)
    _ = _ := Equiv.sum_comp perm (fun z => term (U x z) (Q z y))

theorem diag {T U : X → X → α} (h : Block L L' L L' T U) (i x : X) : T i i = U x x :=
  h ((L i).property.trans (L' x).property.symm)

def overlap [Fintype Z] (T : X → Z → Bool) (i j : X) :=
  (Finset.univ.filter fun a => T i a = true ∧ T j a = true).card

def hist [Fintype X] (T : X → X → Nat) (i : X) (k : Nat) :=
  (Finset.univ.filter fun j => T i j = k).card

theorem gram [Fintype Z] {T U : X → Z → Bool} (law : Laws c d)
    (h : Block L L' R R' T U) : Block L L' L L' (overlap T) (overlap U) := by
  intro i j x y eq
  simpa [overlap] using
    (fold law h (flip law h) (fun a b => if a = true ∧ b = true then 1 else 0) eq)

theorem hist_eq [Fintype X] {T U : X → X → Nat} (law : Laws c d)
    (h : Block L L' L L' T U) (i x : X) (k : Nat) : hist T i k = hist U x k := by
  have prod := fold law h (const (L := L) (L' := L') (R := L) (R' := L') ())
    (fun a _ => if a = k then 1 else 0)
  simpa only [hist,Finset.sum_boole] using diag prod i x

theorem degree_eq [Fintype Z] {T U : X → Z → Bool} (law : Laws c d)
    (h : Block L L' R R' T U) (i x : X) :
    (Finset.univ.filter (fun j => T i j = true)).card =
      (Finset.univ.filter (fun j => U x j = true)).card := by
  simpa only [overlap,and_self] using diag (gram law h) i x

end Block

def cross {c l r} (f : Frame c l r) (i : A) (j : B) := c (f.e (.inl i)) (f.e (.inr j))

def basic {c l r} (f : Frame c l r) (v : Nat) (i : A) (j : B) := decide (cross f i j = v)

/-- Every named target cross color occurs in the source cross rectangle. -/
theorem cross_source {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l r} (f : Frame (color (closure G)) l r)
    (g : Frame (targetName p) l r) (x : A) (y : B) :
    ∃ i j, cross f i j = cross g x y := by
  obtain ⟨s,t,hit⟩ := StrategyColors.exists_source p (g.e (.inl x)) (g.e (.inr y))
  have h := (associated p).mpr (StrategyColors.maps_support p hit)
  obtain ⟨hs,ht⟩ := SmallShore.endpoints p h
  obtain ⟨i,hi⟩ := (f.left_iff s).mpr (hs.trans (g.left x))
  obtain ⟨j,hj⟩ := (f.right_iff t).mpr (ht.trans (g.right y))
  exact ⟨i,j,by simpa only [cross,hi,hj] using h⟩

theorem basic_block {c d l r} (f : Frame c l r) (g : Frame d l r) (v : Nat) :
    Block f.leftShore g.leftShore f.rightShore g.rightShore (basic f v) (basic g v) :=
  fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t = v)) eq

theorem biregular {c l r} (law : Laws c c) (f : Frame c l r) :
    FiberRectangles.BiregularColors (cross f) := by
  intro v
  let h := basic_block f f v
  exact ⟨_,_,fun i => Block.degree_eq law h i 0,
    fun j => Block.degree_eq law (Block.flip law h) j 0⟩

/-- The four degree and Gram-histogram tests hold with the same counts in both graphs. -/
theorem statistics {c d l r} (law : Laws c d) (f : Frame c l r) (g : Frame d l r) (v : Nat) :
    (∀ i x, FiberRectangles.degree (basic f v i) = FiberRectangles.degree (basic g v x)) ∧
    (∀ j y, FiberRectangles.degree (fun i => basic f v i j) =
      FiberRectangles.degree (fun x => basic g v x y)) ∧
    (∀ i x k, Block.hist (Block.overlap (basic f v)) i k = Block.hist (Block.overlap (basic g v)) x k) ∧
    (∀ j y k, Block.hist (Block.overlap (fun j i => basic f v i j)) j k =
      Block.hist (Block.overlap (fun y x => basic g v x y)) y k) := by
  let h := basic_block f g v
  let t := Block.flip law h
  exact ⟨Block.degree_eq law h,Block.degree_eq law t,
    Block.hist_eq law (Block.gram law h),Block.hist_eq law (Block.gram law t)⟩

/-- A mixed six-by-ten rectangle has exactly two names, with valencies five and three. -/
theorem uniform_or_two {c l r} (law : Laws c c) (f : Frame c l r) :
    (∃ v, ∀ i j, cross f i j = v) ∨
    (∃ v w, v ≠ w ∧ (∀ i j, cross f i j = v ∨ cross f i j = w) ∧
      (∀ i, FiberRectangles.degree (basic f v i) = 5) ∧
      (∀ j, FiberRectangles.degree (fun i => basic f v i j) = 3)) := by
  classical
  let v := cross f 0 0
  by_cases all : ∀ i j, cross f i j = v
  · exact Or.inl ⟨v,all⟩
  push_neg at all
  obtain ⟨a,b,hab⟩ := all
  let w := cross f a b
  let S (k : Nat) (i : A) := Finset.univ.filter (fun j : B => cross f i j = k)
  have deg (k : Nat) (i : A) : FiberRectangles.degree (basic f k i) = (S k i).card := by
    simp [FiberRectangles.degree,basic,S]
  obtain ⟨r₁,s₁,hr₁,hs₁⟩ := biregular law f v
  obtain ⟨r₂,s₂,hr₂,hs₂⟩ := biregular law f w
  have bal₁ := FiberRectangles.balance (basic f v) hr₁ hs₁
  have bal₂ := FiberRectangles.balance (basic f w) hr₂ hs₂
  have card₁ (i : A) : (S v i).card = r₁ := (deg v i).symm.trans (hr₁ i)
  have card₂ (i : A) : (S w i).card = r₂ := (deg w i).symm.trans (hr₂ i)
  have pos₁ : 0 < r₁ := (card₁ 0) ▸ Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have pos₂ : 0 < r₂ := (card₂ a) ▸ Finset.card_pos.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have disj (i : A) : Disjoint (S v i) (S w i) := by
    refine Finset.disjoint_left.mpr fun j hv hw => ?_
    exact hab ((Finset.mem_filter.mp hw).2.symm.trans (Finset.mem_filter.mp hv).2)
  have size (i : A) : (S v i ∪ S w i).card = r₁+r₂ := by
    rw [Finset.card_union_of_disjoint (disj i),card₁,card₂]
  have bound := Finset.card_le_univ (S v 0 ∪ S w 0)
  rw [size] at bound
  change r₁+r₂ ≤ 10 at bound
  change 6*r₁ = 10*s₁ at bal₁
  change 6*r₂ = 10*s₂ at bal₂
  have num : r₁=5 ∧ s₁=3 ∧ r₂=5 := by omega
  refine Or.inr ⟨v,w,Ne.symm hab,?_,fun i => (hr₁ i).trans num.1,fun j => (hs₁ j).trans num.2.1⟩
  intro i j
  have full : S v i ∪ S w i = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [size,num.1,num.2.2]; decide)
  have mem : j ∈ S v i ∪ S w i := full ▸ Finset.mem_univ _
  simpa only [Finset.mem_union,S,Finset.mem_filter,Finset.mem_univ,true_and] using mem

end QGI.Coherent.SixTenCoordinates
