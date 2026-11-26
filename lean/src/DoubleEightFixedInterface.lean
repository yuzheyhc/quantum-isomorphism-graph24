import DoubleEightNonuniformCoverage
import DoubleEightShoreCensus
import DoubleEightShoreLabels

namespace QGI.DoubleEight.FixedInterface
open ShoreCensus

abbrev Word := Placements.Word
def named (w : Word) : Coloring := fun i j => (ShoreCheck.colorAt w i j).val
def transpose (c : Coloring) : Coloring := fun i j => c j i
def Same (c d : Coloring) : Prop := ∀ i j x y, c i j = c x y ↔ d i j = d x y

def product (a b : Coloring) (u v : Nat) (i j : V) : Nat :=
  (List.ofFn fun z : V => if a i z = u ∧ b z j = v then 1 else 0).sum

def ConstantProduct (a b out : Coloring) : Prop :=
  ∀ u v i j x y, out i j = out x y → product a b u v i j = product a b u v x y

/-- Ordinary two-step intersection conditions with the two possible middle shores. -/
def Compatible (cross shore : Coloring) : Prop :=
  ConstantProduct cross (transpose cross) shore ∧ ConstantProduct shore cross cross

theorem transfer {a b t a' b' t' : Coloring} (ca : Same a a') (cb : Same b b')
    (ct : Same t t') (h : ConstantProduct a b t) : ConstantProduct a' b' t' := by
  intro u v i j x y eq
  by_cases hu : ∃ k l, a' k l = u
  · obtain ⟨k,l,rfl⟩ := hu
    by_cases hv : ∃ z w, b' z w = v
    · obtain ⟨z,w,rfl⟩ := hv
      unfold Same at ca cb
      simpa only [product, ca, cb] using h (a k l) (b z w) i j x y ((ct _ _ _ _).mpr eq)
    · push_neg at hv
      simp [product, hv]
  · push_neg at hu
    simp [product, hu]

theorem same_transpose {c d : Coloring} (h : Same c d) : Same (transpose c) (transpose d) :=
  fun i j x y => h j i y x

private theorem regular {cross shore : Coloring} {w a : Word}
    (hw : Same cross (named w)) (ha : Same shore (named a)) (hc : Compatible cross shore) :
    ShoreCheck.IntersectionRegular w a := by
  have gram := transfer hw (same_transpose hw) ha hc.1
  have mixed := transfer ha hw hw hc.2
  intro g r s i j x y same
  cases g
  · exact (by simpa only [ShoreCheck.directProduct, Bool.false_eq_true, if_false, product, named,
      Fin.val_inj] using mixed r.val s.val i j x y (congrArg Fin.val same))
  · exact (by simpa only [ShoreCheck.directProduct, if_true, product, named, transpose,
      Fin.val_inj] using gram r.val s.val i j x y (congrArg Fin.val same))

/-- Typed colors keep names on distinct rectangles separate. -/
def completion (cross left right : Coloring) : V ⊕ V → V ⊕ V → Nat × Nat
  | .inl i, .inl j => (0, left i j)
  | .inl i, .inr j => (1, cross i j)
  | .inr i, .inl j => (2, cross j i)
  | .inr i, .inr j => (3, right i j)

private def encode (c : Nat × Nat) : Nat := 8*c.1 + c.2

private theorem model_coordinates (c l r : Word)
    (small : ∀ w ∈ [c,l,r], ∀ i j : V, w.getD (8*i.val+j.val) 255 = (ShoreCheck.colorAt w i j).val)
    (i j : V ⊕ V) :
    encode (completion (named c) (named l) (named r) i j) =
      Placements.model c l r (finSumFinEquiv i) (finSumFinEquiv j) := by
  have coordL (i : V) : (finSumFinEquiv (Sum.inl i : V ⊕ V)).val = i.val := rfl
  have coordR (i : V) : (finSumFinEquiv (Sum.inr i : V ⊕ V)).val = 8+i.val := rfl
  have hc := small c (by simp)
  have hl := small l (by simp)
  have hr := small r (by simp)
  cases i <;> cases j <;>
    simp [Placements.model, coordL, coordR, completion, encode, named, Fin.isLt, hc, hl, hr]

private theorem as_model {c l r : Word} {cross left right : Coloring}
    (hc : Same cross (named c)) (hl : Same left (named l)) (hr : Same right (named r))
    (small : ∀ w ∈ [c,l,r], ∀ i j : V, w.getD (8*i.val+j.val) 255 = (ShoreCheck.colorAt w i j).val) :
    PartitionIso (completion cross left right) (Placements.model c l r) := by
  refine ⟨finSumFinEquiv, fun i j x y => ?_⟩
  rw [← model_coordinates c l r small i j, ← model_coordinates c l r small x y]
  have enc (a b : Nat × Nat) (ha : a.2 < 8) (hb : b.2 < 8) :
      encode a = encode b ↔ a = b := by
    rcases a with ⟨u,v⟩
    rcases b with ⟨s,t⟩
    simp only [encode, Prod.mk.injEq] at *
    omega
  have bounded (u v : V ⊕ V) :
      (completion (named c) (named l) (named r) u v).2 < 8 := by
    cases u <;> cases v <;> apply Fin.isLt
  rw [enc _ _ (bounded i j) (bounded x y)]
  cases i <;> cases j <;> cases x <;> cases y <;> simp [completion]
    <;> first | apply hc | apply hl | apply hr

private def Word.OK (w : Word) : Prop :=
  ∀ i j : V, w.getD (8*i.val+j.val) 255 = (ShoreCheck.colorAt w i j).val
private instance (w : Word) : Decidable (Word.OK w) := by unfold Word.OK; infer_instance

private theorem bank_ok : (ShoreCheck.bank.all (fun w => decide (Word.OK w))) = true := by native_decide

private theorem interface_ok : ∀ k : Fin 88,
    let c := (Nonuniform.layer k).word
    Word.OK c ∧ Same (transpose (named c)) (named (ShoreCheck.transposeWord c)) ∧
      c ∈ ShoreCheck.orientedInterfaces ∧ ShoreCheck.transposeWord c ∈ ShoreCheck.orientedInterfaces := by
  unfold Same
  native_decide

/-- Ordinary two-step intersection identities imply that the two shore words
in the explicit bank are covered by a point permutation to a catalog row. -/
theorem of_bank_coordinates (k : Fin 88) {cross left right : Coloring} {l r : Word}
    (hc : Same cross (named (Nonuniform.layer k).word))
    (bl : l ∈ ShoreCheck.bank) (br : r ∈ ShoreCheck.bank)
    (hl : Same left (named l)) (hr : Same right (named r))
    (cl : Compatible cross left) (cr : Compatible (transpose cross) right) :
    ∃ (t : Nat) (m : Word), Layers.matrices[t]? = some m ∧
      PartitionIso (completion cross left right) (Placements.color m) := by
  obtain ⟨wc, ht, inm, intm⟩ := interface_ok k
  have ht' : Same (transpose cross) (named (ShoreCheck.transposeWord (Nonuniform.layer k).word)) :=
    fun i j x y => ((same_transpose hc) i j x y).trans (ht i j x y)
  have lmem := ShoreCheck.selected_of_intersection_regular inm bl (regular hc hl cl)
  have rmem := ShoreCheck.selected_of_intersection_regular intm br (regular ht' hr cr)
  obtain ⟨t,m,member,f,hf⟩ := Nonuniform.every_listed_placement k
    (Array.mem_toList_iff.mp lmem) (Array.mem_toList_iff.mp rmem)
  have smallL := of_decide_eq_true (List.all_eq_true.mp bank_ok l bl)
  have smallR := of_decide_eq_true (List.all_eq_true.mp bank_ok r br)
  have small : ∀ w ∈ [(Nonuniform.layer k).word,l,r], Word.OK w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  obtain ⟨e, he⟩ := as_model hc hl hr small
  exact ⟨t,m,member,e.trans f, fun i j x y => (he i j x y).trans (hf (e i) (e j) (e x) (e y))⟩

open scoped BigOperators

/-- For two named relations the number of intermediate vertices depends only
on the relation of the endpoints: the ordinary intersection-number law. -/
def HasIntersectionNumbers {X A : Type} [Fintype X] [DecidableEq A] (m : X → X → A) : Prop :=
  ∀ a b i j x y, m i j = m x y →
    (∑ z, if m i z = a ∧ m z j = b then 1 else 0 : Nat) =
    (∑ z, if m x z = a ∧ m z y = b then 1 else 0 : Nat)

theorem compatibility_of_products {c l r : Coloring}
    (h : HasIntersectionNumbers (completion c l r)) :
    Compatible c l ∧ Compatible (transpose c) r := by
  unfold HasIntersectionNumbers at h
  simp only [Fintype.sum_sum_type] at h
  refine ⟨⟨?_,?_⟩, ⟨?_,?_⟩⟩
  · intro a b i j x y eq
    simp only [product, List.sum_ofFn]
    simpa [completion, transpose] using
      h (1,a) (2,b) (.inl i) (.inl j) (.inl x) (.inl y) (by simp [completion, eq])
  · intro a b i j x y eq
    simp only [product, List.sum_ofFn]
    simpa [completion] using
      h (0,a) (1,b) (.inl i) (.inr j) (.inl x) (.inr y) (by simp [completion, eq])
  · intro a b i j x y eq
    simp only [product, List.sum_ofFn]
    simpa [completion, transpose] using
      h (2,a) (1,b) (.inr i) (.inr j) (.inr x) (.inr y) (by simp [completion, eq])
  · intro a b i j x y eq
    change c j i = c y x at eq
    simp only [product, List.sum_ofFn]
    simpa [completion, transpose] using
      h (3,a) (2,b) (.inr i) (.inl j) (.inr x) (.inl y) (by simp [completion, eq])

/-- Arbitrarily colored homogeneous shores on a listed nonuniform cross
partition. Neither shore needs a supplied labeling into the bank. -/
theorem every_fixed_nonuniform (k : Fin 88) (cross left right : Coloring)
    (hc : Same cross (named (Nonuniform.layer k).word)) (hl : Homogeneous left)
    (hr : Homogeneous right) (products : HasIntersectionNumbers (completion cross left right)) :
    ∃ (t : Nat) (m : Word), Layers.matrices[t]? = some m ∧
      PartitionIso (completion cross left right) (Placements.color m) := by
  obtain ⟨l,bl,h₁⟩ := ShoreLabels.exists_bank_word left hl
  obtain ⟨r,br,h₂⟩ := ShoreLabels.exists_bank_word right hr
  obtain ⟨cl,cr⟩ := compatibility_of_products products
  apply of_bank_coordinates k hc bl br _ _ cl cr
  · exact fun i j x y => (h₁ i j x y).trans Fin.val_inj.symm
  · exact fun i j x y => (h₂ i j x y).trans Fin.val_inj.symm

theorem rename_products {X A B : Type} [Fintype X] [DecidableEq A] [DecidableEq B]
    {m : X → X → A} {d : X → X → B} (same : ∀ i j x y, m i j = m x y ↔ d i j = d x y)
    (closed : HasIntersectionNumbers m) : HasIntersectionNumbers d := by
  intro u v i j x y eq
  by_cases hu : ∃ k l, d k l = u
  · obtain ⟨k,l,rfl⟩ := hu
    by_cases hv : ∃ z w, d z w = v
    · obtain ⟨z,w,rfl⟩ := hv
      simpa only [same] using closed (m k l) (m z w) i j x y ((same _ _ _ _).mpr eq)
    · push_neg at hv
      simp [hv]
  · push_neg at hu
    simp [hu]

/-- A full two-shore coloring in fixed interface coordinates, with arbitrary
original relation names. The other assumptions are the defining color laws. -/
theorem every_raw_nonuniform (k : Fin 88) (m : V ⊕ V → V ⊕ V → Nat)
    (cross : Same (fun i j => m (.inl i) (.inr j)) (named (Nonuniform.layer k).word))
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    ∃ (t : Nat) (row : Word), Layers.matrices[t]? = some row ∧ PartitionIso m (Placements.color row) := by
  let c : Coloring := fun i j => m (.inl i) (.inr j)
  let l : Coloring := fun i j => m (.inl i) (.inl j)
  let r : Coloring := fun i j => m (.inr i) (.inr j)
  have eqv : ∀ i j x y, m i j = m x y ↔ completion c l r i j = completion c l r x y := by
    rintro (i|i) (j|j) (x|x) (y|y) <;> simp [completion, c, l, r]
      <;> first | exact ⟨rev _ _ _ _, rev _ _ _ _⟩
                | intro h; have sideEq := rectangle _ _ _ _ h; simp [side] at sideEq
  obtain ⟨t,row,mem,f,hf⟩ := every_fixed_nonuniform k c l r cross hl hr (rename_products eqv products)
  exact ⟨t,row,mem,f,fun i j x y => (eqv i j x y).trans (hf i j x y)⟩

end QGI.DoubleEight.FixedInterface
