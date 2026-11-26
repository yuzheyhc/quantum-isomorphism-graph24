import QuantumGraph

noncomputable section
open scoped BigOperators

/-! Consequences of the *game* definition of QuantumIso. The formulas below
hold on the distinguished state or on vectors obtained by applying Alice words.
The ambient Hilbert space need not be the cyclic representation. -/
namespace QGI.Synchrony

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Move (n : Nat) := Question n × Fin n

/-- Apply the rightmost measurement outcome in the list first. -/
def word (P : Question n → Fin n → (K →L[ℂ] K)) :
    List (Move n) → K → K
  | [], v => v
  | e :: es, v => P e.1 e.2 (word P es v)

private theorem word_append (P : Question n → Fin n → (K →L[ℂ] K))
    (w w' : List (Move n)) (v : K) :
    word P (w ++ w') v = word P w (word P w' v) := by
  induction w with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, word, ih]

private theorem word_zero (P : Question n → Fin n → (K →L[ℂ] K))
    (w : List (Move n)) : word P w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons e es ih => simp [word, ih]

private theorem extract_outcome (L : K →L[ℂ] K) (P : Fin n → (K →L[ℂ] K))
    (hp : IsPVM P) (a : Fin n) (v : K)
    (off : ∀ b, b ≠ a → L (P b v) = 0) : L v = L (P a v) := by
  classical
  calc
    L v = L (∑ b, P b v) := congrArg (fun t => L t) (hp.complete v).symm
    _ = ∑ b, L (P b v) := map_sum L _ _
    _ = L (P a v) := Finset.sum_eq_single a
      (fun b _ hba => off b hba) (by simp)

variable (p : PerfectStrategy G H K)

private theorem supported_pair (q r : Question n) (a b : Fin n)
    (offB : ∀ b', b' ≠ b → Loses G H q r a b')
    (offA : ∀ a', a' ≠ a → Loses G H q r a' b) :
    p.alice q a p.psi = p.bob r b p.psi := by
  have hA := extract_outcome (p.alice q a) (p.bob r) (p.bobPVM r) b p.psi
    (fun b' h => p.perfect q r a b' (offB b' h))
  have hB := extract_outcome (p.bob r b) (p.alice q) (p.alicePVM q) a p.psi
    (fun a' h => (p.commute q r a' b p.psi).symm.trans
      (p.perfect q r a' b (offA a' h)))
  exact hA.trans ((p.commute q r a b p.psi).trans hB.symm)

private theorem unequal_same_question (q : Question n) {a b : Fin n} (h : a ≠ b) :
    Loses G H q q a b := by
  rcases q with ⟨s, x⟩
  intro eqTypes
  have hbit := congrArg (fun t : Bool × Bool => t.1) eqTypes
  cases s <;> simp [rel, ends, h] at hbit

/-- Alice and Bob agree, on the state, about each individual outcome. -/
theorem same_outcome (q : Question n) (a : Fin n) :
    p.alice q a p.psi = p.bob q a p.psi :=
  supported_pair p q q a a
    (fun _ h => unequal_same_question q (Ne.symm h))
    (fun _ h => unequal_same_question q h)

/-- Asking for the image of x and asking for the inverse image of a
give the same state vector for the corresponding answers. -/
theorem inverse_outcome (x a : Fin n) :
    p.alice (false,x) a p.psi = p.bob (true,a) x p.psi := by
  apply supported_pair p
  · intro y hy eqTypes
    have hbit := congrArg (fun t : Bool × Bool => t.1) eqTypes
    simp [rel, ends, Ne.symm hy] at hbit
  · intro b hb eqTypes
    have hbit := congrArg (fun t : Bool × Bool => t.1) eqTypes
    simp [rel, ends, hb] at hbit

theorem miss_on_state (q r : Question n) (a b : Fin n)
    (h : Loses G H q r a b) :
    p.alice q a (p.alice r b p.psi) = 0 := by
  rw [same_outcome p r b]
  exact p.perfect q r a b h

private theorem commute_bob_word (q : Question n) (a : Fin n)
    (w : List (Move n)) (v : K) :
    p.alice q a (word p.bob w v) = word p.bob w (p.alice q a v) := by
  induction w with
  | nil => rfl
  | cons e es ih =>
    simp only [word]
    rw [p.commute, ih]

/-- Moving one outcome at a time reverses the word on the other side. -/
theorem word_transfer (w : List (Move n)) :
    word p.alice w p.psi = word p.bob w.reverse p.psi := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    rw [List.reverse_cons, word_append]
    change p.alice e.1 e.2 (word p.alice w p.psi) =
      word p.bob w.reverse (p.bob e.1 e.2 p.psi)
    rw [ih, commute_bob_word, same_outcome]

/-- Losing products vanish on every algebraic cyclic vector. -/
theorem miss_on_word (q r : Question n) (a b : Fin n)
    (h : Loses G H q r a b) (w : List (Move n)) :
    p.alice q a (p.alice r b (word p.alice w p.psi)) = 0 := by
  rw [word_transfer, commute_bob_word p r b, commute_bob_word p q a,
    miss_on_state p q r a b h, word_zero]

theorem inverse_on_word (x a : Fin n) (w : List (Move n)) :
    p.alice (false,x) a (word p.alice w p.psi) =
    p.alice (true,a) x (word p.alice w p.psi) := by
  have same := (inverse_outcome p x a).trans ((same_outcome p (true,a) x).symm)
  rw [word_transfer, commute_bob_word p (false,x) a,
    commute_bob_word p (true,a) x, same]

theorem column_on_word (a : Fin n) (w : List (Move n)) :
    (∑ x, p.alice (false,x) a (word p.alice w p.psi)) = word p.alice w p.psi := by
  calc
    _ = ∑ x, p.alice (true,a) x (word p.alice w p.psi) :=
      Finset.sum_congr rfl (fun x _ => inverse_on_word p x a w)
    _ = _ := (p.alicePVM (true,a)).complete _

private theorem edge_filter (x y a b : Fin n) (w : List (Move n)) :
    (if G.edge x y = true then
      p.alice (false,x) a (p.alice (false,y) b (word p.alice w p.psi)) else 0) =
    (if H.edge a b = true then
      p.alice (false,x) a (p.alice (false,y) b (word p.alice w p.psi)) else 0) := by
  by_cases eqEdge : G.edge x y = H.edge a b
  · rw [eqEdge]
  · have bad : Loses G H (false,x) (false,y) a b := by
      intro h
      exact eqEdge (congrArg (fun t : Bool × Bool => t.2) h)
    simp [miss_on_word p _ _ _ _ bad w]

/-- The adjacency matrix intertwines the forward measurement matrix on the
cyclic vectors: (A_G U)_(x,b) v = (U A_H)_(x,b) v. -/
theorem adjacency_on_word (x b : Fin n) (w : List (Move n)) :
    (∑ y, (if G.edge x y = true then
              p.alice (false,y) b (word p.alice w p.psi) else 0)) =
    ∑ a, (if H.edge a b = true then
              p.alice (false,x) a (word p.alice w p.psi) else 0) := by
  classical
  let v := word p.alice w p.psi
  change (∑ y, (if G.edge x y = true then p.alice (false,y) b v else 0)) =
         ∑ a, (if H.edge a b = true then p.alice (false,x) a v else 0)
  calc
    _ = ∑ y, ∑ a, (if G.edge x y = true then
           p.alice (false,x) a (p.alice (false,y) b v) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : G.edge x y = true
      · simp only [if_pos h]
        exact ((p.alicePVM (false,x)).complete _).symm
      · simp [h]
    _ = ∑ y, ∑ a, (if H.edge a b = true then
           p.alice (false,x) a (p.alice (false,y) b v) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_congr rfl (fun a _ => edge_filter p x y a b w)
    _ = ∑ a, ∑ y, (if H.edge a b = true then
           p.alice (false,x) a (p.alice (false,y) b v) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : H.edge a b = true
      · simp only [if_pos h]
        rw [← map_sum]
        exact congrArg (fun t => p.alice (false,x) a t) (column_on_word p b w)
      · simp [h]

/-- The algebraic cyclic subspace of the given perfect strategy. -/
def cyclic : Submodule ℂ K :=
  Submodule.span ℂ (Set.range (fun w : List (Move n) => word p.alice w p.psi))

theorem psi_mem : p.psi ∈ cyclic p :=
  Submodule.subset_span ⟨[],rfl⟩

theorem psi_ne_zero : p.psi ≠ 0 := by
  intro zeroState
  have impossible := p.norm_psi
  rw [zeroState, norm_zero] at impossible
  exact zero_ne_one impossible

private theorem stable (q : Question n) (a : Fin n) :
    cyclic p ≤ (cyclic p).comap (p.alice q a).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  change p.alice q a (word p.alice w p.psi) ∈ cyclic p
  exact Submodule.subset_span ⟨(q,a) :: w,rfl⟩

/-- Two ambient operators agreeing on the word generators agree on their span. -/
private theorem eq_on_cyclic {L R : K →ₗ[ℂ] K}
    (hw : ∀ w : List (Move n), L (word p.alice w p.psi) = R (word p.alice w p.psi))
    {v : K} (hv : v ∈ cyclic p) : L v = R v := by
  have hker : cyclic p ≤ LinearMap.ker (L - R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    change L (word p.alice w p.psi) - R (word p.alice w p.psi) = 0
    exact sub_eq_zero.mpr (hw w)
  have hz := hker hv
  change L v - R v = 0 at hz
  exact sub_eq_zero.mp hz

/-- Alice's restricted measurement maps preserve the cyclic space. -/
def restricted (q : Question n) (a : Fin n) : cyclic p →ₗ[ℂ] cyclic p where
  toFun v := ⟨p.alice q a v,stable p q a v.property⟩
  map_add' v z := Subtype.ext (map_add (p.alice q a) (v : K) (z : K))
  map_smul' c v := Subtype.ext ((p.alice q a).map_smul c (v : K))

/-- Forward and reverse entries of the *restricted* strategy coincide as operators. -/
theorem restricted_inverse (x a : Fin n) :
    restricted p (false,x) a = restricted p (true,a) x := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact eq_on_cyclic p
    (L := (p.alice (false,x) a).toLinearMap) (R := (p.alice (true,a) x).toLinearMap)
    (inverse_on_word p x a) v.property

/-- Losing products are the zero map throughout the restricted space. -/
theorem restricted_mismatch (q r : Question n) (a b : Fin n)
    (h : Loses G H q r a b) :
    (restricted p q a).comp (restricted p r b) = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact eq_on_cyclic p
    (L := (p.alice q a).toLinearMap.comp (p.alice r b).toLinearMap) (R := 0)
    (miss_on_word p q r a b h) v.property

theorem restricted_projection (q : Question n) (a : Fin n) :
    (restricted p q a).comp (restricted p q a) = restricted p q a ∧
    ∀ v z : cyclic p,
      @inner ℂ K _ (restricted p q a v : K) (z : K) =
      @inner ℂ K _ (v : K) (restricted p q a z : K) := by
  constructor
  · apply LinearMap.ext
    intro v
    exact Subtype.ext ((p.alicePVM q).idempotent a (v : K))
  · intro v z
    exact (p.alicePVM q).selfAdjoint a (v : K) (z : K)

theorem magic_orthogonal (x a b : Fin n) (h : a ≠ b) :
    (restricted p (false,x) a).comp (restricted p (false,x) b) = 0 ∧
    (restricted p (false,a) x).comp (restricted p (false,b) x) = 0 := by
  constructor
  · exact restricted_mismatch p _ _ a b (unequal_same_question _ h)
  · rw [restricted_inverse p a x, restricted_inverse p b x]
    exact restricted_mismatch p _ _ a b (unequal_same_question _ h)

/-- Row and column sums are the identity on the cyclic module. We display the
pointwise equations in K using its injective inclusion. -/
theorem magic_sums (x : Fin n) (v : cyclic p) :
    (∑ a : Fin n, (restricted p (false,x) a v : K)) = (v : K) ∧
    (∑ a : Fin n, (restricted p (false,a) x v : K)) = (v : K) := by
  constructor
  · exact (p.alicePVM (false,x)).complete _
  · calc
      _ = ∑ a : Fin n, (restricted p (true,x) a v : K) :=
        Finset.sum_congr rfl (fun a _ => by rw [restricted_inverse p a x])
      _ = _ := (p.alicePVM (true,x)).complete _

private def maskedSum (mask : Fin n → Bool) (P : Fin n → (K →L[ℂ] K)) :
    K →ₗ[ℂ] K where
  toFun v := ∑ i, if mask i = true then P i v else 0
  map_add' v z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : mask i = true <;> simp [h]
  map_smul' c v := by
    change (∑ i, if mask i = true then P i (c • v) else 0) =
      c • ∑ i, if mask i = true then P i v else 0
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : mask i = true <;> simp [h]

theorem adjacency_on_cyclic (x b : Fin n) (v : cyclic p) :
    (∑ y, if G.edge x y = true then (restricted p (false,y) b v : K) else 0) =
     ∑ a, if H.edge a b = true then (restricted p (false,x) a v : K) else 0 :=
  eq_on_cyclic p
    (L := maskedSum (G.edge x) (fun y => p.alice (false,y) b))
    (R := maskedSum (fun a => H.edge a b) (p.alice (false,x)))
    (adjacency_on_word p x b) v.property

end QGI.Synchrony
