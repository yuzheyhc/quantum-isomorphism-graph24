import NineNinePappus

noncomputable section
namespace QGI.SevenFourteen.Heawood
/-- SageMath's documented Heawood graph6 string MhEGHC@AI?_PC@_G_,
read in graph6 order (upper triangle, most significant bit first).
https://doc.sagemath.org/html/en/reference/graphs/sage/graphs/generators/smallgraphs.html#sage.graphs.generators.smallgraphs.HeawoodGraph -/
def edge (i j : Fin 14) : Bool :=
  let upper := max i.val j.val
  let index := upper*(upper-1)/2 + min i.val j.val
  let digit := ("MhEGHC@AI?_PC@_G_".toList.getD (1+index/6) '?').toNat - 63
  decide (i≠j) && digit.testBit (5-index%6)
abbrev S := Fin 7
abbrev Index := S ⊕ S
def fano (line point : S) : Bool := ((![112,76,67,42,37,25,22] : S → Nat) line).testBit (6-point.val)
def relation : Index → Index → Bool
  | .inl i,.inr j => fano j i
  | .inr j,.inl i => fano j i
  | _,_ => false
private def number : Index → Fin 14 :=
  Sum.elim (![0,2,10,4,6,12,8] : S → Fin 14) (![1,5,13,3,7,9,11] : S → Fin 14)
theorem numbering : ∃ e : Index ≃ Fin 14, ∀ i j, relation i j=edge (e i) (e j) := by
  have one : ∀ i j, number i=number j → i=j := by native_decide
  have onto : ∀ j, ∃ i, number i=j := by native_decide
  exact ⟨Equiv.ofBijective number ⟨fun _ _ => one _ _,onto⟩,
    by change ∀ i j, relation i j=edge (number i) (number j); native_decide⟩
end QGI.SevenFourteen.Heawood

namespace QGI.Literature
/-- Simon Schmidt, *On the quantum symmetry of distance-transitive graphs*,
Theorem 1.5, Table 2 and §5.1, for the Heawood graph. Its universal
magic unitary therefore has commuting images in each Hilbert-space
representation. https://arxiv.org/pdf/1906.06537 -/
axiom schmidt_heawood {I E : Type} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (adj : I → I → Bool) (e : I ≃ Fin 14)
    (graph : ∀ i j, adj i j=SevenFourteen.Heawood.edge (e i) (e j))
    (U : I → I → (E →L[ℂ] E)) (proj : ∀ i j, U i j*U i j=U i j ∧ U i j=(U i j).adjoint)
    (row : ∀ i, ∑ a, U i a=1) (col : ∀ a, ∑ i, U i a=1)
    (inter : ∀ i b, (∑ a, if adj a b then U i a else 0)=∑ j, if adj i j then U j b else 0) :
    ∀ i a j b, Commute (U i a) (U j b)
end QGI.Literature

namespace QGI.Coherent.SevenFourteenQuotient

/-- A quantum permutation preserving an equivalence relation descends to
a quantum permutation of its classes. On singleton columns its entries
are the original entries. -/
theorem commuting {I X E : Type} [Fintype I] [DecidableEq I] [Fintype X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (tag : X → I) (rep : I → X) (section_ : ∀ i, tag (rep i)=i)
    (P : X → X → (E →L[ℂ] E)) (proj : ∀ x y, P x y*P x y=P x y ∧ P x y=(P x y).adjoint)
    (row : ∀ x, ∑ y, P x y=1) (col : ∀ y, ∑ x, P x y=1)
    (orth : ∀ x a b, a≠b → P x a*P x b=0)
    (classes : ∀ x y a b, ¬(tag x=tag y ↔ tag a=tag b) → P x a*P y b=0)
    (graph : I → I → Bool)
    (edges : ∀ x y a b, graph (tag x) (tag y)≠graph (tag a) (tag b) → P x a*P y b=0)
    (rigid : ∀ U : I → I → (E →L[ℂ] E),
      (∀ i a, U i a*U i a=U i a ∧ U i a=(U i a).adjoint) →
      (∀ i, ∑ a, U i a=1) → (∀ a, ∑ i, U i a=1) →
      (∀ i b, (∑ a, if graph a b then U i a else 0)=∑ j, if graph i j then U j b else 0) →
      ∀ i a j b, Commute (U i a) (U j b))
    (i a j b : I) (oneA : ∀ x, tag x=a → x=rep a) (oneB : ∀ x, tag x=b → x=rep b) :
    Commute (P (rep i) (rep a)) (P (rep j) (rep b)) := by
  classical
  let Q := fun i a => ∑ y : X, if tag y=a then P (rep i) y else 0
  have left (i a y) : Q i a*P (rep i) y=if tag y=a then P (rep i) y else 0 := by
    unfold Q
    rw [Finset.sum_mul]
    rw [Finset.sum_eq_single y]
    · by_cases hit : tag y=a <;> simp [hit,(proj _ _).1]
    · intro z _ ne
      by_cases hit : tag z=a <;> simp [hit,orth _ _ _ ne]
    · simp
  have qproj (i a) : Q i a*Q i a=Q i a ∧ Q i a=(Q i a).adjoint := by
    constructor
    · change Q i a*(∑ y, if tag y=a then P (rep i) y else 0)=_
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      by_cases h : tag y=a <;> simp [h,left]
    · unfold Q
      rw [map_sum]
      apply Finset.sum_congr rfl; intro y _
      by_cases h : tag y=a
      · simpa only [h,if_true] using (proj (rep i) y).2
      · simp [h]
  have rr (i) : ∑ a, Q i a=1 := by
    unfold Q; rw [Finset.sum_comm]; simpa using row (rep i)
  have colForm (i a) : Q i a=∑ x : X, if tag x=i then P x (rep a) else 0 := by
    have eq := NamedQuantumGraph.intertwines (fun x y => decide (tag x=tag y)) P row col
      (fun x y u v ne => classes x y u v (fun e => ne (Bool.decide_congr e))) (rep i) (rep a)
    have flip (x : X) : i=tag x ↔ tag x=i := eq_comm
    simpa only [Q,section_,decide_eq_true_eq,flip] using eq
  have cc (a) : ∑ i, Q i a=1 := by
    rw [Finset.sum_congr rfl (fun i _ => colForm i a),Finset.sum_comm]
    simpa using col (rep a)
  have bad (i j a b) (ne : graph i j≠graph a b) : Q i a*Q j b=0 := by
    unfold Q; rw [Finset.sum_mul]
    apply Finset.sum_eq_zero; intro y _
    split_ifs with hy
    · rw [Finset.mul_sum]; apply Finset.sum_eq_zero; intro z _
      split_ifs with hz
      · exact edges _ _ _ _ (by simpa only [section_,hy,hz] using ne)
      · exact mul_zero _
    · exact zero_mul _
  have all := rigid Q qproj rr cc (NamedQuantumGraph.intertwines graph Q rr cc bad)
  have same (u v) (h : ∀ x, tag x=v → x=rep v) : Q u v=P (rep u) (rep v) := by
    unfold Q
    rw [Finset.sum_eq_single (rep v)]
    · rw [section_,if_pos rfl]
    · intro z _ ne; exact if_neg (fun e => ne (h z e))
    · simp
  simpa only [same i a oneA,same j b oneB] using all i a j b

end QGI.Coherent.SevenFourteenQuotient




