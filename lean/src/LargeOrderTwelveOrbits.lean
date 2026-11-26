import LargeOrderPointClosure

noncomputable section
namespace QGI.Coherent.LargeOrderTwelveOrbits

/-- Two distinct mates at each point of a twelve-point set generate at
most three equivalence classes. One representative of each class suffices. -/
theorem generators (a b : Fin 12 → Fin 12) (aa : Function.Involutive a) (bb : Function.Involutive b)
    (af : ∀ j, a j≠j) (bf : ∀ j, b j≠j) (different : ∀ j, a j ≠ b j) :
    ∃ rep : Fin 3 → Fin 12, ∀ X : Finset (Fin 12), (∀ i, rep i∈X) →
      (∀ j∈X, a j∈X) → (∀ j∈X, b j∈X) → ∀ j, j∈X := by
  classical
  let stable (X : Finset (Fin 12)) := (∀ i, i∈X ↔ a i∈X) ∧ (∀ i, i∈X ↔ b i∈X)
  let rel (i j : Fin 12) := ∀ X, stable X → (i∈X ↔ j∈X)
  let ss : Setoid (Fin 12) := ⟨rel,fun _ _ _ => Iff.rfl,fun h X hX => (h X hX).symm,
    fun h k X hX => (h X hX).trans (k X hX)⟩
  let Q := Quotient ss
  let key : Fin 12 → Q := Quotient.mk ss
  letI : Fintype Q := Fintype.ofFinite Q
  have sa (j) : key (a j)=key j := Quotient.sound (show rel (a j) j from fun X h => (h.1 j).symm)
  have sb (j) : key (b j)=key j := Quotient.sound (show rel (b j) j from fun X h => (h.2 j).symm)
  have four (s : Q) : 4≤(Finset.univ.filter fun j => key j=s).card := by
    let j : Fin 12 := s.out
    have hj : key j=s := Quotient.out_eq s
    have one : a (b j)≠j := fun eq => different j ((aa (b j)).symm.trans (congrArg a eq) |> Eq.symm)
    have two : a (b j)≠a j := fun eq => bf j (aa.injective eq)
    let T : Finset (Fin 12) := {a (b j),a j,b j,j}
    have card : T.card=4 := by simp [T,one,two,af,bf,different]
    have sub : T ⊆ Finset.univ.filter (fun k => key k=s) := by
      intro k hk
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at hk
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rcases hk with rfl|rfl|rfl|rfl <;> simp only [sa,sb,hj]
    exact card ▸ Finset.card_le_card sub
  have sum := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin 12)) (Finset.univ : Finset Q) key
  have lower : (∑ _ : Q, 4 : Nat) ≤ ∑ s : Q, (Finset.univ.filter fun j => key j=s).card := Finset.sum_le_sum (fun s _ => four s)
  have total : (∑ s : Q, (Finset.univ.filter fun j => key j=s).card)=12 := by simpa using sum
  rw [total,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at lower
  change Fintype.card Q * 4 ≤12 at lower
  have bound : Fintype.card Q ≤3 := by omega
  let e := Fintype.equivFin Q
  let rep (i : Fin 3) : Fin 12 := if h : i.val<Fintype.card Q then (e.symm ⟨i.val,h⟩).out else 0
  refine ⟨rep,fun X incl A B j => ?_⟩
  have closed : stable X := ⟨fun i => ⟨A i,fun h => (aa i) ▸ A _ h⟩,fun i => ⟨B i,fun h => (bb i) ▸ B _ h⟩⟩
  let i : Fin 3 := (e (key j)).castLE bound
  have eq : rep i=(key j).out := by
    simp only [rep,i,Fin.coe_castLE,dif_pos (e (key j)).isLt,Fin.eta,Equiv.symm_apply_apply]
  have belongs := incl i
  rw [eq] at belongs
  have reach : rel (key j).out j := Quotient.exact (Quotient.out_eq (key j))
  exact (reach X closed).mp belongs

end QGI.Coherent.LargeOrderTwelveOrbits
