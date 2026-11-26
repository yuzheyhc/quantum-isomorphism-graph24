import EightTwelveSignPlacement

namespace QGI.EightTwelveSigns
open Cliques

structure RowPresentation (o : Pairing) (b : I → Finset J) where
  rep : Rep
  left : Equiv.Perm I
  right : Equiv.Perm J
  catalog : key rep=atlas o
  names : ∀ j k, rightName (atlas o) (right j) (right k)=rightName (atlas o) j k
  hit : ∀ i j, right j∈b (left i) ↔ inside rep i j=true

def Uniform (o : Pairing) (b : I → Finset J) :=
  ∀ i t j k, (j∈b i ↔ k∈b t) → sig o (b i) j=sig o (b t) k

theorem present (o : Pairing) (b : I → Finset J)
    (split : ∀ i a, point o a false∈b i ↔ point o a true∉b i)
    (gram : ∀ i t, i≠t → (b i∩b t).card=2 ∨ (b i∩b t).card=3)
    (weight : ∀ i, (b i).card=6) (uniform : Uniform o b) :
    Nonempty (RowPresentation o b) := by
  classical
  choose w hw using fun i => word_for (b i) (split i)
  have adjacent (i j : I) (h : i≠j) : Adj (w i) (w j) := by
    have eq := distances o (w i) (w j)
    rw [hw,hw] at eq
    obtain h|h := gram i j h <;> unfold Adj <;> omega
  have inj : Function.Injective w := by
    intro i j eq
    by_contra ne
    have d := gram i j ne
    rw [←hw i,eq,hw j,Finset.inter_self,weight] at d
    omega
  let f := Finset.univ.image w
  have card : f.card=8 := by simp [f,Finset.card_image_of_injective _ inj]
  obtain ⟨s,hs⟩ := exhaustive card (by
    intro u hu v hv ne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact adjacent i j (fun h => ne (congrArg w h)))
  have found (t : I) : ∃ i : I, w i=wordAt s t := by
    exact (Finset.mem_image.mp (hs ▸ (Finset.mem_image_of_mem (wordAt s) (Finset.mem_univ t)) : wordAt s t∈f)).imp
      (fun _ ⟨_,eq⟩ => eq)
  choose idx hi using found
  have wr (t : I) : rowSet o (wordAt s t)=b (idx t) := (congrArg (rowSet o) (hi t)).symm.trans (hw _)
  have anchor_mem (t : I) (bit : Bool) : anchor o (wordAt s t) bit∈b (idx t) ↔ bit=true := by
    rw [←wr,anchor,readPoint]
    cases bit <;> simp
  let p := profile o (wordAt s 0)
  have sig_eq (t : I) (j : J) : sig o (rowSet o (wordAt s t)) j =
      if j∈rowSet o (wordAt s t) then p.1 else p.2 := by
    rw [wr]
    by_cases mem : j∈b (idx t)
    · rw [if_pos mem]
      change _=sig o (rowSet o (wordAt s 0)) _
      rw [wr]
      exact uniform _ _ _ _ (iff_of_true mem ((anchor_mem 0 true).mpr rfl))
    · rw [if_neg mem]
      change _=sig o (rowSet o (wordAt s 0)) _
      rw [wr]
      exact uniform _ _ _ _ (iff_of_false mem (fun h => Bool.noConfusion ((anchor_mem 0 false).mp h)))
  have summary_ok (t : I) : summary o (wordAt s t)=some p := by
    have eq : profile o (wordAt s t)=p := by
      apply Prod.ext
      · simpa only [profile,wr,if_pos ((anchor_mem t true).mpr rfl)] using sig_eq t (anchor o (wordAt s t) true)
      · simpa only [profile,wr,if_neg (show anchor o (wordAt s t) false∉b (idx t) from
          fun h => Bool.noConfusion ((anchor_mem t false).mp h))] using sig_eq t (anchor o (wordAt s t) false)
    simp only [summary,eq,if_pos (sig_eq t)]
  obtain ⟨a,g,ka,right,rows⟩ := classify o s p summary_ok
  choose t ht using rows
  let left := fun i : I => idx (t i)
  have cell (i j) : g j∈b (left i) ↔ inside a i j=true := by rw [←ht,wr]
  have mono : Function.Injective left := by
    intro i k eq
    apply differentRows a
    funext j
    exact Bool.eq_iff_iff.mpr (((cell i j).symm.trans (eq ▸ Iff.rfl)).trans (cell k j))
  exact ⟨⟨a,Equiv.ofBijective left (Finite.injective_iff_bijective.mp mono),g,ka,right,cell⟩⟩

end QGI.EightTwelveSigns
