import SixEightGeometry
import RegionalSignatureBound

noncomputable section
namespace QGI.Coherent.ShoreSignatureSize
open SixTenCoordinates SixEightGeometry
open FourTwelveFunctional (source)
open Classical

/-- In a nonuniform named rectangle each row signature class has at
most half as many points as the whole row shore. -/
theorem half {n l r k m : Nat} [NeZero k] [NeZero m] {c : Fin n → Fin n → Nat} (law : Laws c c)
    (A : Shore c l (Fin k)) (B : Shore c r (Fin m)) (mixed : ¬∀ i j, rect A B i j=rect A B 0 0) (i : Fin k) :
    (Finset.univ.filter (fun t => ∀ j, rect A B t j=rect A B i j)).card≤k/2 := by
  let M := rect A B
  let R (v : Nat) (i : Fin k) := Finset.univ.filter (fun j => M i j=v)
  let C (v : Nat) (j : Fin m) := Finset.univ.filter (fun i => M i j=v)
  have mark (v) : Block A A B B (fun i j => decide (M i j=v)) (fun i j => decide (M i j=v)) :=
    fun ⦃_ _ _ _⦄ h => congrArg (fun x => decide (x=v)) h
  have rows (v x y) : (R v x).card=(R v y).card := by
    simpa only [R,decide_eq_true_eq] using Block.degree_eq law (mark v) x y
  have cols (v x y) : (C v x).card=(C v y).card := by
    simpa only [C,decide_eq_true_eq] using Block.degree_eq law (Block.flip law (mark v)) x y
  push_neg at mixed
  obtain ⟨i₁,j₁,ne⟩ := mixed
  let v := M 0 0
  let w := M i₁ j₁
  have disj : Disjoint (C v 0) (C w 0) := by
    apply Finset.disjoint_left.mpr
    intro t hv hw
    exact ne ((Finset.mem_filter.mp hw).2.symm.trans (Finset.mem_filter.mp hv).2)
  have sum : (C v 0).card+(C w 0).card≤k := by
    rw [←Finset.card_union_of_disjoint disj]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have pick : ∃ q x y, M x y=q ∧ (C q 0).card≤k/2 := by
    by_cases h : (C v 0).card≤k/2
    · exact ⟨v,0,0,rfl,h⟩
    · exact ⟨w,i₁,j₁,rfl,by omega⟩
  obtain ⟨q,x,y,hq,small⟩ := pick
  have positive : 0<(R q i).card := (Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩⟩ : 0<(R q x).card).trans_eq (rows q x i)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp positive
  apply (Finset.card_le_card (t:=C q j) ?_).trans ((cols q j 0).le.trans small)
  intro b h
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h j).trans (Finset.mem_filter.mp hj).2⟩

end QGI.Coherent.ShoreSignatureSize
