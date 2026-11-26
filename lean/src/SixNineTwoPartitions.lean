import SixNineGridGeometry

noncomputable section
namespace QGI.Coherent.SixNineTwoPartitions
open SixTenCoordinates SixEightGeometry SixNineGridGeometry
open FourTwelveFunctional (source)
open Classical

theorem named {n l r : Nat} {G : Graph n} {A : Shore (source G) l (Fin 6)} {Y : Shore (source G) r (Fin 9)}
    (P : Triple A Y) : Block Y Y Y Y (fun i j => decide (P.b i=P.b j)) (fun i j => decide (P.b i=P.b j)) := by
  let h (j : Fin 9) (i : Fin 6) := decide (P.a i=P.b j)
  have mark : Block A A Y Y (fun i j => h j i) (fun i j => h j i) := by
    intro i j a b eq
    exact decide_eq_decide.mpr ((P.flag i j).symm.trans ((Iff.of_eq (congrArg (·=P.mark) eq)).trans (P.flag a b)))
  have eq (i j) : 0<Block.overlap h i j ↔ P.b i=P.b j := by
    constructor
    · intro pos
      obtain ⟨z,hz⟩ := Finset.card_pos.mp pos
      have pair := (Finset.mem_filter.mp hz).2
      exact (of_decide_eq_true pair.1).symm.trans (of_decide_eq_true pair.2)
    · intro same
      obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun i => P.a i=P.b j)).card by rw [P.aSize]; decide)
      have h₁ := (Finset.mem_filter.mp hz).2
      exact Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true (h₁.trans same.symm),decide_eq_true h₁⟩⟩
  intro i j a b same
  have hg : Block.overlap h i j=Block.overlap h a b := Block.gram (sourceLaws _) (Block.flip (sourceLaws _) mark) same
  exact decide_eq_decide.mpr ((eq i j).symm.trans ((Iff.of_eq (congrArg (0<·) hg)).trans (eq a b)))

theorem alternative {n l r z : Nat} {G : Graph n} {A : Shore (source G) l (Fin 6)} {B : Shore (source G) r (Fin 6)}
    {Y : Shore (source G) z (Fin 9)} (P : Triple A Y) (Q : Triple B Y) :
    (∀ i j, P.b i=P.b j → Q.b i=Q.b j) ∨ HasFour Y := by
  classical
  by_cases h : ∀ i j, P.b i=P.b j → Q.b i=Q.b j
  · exact Or.inl h
  right
  let a (i : Fin 9) := Finset.univ.filter (fun j => P.b j=P.b i)
  let b (i : Fin 9) := Finset.univ.filter (fun j => Q.b j=Q.b i)
  let both (i j : Fin 9) := decide (P.b i=P.b j) && decide (Q.b i=Q.b j)
  have bothNamed : Block Y Y Y Y both both := Block.map₂ (named P) (named Q) (· && ·)
  have eq (i) : FiberRectangles.degree (both i)=(a i∩b i).card := by
    apply congrArg Finset.card; ext j
    simp only [both,a,b,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr eq_comm eq_comm
  have constant (i j) : (a i∩b i).card=(a j∩b j).card := (eq i).symm.trans ((Block.degree_eq (sourceLaws _) bothNamed i j).trans (eq j))
  have sa (i) : (a i).card=3 := P.bSize _
  have sb (i) : (b i).card=3 := Q.bSize _
  push_neg at h
  obtain ⟨x,y,hp,hq⟩ := h
  have xy : a x=a y := by dsimp only [a]; rw [hp]
  have dis : Disjoint (a x∩b x) (a y∩b y) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact hq ((Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2.symm.trans (Finset.mem_filter.mp (Finset.mem_inter.mp hk).2).2)
  have le : (a x∩b x).card+(a y∩b y).card≤3 := by
    rw [←Finset.card_union_of_disjoint dis,←sa x]
    exact Finset.card_le_card (Finset.union_subset (Finset.inter_subset_left) (xy ▸ Finset.inter_subset_left))
  have one (i) : (a i∩b i).card=1 := by
    have pos : i∈a i∩b i := by simp [a,b]
    have ht := Finset.card_pos.mpr ⟨i,pos⟩
    have hx := constant x i; have hy := constant y i
    omega
  let g (i j : Fin 9) := decide (i≠j ∧ (P.b i=P.b j ∨ Q.b i=Q.b j))
  refine ⟨g,fun i => by simp [g],fun i j => by simp [g,eq_comm],fun i => ?_,?_⟩
  · have same : Finset.univ.filter (fun j => g i j=true)=(a i∪b i).erase i := by
      ext j
      simp only [a,b,g,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,Finset.mem_union,decide_eq_true_eq]
      exact and_congr ne_comm (or_congr eq_comm eq_comm)
    have here : i∈a i∪b i := by simp [a,b]
    have cap := Finset.card_union_add_card_inter (a i) (b i)
    change (Finset.univ.filter (fun j => g i j=true)).card=4
    rw [same,Finset.card_erase_of_mem here]
    have h₁ := sa i; have h₂ := sb i; have h₃ := one i; omega
  · intro i j x y hit
    have diag : i=j ↔ x=y := by
      constructor
      · rintro rfl; exact Y.injective (Subtype.ext (Relations.diagonal _ hit.symm))
      · rintro rfl; exact (Y.injective (Subtype.ext (Relations.diagonal _ hit)))
    have p₁ := decide_eq_decide.mp (named P hit)
    have p₂ := decide_eq_decide.mp (named Q hit)
    exact decide_eq_decide.mpr (and_congr (not_congr diag) (or_congr p₁ p₂))

end QGI.Coherent.SixNineTwoPartitions
