import RegionalTenTenPairs

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross TenPointCrossLaws SmallUnion StrategyColorLaws
open SixTenCoordinates (Shore atPoint Block Laws)
open FourTwelveFunctional (source)

theorem label_onto {q : V → Fin 5} (two : ∀ i, (Finset.univ.filter (fun x => q x=i)).card=2) :
    Function.Surjective q := by
  intro i
  obtain ⟨x,h⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (two i).symm)
  exact ⟨x,(Finset.mem_filter.mp h).2⟩

section
variable {n l r v : Nat} {c d : Fin n → Fin n → Nat}
    {F : Shore c l V} {Y : Shore c r V} {T : Shore d l V} {Z : Shore d r V}
    (S : Pairs F Y v)

theorem row_read (i : V) : row F Y v i=Finset.univ.filter (fun j => S.right j=S.left i) := by
  ext j; simp [row,S.member_iff,eq_comm]
theorem col_read (j : V) : col F Y v j=Finset.univ.filter (fun i => S.left i=S.right j) := by
  ext i; simp [col,S.member_iff]

theorem overlap (i k : V) : (row F Y v i∩row F Y v k).card=if S.left i=S.left k then 2 else 0 := by
  rw [row_read S,row_read S]
  by_cases h : S.left i=S.left k
  · rw [if_pos h,h,Finset.inter_self,S.right_two]
  · rw [if_neg h]
    apply Finset.card_eq_zero.mpr
    exact Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_left.mpr (fun j hj hk =>
      h ((Finset.mem_filter.mp hj).2.symm.trans (Finset.mem_filter.mp hk).2)))

def mark (F : Shore c l V) (Y : Shore c r V) (v : Nat) (i j : V) := decide (entry F Y i j=v)

theorem row_gram (law : Laws c d) {i k x y : V}
    (eq : c (atPoint F i) (atPoint F k)=d (atPoint T x) (atPoint T y)) :
    (row F Y v i∩row F Y v k).card=(row T Z v x∩row T Z v y).card := by
  have h : Block F T Y Z (mark F Y v) (mark T Z v) := fun ⦃_ _ _ _⦄ e => congrArg (fun t => decide (t=v)) e
  have expand {s t : V → Prop} [DecidablePred s] [DecidablePred t] :
      Finset.univ.filter s∩Finset.univ.filter t=Finset.univ.filter (fun x => s x ∧ t x) := by ext; simp
  simpa only [Block.overlap,mark,decide_eq_true_eq,row,expand] using Block.gram law h eq

theorem internal (D : Pairs T Z v) (law : Laws c d) {i j x y : V}
    (eq : c (atPoint F i) (atPoint F j)=d (atPoint T x) (atPoint T y)) :
    S.left i=S.left j ↔ D.left x=D.left y := by
  have h := row_gram (Y:=Y) (Z:=Z) (v:=v) law eq
  rw [overlap S,overlap D] at h
  split_ifs at h <;> simp_all

theorem transport (law : Laws c d) (self : Laws d d)
    (left : ∀ i j, c (atPoint F i) (atPoint F j)=d (atPoint T i) (atPoint T j)) :
    ∃ D : Pairs T Z v, D.left=S.left := by
  have eq (i k) : (row T Z v i∩row T Z v k).card=if S.left i=S.left k then 2 else 0 :=
    (row_gram (Y:=Y) (Z:=Z) (v:=v) law (left i k)).symm.trans (overlap S i k)
  have wt (i : V) : (row T Z v i).card=2 := by simpa only [Finset.inter_self,if_pos rfl] using eq i i
  have degree (j : V) : (col T Z v j).card=2 := (col_size T Z self v 0 j).trans (wt 0)
  choose pick hp using fun j => Finset.card_pos.mp ((by decide : 0<2).trans_eq (degree j).symm)
  let R := fun j => S.left (pick j)
  have read (i j : V) : entry T Z i j=v ↔ S.left i=R j := by
    have inc : j∈row T Z v (pick j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hp j)).2⟩
    constructor
    · intro h
      have pos := Finset.card_pos.mpr (show (row T Z v i∩row T Z v (pick j)).Nonempty from
        ⟨j,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,inc⟩⟩)
      by_contra bad
      rw [eq,if_neg bad] at pos
      omega
    · intro h
      have full := eq i (pick j)
      rw [if_pos h] at full
      have sub := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁:=row T Z v i) (s₂:=row T Z v (pick j)))
        ((wt _).trans full.symm).le
      have both : j∈row T Z v i∩row T Z v (pick j) := sub.symm ▸ inc
      have first : j∈row T Z v i := (Finset.mem_inter.mp both).1
      exact (Finset.mem_filter.mp first).2
  refine ⟨⟨S.left,R,S.left_two,?_,read⟩,rfl⟩
  intro q
  obtain ⟨i,rfl⟩ := label_onto S.left_two q
  have same : Finset.univ.filter (fun j => R j=S.left i)=row T Z v i := by
    ext j; simp only [row,Finset.mem_filter,Finset.mem_univ,true_and,read,eq_comm (a:=R j)]
  exact (congrArg Finset.card same).trans (wt i)
end

end QGI.Coherent.TenPointMatched
