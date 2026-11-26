import TenPointCrossLaws
import OddHalfPartition

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross TenPointCrossLaws
open SixTenCoordinates (Shore atPoint sourceLaws Block)
open SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)

structure Pairs {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l V) (Y : Shore c r V) (v : Nat) where
  left : V → Fin 5
  right : V → Fin 5
  left_two : ∀ q, (Finset.univ.filter (fun i => left i=q)).card=2
  right_two : ∀ q, (Finset.univ.filter (fun j => right j=q)).card=2
  member_iff : ∀ i j, (entry F Y i j=v ↔ left i=right j)

theorem of_repeat {n l r : Nat} {c : Fin n → Fin n → Nat} (law : SixTenCoordinates.Laws c c)
    (F : Shore c l V) (Y : Shore c r V) (v : Nat) (size : ∀ i,(row F Y v i).card=2)
    (rep : ¬Function.Injective (col F Y v)) : Nonempty (Pairs F Y v) := by
  classical
  let C := col F Y v
  let B (j i : V) := decide (entry F Y i j=v)
  have cs (j) : (C j).card=2 := (col_size F Y law v 0 j).trans (size 0)
  have degree (j) : FiberRectangles.degree (B j)=2 := by simpa only [FiberRectangles.degree,B,decide_eq_true_eq,C,col] using cs j
  have named := OddHalfPartition.column_block (v:=v) law F Y B (fun _ _ => by simp [B,entry]) degree
  have equiv (j k : V) : B j=B k ↔ C k=C j := by
    constructor
    · intro eq; ext i; simpa only [B,decide_eq_true_eq,C,col,Finset.mem_filter,Finset.mem_univ,true_and] using (Bool.eq_iff_iff.mp (congrFun eq i).symm)
    · intro eq; funext i
      apply Bool.eq_iff_iff.mpr
      simpa only [B,decide_eq_true_eq,C,col,Finset.mem_filter,Finset.mem_univ,true_and] using Finset.ext_iff.mp eq.symm i
  let dup (j : V) := Finset.univ.filter fun t => C t=C j
  have ksize (j) : (dup j).card=(dup 0).card := by
    simpa only [decide_eq_true_eq,equiv,dup] using Block.degree_eq law named j 0
  have pair (j) : (dup j).card=2 := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (cs j).symm)
    have sub : dup j⊆row F Y v i := fun k hk => by
      have h : i∈C k := (Finset.mem_filter.mp hk).2.symm ▸ hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
    have upper := (Finset.card_le_card sub).trans_eq (size i)
    have two : 1<(dup 0).card := by
      apply Classical.byContradiction; intro no; apply rep
      intro a b e
      have bound : (dup a).card≤1 := (ksize a).le.trans (Nat.le_of_not_gt no)
      exact Finset.card_le_one.mp bound a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩) b
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.symm⟩)
    have lower := ksize j; omega
  have classEq {i j} (hit : i∈C j) : row F Y v i=dup j := by
    apply Eq.symm (Finset.eq_of_subset_of_card_le ?_ ((size i).trans (pair j).symm).le)
    intro k hk
    have h : i∈C k := (Finset.mem_filter.mp hk).2.symm ▸ hit
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
  let values := Finset.univ.image C
  have one (s) (hs : s∈values) : (Finset.univ.filter (fun j => C j=s)).card=2 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact pair j
  have number : values.card=5 := by
    have all : Finset.univ.filter (fun j => C j∈values)=Finset.univ := Finset.eq_univ_of_forall
      (fun j => Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    have e := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V) values C
    rw [all,Finset.sum_congr rfl one,Finset.sum_const,smul_eq_mul,Finset.card_univ,Fintype.card_fin] at e
    omega
  let label : values ≃ Fin 5 := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe,Fintype.card_fin] using number)
  let R (j : V) := label ⟨C j,Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
  have hR (k j) : R k=R j ↔ C k=C j := label.injective.eq_iff.trans Subtype.ext_iff
  have onto (q : Fin 5) : ∃ j,R j=q := by
    obtain ⟨s,rfl⟩ := label.surjective q
    obtain ⟨j,_,h⟩ := Finset.mem_image.mp s.property
    exact ⟨j,congrArg label (Subtype.ext h)⟩
  choose nbr hn using fun i => Finset.card_pos.mp ((by decide : 0<2).trans_eq (size i).symm)
  let L (i : V) := R (nbr i)
  have mark (i j) : entry F Y i j=v ↔ L i=R j := by
    have hit : i∈C (nbr i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hn i)).2⟩
    have eq := Finset.ext_iff.mp (classEq hit) j
    simpa only [row,dup,Finset.mem_filter,Finset.mem_univ,true_and,L,hR,eq_comm (a:=C j) (b:=C (nbr i))] using eq
  refine ⟨⟨L,R,?_,?_,mark⟩⟩
  · intro q; obtain ⟨j,rfl⟩ := onto q; simpa only [←mark,col,C] using cs j
  · intro q; obtain ⟨j,rfl⟩ := onto q; simpa only [hR,dup] using pair j

end QGI.Coherent.TenPointMatched
