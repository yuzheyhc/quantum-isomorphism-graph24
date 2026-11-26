import FourPointInterface
import FiberPairExtension
import LargeOrderFourteen

noncomputable section
namespace QGI.Coherent.FourByEven
open FourTwelveCycle FourTwelveTypes SixTenCoordinates StrategyColorLaws FiberPairExtension
open SmallUnion SmallFiberExtension LargeOrderBlocks
open FourTwelveFunctional (source)

/-- The number of distinct columns divides the size of the other fiber.
For orders 10 and 14 only one opposite pair of labels can occur. -/
private theorem matching {m : Nat} [NeZero m] (b : Fin m → Edge) (order : m=10 ∨ m=14)
    (regular : ∀ i, degree b i=degree b 0) (same : ∀ i j, mult b (b i)=mult b (b j)) :
    ∃ e, ∀ j, b j=e ∨ b j=opposite e := by
  classical
  let s := Finset.univ.image b
  have mem (e : Edge) : e∈s ↔ ∃ j, b j=e := by simp [s]
  have pos (e : Edge) : e∈s ↔ 0 < mult b e := by simp [s,mult,Finset.card_pos,Finset.Nonempty]
  have closed (e) : e∈s ↔ opposite e∈s := by rw [pos,pos,opposite_mult b regular e]
  have value (e : Edge) : mult b e = if e∈s then mult b (b 0) else 0 := by
    by_cases h : e∈s
    · obtain ⟨j,rfl⟩ := (mem e).mp h
      rw [if_pos h]; exact same _ _
    · rw [if_neg h]; have hz := (pos e).not.mp h; omega
  have total : (∑ e, mult b e)=m := by
    simpa [mult] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m)) (Finset.univ : Finset Edge) b
  have sum : s.card * mult b (b 0)=m := by
    calc
      _ = ∑ e : Edge, if e∈s then mult b (b 0) else 0 := by simp
      _ = ∑ e : Edge, mult b e := Finset.sum_congr rfl (fun e _ => (value e).symm)
      _ = m := total
  have cases' : ∀ t : Finset Edge, (∀ e, e∈t ↔ opposite e∈t) →
      (∃ e, ∀ j∈t, j=e ∨ j=opposite e) ∨ t.card=4 ∨ t.card=6 := by decide
  rcases cases' s closed with ⟨e,he⟩|h|h
  · exact ⟨e,fun j => he _ ((mem _).mpr ⟨j,rfl⟩)⟩
  all_goals rw [h] at sum; rcases order with h|h <;> omega

/-- Every named four-by-ten or four-by-fourteen cross rectangle has the
twin property. The proof works inside an arbitrary ambient order. -/
theorem rectangle {n m l r : Nat} [NeZero m] {c : Fin n → Fin n → Nat}
    (law : Laws c c) (F : Shore c l (Fin 4)) (Y : Shore c r (Fin m)) (order : m=10 ∨ m=14) :
    FiberPairExtension.twins c l r := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  let S (v : Nat) (j : Fin m) := Finset.univ.filter (fun i => M i j=v)
  suffices twin : SplitRectangle.Twins M by
    constructor
    · intro i x j eq y
      simpa only [M,atPoint,Equiv.apply_symm_apply] using twin.1 (F.symm i) (F.symm x) (Y.symm j)
        (by simpa only [M,atPoint,Equiv.apply_symm_apply] using eq) (Y.symm y)
    · intro i j y eq x
      simpa only [M,atPoint,Equiv.apply_symm_apply] using twin.2 (F.symm i) (Y.symm j) (Y.symm y)
        (by simpa only [M,atPoint,Equiv.apply_symm_apply] using eq) (F.symm x)
  let a := M 0 0
  by_cases all : ∀ i j, M i j=a
  · exact ⟨fun i x _ _ y => (all i y).trans (all x y).symm,fun _ j y _ x => (all x j).trans (all x y).symm⟩
  push_neg at all
  obtain ⟨i₁,j₁,ne⟩ := all
  let b := M i₁ j₁
  have diff : a≠b := ne.symm
  let B (v : Nat) := fun i j => decide (M i j=v)
  have block (v) : Block F F Y Y (B v) (B v) := fun ⦃_ _ _ _⦄ h => congrArg (fun x => decide (x=v)) h
  have constant (v j) : (S v j).card=(S v 0).card := by
    simpa only [S,B,decide_eq_true_eq] using Block.degree_eq law (Block.flip law (block v)) j 0
  have min (i j) : 2 ≤ (S (M i j) 0).card := by
    let v := M i j
    have h := FiberRectangles.balance (B v) (fun t => Block.degree_eq law (block v) t 0)
      (fun j => Block.degree_eq law (Block.flip law (block v)) j 0)
    change 4 * FiberRectangles.degree (B v 0) = m * FiberRectangles.degree (fun i => B v i 0) at h
    have eq : FiberRectangles.degree (fun i => B v i 0) = (S v 0).card := by simp [FiberRectangles.degree,S,B]
    rw [eq] at h
    have pos : 0 < (S v 0).card :=
      (Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ : 0 < (S v j).card).trans_eq (constant v j)
    change 2 ≤ (S v 0).card
    rcases order with rfl|rfl <;> omega
  have disj (j) : Disjoint (S a j) (S b j) := Finset.disjoint_left.mpr
    fun _ av bv => diff ((Finset.mem_filter.mp av).2.symm.trans (Finset.mem_filter.mp bv).2)
  have cap := Finset.card_le_univ (S a 0 ∪ S b 0)
  rw [Finset.card_union_of_disjoint (disj _)] at cap
  change _ ≤ 4 at cap
  have ma : 2 ≤ (S a 0).card := min 0 0
  have mb : 2 ≤ (S b 0).card := min i₁ j₁
  have va (j) : (S a j).card=2 := (constant a j).trans (by omega)
  have vb (j) : (S b j).card=2 := (constant b j).trans (by omega)
  have palette (i j) : M i j=a ∨ M i j=b := by
    have all := Finset.eq_univ_of_card (S a j ∪ S b j) (by rw [Finset.card_union_of_disjoint (disj _),va,vb]; decide)
    have hit : i∈S a j ∪ S b j := all ▸ Finset.mem_univ _
    simpa [S] using hit
  choose e he using fun j => (show ∀ s : Finset (Fin 4), s.card=2 → ∃ e : Edge, edge e=s by decide) _ (va j)
  have bits (i j) : B a i j=true ↔ i∈edge (e j) := by simp [B,he,S]
  have rows (i) : degree e i=degree e 0 := by
    simpa only [degree,bits] using Block.degree_eq law (block a) i 0
  have meets (i j : Fin m) : Block.overlap (fun j i => B a i j) i j = 2 ↔ e i=e j := by
    have sets : Finset.univ.filter (fun k => B a k i=true ∧ B a k j=true) = edge (e i) ∩ edge (e j) := by
      ext k; simp [bits]
    simpa only [Block.overlap,sets,overlap] using edge_overlap (e i) (e j)
  have uniform (i j : Fin m) : mult e (e i)=mult e (e j) := by
    simpa only [Block.hist,meets,mult,eq_comm] using Block.hist_eq law (Block.gram law (Block.flip law (block a))) i j 2
  obtain ⟨v,hv⟩ := matching e order rows uniform
  let ls (i : Fin 4) := decide (i∈edge v)
  let rs (j : Fin m) := decide (e j=v)
  have op : ∀ t : Edge, opposite t ≠ t := by decide
  have mark (i j) : M i j=a ↔ ls i=rs j := by
    have h : M i j=a ↔ i∈edge (e j) := by simpa [B] using bits i j
    rw [h]
    rcases hv j with ht|ht <;> simp [ls,rs,ht,op,opposite_edge]
  have eq : M=fun i j => if ls i=rs j then a else b := by
    funext i j
    by_cases h : M i j=a
    · rw [if_pos ((mark _ _).mp h),h]
    · rw [if_neg (mt (mark _ _).mpr h)]; exact (palette _ _).resolve_left h
  rw [eq]
  exact SplitRectangle.twins_of_halves ls rs a b

end QGI.Coherent.FourByEven

