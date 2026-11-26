import NineNineNormal
import SixTenCoordinates

namespace QGI.NineNine.Partition
open BareLex (V)
open Coherent.SixTenCoordinates (Shore atPoint Block Laws)
abbrev Tri := Fin 3
def tag (i : V) : Tri := Fin.ofNat' 3 (i.val/3)

theorem onto : Function.Surjective tag := by decide
theorem three_each : ∀ r : Tri, (Finset.univ.filter (fun j => tag j=r)).card=3 := by decide

/-- Two equitable partitions into triples with constant sizes of their
nonempty joint classes coincide as partitions if some two blocks are disjoint. -/
theorem same (f : V → Tri) (three : ∀ t, (Finset.univ.filter fun i => f i=t).card=3)
    (joint : ∀ j, (Finset.univ.filter (fun i => tag j=tag i ∧ f j=f i)).card=
      (Finset.univ.filter (fun i => tag 0=tag i ∧ f 0=f i)).card)
    (missing : ∃ k l, ∀ j, tag j=k → f j≠l) : ∀ j k, tag j=tag k → f j=f k := by
  exact (by native_decide : ∀ g : V → Tri, (∀ t, (Finset.univ.filter fun i => g i=t).card=3) →
    (∀ j, (Finset.univ.filter (fun i => tag j=tag i ∧ g j=g i)).card=
      (Finset.univ.filter (fun i => tag 0=tag i ∧ g 0=g i)).card) →
    (∃ k l, ∀ j, tag j=k → g j≠l) → ∀ j k, tag j=tag k → g j=g k) f three joint missing

variable {n : Nat} {c : Fin n → Fin n → Nat} {a s : Nat}
abbrev cells (A : Shore c a V) (Y : Shore c s V) (i j : V) := c (atPoint A i) (atPoint Y j)

private theorem class_block (law : Laws c c) (A : Shore c a V) (Y : Shore c s V) (v : Nat)
    (l r : V → Tri) (onto : Function.Surjective l) (hit : ∀ i j, cells A Y i j=v ↔ l i=r j) :
    Block Y Y Y Y (fun j k => decide (r j=r k)) (fun j k => decide (r j=r k)) := by
  have B := Block.map (Block.names (L:=A) (L':=A) (R:=Y) (R':=Y)) (fun t => decide (t=v))
  have gram := Block.gram law (Block.flip law B)
  have nonempty (j k : V) : 0 < Block.overlap (fun x i => decide (cells A Y i x=v)) j k ↔ r j=r k := by
    unfold Block.overlap; rw [Finset.card_pos]
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨x,y⟩ := (Finset.mem_filter.mp hi).2
      exact ((hit _ _).mp (of_decide_eq_true x)).symm.trans ((hit _ _).mp (of_decide_eq_true y))
    · intro eq
      obtain ⟨i,hi⟩ := onto (r j)
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true ((hit _ _).mpr hi),
        decide_eq_true ((hit _ _).mpr (hi.trans eq))⟩⟩
  intro j k y z eq
  exact Bool.decide_congr ((nonempty j k).symm.trans
    ((show 0 < Block.overlap (fun x i => decide (cells A Y i x=v)) j k ↔
      0 < Block.overlap (fun x i => decide (cells A Y i x=v)) y z by rw [gram eq]).trans (nonempty y z)))

/-- In a coherent configuration two disjoint cross colors, each consisting
of three complete squares, have the same column partition. -/
theorem compatible (law : Laws c c) (A : Shore c a V) (Y : Shore c s V) {u v : Nat}
    (different : u≠v) (mark : ∀ i j, cells A Y i j=u ↔ tag i=tag j)
    (l r : V → Tri) (onto : Function.Surjective l)
    (three : ∀ t, (Finset.univ.filter fun i => r i=t).card=3)
    (other : ∀ i j, cells A Y i j=v ↔ l i=r j) : ∀ j k, tag j=tag k → r j=r k := by
  have L := class_block law A Y u tag tag Partition.onto mark
  have R := class_block law A Y v l r onto other
  have inter := Block.map₂ L R (fun p q => p && q)
  apply same r three
  · intro j
    have h := Block.degree_eq law inter j 0
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using h
  · refine ⟨tag 0,l 0,fun j h eq => different ?_⟩
    exact ((mark 0 j).mpr h.symm).symm.trans ((other 0 j).mpr eq.symm)

end QGI.NineNine.Partition
