import RegionalEightTwelveGeometry
import SixTenCoordinates

namespace QGI.Coherent.RegionalEightTwelveStats
open SixTenCoordinates RegionalEightTwelveGeometry

def family {n l r : Nat} {c : Fin n → Fin n → Nat}
    (F : Shore c l Point) (Y : Shore c r Index) (v : Nat) (j : Index) : Cell :=
  Finset.univ.filter fun i => c (atPoint Y j) (atPoint F i)=v

def color {n l r : Nat} {c : Fin n → Fin n → Nat}
    (F : Shore c l Point) (Y : Shore c r Index) (j : Index) (i : Point) := c (atPoint Y j) (atPoint F i)

theorem incidence {n l r : Nat} {c d : Fin n → Fin n → Nat}
    (F : Shore c l Point) (Y : Shore c r Index) (T : Shore d l Point) (Z : Shore d r Index) (v : Nat) :
    Block Y Z F T (fun j i => decide (i∈family F Y v j)) (fun j i => decide (i∈family T Z v j)) := by
  intro i j x y eq
  simp only [family,Finset.mem_filter,Finset.mem_univ,true_and,eq]

theorem mixed_counts {n l r : Nat} {c d : Fin n → Fin n → Nat} (law : Laws c d)
    (F : Shore c l Point) (Y : Shore c r Index) (T : Shore d l Point) (Z : Shore d r Index)
    (v w : Nat) {i j x y : Index} (hit : c (atPoint Y i) (atPoint Y j)=d (atPoint Z x) (atPoint Z y)) :
    (family F Y v i ∩ family F Y w j).card=(family T Z v x ∩ family T Z w y).card := by
  have h := Block.fold law (incidence F Y T Z v) (Block.flip law (incidence F Y T Z w))
    (fun a b => if a=true ∧ b=true then 1 else 0) hit
  simpa only [decide_eq_true_eq,Finset.sum_boole,←Finset.mem_inter,Finset.filter_mem_eq_inter,Finset.univ_inter] using h

theorem degrees {n l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r Index) (v : Nat) :
    let a := family F Y v
    (∀ j, (a j).card=(a 0).card) ∧ (∀ i, (incident a i).card=(incident a 0).card) ∧
      12*(a 0).card=8*(incident a 0).card := by
  let a := family F Y v
  have block := incidence F Y F Y v
  have cols (j) : (a j).card=(a 0).card := by simpa [a] using Block.degree_eq law block j 0
  have rows (i) : (incident a i).card=(incident a 0).card := by
    simpa [incident,a] using Block.degree_eq law (Block.flip law block) i 0
  have each (i) : (incident a i).card=∑ j, if i∈a j then 1 else 0 := by simp [incident]
  have count : ∑ i : Point, (incident a i).card=∑ j, (a j).card := by
    simp_rw [each]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; simp
  refine ⟨cols,rows,?_⟩
  simpa only [cols,rows,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using count.symm

def copies (a : Index → Cell) (j : Index) := (Finset.univ.filter (fun k => a k=a j)).card

theorem uniform_copies {n l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r Index) (v : Nat) : ∀ j, copies (family F Y v) j=copies (family F Y v) 0 := by
  let a := family F Y v
  have weights := (degrees law F Y v).1
  have eq (j k) : (a j∩a k).card=(a 0).card ↔ a k=a j := by
    constructor
    · intro h
      exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (h.trans (weights k).symm).ge).symm.trans
        (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (h.trans (weights j).symm).ge)
    · intro h
      rw [h,Finset.inter_self]
      exact weights j
  have gram : Block Y Y Y Y (fun i j => (a i∩a j).card) (fun i j => (a i∩a j).card) :=
    fun _ _ _ _ hit => mixed_counts law F Y F Y v v hit
  intro j
  have hist := Block.hist_eq law gram j 0 (a 0).card
  change (Finset.univ.filter (fun k => (a j∩a k).card=(a 0).card)).card=
    (Finset.univ.filter (fun k => (a 0∩a k).card=(a 0).card)).card at hist
  simpa only [copies,eq] using hist

end QGI.Coherent.RegionalEightTwelveStats

