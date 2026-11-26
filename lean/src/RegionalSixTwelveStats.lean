import RegionalSixTwelveGeometry
import SixTenCoordinates

namespace QGI.Coherent.RegionalSixTwelveStats
open SixTenCoordinates
open RegionalSixTwelveGeometry (Point Family)

abbrev Right := Fin 12
abbrev Cell := RegionalSixTwelveGeometry.Block

variable {m : Nat}

def support (b : Fin m → Cell) : Family := Finset.univ.image b
def mu (b : Fin m → Cell) (s : Cell) := (Finset.univ.filter fun j => b j=s).card

theorem weighted (b : Fin m → Cell) (copies : Nat) (uniform : ∀ j, mu b (b j)=copies) (φ : Cell → Nat) :
    ∑ j, φ (b j)=copies*∑ s∈support b, φ s := by
  have full : ∀ j∈(Finset.univ : Finset (Fin m)), b j∈support b := fun j _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [←Finset.sum_fiberwise_of_maps_to full (fun j => φ (b j)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
  calc
    _ = ∑ _k ∈ (Finset.univ.filter fun k => b k=b j), φ (b j) := Finset.sum_congr rfl
      (fun k hk => congrArg φ (Finset.mem_filter.mp hk).2)
    _ = copies*φ (b j) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      exact congrArg (·*φ (b j)) (uniform j)

def family {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Point) (Y : Shore c r (Fin m)) (v : Nat) (j : (Fin m)) : Cell :=
  Finset.univ.filter fun i => c (atPoint Y j) (atPoint F i)=v

def color {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Point) (Y : Shore c r (Fin m)) (j : (Fin m)) (i : Point) :=
  c (atPoint Y j) (atPoint F i)

theorem incidence {n l r : Nat} {c d : Fin n → Fin n → Nat}
    (F : Shore c l Point) (Y : Shore c r (Fin m)) (T : Shore d l Point) (Z : Shore d r (Fin m)) (v : Nat) :
    Block Y Z F T (fun j i => decide (i∈family F Y v j)) (fun j i => decide (i∈family T Z v j)) := by
  intro i j x y eq
  simp only [family,Finset.mem_filter,Finset.mem_univ,true_and,eq]

private theorem gram_sets (b : Fin m → Cell) (i j) :
    Block.overlap (fun j i => decide (i∈b j)) i j=(b i∩b j).card := by
  unfold Block.overlap
  congr 1
  ext s
  simp

private theorem full_inter (a b : Cell) (same : a.card=b.card) : (a∩b).card=a.card ↔ a=b := by
  constructor
  · intro h
    have left := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁:=a) (s₂:=b)) h.ge
    have right := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁:=a) (s₂:=b)) (h.trans same).ge
    exact left.symm.trans right
  · rintro rfl; simp

theorem overlap_names {n l r : Nat} {c d : Fin n → Fin n → Nat}
    (law : Laws c d) (F : Shore c l Point) (Y : Shore c r (Fin m)) (T : Shore d l Point) (Z : Shore d r (Fin m)) (v : Nat) :
    Block Y Z Y Z (fun i j => (family F Y v i∩family F Y v j).card) (fun x y => (family T Z v x∩family T Z v y).card) := by
  intro i j x y h
  simpa only [gram_sets] using Block.gram law (incidence F Y T Z v) h

theorem statistics {n l r : Nat} [NeZero m] {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r (Fin m)) (v : Nat) :
    let b := family F Y v
    (∀ j, (b j).card=(b 0).card) ∧ (∀ j, mu b (b j)=mu b (b 0)) ∧ (support b).card∣m ∧
      RegionalSixTwelveGeometry.Regular (support b) := by
  let b := family F Y v
  let a := fun j i => decide (i∈b j)
  have inc : Block Y Y F F a a := incidence F Y F Y v
  have weights (j) : (b j).card=(b 0).card := by simpa [a] using Block.degree_eq law inc j 0
  have gram := overlap_names law F Y F Y v
  have eq (j t) : (b j∩b t).card=(b 0).card ↔ b t=b j := by
    rw [←weights j,full_inter _ _ ((weights j).trans (weights t).symm),eq_comm]
  have freq (j) : mu b (b j)=mu b (b 0) := by
    have h := Block.hist_eq law gram j 0 (b 0).card
    change (Finset.univ.filter (fun t => (b j∩b t).card=(b 0).card)).card=
      (Finset.univ.filter (fun t => (b 0∩b t).card=(b 0).card)).card at h
    simpa only [mu,eq] using h
  have mpos : 0 < mu b (b 0) := Finset.card_pos.mpr ⟨(0:(Fin m)),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have total := weighted b _ freq (fun _ => 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at total
  refine ⟨weights,freq,⟨mu b (b 0),total.trans (Nat.mul_comm ..)⟩,fun i => ?_⟩
  have count (i) : ∑ j, (if i∈b j then 1 else 0)=mu b (b 0)*RegionalSixTwelveGeometry.degree (support b) i := by
    simpa only [RegionalSixTwelveGeometry.degree,Finset.sum_boole] using weighted b _ freq (fun s => if i∈s then 1 else 0)
  apply Nat.eq_of_mul_eq_mul_left mpos
  rw [←count,←count,Finset.sum_boole,Finset.sum_boole]
  simpa only [a,decide_eq_true_eq] using Block.degree_eq law (Block.flip law inc) i 0

theorem half_values {n l r : Nat} [NeZero m] {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r (Fin m)) {v w : Nat} (vw : v≠w)
    (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w) :
    RegionalSixTwelveGeometry.TwoValues (support (family F Y v)) := by
  let b := family F Y v
  let a := fun j i => decide (i∈b j)
  have inc : Block Y Y F F a a := incidence F Y F Y v
  have gram := overlap_names law F Y F Y v
  have fold := Block.fold law gram inc (fun x z => if z=true then x else 0)
  have freq := (statistics law F Y v).2.1
  have mpos : 0 < mu b (b 0) := Finset.card_pos.mpr ⟨(0:(Fin m)),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have times (j i) : ∑ t, (if i∈b t then (b j∩b t).card else 0)=
      mu b (b 0)*RegionalSixTwelveGeometry.cubic (support b) i (b j) :=
    weighted b _ freq (fun s => if i∈s then (b j∩s).card else 0)
  intro s hs t ht i x agree
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ht
  have equal : color F Y j i=color F Y k x := by
    by_cases hi : color F Y j i=v
    · exact hi.trans ((Finset.mem_filter.mp (agree.mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))).2.symm)
    · have hx : color F Y k x≠v := fun h => hi (Finset.mem_filter.mp (agree.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))).2
      exact ((two j i).resolve_left hi).trans ((two k x).resolve_left hx).symm
  apply Nat.eq_of_mul_eq_mul_left mpos
  change mu b (b 0)*RegionalSixTwelveGeometry.cubic (support b) i (b j)=mu b (b 0)*RegionalSixTwelveGeometry.cubic (support b) x (b k)
  rw [←times,←times]
  simpa only [a,decide_eq_true_eq] using fold equal

end QGI.Coherent.RegionalSixTwelveStats

