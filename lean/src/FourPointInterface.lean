import FourEightGeometry

namespace QGI.Coherent.FourPointInterface
open FourTwelveCycle FourTwelveTypes

/-- The squared Gram diagonal for columns that are pairs on a four-point fiber. -/
def gramDiagonal {m : Nat} (b : Fin m → Edge) (j : Fin m) : Nat :=
  ∑ k, overlap (b j) (b k) ^ 2

private theorem two_pairs : ∀ e f : Edge,
    overlap e f ^ 2 + (if f = opposite e then 1 else 0) =
      1 + 3 * (if f = e then 1 else 0) := by decide

/-- Row regularity alone gives the identity for every column count. -/
theorem gramDiagonal_eq {m : Nat} (b : Fin m → Edge)
    (rows : ∀ i, degree b i = degree b 0) (j : Fin m) :
    gramDiagonal b j = m + 2 * mult b (b j) := by
  have eq := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ)
    (fun k _ => two_pairs (b j) (b k))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at eq
  change gramDiagonal b j + mult b (opposite (b j)) = m + 3 * mult b (b j) at eq
  rw [← opposite_mult b rows (b j)] at eq
  omega

theorem equal_multiplicities {m : Nat} (b : Fin m → Edge)
    (rows : ∀ i, degree b i = degree b 0) (diagonal : ∀ j k, gramDiagonal b j = gramDiagonal b k)
    (j k : Fin m) : mult b (b j) = mult b (b k) := by
  have eq := diagonal j k
  rw [gramDiagonal_eq b rows,gramDiagonal_eq b rows] at eq
  omega

/-- In particular the two-neighbor branch of either 4-by-8 interface
in a 4+8+8 configuration is a repeated matching or a doubled cycle. -/
theorem eight_columns (b : Fin 8 → Edge) (rows : ∀ i, degree b i = degree b 0)
    (diagonal : ∀ j k, gramDiagonal b j = gramDiagonal b k) :
    (∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ Nonempty (FourEightGeometry.RepeatedCycle b) :=
  FourEightGeometry.normalize b rows (equal_multiplicities b rows diagonal)

end QGI.Coherent.FourPointInterface

namespace QGI.Coherent.FourPointInterface
open FourTwelveCycle FourTwelveTypes StrategyColorLaws
open private gram_entry from FourTwelveCycle

/-- A relation from one whole fiber to pairs in a four-point fiber,
with their labels in the original coherent configuration. -/
structure PairColumns {n m : Nat} [NeZero m] (C : CoherentAlgebra n) (v : Nat)
    (F : Fin 4 ↪ Fin n) (Y : Fin m ↪ Fin n) (b : Fin m → Edge) : Prop where
  left : ∀ i, Relations.color C (F i) (F i) = Relations.color C (F 0) (F 0)
  right : ∀ z, z ∈ Set.range Y ↔ Relations.color C z z = Relations.color C (Y 0) (Y 0)
  cells : ∀ j, neighbors (Relations.color C) v (Y j) = (edge (b j)).map F

theorem of_coherent {n m : Nat} [NeZero m] {C : CoherentAlgebra n} {v : Nat}
    {F : Fin 4 ↪ Fin n} {Y : Fin m ↪ Fin n} {b : Fin m → Edge} (P : PairColumns C v F Y b) :
    (∀ i, degree b i = degree b 0) ∧ (∀ j k, gramDiagonal b j = gramDiagonal b k) := by
  classical
  let c := Relations.color C
  let B := mark c v
  have member : B ∈ C.space := Relations.indicator_mem C v
  have anchor : F (FourTwelveCycle.ends (b 0)).1 ∈ neighbors c v (Y 0) := by
    rw [P.cells]; simp [edge]
  have outside (z : Fin n) (miss : z ∉ Set.range Y) : neighbors c v z = ∅ := by
    apply Finset.eq_empty_of_forall_not_mem
    intro x hx
    have eq := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp anchor).2.symm
    exact miss ((P.right z).mpr (Relations.end_colors C eq).1)
  have rows (i : Fin 4) : (B.conjTranspose * B) (F i) (F i) = (degree b i : ℂ) := by
    classical
    rw [Matrix.mul_apply]
    have shift := Fintype.sum_of_injective Y Y.injective
      (fun j => if i ∈ edge (b j) then (1 : ℂ) else 0)
      (fun z => B.conjTranspose (F i) z * B z (F i)) (by
        intro z hz
        have h : c z (F i) ≠ v := by
          intro h
          have mem : F i ∈ neighbors c v z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
          rw [outside z hz] at mem; exact Finset.not_mem_empty _ mem
        simp [B,mark,h]) (by
        intro j
        have cell : c (Y j) (F i) = v ↔ i ∈ edge (b j) := by
          have eq : F i ∈ neighbors c v (Y j) ↔ i ∈ edge (b j) := by rw [P.cells]; simp
          simpa only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and] using eq
        by_cases inside : i ∈ edge (b j) <;> simp [B,mark,Matrix.conjTranspose_apply,cell,inside])
    rw [←shift]
    simp [degree]
  let K := B * B.conjTranspose
  have kval (x y : Fin n) : K x y = (((neighbors c v x) ∩ (neighbors c v y)).card : ℂ) :=
    gram_entry c v x y
  have diag (j : Fin m) : (K * K) (Y j) (Y j) = (gramDiagonal b j : ℂ) := by
    rw [Matrix.mul_apply]
    have shift := Fintype.sum_of_injective Y Y.injective (fun k => (overlap (b j) (b k) : ℂ)^2)
      (fun z => K (Y j) z * K z (Y j)) (by
        intro z miss; simp [kval,outside z miss]) (by
        intro k
        simp only [kval,c,P.cells,←Finset.map_inter,Finset.card_map,overlap,pow_two,
          Finset.inter_comm (edge (b k)) (edge (b j))])
    rw [←shift]; simp [gramDiagonal]
  have km := C.mul_mem member (C.adjoint_mem member)
  constructor
  · intro i
    have h := (Relations.same C _ _ _ _).mp (P.left i) _ (C.mul_mem (C.adjoint_mem member) member)
    rw [rows,rows] at h; exact_mod_cast h
  · intro j k
    have h := (Relations.same C _ _ _ _).mp
      (((P.right _).mp ⟨j,rfl⟩).trans ((P.right _).mp ⟨k,rfl⟩).symm) _ (C.mul_mem km km)
    change (K*K) (Y j) (Y j) = (K*K) (Y k) (Y k) at h
    rw [diag,diag] at h; exact_mod_cast h

theorem classify_coherent_eight {n : Nat} {C : CoherentAlgebra n} {v : Nat}
    {F : Fin 4 ↪ Fin n} {Y : Fin 8 ↪ Fin n} {b : Fin 8 → Edge} (P : PairColumns C v F Y b) :
    (∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ Nonempty (FourEightGeometry.RepeatedCycle b) :=
  eight_columns b (of_coherent P).1 (of_coherent P).2

end QGI.Coherent.FourPointInterface
