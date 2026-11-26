import ElevenBiplane
import SmallUnionRealization

namespace QGI.Coherent.ElevenDesign
open SixTenCoordinates SmallUnion
abbrev V := Fin 11
abbrev M := V → V → Nat
def flat (N : M) := ∀ i j x y, (i=j ↔ x=y) → N i j=N x y
def uniform (T : M) := ∀ i j, T i j=T 0 0
def thin (T : M) := ∃ i j, ∀ z, T i z=T i j → z=j
abbrev bip := ElevenBiplane.Parameters
end QGI.Coherent.ElevenDesign

namespace QGI.Literature
open Coherent.ElevenDesign Coherent.SmallUnion
open Coherent.SixTenCoordinates (Shore atPoint)
/-- Sharafdini and Hirasaka, Theorem 1.1 and Theorem 1.2 with Remark 1.3,
restricted to two distinct fibers of prime size 11. If a nonuniform
rectangle has no matching, its rank and both internal ranks equal two.
The restriction to the union of two fibers is a coherent configuration.
https://arxiv.org/pdf/1309.3725 -/
axiom sharafdini_hirasaka_eleven_ranks {n l r : Nat} {c : Table n} (hc : Configuration c)
    (A : Shore c l V) (Y : Shore c r V) (apart : l≠r)
    (mix : ¬uniform (fun i j => c (atPoint A i) (atPoint Y j)))
    (no : ¬thin (fun i j => c (atPoint A i) (atPoint Y j))) :
    flat (fun i j => c (atPoint A i) (atPoint A j)) ∧ flat (fun i j => c (atPoint Y i) (atPoint Y j)) ∧
    ∃ v w, ∀ i j, c (atPoint A i) (atPoint Y j)=v ∨ c (atPoint A i) (atPoint Y j)=w

/-- Uniqueness of the symmetric (11,5,2) design by rooting at a point
and reconstructing the pentagon family on the five blocks through it. -/
theorem unique_eleven_biplane (A B : V → V → Bool) (ha : bip A) (hb : bip B) :
    ∃ e f : Equiv.Perm V, ∀ i j, A i j=B (e i) (f j) :=
  Coherent.ElevenBiplane.unique_design A B ha hb
end QGI.Literature

namespace QGI.Coherent.ElevenDesign
open SixTenCoordinates
open private degree_as_sum from FiberRectangles

private theorem mass (B : V → V → Bool) (k : Nat) (rd : ∀ i, FiberRectangles.degree (B i)=k)
    (cd : ∀ j, FiberRectangles.degree (fun i => B i j)=k) :
    ∑ j, Block.overlap B 0 j=k*k := by
  classical
  have expand (i j : V) : Block.overlap B i j=∑ z, if B i z then (if B j z then 1 else 0 : Nat) else 0 := by
    change (Finset.univ.filter (fun z => B i z=true ∧ B j z=true)).card=_
    have sum := Finset.sum_boole (α:=Nat) (fun z : V => B i z=true ∧ B j z=true) Finset.univ
    rw [Nat.cast_id] at sum
    rw [←sum]
    apply Finset.sum_congr rfl
    intro z _
    cases B i z <;> cases B j z <;> rfl
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z : V, if B 0 z then k else 0 := Finset.sum_congr rfl (fun z _ => by
      cases h : B 0 z <;> simp only [Bool.false_eq_true,if_false,if_true,Finset.sum_const_zero]
      simpa only [←degree_as_sum] using cd z)
    _ = _ := by
      rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,smul_eq_mul]
      exact congrArg (·*k) (rd 0)

theorem parameters (B : V → V → Bool) {k : Nat} (lo : 2≤k) (hi : k≤5)
    (rd : ∀ i, FiberRectangles.degree (B i)=k) (cd : ∀ j, FiberRectangles.degree (fun i => B i j)=k)
    (constant : ∀ i j, i≠j → Block.overlap B i j=Block.overlap B 0 1) : bip B := by
  classical
  let t := Block.overlap B 0 1
  have eq (j : V) : Block.overlap B 0 j=if j=0 then k else t := by
    split_ifs with h
    · subst j; simpa [Block.overlap,FiberRectangles.degree] using rd 0
    · exact constant _ _ (Ne.symm h)
  have total := mass B k rd cd
  simp_rw [eq] at total
  have others : (Finset.univ.filter (fun j : V => ¬ j=0)).card=10 := by decide
  rw [Finset.sum_ite,Finset.sum_const,Finset.sum_const,others] at total
  have single : (Finset.univ.filter (fun j : V => j=0)).card=1 := by decide
  rw [single] at total
  simp only [one_smul,smul_eq_mul] at total
  have size : k=5 ∧ t=2 := by
    interval_cases k <;> simp_all <;> omega
  exact ⟨fun i => (rd i).trans size.1,fun j => (cd j).trans size.1,fun i j ne => (constant i j ne).trans size.2⟩

end QGI.Coherent.ElevenDesign
