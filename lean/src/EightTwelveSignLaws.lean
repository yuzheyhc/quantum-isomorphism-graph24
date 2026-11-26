import EightTwelveSignGeometry
import EightTwelveSignRows

noncomputable section
namespace QGI.Coherent.EightTwelveSignLaws
open EightTwelveSigns SixTenCoordinates RegionalEightTwelveStats
open EightTwelveHalf (P C)
open RegionalEightTwelveHalfLaws (rowCells crossGram)
open EightTwelveSignGeometry (zero_iff_complement)

private theorem occurs : ∀ (a : Key) (i j : J), ∃ k, rightName a i k=rightName a 0 j := by native_decide

theorem pairing {a : Key} {f : J → C} (weight : ∀ j, (f j).card=4)
    (inj : Function.Injective f) (opp : ∀ j, ∃ k, f k=(f j)ᶜ)
    (block : ∀ j k x y, rightName a j k=rightName a x y → (f j∩f k).card=(f x∩f y).card) :
    ∃ o : Pairing, atlas o=a ∧ ∀ i, f (point o i false)=(f (point o i true))ᶜ := by
  obtain ⟨z,oz⟩ := opp 0
  let c := rightName a 0 z
  have forces {j k} (eq : rightName a j k=c) : f k=(f j)ᶜ :=
    (zero_iff_complement (weight j) (weight k)).mp ((block j k 0 z eq).trans ((zero_iff_complement (weight 0) (weight z)).mpr oz))
  have iff' (j k) : rightName a j k=c ↔ f k=(f j)ᶜ := by
    refine ⟨forces,fun h => ?_⟩
    obtain ⟨u,hu⟩ := occurs a j z
    have uk : u=k := inj ((forces hu).trans h.symm)
    exact uk ▸ hu
  have matching : Matching a c := by
    refine ⟨?_,?_,?_⟩
    · intro j h
      have hz := (zero_iff_complement (weight j) (weight j)).mpr (forces h)
      rw [Finset.inter_self,weight] at hz
      omega
    · intro j k h; apply (iff' k j).mpr; rw [forces h,compl_compl]
    · intro j; obtain ⟨k,hk⟩ := opp j
      exact ⟨k,(iff' j k).mpr hk,fun y hy => inj ((forces hy).trans hk.symm)⟩
  obtain ⟨o,ka,tagged⟩ := findPairing a z matching
  refine ⟨o,ka,fun i => ?_⟩
  have eq := (coordinates o).2 i
  rw [ka,tagged] at eq
  rw [forces eq,compl_compl]

theorem row_gram (f : J → C) (i j : P) :
    (rowCells f i∩rowCells f j).card=crossGram f i j := by
  unfold crossGram
  congr 1; ext t; simp [rowCells]

theorem row_weight (f : J → C) (i : P) : (rowCells f i).card=crossGram f i i := by
  simpa only [Finset.inter_self] using row_gram f i i

theorem split_rows {o : Pairing} {f : J → C} (split : ∀ i, f (point o i false)=(f (point o i true))ᶜ) (i : P) (a : Axis) :
    point o a false∈rowCells f i ↔ point o a true∉rowCells f i := by simp [rowCells,split]

variable {n l r v w : Nat} {c : Fin n → Fin n → Nat}
    (law : Laws c c) (F : Shore c l P) (Y : Shore c r J)

include law in
theorem uniform {o : Pairing} (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w)
    (names : ∀ i j x y, c (atPoint Y i) (atPoint Y j)=c (atPoint Y x) (atPoint Y y) →
      rightName (atlas o) i j=rightName (atlas o) x y) : Uniform o (rowCells (family F Y v)) := by
  let f := family F Y v
  intro i t j k hits
  have cross : c (atPoint Y j) (atPoint F i)=c (atPoint Y k) (atPoint F t) := by
    apply (RegionalEightTwelveHalfModels.both_colors (two j i) (two k t)).mpr
    simpa only [rowCells,family,Finset.mem_filter,Finset.mem_univ,true_and,color] using hits
  have named : Block Y Y Y Y (rightName (atlas o)) (rightName (atlas o)) :=
    fun ⦃j k x y⦄ h => names _ _ _ _ h
  unfold sig
  apply List.map_congr_left
  intro z _
  let u := rightName (atlas o) 0 z
  have d := Block.fold law named (incidence F Y F Y v) (fun x y => if x=u ∧ y=true then 1 else 0) cross
  have read (j : J) (i : P) : (Finset.univ.filter (fun z => rightName (atlas o) j z=u ∧ i∈f z)).card =
      ((rowCells f i).filter (fun z => rightName (atlas o) j z=u)).card := by
    congr 1; ext z; simp [rowCells,and_comm]
  change ((rowCells f i).filter (fun z => rightName (atlas o) j z=u)).card=((rowCells f t).filter (fun z => rightName (atlas o) k z=u)).card
  rw [←read j i,←read k t]
  simpa only [decide_eq_true_eq,Finset.sum_boole] using d

end QGI.Coherent.EightTwelveSignLaws
