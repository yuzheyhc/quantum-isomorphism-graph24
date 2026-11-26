import SixTwelveAlternatives
import LargeOrderFourFourTwelveGeometry
import SixSixEightPins

noncomputable section
namespace QGI.Coherent.FourSixTwelveParity
open SixTenCoordinates FourTwelveCycle FourTwelveTypes LargeOrderSquareInterface LargeOrderFourFourTwelveGeometry
open RegionalTetraLayout (Face Slot)
open FourTwelveFunctional (source)
open private doubled_degree from RegionalTetraTriples
variable {n l r v a b : Nat} {G : Graph n}

theorem exclude (F : Shore (source G) l I) (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v Twelve)
    (B : Layout F Y) (P : RegionalTetraLayout.Layout S Y a b) (diff : a≠b) (flat : SixSixEightPins.Flat F S) : False := by
  let Z := P.right.trans Y
  let T := P.left.trans S
  let R (i : I) (j : Face × Slot) := decide (source G (atPoint Z j) (atPoint F i)=B.mark)
  let E (j : Face × Slot) (e : Edge) := decide (j.1∈edge e)
  have raw : Block Z Z F F (fun j i => R i j) (fun j i => R i j) :=
    fun ⦃_ _ _ _⦄ eq => congrArg (fun x => decide (x=B.mark)) eq
  have inc : Block Z Z T T E E := by
    intro ⟨q,k⟩ e ⟨u,h⟩ f hit
    change RegionalSixTwelveStats.color S Y (P.right (q,k)) (P.left e)=RegionalSixTwelveStats.color S Y (P.right (u,h)) (P.left f) at hit
    rw [P.names,P.names] at hit
    by_cases he : q∈edge e <;> by_cases hf : u∈edge f <;> simp_all [E]
  let count (i : I) (q : Face) := (Finset.univ.filter (fun k : Slot => R i (q,k)=true)).card
  have expand (i e) : (∑ j : Face × Slot, if R i j=true ∧ E j e=true then 1 else 0)=∑ q∈edge e, count i q := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ q : Face, if q∈edge e then count i q else 0 := Finset.sum_congr rfl (fun q _ => by
        by_cases h : q∈edge e <;> simp [h,E,count])
      _ = _ := by rw [←Finset.sum_filter]; simp
  let c := ∑ q∈edge 0, count 0 q
  have equal (i : I) (e : Edge) : ∑ q∈edge e, count i q=c := by
    have hit : source G (atPoint F i) (atPoint T e)=source G (atPoint F 0) (atPoint T 0) :=
      (flat i (P.left e)).trans (flat 0 (P.left 0)).symm
    have h := Block.fold (sourceLaws _) (Block.flip (sourceLaws _) raw) inc (fun u w => if u=true ∧ w=true then 1 else 0) hit
    exact (expand i e).symm.trans (h.trans (expand 0 0))
  have same (i : I) : count i 0=count 0 0 := by
    have h := doubled_degree (count i) 1 c (fun e _ => equal i e) 0 (by decide)
    have k := doubled_degree (count 0) 1 c (fun e _ => equal 0 e) 0 (by decide)
    omega
  have formula (i : I) : count i 0=(Finset.univ.filter (fun k : Slot => i∈edge (B.col (P.right (0,k))))).card := by
    apply congrArg Finset.card; ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,R,decide_eq_true_eq]
    exact B.cells _ _
  have check : ∀ f : Slot → Edge, ¬ ∀ i : I, (Finset.univ.filter (fun k => i∈edge (f k))).card=
      (Finset.univ.filter (fun k => (0 : I)∈edge (f k))).card := by native_decide
  exact check (fun k => B.col (P.right (0,k))) (fun i => (formula i).symm.trans ((same i).trans (formula 0)))
end QGI.Coherent.FourSixTwelveParity
