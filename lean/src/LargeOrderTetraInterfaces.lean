import LargeOrderSquareInterface
import LargeOrderFourSixGlue

noncomputable section
namespace QGI.Coherent.LargeOrderTetraInterfaces
open SixTenCoordinates LargeOrderSquareInterface LargeOrderStrongPaths
open FourSixSix (E)
open FourSixSix.Interfaces (flag)
open private maskVal edgeDegree pairGram rowCheck from FourSixSixComplete

def raw {n l r : Nat} {X Y : Type} {c : Fin n → Fin n → Nat} (F : Shore c l X) (S : Shore c r Y)
    (i : X) (j : Y) := c (atPoint F i) (atPoint S j)

def dot (i j : E) : Nat := ∑ k : I, if flag k i=true ∧ flag k j=true then 1 else 0

private theorem four_columns : ∀ e : I → E, (∀ i : I, FiberRectangles.degree (fun j => flag i (e j))=2) →
    ¬∀ a : E, (∑ j : I, dot a (e j)*dot a (e j))=∑ j : I, dot 0 (e j)*dot 0 (e j) := by native_decide

variable {n l r v s : Nat} {c : Fin n → Fin n → Nat}

/-- A second nonconstant four-by-four interface would require all six edge
multiplicities to agree on its four columns. -/
theorem uniform_four (law : Laws c c) (F : Shore c l I) (Y : Shore c v E) (S : Shore c r I)
    (inc : Shape F Y flag) (no : ¬Pin F S) : ∀ i j, raw F S i j=raw F S 0 0 := by
  classical
  by_contra h
  obtain ⟨B,_,row,col,same⟩ := binary law F S no h
  obtain ⟨e,he⟩ := FourSixSix.Interfaces.columnChoice col
  have bits : Block F F S S (fun i j => flag i (e j)) (fun i j => flag i (e j)) :=
    fun ⦃i j x y⦄ h => (he i j).symm.trans (((same i j x y).mpr h).trans (he x y))
  have product : Block Y Y S S (fun i j => dot i (e j)) (fun i j => dot i (e j)) :=
    Block.fold law (Block.flip law inc) bits (fun a b => if a=true ∧ b=true then 1 else 0)
  exact four_columns e (fun i => (congrArg FiberRectangles.degree (funext (he i))).symm.trans (row i)) (fun a =>
    Block.diag (Block.fold law product (Block.flip law product) (· * ·)) a 0)

/-- Tetrahedral incidence on both sides of a four-point fiber gives a
unique partner for each edge on the two six-point shores. -/
theorem dual_tetra (law : Laws c c) (F : Shore c l I) (Y : Shore c v E) (Z : Shore c s E)
    (left : Shape F Y flag) (right : Shape F Z flag) : MapsOne c v s := by
  have prod : Block Y Y Z Z dot dot := Block.fold law (Block.flip law left) right
    (fun a b => if a=true ∧ b=true then 1 else 0)
  have one : ∀ k : E, dot 0 k=dot 0 0 → k=0 := by decide
  refine ⟨atPoint Y 0,atPoint Z 0,(Y 0).property,(Z 0).property,fun z eq => ?_⟩
  let k := Z.symm ⟨z,(law.last eq).trans (Z 0).property⟩
  have hk : atPoint Z k=z := congrArg Subtype.val (Z.apply_symm_apply _)
  exact hk.symm.trans (congrArg (atPoint Z) (one k (prod (by rw [hk]; exact eq))))

/-- When the four-point shore is uniform towards a further fiber, the
interactions of its six tetrahedral edges are determined by two anchors. -/
theorem anchored_rows {m : Nat} (law : Laws c c) (F : Shore c l I) (Y : Shore c v E) (Z : Shore c s (Fin m))
    (inc : Shape F Y flag) (uniform : ∀ i j, raw F Z i j=raw F Z 0 j)
    (i x : E) (j : Fin m) (ha : raw Y Y 0 i=raw Y Y 0 x) (hb : raw Y Y 1 i=raw Y Y 1 x) :
    raw Y Z i j=raw Y Z x j := by
  let a := raw Y Z i j
  let bit (i j) := decide (raw Y Z i j=a)
  have bits : Block Y Y Z Z bit bit := fun ⦃_ _ _ _⦄ h => congrArg (fun n => decide (n=a)) h
  have gram : Block Y Y Y Y pairGram pairGram := Block.gram law (Block.flip law inc)
  have mixed := Block.fold law inc bits (fun b d => if b=true ∧ d=true then 1 else 0)
  let m := QGI.SixTen.Cross.encode (fun x : E => bit x j)
  have val (x : E) : maskVal m x=bit x j := QGI.SixTen.Cross.decode _ _
  have deg (i : I) : edgeDegree m i=edgeDegree m 0 := by
    simpa only [edgeDegree,val] using mixed (uniform i j)
  have eq := (val i).symm.trans ((rowCheck m (List.mem_range.mpr (QGI.SixTen.Cross.encode_lt _))
    i x (gram ha) (gram hb) deg).trans (val x))
  exact (of_decide_eq_true (eq.symm.trans (decide_eq_true rfl))).symm

end QGI.Coherent.LargeOrderTetraInterfaces
