import RegionalTenTwelve
import SixTenCrossNormal
import OddShoreAttachment

noncomputable section
namespace QGI.Coherent.SixSixTenInterfaces
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws BinaryShore
open FourTwelveFunctional (source)
open TenTwelveCatalog (left leftBank pool Simple)
open private simple_twins from RegionalTenTwelve
open private listed left_complete from TenTwelveCatalog
abbrev S := Fin 6
abbrev T := Fin 10
def allowed (a : TenPointCross.Key) (s : Cell 10) := (leftBank a s).filter (fun t => decide (Admits (left a) 3 t))
private theorem twice {m : BinaryShore.Table 10} {s : Cell 10} (h : Admits m 3 s) : Admits m 6 s := by
  refine ⟨h.1,fun i => ?_⟩
  obtain ⟨q,hq⟩ := h.2 i
  refine ⟨2*q,?_⟩
  calc 6*_ = 2*(3*count m s (first s) (m 0 i)) := by omega
       _ = _ := by rw [hq]; ring
set_option maxRecDepth 20000 in
private theorem census : ∀ a : TenPointCross.Key, (pool BinaryShoreMasks.masks10x12 a.val).all
    (fun s => decide (Admits (left a) 3 s → Simple (allowed a s) s ∨ a=2))=true := by native_decide

variable {n l r : Nat} {G : Graph n}
abbrev rect (F : Shore (source G) l T) (A : Shore (source G) r S) (i : T) (j : S) := source G (atPoint F i) (atPoint A j)
theorem shape (F : Shore (source G) l T) (A : Shore (source G) r S) (a : TenPointCross.Key)
    (ca : TenPointCrossLaws.Chart F a) :
    SplitRectangle.Twins (rect F A) ∨ a=2 ∧ ∀ i x, (∀ j, rect F A j i=rect F A j x) → i=x := by
  classical
  let f := rect F A
  rcases OddHalfPartition.palette (p:=3) (sourceLaws _) F A (by intro x y pos eq; omega) with ⟨v,h⟩|⟨v,w,_,two,wt⟩
  · exact Or.inl ⟨fun i x _ _ j => (h i j).trans (h x j).symm,fun _ j z _ i => (h i j).trans (h i z).symm⟩
  let B := fun i j => decide (f i j=v)
  let R := fun j i => B i j
  have bits : Block F F A A B B := fun ⦃_ _ _ _⦄ e => congrArg (fun u => decide (u=v)) e
  have rows (i) : degree B i=3 := by simpa only [degree,B,f,rect,decide_eq_true_eq] using wt i
  have rev := Block.flip (sourceLaws _) bits
  have eqrows := Block.degree_eq (sourceLaws _) rev
  have balance := FiberRectangles.balance B rows (fun j => eqrows j 0)
  have cols (j) : (support B j).card=5 := (eqrows j 0).trans (by omega)
  have H : BinaryShore.Chart (b:=3) (d:=5) F A B (left a) :=
    ⟨sourceLaws _,bits,fun i j x y eq => (RegionalEightTwelveHalfModels.both_colors (two i j) (two x y)).mpr
      (by simpa only [B,decide_eq_decide] using eq),fun i j x y => (ca i j x y).symm,rows,cols⟩
  obtain ⟨ok,pro⟩ := necessary H (by decide) (by decide)
  have mem (j : S) : support B j∈allowed a (support B 0) := List.mem_filter.mpr
    ⟨TenTwelveCatalog.inLeft a (cols j) (twice (ok j)) (pro j 0),decide_eq_true (ok j)⟩
  have seed := listed _ (cols 0) (twice (ok 0)) (left_complete a)
  rcases (of_decide_eq_true (List.all_eq_true.mp (census a) _ seed)) (ok 0) with simp|key
  · exact Or.inl (simple_twins f two _ (fun j => simp _ (mem j)))
  have histL (i u : S) (k : Nat) := Block.degree_eq (sourceLaws _)
    (Block.map (Block.gram (sourceLaws _) rev) (fun z => decide (z=k))) i u
  have histR (j u : T) (k : Nat) := Block.degree_eq (sourceLaws _)
    (Block.map (Block.gram (sourceLaws _) bits) (fun z => decide (z=k))) j u
  obtain ⟨e,g,map⟩ := SixTen.Cross.normal R cols rows (fun i u k => by simpa only [decide_eq_true_eq] using histL i u k)
    (fun j u k => by simpa only [decide_eq_true_eq] using histR j u k)
  rcases map with split|design
  · let ls (i : T) := decide ((g i).val<5)
    let rs (j : S) := decide ((e j).val<3)
    have mark (i j) : f i j=v ↔ ls i=rs j := by
      have h := split j i
      change decide (f i j=v)=decide (((e j).val<3) ↔ ((g i).val<5)) at h
      calc f i j=v ↔ decide (f i j=v)=true := by simp
           _ ↔ ls i=rs j := by rw [h]; simp only [ls,rs,decide_eq_true_eq,decide_eq_decide]; tauto
    have model : f=fun i j => if ls i=rs j then v else w := by
      funext i j; by_cases h : ls i=rs j
      · rw [if_pos h]; exact (mark i j).mpr h
      · rw [if_neg h]; exact (two i j).resolve_left (mt (mark i j).mp h)
    apply Or.inl; change SplitRectangle.Twins f; rw [model]
    exact SplitRectangle.twins_of_halves ls rs v w
  · refine Or.inr ⟨key,fun i x same => e.injective ?_⟩
    apply (show ∀ i x : S, (∀ j : T, SixTen.Cross.design i j=SixTen.Cross.design x j) → i=x by decide)
    intro j; obtain ⟨z,rfl⟩ := g.surjective j
    rw [←design,←design]
    exact congrArg (fun t => decide (t=v)) (same z)
end QGI.Coherent.SixSixTenInterfaces
