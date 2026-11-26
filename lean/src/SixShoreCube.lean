import SixShoreAtlas

namespace QGI.SixShoreCube
open SixShoreAtlas
abbrev W := Fin 9
abbrev Motion := Fin 48
def axes : Fin 6 → Fin 3 → Fin 3 := ![![0,1,2],![0,2,1],![1,0,2],![1,2,0],![2,0,1],![2,1,0]]
def move (g : Motion) (i : Point) : Point :=
  let j := axes (Fin.ofNat' 6 (g.val/8)) (Fin.ofNat' 3 (i.val/2))
  let b := i.val.testBit 0 ^^ g.val.testBit (i.val/2)
  Fin.ofNat' 6 (2*j.val+b.toNat)
def fits (g : Motion) (s t : W) := decide (∀ i, mask s i=mask t (move g i))
def meet (s t : W) := (subsets s∩subsets t).card
private def test : List W → List (W×W) → List Motion → Bool
  | [],_,gs => !gs.isEmpty
  | x::xs,pairs,gs => test xs pairs gs && (List.finRange 9).all (fun y =>
      if meet x x=meet y y ∧ ∀ e∈pairs, meet x e.1=meet y e.2 then
        test xs ((x,y)::pairs) (gs.filter (fun g => fits g x y)) else true)

private theorem tested : test (List.finRange 9) [] (List.finRange 48)=true := by native_decide
private theorem eq_meet : ∀ x y : W, meet x y=meet x x → meet y y=meet x x → y=x := by native_decide
theorem bijective : ∀ g : Motion, Function.Injective (move g) := by unfold Function.Injective; native_decide
theorem internal : ∀ a : Key, hard a → ∀ g : Motion, ∀ i j : Point, cell a i j=cell a (move g i) (move g j) ∨
    cell a j i=cell a (move g i) (move g j) := by native_decide

/-- A common intersection matrix of selected half-cube columns, with the full column allowed, determines a signed coordinate permutation on the six points. -/
theorem extend {X : Type*} (a b : X → W) (gram : ∀ i j, meet (a i) (a j)=meet (b i) (b j)) :
    ∃ g : Motion, ∀ i, fits g (a i) (b i)=true := by
  classical
  have go (rows : List W) (pairs : List (W×W)) (gs : List Motion)
      (real : ∀ e∈pairs, ∃ j, a j=e.1 ∧ b j=e.2)
      (ok : test rows pairs gs=true) : ∃ g∈gs, ∀ i, a i∈rows → fits g (a i) (b i)=true := by
    induction rows generalizing pairs gs with
    | nil =>
      cases gs with
      | nil => contradiction
      | cons g gs => exact ⟨g,List.mem_cons_self,by simp⟩
    | cons x xs ih =>
      simp only [test,Bool.and_eq_true] at ok
      obtain ⟨skip,next⟩ := ok
      by_cases hit : ∃ i, a i=x
      · obtain ⟨i,hi⟩ := hit
        have cond : meet x x=meet (b i) (b i) ∧ ∀ e∈pairs, meet x e.1=meet (b i) e.2 := by
          refine ⟨hi ▸ gram i i,fun e he => ?_⟩
          obtain ⟨j,hj,hb⟩ := real e he
          rw [←hi,←hj,←hb]; exact gram i j
        have atI := List.all_eq_true.mp next (b i) (List.mem_finRange _)
        simp only [if_pos cond] at atI
        obtain ⟨g,hg,rest⟩ := ih ((x,b i)::pairs) _ (by
          intro e he; rcases List.mem_cons.mp he with rfl|he
          · exact ⟨i,hi,rfl⟩
          · exact real e he) atI
        obtain ⟨ing,hg⟩ := List.mem_filter.mp hg
        refine ⟨g,ing,fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with h|h
        · have eq : b j=b i := eq_meet (b i) (b j) (by rw [←gram,←gram,hi,h]) (by rw [←gram,←gram,hi,h])
          rw [h,eq]; exact hg
        · exact rest _ h
      · obtain ⟨g,hg,rest⟩ := ih pairs gs real skip
        exact ⟨g,hg,fun i hi => rest i ((List.mem_cons.mp hi).resolve_left (fun h => hit ⟨i,h⟩))⟩
  obtain ⟨g,_,hg⟩ := go (List.finRange 9) [] (List.finRange 48) (by simp) tested
  exact ⟨g,fun i => hg i (List.mem_finRange _)⟩
end QGI.SixShoreCube
