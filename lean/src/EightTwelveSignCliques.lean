import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import data.EightTwelveSignPlacements

namespace QGI.EightTwelveSigns.Cliques
abbrev Word := Fin 64
abbrev Shape := Fin 240
def wordAt (s : Shape) (i : Fin 8) : Word :=
  Fin.ofNat' 64 (((Input.words[s.val]?).getD 0) >>> (6*i.val))
def family (s : Shape) : Finset Word := Finset.univ.image (wordAt s)
def distance (u v : Word) := (Finset.univ.filter (fun i : Fin 6 => u.val.testBit i.val ≠ v.val.testBit i.val)).card
def Adj (u v : Word) := distance u v=3 ∨ distance u v=4
instance (u v : Word) : Decidable (Adj u v) := by unfold Adj; infer_instance
def accept (f : Finset Word) := decide (∃ s : Shape, family s=f)

def search : Nat → Finset Word → List Word → Bool
  | 0, _, _ => false
  | fuel+1, used, pool =>
    if used.card=8 then accept used
    else if used.card+pool.length<8 then true
    else match pool with
      | [] => false
      | x::xs => search fuel used xs && search fuel (insert x used) (xs.filter (fun y => decide (Adj x y)))

private theorem sound {f : Finset Word} (size : f.card=8)
    (clique : ∀ x∈f, ∀ y∈f, x≠y → Adj x y)
    (fuel : Nat) (used : Finset Word) (pool : List Word)
    (sub : used⊆f) (rest : ∀ x∈f, x∉used → x∈pool)
    (ok : search fuel used pool=true) : ∃ s : Shape, family s=f := by
  induction fuel generalizing used pool with
  | zero => contradiction
  | succ fuel ih =>
    unfold search at ok
    split at ok
    next full =>
      have eq := Finset.eq_of_subset_of_card_le sub (by omega)
      exact eq ▸ of_decide_eq_true ok
    next =>
      split at ok
      next small =>
        have incl : f⊆used ∪ pool.toFinset := by
          intro x hx
          by_cases h : x∈used
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (rest x hx h))
        have h := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
        have bound := List.toFinset_card_le pool
        omega
      next =>
        cases pool with
        | nil => contradiction
        | cons x xs =>
          simp only [Bool.and_eq_true] at ok
          obtain ⟨left,right⟩ := ok
          by_cases hit : x∈f
          · apply ih (insert x used) _ (Finset.insert_subset hit sub) _ right
            intro y hy outside
            have ne : x≠y := fun e => outside (e ▸ Finset.mem_insert_self x used)
            have tail := (List.mem_cons.mp (rest y hy (fun h => outside (Finset.mem_insert_of_mem h)))).resolve_left ne.symm
            exact List.mem_filter.mpr ⟨tail,decide_eq_true (clique x hit y hy ne)⟩
          · apply ih used xs sub _ left
            intro y hy hu
            exact (List.mem_cons.mp (rest y hy hu)).resolve_left (fun e => hit (e ▸ hy))

attribute [local irreducible] Input.words
set_option maxRecDepth 20000 in
private theorem tested : search 66 ∅ (List.finRange 64)=true := by native_decide

/-- All eight-element families of six-bit words at pairwise distances three or four. -/
theorem exhaustive {f : Finset Word} (size : f.card=8)
    (clique : ∀ x∈f, ∀ y∈f, x≠y → Adj x y) : ∃ s : Shape, family s=f :=
  sound size clique 66 ∅ (List.finRange 64) (Finset.empty_subset _) (fun x _ _ => List.mem_finRange x) tested

theorem distinct (s : Shape) : Function.Injective (wordAt s) := by
  revert s
  unfold Function.Injective
  native_decide

end QGI.EightTwelveSigns.Cliques
