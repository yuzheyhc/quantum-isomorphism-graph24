import DoubleEightPrepared
import SixteenPointSound
import Single16Maps
import HomogeneousCensus

namespace QGI.LargeOrderSingle
open SixteenMapSearch
open DoubleEight.Prepared
open private Table Table.trans tab stages stage_congr sorted_eq perm_of_equiv coefficients histogram histogram_at get_ofFn from DoubleEightPrepared
open private sorted from SixteenMapSearch

abbrev Index := Fin 208
abbrev V := Fin 16
def row (a : Index) : Array Nat := Single16.Input.matrices.toArray[a.val]?.getD #[]
private def cache := Vector.ofFn fun a : Index => prepare [16] (a.val+1) (row a)
def scheme (a : Index) := (cache.get a).getD ⟨0,#[],0,#[],#[],#[],[]⟩

private theorem present : ∀ a : Index, (cache.get a).isSome=true := by native_decide
theorem prepare_row (a : Index) : prepare [16] (a.val+1) (row a)=some (scheme a) := by
  have atA : cache.get a=prepare [16] (a.val+1) (row a) := by simp only [cache,get_ofFn]
  rw [←atA,scheme]
  cases e : cache.get a with
  | none => have h := present a; simp [e] at h
  | some s => rfl

attribute [local irreducible] scheme row
private theorem bounds : ∀ a : Index, ∀ i j : V, pointColor (scheme a) i j < (scheme a).rank := by native_decide
def name (a : Index) (i j : V) : Fin (scheme a).rank := ⟨_,bounds a i j⟩

private def intrinsic (a : Index) := stages (tab (scheme a)) 3
private def lookup := (List.finRange 208).flatMap fun a => List.ofFn (fun i : Fin (scheme a).rank =>
  ((intrinsic a).get i,refinedKey (scheme a) i.val))
private def decode (v : Nat) := ((lookup.find? (fun p => p.1=v)).map Prod.snd).getD 0

/-- The invariant refinement can have collisions. On these rows its value
determines the original executable's pruning key, checked for every color. -/
private theorem key_ok : ∀ a : Index, ∀ i : Fin (scheme a).rank,
    decode ((intrinsic a).get i)=refinedKey (scheme a) i.val := by native_decide
private theorem facts : ∀ a : Index,
    (∀ k : Fin (scheme a).rank, transposeName (scheme a) k.val < (scheme a).rank) ∧
    (scheme a).profile=sorted (List.ofFn fun k : Fin (scheme a).rank => refinedKey (scheme a) k.val) ∧
    (∀ k : Fin (scheme a).rank, ∃ x y, name a x y=k) ∧
    ∀ x y, transposeName (scheme a) (name a x y).val=(name a y x).val := by native_decide

theorem onto (a : Index) (k : Fin (scheme a).rank) : ∃ x y, name a x y=k := (facts a).2.2.1 k

private def histAt (a : Index) (x y : V) :=
  histogram (List.ofFn fun z : V => finProdFinEquiv (name a x z,name a z y))
private theorem histograms : ∀ a : Index, ∀ x y : V,
    coefficients (scheme a) (name a x y)=histAt a x y := by native_decide
private theorem coefficient_at (a : Index) (x y : V) (i j : Fin (scheme a).rank) :
    coefficient (scheme a) (name a x y).val i.val j.val =
      ∑ z : V, if name a x z=i ∧ name a z y=j then 1 else 0 := by
  have h := congrArg (fun v => Vector.get v (finProdFinEquiv (i,j))) (histograms a x y)
  simpa only [coefficients,get_ofFn,Equiv.symm_apply_apply,histAt,histogram_at,List.map_ofFn,
    Function.comp_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq,List.sum_ofFn] using h

end QGI.LargeOrderSingle
