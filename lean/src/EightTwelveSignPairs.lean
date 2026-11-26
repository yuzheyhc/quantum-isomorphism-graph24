import EightTwelveSignCliques
import EightTwelveSignWitnesses

namespace QGI.EightTwelveSigns
open Cliques
abbrev Pairing := Fin 75
abbrev Axis := Fin 6
def pairData (o : Pairing) := (Input.pairings[o.val]?).getD (0,0,0)
def atlas (o : Pairing) : Key := Fin.ofNat' 59 (pairData o).1
def tag (o : Pairing) := (pairData o).2.1
def point (o : Pairing) (a : Axis) (b : Bool) : J :=
  Fin.ofNat' 12 (EightTwelveCatalog.digit (pairData o).2.2 (2*a.val+b.toNat))
def rowSet (o : Pairing) (w : Word) : Finset J := Finset.univ.image (fun a => point o a (w.val.testBit a.val))
def Matching (a : Key) (c : Nat) :=
  (∀ i : J, rightName a i i≠c) ∧ (∀ i j : J, rightName a i j=c → rightName a j i=c) ∧
  ∀ i : J, ∃! j : J, rightName a i j=c
instance (a : Key) (c : Nat) : Decidable (Matching a c) := by unfold Matching ExistsUnique; infer_instance

attribute [local irreducible] Input.pairings EightTwelveCatalog.row
theorem findPairing : ∀ (a : Key) (j : J), Matching a (rightName a 0 j) →
    ∃ o : Pairing, atlas o=a ∧ tag o=rightName a 0 j := by native_decide
theorem coordinates : ∀ (o : Pairing),
    Function.Bijective (fun ab : Axis × Bool => point o ab.1 ab.2) ∧
    ∀ i : Axis, rightName (atlas o) (point o i false) (point o i true)=tag o := by
  unfold Function.Bijective Function.Injective Function.Surjective
  native_decide
theorem readPoint (o : Pairing) (w : Word) (i : Axis) (b : Bool) :
    point o i b∈rowSet o w ↔ w.val.testBit i.val=b := by
  constructor
  · intro h
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp h
    have t := (coordinates o).1.1 (a₁:=(j,w.val.testBit j.val)) (a₂:=(i,b)) e
    have ij := congrArg Prod.fst t
    change j=i at ij
    subst j
    exact congrArg Prod.snd t
  · intro eq
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg (point o i) eq⟩

private theorem encode : ∀ f : Axis → Bool, ∃ w : Word, ∀ i, w.val.testBit i.val=f i := by native_decide

theorem word_for {o : Pairing} (s : Finset J)
    (split : ∀ a : Axis, point o a false∈s ↔ point o a true∉s) :
    ∃ w : Word, rowSet o w=s := by
  obtain ⟨w,hw⟩ := encode (fun a => decide (point o a true∈s))
  refine ⟨w,?_⟩
  ext j
  obtain ⟨⟨a,b⟩,rfl⟩ := (coordinates o).1.2 j
  rw [readPoint,hw]
  cases b
  · simp [split]
  · simp

theorem distances : ∀ (o : Pairing) (u v : Word),
    distance u v+(rowSet o u∩rowSet o v).card=6 := by native_decide

end QGI.EightTwelveSigns
