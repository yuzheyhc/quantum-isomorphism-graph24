import EightTwelveSignPairs

namespace QGI.EightTwelveSigns
open Cliques
abbrev Profile := List Nat × List Nat
def sig (o : Pairing) (s : Finset J) (j : J) : List Nat := (List.finRange 12).map fun t =>
  (s.filter fun z => rightName (atlas o) j z=rightName (atlas o) 0 t).card
def anchor (o : Pairing) (w : Word) (b : Bool) := point o 0 (if b then w.val.testBit 0 else !(w.val.testBit 0))
def profile (o : Pairing) (w : Word) : Profile :=
  (sig o (rowSet o w) (anchor o w true),sig o (rowSet o w) (anchor o w false))
def summary (o : Pairing) (w : Word) : Option Profile :=
  let s := rowSet o w
  let p := profile o w
  if ∀ j, sig o s j=if j∈s then p.1 else p.2 then some p else none

def action (g : Nat) (i : J) : J := EightTwelveCatalog.mapPoint g i
def Fits (o : Pairing) (s : Shape) (a : Rep) (g : Nat) :=
  key a=atlas o ∧ Function.Injective (action g) ∧
  (∀ i j, rightName (atlas o) (action g i) (action g j)=rightName (atlas o) i j) ∧
  ∀ i : I, ∃ t : I, ∀ j : J, (action g j∈rowSet o (wordAt s t)) ↔ inside a i j=true
instance (o : Pairing) (s : Shape) (a : Rep) (g : Nat) : Decidable (Fits o s a g) := by
  unfold Fits Function.Injective; infer_instance

def witness (o : Pairing) (s : Shape) : Rep × Nat :=
  let row := (Input.placements.find? fun r => r.1=o.val).map Prod.snd
  let p := (((row.getD #[])[s.val]?).getD (0,0))
  (Fin.ofNat' 32 p.1,p.2)

def checked (o : Pairing) : Bool :=
  let table := Array.ofFn (summary o)
  let get := fun w : Word => (table[w.val]?).getD none
  (List.finRange 240).all fun s =>
    let base := get (wordAt s 0)
    let w := witness o s
    !(base.isSome && (List.finRange 8).all (fun t => get (wordAt s t)==base)) || decide (Fits o s w.1 w.2)

attribute [local irreducible] Input.words Input.pairings Input.placements Input.reps EightTwelveCatalog.row
set_option maxRecDepth 20000 in
private theorem verified : ∀ o : Pairing, checked o=true := by native_decide

private theorem lookup {X : Type} {n : Nat} (f : Fin n → X) (i : Fin n) (z : X) :
    ((Array.ofFn f)[i.val]?).getD z=f i := by
  have lt : i.val < (Array.ofFn f).size := by simpa only [Array.size_ofFn] using i.isLt
  rw [getElem?_pos (Array.ofFn f) i.val lt]
  simp only [Option.getD_some,Array.getElem_ofFn]

attribute [local irreducible] summary Fits witness rightName rowSet
set_option maxHeartbeats 1200000 in
theorem classify (o : Pairing) (s : Shape) (p : Profile)
    (valid : ∀ t : I, summary o (wordAt s t)=some p) :
    ∃ a : Rep, ∃ g : Equiv.Perm J, key a=atlas o ∧
    (∀ i j, rightName (atlas o) (g i) (g j)=rightName (atlas o) i j) ∧
    ∀ i : I, ∃ t : I, ∀ j : J, (g j∈rowSet o (wordAt s t)) ↔ inside a i j=true := by
  have ok := List.all_eq_true.mp (verified o) s (List.mem_finRange _)
  have passed : ((List.finRange 8).all (fun t => ((some p : Option Profile)==some p)))=true := by simp
  simp only [lookup,valid,Option.isSome_some,passed,Bool.and_self,Bool.not_true,Bool.false_or,decide_eq_true_eq] at ok
  have fit : Fits o s (witness o s).1 (witness o s).2 := ok
  unfold Fits at fit
  obtain ⟨eq,inj,colors,rows⟩ := fit
  exact ⟨_,Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj),eq,colors,rows⟩

theorem differentRows : ∀ a : Rep, Function.Injective (inside a) := by
  unfold Function.Injective
  native_decide

end QGI.EightTwelveSigns
