import BinaryShoreLaws
import SixShoreModels
import TenTwelveCatalog


namespace QGI.SixShoreAtlas
open Coherent.BinaryShore
def candidates (a : Key) (b : Nat) (s : Cell 6) := ((Finset.univ.powersetCard 3).filter (fun t => Admits (cell a) b t ∧ profile (cell a) t=profile (cell a) s))
def mask (w : Fin 9) (i : Point) := decide (w=8 ∨ w.val.testBit (i.val/2)=i.val.testBit 0)
def subsets (w : Fin 9) := Finset.univ.filter (fun i => mask w i=true)
attribute [local irreducible] matrices
private theorem basic : ∀ a : Key, ∀ b∈[4,8], ∀ s∈Finset.univ.powersetCard 3, Admits (cell a) b s →
    (¬hard a → ∀ t∈candidates a b s, t=s ∨ t=sᶜ) ∧ (hard a → ∃ w : Fin 9, subsets w=s) := by native_decide
theorem cases_of (a : Key) {b : Nat} (hb : b=4 ∨ b=8) {s : Cell 6} (sz : s.card=3) (ok : Admits (cell a) b s) :
    (¬hard a → ∀ t∈candidates a b s, t=s ∨ t=sᶜ) ∧ (hard a → ∃ w : Fin 9, subsets w=s) :=
  basic a b (by rcases hb with rfl|rfl <;> decide) s (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,sz⟩) ok
end QGI.SixShoreAtlas
