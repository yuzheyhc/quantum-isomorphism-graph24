import FourHalfCore
import data.FourHalfWitnesses

namespace QGI.FourHalfCatalog
open Certificate FourHalfInput
set_option maxRecDepth 12000

def permPoint (z : Nat) (i : W) : W := Fin.ofNat' 20 ((z >>> (5*i.val))%32)

def Supports (a : Key) (sw : Bool) (q s : Nat) (r : Proof) : Prop :=
  match r with
  | .map v =>
      (∀ i j, permPoint v i=permPoint v j → i=j) ∧
      ∀ i j, value a sw q s false i j=value a sw q s true (permPoint v i) (permPoint v j)
  | .obstruct pat names =>
      (pat=.tetra ∨ pat=.nearClique) ∧ names.length=pat.edges.length ∧
      (∀ v∈names, v<108) ∧ homCount (matrix a sw q s false) pat names≠homCount (matrix a sw q s true) pat names

private instance (a : Key) (sw : Bool) (q s : Nat) (r : Proof) : Decidable (Supports a sw q s r) := by
  cases r <;> unfold Supports <;> infer_instance

attribute [local irreducible] DoubleEight.Prepared.row FourHalfInput.rows

theorem verified : ∀ i : Fin FourHalfInput.rows.size,
    let r := FourHalfInput.rows[i]
    Supports (Fin.ofNat' 636 r.id) r.swap r.cycle r.halves r.proof := by native_decide

end QGI.FourHalfCatalog
