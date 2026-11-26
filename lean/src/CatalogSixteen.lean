import CatalogFourClique

namespace QGI.CatalogRigidity
open ThetaBridge

/-- Cache the three matrix counts per representative. Only a collision requires
evaluating the ordered four-clique count on its two matrices. -/
private def separates {α β : Type} [DecidableEq β] (count : α → Nat) (x y : β × α) : Bool :=
  if x.1 = y.1 then decide (count x.2 ≠ count y.2) else true

private theorem nodup_of_separates {α β : Type} [DecidableEq β] (rows : List α)
    (first : α → β) (count : α → Nat)
    (h : (rows.map fun a => (first a, a)).Pairwise (fun x y => separates count x y = true)) :
    (rows.map fun a => (first a, count a)).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp h).imp
  intro a b passed eq
  have hKey : first a = first b := congrArg Prod.fst eq
  have hCount : count a = count b := congrArg Prod.snd eq
  simp [separates, hKey, hCount] at passed

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem checked16 :
    (records 16).length = 286 ∧
    ((records 16).map fun a => (key a, a)).Pairwise
      (fun x y => separates fourCliqueNat x y = true) := by
  native_decide

/-- The four counts separate the 286 decoded matrices used by `Represented`. -/
theorem valid16 : (records 16).length = 286 ∧ ((records 16).map key16).Nodup :=
  ⟨checked16.1, nodup_of_separates (records 16) key fourCliqueNat checked16.2⟩

/-- At order 16 the two input graphs each carry a labeling onto a catalog row. -/
theorem represented16 {G H : QGI.Graph 16} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H :=
  catalog_iso_of_key key16 valid16.2 (fun ha hb qc => key16_sound ha hb qc) g h q

end QGI.CatalogRigidity
