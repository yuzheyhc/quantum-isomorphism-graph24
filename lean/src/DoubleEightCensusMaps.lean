import DoubleEightPrepared
import DoubleEightCheck
import SixteenCensusSound

namespace QGI.DoubleEight.CensusMaps
open SixteenMapSearch Prepared

private theorem raw :
    (List.range Input.matrices.length).zip Input.matrices =
      (List.finRange 636).map (fun a : Index => (a.val,row a)) := by native_decide

private theorem prepared :
    preparedSchemes [8,8] Input.matrices = some ((List.finRange 636).map scheme) := by
  unfold preparedSchemes
  rw [raw]
  have compute (xs : List Index) :
      (xs.map fun a => (a.val,row a)).mapM (fun im => prepare [8,8] (im.1+1) im.2) = some (xs.map scheme) := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons, List.mapM_cons, prepare_row, ih]; rfl
  exact compute _

private theorem entries : ∀ a : Index, (scheme a).id = a.val+1 ∧
    ∀ i j : Fin 16, pointColor (scheme a) i j = Placements.color (row a) i j := by
  have rawEntries : ∀ a : Index, ∀ i j : Fin 16,
      ((row a)[16*i.val+j.val]?).getD 0 = Placements.color (row a) i j := by native_decide
  intro a
  refine ⟨scheme_id a, fun i j => ?_⟩
  change ((scheme a).colors[16*i.val+j.val]?).getD 0 = _
  rw [scheme_row]
  exact rawEntries a i j

private theorem counted :
    ∃ C : Counts, census = some C ∧ onMatrices [8,8] Input.matrices = some C := by
  have h := catalogueCheck
  unfold checked at h
  cases eq : census with
  | none => simp [eq] at h
  | some C =>
    refine ⟨C,rfl,?_⟩
    unfold census at eq
    split at eq
    · exact nomatch eq
    · exact eq

/-- For the actual 636 catalog rows, a map accepted by the palette search
is either induced by an explicit point permutation on the original color
tables or its precise key is included in the verified list of exceptions. -/
theorem dichotomy (a b : Index) (pi : List Nat) (rank : (scheme a).rank = (scheme b).rank)
    (profile : (scheme a).profile = (scheme b).profile)
    (listed : pi ∈ enumeratedMaps (scheme a) (scheme b)) :
    (∃ e : Equiv.Perm (Fin 16), ∀ i j, (pi[Placements.color (row a) i j]?).getD 0 =
      Placements.color (row b) (e i) (e j)) ∨
      ∃ C : Counts, census = some C ∧ (a.val+1,b.val+1,pi) ∈ C.exceptions := by
  cases hit : pointTest (scheme a) (scheme b) pi with
  | true =>
    obtain ⟨e,he⟩ := pointTest_sound hit
    exact Or.inl ⟨e,fun i j => by simpa only [(entries a).2,(entries b).2] using he i j⟩
  | false =>
    obtain ⟨C,hc,run⟩ := counted
    have mem (i : Index) : scheme i ∈ (List.finRange 636).map scheme :=
      List.mem_map_of_mem (List.mem_finRange i)
    have key := key_mem_exceptions prepared run (mem a) (mem b) rank profile listed hit
    exact Or.inr ⟨C,hc,by simpa only [(entries a).1,(entries b).1] using key⟩

end QGI.DoubleEight.CensusMaps
