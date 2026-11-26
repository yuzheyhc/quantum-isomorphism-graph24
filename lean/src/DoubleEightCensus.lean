import DoubleEightColumnCoordinates
import DoubleEightColumnCertificate
import DoubleEightColumnMaps
import DoubleEightTwoColors

namespace QGI.DoubleEight.Census

open ShoreCensus FixedInterface InterfaceTransport ColumnMaps

private theorem mapped_keys : ColumnMaps.keys = ColumnEnum.leaves := by native_decide

private theorem profile_index {ds : List Nat} (h : ds ∈ ColumnProfiles.profiles) :
    ∃ p : Fin 6, ds = ColumnEnum.profiles[p.val]! := by
  have all : ∀ ds ∈ ColumnProfiles.profiles, (List.finRange 6).any (fun p => ds == ColumnEnum.profiles[p.val]!) = true := by decide
  obtain ⟨p,_,eq⟩ := List.any_eq_true.mp (all ds h)
  exact ⟨p,beq_iff_eq.mp eq⟩

private theorem same_seed (a : Fin 21) :
    UniformInput.shores.getD a.val #[] = UniformInput.shores[a.val]! := by
  revert a; native_decide

private theorem one_shore {c l : Coloring} {ds : List Nat} (hl : Homogeneous l)
    (hc : Compatible c l) (hds : ds ∈ ColumnProfiles.profiles) (hp : ColumnProfiles.Presentation c ds) :
    (∃ k : Fin 88, Oriented c (named (Nonuniform.layer k).word)) ∨
       (splitRows c ∧ ¬ splitRows (transpose c)) := by
  obtain ⟨a,cols,q,h,eqv⟩ := ColumnCoordinates.coordinates hl hc hds hp
  obtain ⟨p,ep⟩ := profile_index hds
  rw [same_seed,ep] at h
  have mem := ColumnEnum.admissible_mem_leaf a p h
  rw [← mapped_keys] at mem
  rcases key_sound mem with ⟨k,good | good⟩ | ⟨left,right⟩
  · exact Or.inl ⟨k,Or.inl (crossIso_trans eqv good)⟩
  · exact Or.inl ⟨k,Or.inr (crossIso_trans (dualIso eqv) good)⟩
  · exact Or.inr ⟨(splitRows_iff eqv).mpr left, fun no => right ((splitRows_iff (dualIso eqv)).mp no)⟩

private theorem transpose_presentation {c : Coloring} {ds : List Nat} (h : ColumnProfiles.Presentation c ds) :
    ColumnProfiles.Presentation (transpose c) ds := by
  obtain ⟨name,index,inj,spec,card⟩ := h
  exact ⟨name,fun i j => index j i,inj,fun i j => spec j i,fun s => ⟨(card s).2,(card s).1⟩⟩

/-- Every actual nonuniform interface without a cross matching has a
point-and-color identification with one of the catalog interfaces, up to exchanging shores. -/
theorem every_cross {c l r : Coloring} (hl : Homogeneous l) (hr : Homogeneous r)
    (lc : Compatible c l) (rc : Compatible (transpose c) r)
    (mixed : ∃ i j x y, c i j ≠ c x y)
    (least : ∀ i j, 2 ≤ BareLaws.rowHistogram c (c i j) 0) :
    ∃ k : Fin 88, Oriented c (named (Nonuniform.layer k).word) := by
  obtain ⟨ds,hds,hp⟩ := ColumnProfiles.normalize c (BareLaws.biregular hl hr lc rc) mixed least
  rcases one_shore hl lc hds hp with h | h
  · exact h
  rcases one_shore hr rc hds (transpose_presentation hp) with ⟨k,hit | hit⟩ | obstruction
  · exact ⟨k,Or.inr hit⟩
  · exact ⟨k,Or.inl hit⟩
  · exact False.elim (h.2 obstruction.1)

private theorem uniform_row (r : Fin 636) :
    Layers.matrices[r.val]? = some (Uniform.rows.getD r.val #[]) ∧
    ∀ i j : Fin 16, Uniform.color (Uniform.rows.getD r.val #[]) i j =
      Placements.color (Uniform.rows.getD r.val #[]) i j := by
  revert r; native_decide

/-- Every raw coherent coloring of two eight-point fibers either contains a
perfect matching as a color, or admits a point bijection onto an actual row
of the 636-row catalog. There is no catalog-membership hypothesis. -/
theorem matching_or_catalog (m : V ⊕ V → V ⊕ V → Nat)
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m) :
    (∃ v : Nat, ∃ e : Equiv.Perm V, ∀ i j, m (.inl i) (.inr j) = v ↔ e i = j) ∨
    (∃ (t : Nat) (row : Word), Layers.matrices[t]? = some row ∧ PartitionIso m (Placements.color row)) := by
  classical
  let c : Coloring := fun i j => m (.inl i) (.inr j)
  obtain ⟨lc,rc⟩ := BareLaws.raw_compatible m rectangle rev products
  by_cases mixed : ∃ i j x y, c i j ≠ c x y
  · by_cases least : ∀ i j, 2 ≤ BareLaws.rowHistogram c (c i j) 0
    · obtain ⟨k,h⟩ := every_cross hl hr lc rc mixed least
      exact Or.inr (every_raw_either k m h hl hr rectangle rev products)
    · push_neg at least
      obtain ⟨i,j,small⟩ := least
      have degree : FiberRectangles.degree (BareLaws.ofColor c (c i j) 0) < 2 := by
        simpa [FiberRectangles.degree,BareLaws.ofColor,BareLaws.rowHistogram] using small
      exact Or.inl ⟨c i j,TwoColors.matching_of_small_valency (BareLaws.biregular hl hr lc rc)
        _ ⟨i,j,rfl⟩ degree⟩
  · push_neg at mixed
    obtain ⟨t,_,e,he⟩ := every_uniform_two_fiber m hl hr rectangle mixed
      (fun i j x y => rev _ _ _ _ (mixed j i y x))
    obtain ⟨inside,eq⟩ := uniform_row t
    exact Or.inr ⟨t.val,_,inside,e,fun i j x y => by simpa only [eq] using he i j x y⟩

/-- Coverage in the matching-free case of the graph lower-bound argument. -/
theorem catalog_of_no_matching (m : V ⊕ V → V ⊕ V → Nat)
    (hl : Homogeneous (fun i j => m (.inl i) (.inl j)))
    (hr : Homogeneous (fun i j => m (.inr i) (.inr j)))
    (rectangle : ∀ i j x y, m i j = m x y → (side i, side j) = (side x, side y))
    (rev : ∀ i j x y, m i j = m x y → m j i = m y x) (products : HasIntersectionNumbers m)
    (noMatching : ¬ ∃ v : Nat, ∃ e : Equiv.Perm V, ∀ i j, m (.inl i) (.inr j) = v ↔ e i = j) :
    ∃ (t : Nat) (row : Word), Layers.matrices[t]? = some row ∧ PartitionIso m (Placements.color row) :=
  (matching_or_catalog m hl hr rectangle rev products).resolve_left noMatching
end QGI.DoubleEight.Census