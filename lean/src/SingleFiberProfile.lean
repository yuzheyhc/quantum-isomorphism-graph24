import CoprimeProfiles
import HomogeneousCoverage

namespace QGI.Coherent.CoprimeProfiles.Profile

/-- A one-entry fiber profile has constant diagonal on its coherent closure. -/
theorem homogeneous {n : Nat} [NeZero n] {G : Graph n} (P : Profile G [n]) :
    IsHomogeneous G := by
  intro M hM
  refine ⟨M 0 0, ?_⟩
  ext i j
  by_cases h : i = j
  · subst j
    have same := (P.same i 0).mp (Subsingleton.elim (α := Fin 1) (P.tag i) (P.tag 0))
    have v := (Relations.same _ _ _ _ _).mp same M hM
    simpa [schur] using v
  · simp [schur, Matrix.one_apply, h]

open private isomorphic_of_homogeneous_archive from HomogeneousCoverage in
theorem isomorphic_single_sixteen {G H : Graph 16} (P : Profile G [16]) (q : QuantumIso G H) :
    Isomorphic G H :=
  isomorphic_of_homogeneous_archive (Or.inl rfl) P.homogeneous q

end QGI.Coherent.CoprimeProfiles.Profile
