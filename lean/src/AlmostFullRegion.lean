import RegionalTenTen
import PartialFunctional

noncomputable section
namespace QGI.Coherent.AlmostFullRegion
open SixTenCoordinates SmallUnion StrategyColorLaws SmallFiberExtension
open FourTwelveFunctional (source)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

/-- An ordinary graph isomorphism on a named region that respects the diagonal fiber labels. -/
def EdgeRealizes (reg : Nat → Prop) := ∃ e : Region (source G) reg ≃ Region (targetName p) reg,
    (∀ i, source G i.val i.val=targetName p (e i).val (e i).val) ∧ ∀ i j, G.edge i.val j.val=H.edge (e i).val (e j).val

theorem of_named {reg : Nat → Prop} (h : Realizes p reg) : EdgeRealizes p reg := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,fun i => he i i,fun i j => common_edge p (he i j)⟩

/-- Outside a region of codimension at most one, each remaining vertex is determined by its diagonal label. -/
theorem isomorphic (reg : Nat → Prop) (size : n≤(vertices (source G) reg).card+1)
    (h : EdgeRealizes p reg) : Isomorphic G H := by
  classical
  obtain ⟨e,ed,ee⟩ := h
  obtain ⟨m,md⟩ := diagonal_names p
  let S := vertices (source G) reg
  let T := vertices (targetName p) reg
  have mem (i) : i∈S ↔ m i∈T := by simp only [S,T,mem_vertices,source,md]
  let out := Equiv.subtypeEquiv (p:=fun i => i∉S) (q:=fun a => a∉T) m (fun i => not_congr (mem i))
  let E := (Equiv.sumCompl (·∈S)).symm.trans ((Equiv.sumCongr e out).trans (Equiv.sumCompl (·∈T)))
  have inside (i) (hi : i∈S) : E i=(e ⟨i,hi⟩).val := by
    dsimp only [E,Equiv.trans_apply]; rw [Equiv.sumCompl_apply_symm_of_pos _ _ hi]; rfl
  have outside (i) (hi : i∉S) : E i=m i := by
    dsimp only [E,Equiv.trans_apply]; rw [Equiv.sumCompl_apply_symm_of_neg _ _ hi]; rfl
  have tsize : T.card=S.card := by simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm
  have one : Tᶜ.card≤1 := by rw [Finset.card_compl,Fintype.card_fin,tsize]; change n≤S.card+1 at size; omega
  have diag (i) : source G i i=targetName p (E i) (E i) := by
    by_cases hi : i∈S
    · rw [inside i hi]; exact ed ⟨i,hi⟩
    · rw [outside i hi]; exact md i
  have toOut (i j) (hj : j∉S) : G.edge i j=H.edge (E i) (E j) := by
    obtain ⟨z,hit,_⟩ := PartialFunctional.middle _ _ (fun a b => common_products p a b (diag i)) j
    have endName := (commonLaws p).last hit
    have zOut : z∈Tᶜ := Finset.mem_compl.mpr (fun hz => hj ((mem_vertices _ _ _).mpr ((congrArg reg endName).mpr ((mem_vertices _ _ _).mp hz))))
    have jOut : E j∈Tᶜ := Finset.mem_compl.mpr (by rw [outside j hj]; exact mt (mem j).mpr hj)
    exact (Finset.card_le_one.mp one z zOut (E j) jOut) ▸ common_edge p hit
  refine ⟨E,E.symm,E.symm_apply_apply,E.apply_symm_apply,fun i j => ?_⟩
  by_cases hi : i∈S
  · by_cases hj : j∈S
    · rw [inside i hi,inside j hj]; exact ee ⟨i,hi⟩ ⟨j,hj⟩
    · exact toOut i j hj
  · rw [G.symm,H.symm]; exact toOut j i hi

end QGI.Coherent.AlmostFullRegion
