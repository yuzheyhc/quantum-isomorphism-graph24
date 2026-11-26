import SmallCatalogAutomorphisms
import SmallCatalogTypes

namespace QGI.SmallCatalog
open CatalogComparison
open Fifteen (System)
open private get_ofFn from DoubleEightPrepared

private theorem checked {n} [NeZero n] (small : n≤13) (a : Index n) : checkedRow a=true := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => exact List.all_eq_true.mp (allRows ⟨m,by omega⟩) _ (List.mem_finRange _)

theorem positions {n} [NeZero n] (small : n≤13) (a : Index n) :
    ∀ k, (frame a).name ((frame a).spot k).1 ((frame a).spot k).2=k :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (checked small a)).1).1

theorem passes {n} [NeZero n] (small : n≤13) (a : Index n) :
    (model a).check (model a).features [] (chain a)=true :=
  (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (checked small a)).1).2

theorem same_row {n} [NeZero n] (small : n≤13) {a b : Index n} {e}
    (law : Respects (frame a) (frame b) e) : a=b := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
    have ok := allTypes ⟨m,by omega⟩
    exact (of_decide_eq_true ok) a b (ids_eq frame law)

/-- Every pair of entries of the same color is joined by a color-preserving
point permutation. The certificate stores maps out of one spot per color. -/
theorem transitive {n} [NeZero n] (small : n≤13) (a : Index n) (i j x y : Fin n)
    (hit : (frame a).name i j=(frame a).name x y) :
    ∃ e : Equiv.Perm (Fin n), e i=x ∧ e j=y ∧ ∀ u v, (frame a).name u v=(frame a).name (e u) (e v) := by
  classical
  let s := model a
  have cov := (Bool.and_eq_true_iff.mp (checked small a)).2
  have ok := Bool.and_eq_true_iff.mp cov
  have reach := of_decide_eq_true ok.2
  have fromSpot (u v : Fin n) :
      ∃ p : Equiv.Perm (Fin n), p (s.spot (s.name u v)).1=u ∧ p (s.spot (s.name u v)).2=v ∧
        ∀ z t, s.name z t=s.name (p z) (p t) := by
    rcases reach u v with same | moved
    · exact ⟨Equiv.refl _,congrArg Prod.fst same,congrArg Prod.snd same,fun _ _ => rfl⟩
    obtain ⟨w,hw,h⟩ := List.any_eq_true.mp moved
    obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp h
    have valid := of_decide_eq_true (List.all_eq_true.mp ok.1 w hw)
    have inj : Function.Injective (Fifteen.System.point (n:=n) w) := by
      simpa only [get_ofFn,Function.Injective] using valid.1
    exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj),beq_iff_eq.mp hu,beq_iff_eq.mp hv,
      by simpa only [get_ofFn] using valid.2⟩
  obtain ⟨p,pi,pj,pm⟩ := fromSpot i j
  obtain ⟨q,qx,qy,qm⟩ := fromSpot x y
  change s.name i j=s.name x y at hit
  rw [←hit] at qx qy
  refine ⟨p.symm.trans q,?_,?_,fun u v => ?_⟩
  · exact (congrArg q (p.symm_apply_eq.mpr pi.symm)).trans qx
  · exact (congrArg q (p.symm_apply_eq.mpr pj.symm)).trans qy
  · exact (by simpa only [Equiv.apply_symm_apply] using (pm (p.symm u) (p.symm v)).symm :
      s.name u v=s.name (p.symm u) (p.symm v)).trans (qm _ _)

end QGI.SmallCatalog

