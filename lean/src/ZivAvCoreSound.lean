import ZivAvCoefficient

namespace QGI.ZivAv
open SixteenMapSearch QGI.DoubleEight.Prepared
open private vertex from SixteenMapSearch
open private keyedRows rawRows from ZivAvCoreCheck

attribute [local irreducible] rawRows cores14 raw keyed color

private theorem option_keys (v : Option Scheme) :
    (v.map intrinsicKeys).getD ⟨0,#[],0,#[],#[],#[],[]⟩ =
      intrinsicKeys (v.getD ⟨0,#[],0,#[],#[],#[],[]⟩) := by cases v <;> rfl

theorem keyed_eq (a : Index) : keyed a = intrinsicKeys (raw a) := by
  unfold keyed raw keyedRows
  rw [Array.getElem?_map]
  exact option_keys _

/-- All color permutations induced by the restricted strategy enter the
actual numerical search, even when the equivalence exchanges equal fibers. -/
theorem eligible (a : Index) (e : Equiv.Perm (Fin (raw a).rank))
    (tr : ∀ x y u v, e (name a x y) = name a u v → e (name a y x) = name a v u)
    (mul : ∀ x y u v, e (name a x y) = name a u v → ∀ i j : Fin (raw a).rank,
      (∑ z : Vertex, if name a x z = i ∧ name a z y = j then 1 else 0 : Nat) =
      ∑ z : Vertex, if name a u z = e i ∧ name a z v = e j then 1 else 0) :
    List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (keyed a) (keyed a) := by
  rw [keyed_eq]
  have rev (k : Fin (raw a).rank) := (locations a k).2
  have atMapped (k : Fin (raw a).rank) :
      e (name a (atName a k).1 (atName a k).2) = name a (atName a (e k)).1 (atName a (e k)).2 :=
    (congrArg e (locations a k).1).trans (locations a (e k)).1.symm
  apply mem_intrinsic _ e
  · intro k; rw [rev]; exact Fin.isLt _
  · intro k j
    have t := tr _ _ _ _ (atMapped k)
    rw [rev,rev,←t]
    exact Fin.val_inj.trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm)
  · intro k i j
    rw [mult_at,mult_at]
    exact mul _ _ _ _ (atMapped k) i j

theorem points (a : Index) (e : Equiv.Perm (Fin (raw a).rank))
    (passed : pointCheck (keyed a) (List.ofFn fun i => (e i).val) = true) :
    ∃ h : Equiv.Perm Vertex, ∀ x y, e (name a x y) = name a (h x) (h y) := by
  obtain ⟨h,hw⟩ := pointSearch_sound passed
  refine ⟨h,fun x y => Fin.ext ?_⟩
  simpa only [(entries a).2,List.getElem?_ofFn,(entries a).1,dif_pos,Option.getD_some,name]
    using hw x y

end QGI.ZivAv
