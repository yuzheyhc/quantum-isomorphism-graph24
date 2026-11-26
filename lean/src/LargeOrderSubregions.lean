import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.LargeOrderSubregions
open SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)

abbrev Points {k : Nat} (c : Table k) (keep : Nat → Prop) := {i : Fin k // keep (c i i)}

private def coordinates {n k : Nat} {c : Table n} {reg : Nat → Prop} (F : Fin k → Fin n)
    (inj : Function.Injective F) (range : ∀ z, (∃ i, F i=z) ↔ reg (c z z)) (keep : Nat → Prop) :
    Points (restricted c F) keep ≃ Region c (fun s => reg s ∧ keep s) := by
  let h (i : Points (restricted c F) keep) : Region c (fun s => reg s ∧ keep s) :=
    ⟨F i.val,(mem_vertices _ _ _).mpr ⟨(range _).mp ⟨i.val,rfl⟩,i.property⟩⟩
  apply Equiv.ofBijective h
  refine ⟨fun i j eq => Subtype.ext (inj (congrArg Subtype.val eq)),?_⟩
  intro z
  obtain ⟨inReg,ok⟩ := (mem_vertices _ _ _).mp z.property
  obtain ⟨i,hi⟩ := (range z.val).mpr inReg
  exact ⟨⟨i,by change keep (c (F i) (F i)); rw [hi]; exact ok⟩,Subtype.ext hi⟩

private theorem card {n k : Nat} {c : Table n} {reg : Nat → Prop} (F : Fin k → Fin n)
    (inj : Function.Injective F) (range : ∀ z, (∃ i, F i=z) ↔ reg (c z z)) (keep : Nat → Prop) :
    (vertices c (fun s => reg s ∧ keep s)).card=(vertices (restricted c F) keep).card := by
  classical
  have h := Fintype.card_congr (coordinates F inj range keep)
  have body : (vertices (restricted c F) keep)=Finset.univ.filter (fun i => keep (c (F i) (F i))) := by
    ext i; simp only [mem_vertices,Finset.mem_filter,Finset.mem_univ,true_and,restricted,SmallShore.restrict]
  rw [←Fintype.card_coe (vertices c (fun s => reg s ∧ keep s)),body,←h]
  exact Fintype.card_subtype _

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {reg : Nat → Prop} {F T : Fin k → Fin n} (D : DataFor p reg F T)
local notation "c" => restricted (source G) F
local notation "d" => restricted (targetName p) T
include D

theorem small (keep : Nat → Prop) (bound : (vertices c keep).card≤13) :
    ∃ e : Points c keep ≃ Points d keep, ∀ i j, c i.val j.val=d (e i).val (e j).val := by
  let L := coordinates F D.injF D.src keep
  let R := coordinates T D.injG D.tgt keep
  obtain ⟨e,he⟩ := LargeOrderBlocks.small p (fun s => reg s ∧ keep s) ((card F D.injF D.src keep).trans_le bound)
  refine ⟨L.trans (e.trans R.symm),fun i j => ?_⟩
  have ev (x : Points c keep) : T ((L.trans (e.trans R.symm)) x).val=(e (L x)).val :=
    congrArg Subtype.val (R.apply_symm_apply (e (L x)))
  change source G (F i.val) (F j.val)=targetName p _ _
  rw [ev,ev]; exact he (L i) (L j)

theorem pair (keep : Nat → Prop) (bound : (vertices c keep).card≤13)
    (i j : Points c keep) (x y : Points d keep) (hit : c i.val j.val=d x.val y.val) :
    ∃ e : Points c keep ≃ Points d keep, e i=x ∧ e j=y ∧ ∀ u v, c u.val v.val=d (e u).val (e v).val := by
  let L := coordinates F D.injF D.src keep
  let R := coordinates T D.injG D.tgt keep
  have size := (card F D.injF D.src keep).trans_le bound
  obtain ⟨e,hi,hj,he⟩ := SmallUnion.realize_region_pair p _ (Finset.card_pos.mpr ⟨_,(L i).property⟩)
    size (L i) (L j) (R x) (R y) hit
  refine ⟨L.trans (e.trans R.symm),by simp only [Equiv.trans_apply,hi,Equiv.symm_apply_apply],
    by simp only [Equiv.trans_apply,hj,Equiv.symm_apply_apply],fun u v => ?_⟩
  have ev (z : Points c keep) : T ((L.trans (e.trans R.symm)) z).val=(e (L z)).val :=
    congrArg Subtype.val (R.apply_symm_apply (e (L z)))
  change source G (F u.val) (F v.val)=targetName p _ _
  rw [ev,ev]; exact he (L u) (L v)

end QGI.Coherent.LargeOrderSubregions
