import OddShoreAttachment

noncomputable section
namespace QGI.Coherent.LargeOrderSixHalves
open SmallUnion SmallFiberExtension StrategyColorLaws FiberPairExtension SixTenCoordinates
open FourTwelveFunctional (source)
open private shore reverse from RegionalFourFourEight

variable {n l : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem rows {a r : Nat} [NeZero (2*a)] (small : a=2 ∨ a=4)
    (T : Shore c₀ l (Fin 6)) (A : Shore c₀ r (Fin (2*a)))
    (side : Fin 6 → Bool) (sur : Function.Surjective side)
    (coh : Block T T T T (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j))) :
    ∀ i z, side i=side z → ∀ j, c₀ (atPoint T i) (atPoint A j)=c₀ (atPoint T z) (atPoint A j) := by
  rcases OddHalfPartition.palette (p:=a) (sourceLaws _) T A
    (fun x y hx he => by rcases small with rfl|rfl <;> omega) with ⟨v,all⟩|⟨v,w,vw,pal,rd'⟩
  · exact fun i z _ j => (all i j).trans (all z j).symm
  let M := fun i j => decide (c₀ (atPoint T i) (atPoint A j)=v)
  have block : Block T T A A M M := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have rd (i) : FiberRectangles.degree (M i)=a := by simpa only [M,FiberRectangles.degree,decide_eq_true_eq] using rd' i
  have cd (j) := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) block) j 0
  have bal := FiberRectangles.balance M rd cd
  apply (OddHalfPartition.rigid_with_rows (a:=1) (sourceLaws _) T A side sur coh v w vw pal ?_).2
  intro j
  have h : FiberRectangles.degree (fun i => M i j)=3 := (cd j).trans (by rcases small with rfl|rfl <;> omega)
  simpa only [M,FiberRectangles.degree,decide_eq_true_eq] using h

/-- A nonconstant twin interface with a four- or eight-point shore gives the
same three-plus-three cut across all external shores of either size. -/
theorem extend {a r : Nat} [NeZero (2*a)] (small : a=2 ∨ a=4)
    (T : Shore c₀ l (Fin 6)) (A : Shore c₀ r (Fin (2*a)))
    (weak : FiberPairExtension.twins c₀ r l)
    (nonuniform : ∃ i j, c₀ (atPoint A i) (atPoint T j)≠c₀ (atPoint A 0) (atPoint T 0))
    (keep : Nat → Prop) (old : Realizes p keep) (inside : keep r)
    (sizes : ∀ z : Region c₀ keep, (fiber G z.val).card=4 ∨ (fiber G z.val).card=8) :
    Realizes p (fun t => keep t ∨ t=l) := by
  classical
  let c := c₀
  rcases OddHalfPartition.palette (p:=3) (sourceLaws _) A T
    (fun x y hx he => by rcases small with rfl|rfl <;> omega) with ⟨v,all⟩|⟨v,w,vw,pal,rows'⟩
  · obtain ⟨i,j,ne⟩ := nonuniform
    exact (ne ((all i j).trans (all 0 0).symm)).elim
  let B := fun j i => decide (c (atPoint A i) (atPoint T j)=v)
  have block : Block A A T T (fun i j => B j i) (fun i j => B j i) := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have rd (i) : FiberRectangles.degree (fun j => B j i)=3 := by simpa only [B,FiberRectangles.degree,decide_eq_true_eq] using rows' i
  have cd (j) := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) block) j 0
  have named := OddHalfPartition.column_block (v:=v) (sourceLaws _) A T B
    (fun _ _ => by simp only [B,decide_eq_true_eq]; rfl) cd
  let side := fun j => B j 0
  have bit (i j x y) : B j i=B y x ↔ c (atPoint A i) (atPoint T j)=c (atPoint A x) (atPoint T y) := by
    rcases pal i j with h|h <;> rcases pal x y with g|g <;> simp [B,c,h,g,vw,Ne.symm vw]
  have key (i j) : B i=B j ↔ side i=side j := by
    refine ⟨fun h => congrFun h 0,fun h => funext fun k => (bit k i k j).mpr ?_⟩
    exact weak.2 (A 0) (T i) (T j) ((bit 0 i 0 j).mp h) (A k)
  have coh : Block T T T T (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j)) := by
    intro i j x y h; simpa only [←key] using named h
  have sur : Function.Surjective side := by
    have sz : (Finset.univ.filter (fun i => side i=true)).card=3 := rd 0
    intro b
    by_contra no
    have ne (i : Fin 6) : side i≠b := fun h => no ⟨i,h⟩
    cases b with
    | false =>
      have full (i : Fin 6) : side i=true := by cases h : side i <;> simp_all
      simp [full] at sz
    | true =>
      have emp : Finset.univ.filter (fun i : Fin 6 => side i=true)=∅ := Finset.filter_eq_empty_iff.mpr fun i _ => ne i
      rw [emp] at sz; contradiction
  let base : Region c keep := ⟨atPoint A 0,(mem_vertices _ _ _).mpr ((congrArg keep (A 0).property).mpr inside)⟩
  apply DeterminedShore.attach p (atPoint T 0) (T 0).property ((RegionalTwoAnchor.card T).le.trans (by decide))
    keep old base (by rw [show c₀ base.val base.val=r from (A 0).property]; exact reverse weak)
  intro i z h j
  have same : side (T.symm i)=side (T.symm z) := (bit 0 _ 0 _).mpr (by
    simpa only [base,atPoint,Equiv.apply_symm_apply] using (Relations.transpose _ h))
  rcases sizes j with four|eight
  · obtain ⟨E⟩ := shore j.val four
    simpa only [atPoint,Equiv.apply_symm_apply] using
      rows (a:=2) (Or.inl rfl) T E side sur coh (T.symm i) (T.symm z) same (E.symm ⟨j.val,rfl⟩)
  · obtain ⟨E⟩ := shore j.val eight
    simpa only [atPoint,Equiv.apply_symm_apply] using
      rows (a:=4) (Or.inr rfl) T E side sur coh (T.symm i) (T.symm z) same (E.symm ⟨j.val,rfl⟩)

end QGI.Coherent.LargeOrderSixHalves
