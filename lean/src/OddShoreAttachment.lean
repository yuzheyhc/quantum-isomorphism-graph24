import DeterminedShore
import OddHalfPartition

noncomputable section
namespace QGI.Coherent.OddShoreAttachment
open SmallUnion SmallFiberExtension StrategyColorLaws FiberPairExtension SixTenCoordinates
open FourTwelveFunctional (source fiber_eq)
open private reverse shore from RegionalFourFourEight
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

private theorem even_rows {l r q : Nat} [NeZero (2*q)] (half : q=2 ∨ q=3) (T : Shore (source G) l (Fin 10)) (A : Shore (source G) r (Fin (2*q)))
    (side : Fin 10 → Bool) (sur : Function.Surjective side)
    (coh : Block T T T T (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j))) :
    ∀ i z, side i=side z → ∀ j, source G (atPoint T i) (atPoint A j)=source G (atPoint T z) (atPoint A j) := by
  rcases OddHalfPartition.palette (p:=q) (sourceLaws _) T A (fun x y hx he => by rcases half with rfl|rfl <;> omega) with ⟨v,all⟩|⟨v,w,vw,pal,rows⟩
  · exact fun i z _ j => (all i j).trans (all z j).symm
  let M := fun i j => decide (source G (atPoint T i) (atPoint A j)=v)
  have block : Block T T A A M M := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have rd (i) : FiberRectangles.degree (M i)=q := by simpa only [M,FiberRectangles.degree,decide_eq_true_eq] using rows i
  have cd (j) := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) block) j 0
  have bal := FiberRectangles.balance M rd cd
  apply (OddHalfPartition.rigid_with_rows (a:=2) (sourceLaws _) T A side sur coh v w vw pal ?_).2
  intro j
  have h : FiberRectangles.degree (fun i => M i j)=5 := (cd j).trans (by rcases half with rfl|rfl <;> omega)
  simpa only [M,FiberRectangles.degree,decide_eq_true_eq] using h

theorem extend_common {l q : Nat} [NeZero (2*q)] (half : q=2 ∨ q=3)
    (T : Shore (source G) l (Fin 10)) (keep : Nat → Prop) (old : Realizes p keep) (base : Region (source G) keep)
    (sizes : ∀ i : Region (source G) keep, (fiber G i.val).card=2*q)
    (shape : ∀ a : Region (source G) keep, FiberPairExtension.twins (source G) l (source G a.val a.val)) :
    Realizes p (fun t => keep t ∨ t=l) := by
  classical
  let c := source G
  have useAnchor (a : Region c keep)
      (det : ∀ i z : Cell c l, c i.val a.val=c z.val a.val → ∀ j : Region c keep, c i.val j.val=c z.val j.val) :
      Realizes p (fun t => keep t ∨ t=l) :=
    DeterminedShore.attach p (atPoint T 0) (T 0).property ((RegionalTwoAnchor.card T).le.trans (by decide)) keep old a (shape a) det
  by_cases simple : ∀ (j : Region c keep) (i z : Cell c l), c i.val j.val=c z.val j.val
  · exact useAnchor base (fun i z _ j => simple j i z)
  push_neg at simple
  obtain ⟨a,i₀,z₀,ne⟩ := simple
  obtain ⟨A⟩ := shore a.val (sizes a)
  let iA := A.symm ⟨a.val,rfl⟩
  have atA : atPoint A iA=a.val := congrArg Subtype.val (A.apply_symm_apply _)
  rcases OddHalfPartition.palette (p:=5) (sourceLaws _) A T (fun x y hx he => by rcases half with rfl|rfl <;> omega) with ⟨v,all⟩|⟨v,w,vw,pal,rows⟩
  · have h := (all iA (T.symm i₀)).trans (all iA (T.symm z₀)).symm
    exact (ne (Relations.transpose _ (by simpa only [atA,atPoint,Equiv.apply_symm_apply] using h))).elim
  let B := fun j i => decide (c (atPoint A i) (atPoint T j)=v)
  have block : Block A A T T (fun i j => B j i) (fun i j => B j i) := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have rd (i) : FiberRectangles.degree (fun j => B j i)=5 := by simpa only [B,FiberRectangles.degree,decide_eq_true_eq] using rows i
  have cd (j) := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) block) j 0
  have bal := FiberRectangles.balance (fun i j => B j i) rd cd
  have deg (j) : FiberRectangles.degree (B j)=q := (cd j).trans (by rcases half with rfl|rfl <;> omega)
  have named := OddHalfPartition.column_block (v:=v) (sourceLaws _) A T B (fun _ _ => by simp only [B,decide_eq_true_eq]; rfl) deg
  let side := fun j => B j iA
  have bit (i j x y) : B j i=B y x ↔ c (atPoint A i) (atPoint T j)=c (atPoint A x) (atPoint T y) := by
    rcases pal i j with h|h <;> rcases pal x y with g|g <;> simp [B,c,h,g,vw,Ne.symm vw]
  have key (i j) : B i=B j ↔ side i=side j := by
    refine ⟨fun h => congrFun h iA,fun h => funext fun k => (bit k i k j).mpr ?_⟩
    exact (reverse (shape a)).2 (A iA) (T i) (T j) ((bit iA i iA j).mp h) (A k)
  have coh : Block T T T T (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j)) := by
    intro i j x y h; simpa only [←key] using named h
  have sur : Function.Surjective side := by
    have sz : (Finset.univ.filter (fun i => side i=true)).card=5 := rd iA
    intro b
    by_contra no
    have ne (i : Fin 10) : side i≠b := fun h => no ⟨i,h⟩
    cases b with
    | false =>
      have all (i : Fin 10) : side i=true := by
        cases h : side i with
        | false => exact (ne i h).elim
        | true => rfl
      simp [all] at sz
    | true =>
      have emp : Finset.univ.filter (fun i : Fin 10 => side i=true)=∅ :=
        Finset.filter_eq_empty_iff.mpr fun i _ => ne i
      rw [emp] at sz
      contradiction
  apply useAnchor a
  intro i z h j
  obtain ⟨E⟩ := shore j.val (sizes j)
  have same : side (T.symm i)=side (T.symm z) := (bit iA _ iA _).mpr (by
    simpa only [atA,atPoint,Equiv.apply_symm_apply] using (Relations.transpose _ h))
  simpa only [atPoint,Equiv.apply_symm_apply] using
    even_rows half T E side sur coh (T.symm i) (T.symm z) same (E.symm ⟨j.val,rfl⟩)

theorem extend {l : Nat} (T : Shore (source G) l (Fin 10)) (keep : Nat → Prop) (old : Realizes p keep)
    (base : Region (source G) keep)
    (sizes : ∀ i : Region (source G) keep, (fiber G i.val).card=4) : Realizes p (fun t => keep t ∨ t=l) := by
  apply extend_common p (q:=2) (Or.inl rfl) T keep old base sizes
  intro a
  obtain ⟨A⟩ := shore a.val (sizes a)
  exact reverse (FourByEven.rectangle (sourceLaws _) A T (Or.inl rfl))

theorem realize (reg : Nat → Prop) (total : (vertices (source G) reg).card=22)
    (ten : ∃ x, reg (source G x x) ∧ (fiber G x).card=10)
    (sizes : ∀ i, reg (source G i i) → (fiber G i).card=4 ∨ (fiber G i).card=10)
    (unique : ∀ i j, reg (source G i i) → reg (source G j j) → (fiber G i).card=10 →
      (fiber G j).card=10 → source G i i=source G j j) : Realizes p reg := by
  classical
  obtain ⟨x,hx,sx⟩ := ten
  obtain ⟨T⟩ := shore x sx
  let c := source G
  let l := c x x
  let keep := fun t => reg t ∧ t≠l
  have parts : vertices c reg=vertices c keep ∪ vertices c (·=l) := by
    ext i
    simp only [mem_vertices,Finset.mem_union,keep]
    by_cases eq : c i i=l
    · have ir : reg (c i i) := (congrArg reg eq).mpr hx
      simp [eq,hx,l] at * <;> tauto
    · simp [eq]
  have dis : Disjoint (vertices c keep) (vertices c (·=l)) :=
    Finset.disjoint_left.mpr fun i h k => ((mem_vertices _ _ _).mp h).2 ((mem_vertices _ _ _).mp k)
  have nKeep : (vertices c keep).card=12 := by
    rw [parts,Finset.card_union_of_disjoint dis,RegionalTwoAnchor.card T] at total
    omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (nKeep.symm ▸ (by decide : 0<12))
  have small := LargeOrderBlocks.small p keep (nKeep.le.trans (by decide))
  apply RegionalFourFourEight.restrict_map p (extend p T keep small ⟨b,hb⟩ (fun i => ?_))
  · intro i hi; by_cases eq : c i i=l
    · exact Or.inr eq
    · exact Or.inl ⟨hi,eq⟩
  · obtain ⟨ir,ne⟩ := (mem_vertices c keep i.val).mp i.property
    exact (sizes i.val ir).resolve_right (fun s => ne (unique i.val x ir hx s sx))

end QGI.Coherent.OddShoreAttachment
