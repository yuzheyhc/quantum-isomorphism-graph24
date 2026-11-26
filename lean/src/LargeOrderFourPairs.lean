import FiberPairExtension
import LargeOrderTetra

noncomputable section
namespace QGI.Coherent.LargeOrderFourPairs
open SmallUnion SmallFiberExtension StrategyColorLaws FiberPairExtension
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension
open private rectangle from FiberPairExtension

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

private def within {Q : Type} (a : Q → Fin 2 → Fin n) (q : Q) (s : Nat) : Prop :=
  s=source G (a q 0) (a q 0) ∨ s=source G (a q 1) (a q 1)

private theorem inside {Q : Type} (a : Q → Fin 2 → Fin n) (q : Q) (j : Fin 2) : within (G:=G) a q (source G (a q j) (a q j)) := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Prescribed compatible points in groups of one or two fibers extend to
the entire region if every interface between different groups has twins. -/
theorem synchronized {Q : Type} (reg : Nat → Prop) (a b : Q → Fin 2 → Fin n)
    (matched : ∀ q r i j, source G (a q i) (a r j)=targetName p (b q i) (b r j))
    (bound : ∀ q, (vertices (source G) (fun s =>
      s=source G (a q 0) (a q 0) ∨ s=source G (a q 1) (a q 1))).card≤13)
    (cover : ∀ x, reg (source G x x) → ∃ q j, source G x x=source G (a q j) (a q j))
    (cross : ∀ q r : Q, q≠r → ∀ i j, twins (source G) (source G (a q i) (a q i)) (source G (a r j) (a r j))) :
    Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  let S := within (G:=G) a
  let A (q : Q) (i : Fin 2) : Region c (S q) := ⟨a q i,(mem_vertices _ _ _).mpr (inside a q i)⟩
  let B (q : Q) (i : Fin 2) : Region d (S q) := ⟨b q i,(mem_vertices _ _ _).mpr
    ((congrArg (S q) (matched q q i i)).mp (inside a q i))⟩
  have pairs (q : Q) : ∃ e : Region c (S q) ≃ Region d (S q),
      (∀ i, e (A q i)=B q i) ∧ ∀ x y, c x.val y.val=d (e x).val (e y).val := by
    obtain ⟨e,h0,h1,ok⟩ := realize_region_pair p (S q) (Finset.card_pos.mpr ⟨_,(A q 0).property⟩)
      (bound q) (A q 0) (A q 1) (B q 0) (B q 1) (matched q q 0 1)
    exact ⟨e,fun i => by fin_cases i <;> assumption,ok⟩
  choose f same preservation using pairs
  let X := Region c reg
  have included (x : X) := cover x.val ((mem_vertices _ _ _).mp x.property)
  choose q j hk using included
  let member (x : X) : Region c (S (q x)) :=
    ⟨x.val,(mem_vertices _ _ _).mpr (by change S (q x) (source G x.val x.val); rw [hk x]; exact inside a _ _)⟩
  let image (x : X) := (f (q x) (member x)).val
  have shift {m t : Q} (eq : m=t) (z : Fin n) (hm : z∈vertices c (S m)) (ht : z∈vertices c (S t)) :
      (f m ⟨z,hm⟩).val=(f t ⟨z,ht⟩).val := by subst t; rfl
  have hit (x y : X) : c x.val y.val=d (image x) (image y) := by
    let m := q x
    let t := q y
    by_cases equal : m=t
    · let w : Region c (S m) := ⟨y.val,equal ▸ (member y).property⟩
      have ev : (f m w).val=image y := shift equal y.val w.property (member y).property
      rw [←ev]; exact preservation m (member x) w
    let l := c (a m (j x)) (a m (j x))
    let r := c (a t (j y)) (a t (j y))
    let take (z : Cell c l) : Region c (S m) := ⟨z.val,(mem_vertices _ _ _).mpr (z.property.symm ▸ inside a m (j x))⟩
    let chosen (z : Cell c l) : Cell d l := ⟨(f m (take z)).val,
      (preservation m (take z) (take z)).symm.trans z.property⟩
    let root : Cell c l := ⟨a m (j x),rfl⟩
    have ok : c root.val (A t (j y)).val=d (chosen root).val (f t (A t (j y))).val := by
      change c _ _=d (f m (A m (j x))).val (f t (A t (j y))).val
      rw [same,same]; exact matched m t (j x) (j y)
    exact rectangle p Subtype.val (fun z => (f t z).val) chosen
      (fun z w => preservation m (take z) (take w)) (preservation t) root (A t (j y)) rfl ok
      (cross m t equal (j x) (j y)) ⟨x.val,hk x⟩ (member y) (hk y)
  obtain ⟨e,he⟩ := bundle p reg image hit
  exact ⟨e,fun i j => by rw [he,he]; exact hit i j⟩

/-- On four fibers arranged in two pairs, all interactions across the cut
can be propagated from a single simultaneously matched point per fiber.
Inside each pair the prescribed two points extend by small separability. -/
theorem realize (reg : Nat → Prop) (a : Fin 2 → Fin 2 → Fin n)
    (bound : ∀ q, (vertices (source G) (fun s =>
      s=source G (a q 0) (a q 0) ∨ s=source G (a q 1) (a q 1))).card≤13)
    (cover : ∀ x, reg (source G x x) → ∃ q j, source G x x=source G (a q j) (a q j))
    (cross : ∀ q r : Fin 2, q≠r → ∀ i j, twins (source G) (source G (a q i) (a q i)) (source G (a r j) (a r j))) :
    Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  let idx : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv
  let u := fun k : Fin 4 => a (idx.symm k).1 (idx.symm k).2
  obtain ⟨v,hv⟩ := LargeOrderTetra.synchronize p u
  let b := fun (q j : Fin 2) => v (idx (q,j))
  have matched (q r i j : Fin 2) : c (a q i) (a r j)=d (b q i) (b r j) := by
    simpa only [u,idx.symm_apply_apply] using hv (idx (q,i)) (idx (r,j))
  exact synchronized p reg a b matched bound cover cross

end QGI.Coherent.LargeOrderFourPairs
