import SixNineTriples

noncomputable section
namespace QGI.Coherent.SixNineAttachments
open Relations SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private narrow from TwoAnchorUnionGlue

private def cell {n : Nat} (c : Table n) (s : Nat) : ThreeRectangleExtension.Cell c s ≃ {x // c x x=s} :=
  Equiv.subtypeEquivRight (fun x => mem_vertices c (·=s) x)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

/-- Attach a nine-point fiber to a named exterior along three rectangles.
Only one other exterior fiber is present and its cross color is constant. -/
theorem attach_keep {r v : Nat} (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9))
    (reg keep : Nat → Prop) (hr : keep r)
    (cover : ∀ i, reg (source G i i) → keep (source G i i) ∨ source G i i=v)
    (uniform : ∀ i j a b, keep (source G i i) → source G i i≠r → source G j j=v →
      source G a a=source G i i → source G b b=source G j j → source G i j=source G a b)
    (old : Realizes p keep) (v₀ : Nat) (A : Fin 6 → Fin 3) (B : Fin 9 → Fin 3)
    (oa : Function.Surjective A) (ob : Function.Surjective B)
    (rect : ∀ i j, source G (atPoint S i) (atPoint Y j)=v₀ ↔ A i=B j)
    (wt : ∀ j k, B j=B k → ∀ i, source G (atPoint S i) (atPoint Y j)=source G (atPoint S i) (atPoint Y k)) : Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  obtain ⟨f,hf⟩ := old
  let sub := narrow f hf hr
  let fc := (cell c r).trans (sub.trans (cell d r).symm)
  let inOld (i : ThreeRectangleExtension.Cell c r) : Region c keep :=
    ⟨i.val,(mem_vertices c keep i.val).mpr (by
      have hi : c i.val i.val=r := (mem_vertices c (·=r) i.val).mp i.property
      rwa [hi])⟩
  have fcNames (i j : ThreeRectangleExtension.Cell c r) : c i.val j.val=d (fc i).val (fc j).val := hf (inOld i) (inOld j)
  let ix := (cell c r).trans S.symm
  let iy := (cell c v).trans Y.symm
  have ls (i) : atPoint S (ix i)=i.val := congrArg Subtype.val (S.apply_symm_apply _)
  have rs (j) : atPoint Y (iy j)=j.val := congrArg Subtype.val (Y.apply_symm_apply _)
  obtain ⟨g,hg,cross⟩ := ThreeRectangleExtension.three_map p (s:=v) ((RegionalTwoAnchor.card Y).trans_le (by decide))
    (A ∘ ix) (B ∘ iy) (oa.comp ix.surjective) (ob.comp iy.surjective)
    (fun i j => by simpa only [ls,rs,Function.comp_apply] using rect (ix i) (iy j))
    (fun j k h i => by simpa only [ls,rs] using wt _ _ h (ix i)) fc fcNames
  apply RegionalFourFourEight.restrict_map p (ThreeRectangleExtension.merge_maps p keep v f g hf hg (fun i j => ?_))
  · exact cover
  · by_cases hy : c i.val i.val=r
    · let k : ThreeRectangleExtension.Cell c r := ⟨i.val,(mem_vertices _ _ _).mpr hy⟩
      exact cross k j
    · obtain ⟨a,b,hit⟩ := StrategyColors.exists_source p (f i).val (g j).val
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨ha,hb⟩ := SmallShore.endpoints p eq
      have jv : c j.val j.val=v := (mem_vertices _ _ _).mp j.property
      exact (uniform _ _ _ _ ((mem_vertices _ _ _).mp i.property) hy jv (ha.trans (hf i i).symm) (hb.trans (hg j j).symm)).trans eq

theorem attach {k l r v : Nat} [NeZero k] (F : Shore (source G) l (Fin k))
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9)) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (uniform : ∀ i j, source G i i=l → source G j j=v → source G i j=source G (atPoint F 0) (atPoint Y 0))
    (small46 : Realizes p (fun t => t=l ∨ t=r)) (v₀ : Nat) (A : Fin 6 → Fin 3) (B : Fin 9 → Fin 3)
    (oa : Function.Surjective A) (ob : Function.Surjective B)
    (rect : ∀ i j, source G (atPoint S i) (atPoint Y j)=v₀ ↔ A i=B j)
    (wt : ∀ j k, B j=B k → ∀ i, source G (atPoint S i) (atPoint Y j)=source G (atPoint S i) (atPoint Y k)) : Realizes p reg := by
  apply attach_keep p S Y reg (fun t => t=l ∨ t=r) (Or.inr rfl) _ _ small46 v₀ A B oa ob rect wt
  · intro i h; rcases cover i h with h|h|h <;> tauto
  · intro i j a b hi no jv ai bj
    have hl := hi.resolve_right no
    exact (uniform _ _ hl jv).trans (uniform _ _ (ai.trans hl) (bj.trans jv)).symm

end QGI.Coherent.SixNineAttachments
