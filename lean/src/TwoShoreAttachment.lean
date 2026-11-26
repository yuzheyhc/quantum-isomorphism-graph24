import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.TwoShoreAttachment
open SmallFiberExtension SmallUnion StrategyColorLaws FiberPairExtension
open FourTwelveFunctional (source)
open private rectangle from FiberPairExtension
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

/-- Attach two fibers of combined size at most thirteen to a named region.
Twin rectangles meet a single old fiber. All other external rectangles are uniform. -/
theorem attach {l₀ l₁ r : Nat} (x z : Fin n) (hx : source G x x=l₀) (hz : source G z z=l₁)
    (small : (vertices (source G) (fun s => s=l₀ ∨ s=l₁)).card≤13)
    (keep : Nat → Prop) (old : Realizes p keep) (y : Region (source G) keep) (hy : source G y.val y.val=r)
    (first : twins (source G) l₀ r) (second : twins (source G) l₁ r)
    (uniform : ∀ (i j a b : Fin n), (source G i i=l₀ ∨ source G i i=l₁) → keep (source G j j) →
      source G j j≠r → source G a a=source G i i → source G b b=source G j j → source G i j=source G a b) :
    Realizes p (fun t => (t=l₀ ∨ t=l₁) ∨ keep t) := by
  classical
  let c := source G
  let d := targetName p
  let s := fun t => t=l₀ ∨ t=l₁
  let total := fun t => s t ∨ keep t
  obtain ⟨e,he⟩ := old
  obtain ⟨b₀,hx₀,_⟩ := PartialFunctional.middle c d (fun a b => common_products p a b (he y y)) x
  obtain ⟨b₁,h₀₁,h₁y⟩ := PartialFunctional.middle c d (fun a b => common_products p a b (common_transpose p hx₀)) z
  let a₀ : Region c s := ⟨x,(mem_vertices _ _ _).mpr (Or.inl hx)⟩
  let a₁ : Region c s := ⟨z,(mem_vertices _ _ _).mpr (Or.inr hz)⟩
  let t₀ : Region d s := ⟨b₀,(mem_vertices _ _ _).mpr (Or.inl ((SmallShore.endpoints p hx₀).2.symm.trans hx))⟩
  let t₁ : Region d s := ⟨b₁,(mem_vertices _ _ _).mpr (Or.inr ((SmallShore.endpoints p h₀₁).2.symm.trans hz))⟩
  obtain ⟨f,i₀,i₁,hf⟩ := realize_region_pair p s (Finset.card_pos.mpr ⟨_,a₀.property⟩) small a₀ a₁ t₀ t₁ h₀₁
  have across (a : Region c s) (j : Region c keep) : c a.val j.val=d (f a).val (e j).val := by
    by_cases hr : c j.val j.val=r
    · have propagate {t : Nat} (atA : Region c s) (tag : c atA.val atA.val=t) (includeT : s t)
          (anchor : c atA.val y.val=d (f atA).val (e y).val) (shape : twins c t r)
          (h : c a.val a.val=t) : c a.val j.val=d (f a).val (e j).val := by
        let take (u : Cell c t) : Region c s := ⟨u.val,(mem_vertices _ _ _).mpr ((congrArg s u.property).mpr includeT)⟩
        let out (u : Cell c t) : Cell d t := ⟨(f (take u)).val,(hf (take u) (take u)).symm.trans u.property⟩
        exact rectangle p Subtype.val (fun v => (e v).val) out (fun u v => hf (take u) (take v)) he
          ⟨atA.val,tag⟩ y hy anchor shape ⟨a.val,h⟩ j hr
      rcases (mem_vertices _ _ _).mp a.property with h|h
      · exact propagate a₀ hx (Or.inl rfl) (by rw [i₀]; exact common_transpose p hx₀) first h
      · exact propagate a₁ hz (Or.inr rfl) (by rw [i₁]; exact h₁y) second h
    · obtain ⟨u,v,act⟩ := StrategyColors.exists_source p (f a).val (e j).val
      have eq := (associated p).mpr (StrategyColors.maps_support p act)
      obtain ⟨du,dv⟩ := SmallShore.endpoints p eq
      exact (uniform _ _ _ _ ((mem_vertices _ _ _).mp a.property) ((mem_vertices _ _ _).mp j.property) hr
        (du.trans (hf a a).symm) (dv.trans (he j j).symm)).trans eq
  let X := Region c total
  let A (i : X) (h : s (c i.val i.val)) : Region c s := ⟨i.val,(mem_vertices _ _ _).mpr h⟩
  let B (i : X) (h : ¬s (c i.val i.val)) : Region c keep :=
    ⟨i.val,(mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp i.property).resolve_left h)⟩
  let out (i : X) := if h : s (c i.val i.val) then (f (A i h)).val else (e (B i h)).val
  have named (i j : X) : c i.val j.val=d (out i) (out j) := by
    by_cases hi : s (c i.val i.val) <;> by_cases hj : s (c j.val j.val)
    · simpa only [out,dif_pos hi,dif_pos hj] using hf (A i hi) (A j hj)
    · simpa only [out,dif_pos hi,dif_neg hj] using across (A i hi) (B j hj)
    · simpa only [out,dif_neg hi,dif_pos hj] using common_transpose p (across (A j hj) (B i hi))
    · simpa only [out,dif_neg hi,dif_neg hj] using he (B i hi) (B j hj)
  obtain ⟨g,hg⟩ := bundle p total out named
  exact ⟨g,fun i j => by rw [hg,hg]; exact named i j⟩

end QGI.Coherent.TwoShoreAttachment
