import SmallFiberExtension

noncomputable section
namespace QGI.Coherent.SixSixAttachment
open StrategyColorLaws SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

/-- A named map on the retained region extends through an interface on
which two prescribed points distinguish row types. An entry of the
interface must distinguish each new column up to equality on the whole
retained region. This allows repeated columns and nonsingleton colors. -/
theorem attach (old mark : Nat → Prop) {a s : Nat} (ha : old a)
    (hsize : (vertices (source G) (fun t => t=a ∨ t=s)).card ≤ 13)
    (r₀ r₁ : Fin n) (d₀ : source G r₀ r₀=a) (d₁ : source G r₁ r₁=a)
    (rows : ∀ i j, source G i i=a → source G j j=a →
      source G r₀ i=source G r₀ j → source G r₁ i=source G r₁ j →
      ∀ k, source G k k=s → mark (source G i k) → source G i k=source G j k)
    (columns : ∀ k, source G k k=s → ∃ b, source G b b=a ∧ mark (source G b k) ∧
      ∀ z, source G b z=source G b k → ∀ i, old (source G i i) → source G i z=source G i k)
    (given : Realizes p old) : Realizes p (fun t => old t ∨ t=s) := by
  classical
  let c := source G
  let d := targetName p
  let pair := fun t : Nat => t=a ∨ t=s
  let total := fun t : Nat => old t ∨ t=s
  let inOld (x : Fin n) (h : old (c x x)) : Region c old := ⟨x,(mem_vertices _ _ _).mpr h⟩
  let inPair (x : Fin n) (h : pair (c x x)) : Region c pair := ⟨x,(mem_vertices _ _ _).mpr h⟩
  obtain ⟨e,he⟩ := given
  let a₀ := inOld r₀ ((congrArg old d₀).mpr ha)
  let a₁ := inOld r₁ ((congrArg old d₁).mpr ha)
  let b₀ := inPair r₀ (Or.inl d₀)
  let b₁ := inPair r₁ (Or.inl d₁)
  let t₀ : Region d pair := ⟨(e a₀).val,(mem_vertices _ _ _).mpr (Or.inl ((he a₀ a₀).symm.trans d₀))⟩
  let t₁ : Region d pair := ⟨(e a₁).val,(mem_vertices _ _ _).mpr (Or.inl ((he a₁ a₁).symm.trans d₁))⟩
  obtain ⟨t,h₀,h₁,ht⟩ := realize_region_pair p pair (Finset.card_pos.mpr ⟨r₀,b₀.property⟩)
    hsize b₀ b₁ t₀ t₁ (he a₀ a₁)
  have ref₀ : (t b₀).val=(e a₀).val := congrArg Subtype.val h₀
  have ref₁ : (t b₁).val=(e a₁).val := congrArg Subtype.val h₁
  have aligned (i k : Fin n) (hi : c i i=a) (hk : c k k=s) (marked : mark (c i k)) :
      c i k = d (e (inOld i (hi ▸ ha))).val (t (inPair k (Or.inr hk))).val := by
    let v := inOld i (hi ▸ ha)
    let w : Region d pair := ⟨(e v).val,(mem_vertices _ _ _).mpr (Or.inl ((he v v).symm.trans hi))⟩
    let j := t.symm w
    have tj : (t j).val=(e v).val := congrArg Subtype.val (t.apply_symm_apply w)
    have dj : c j.val j.val=a := (ht j j).trans (by rw [tj]; exact (he v v).symm.trans hi)
    have eq₀ : c r₀ i = c r₀ j.val := (he a₀ v).trans (by rw [←ref₀,←tj]; exact (ht b₀ j).symm)
    have eq₁ : c r₁ i = c r₁ j.val := (he a₁ v).trans (by rw [←ref₁,←tj]; exact (ht b₁ j).symm)
    exact (rows i j.val hi dj eq₀ eq₁ k hk marked).trans ((ht j (inPair k (Or.inr hk))).trans (by rw [tj]))
  have mixed (i k : Fin n) (hi : old (c i i)) (hk : c k k=s) :
      c i k=d (e (inOld i hi)).val (t (inPair k (Or.inr hk))).val := by
    obtain ⟨b,hb,marked,select⟩ := columns k hk
    let ib := inOld b ((congrArg old hb).mpr ha)
    have pairName := he (inOld i hi) ib
    obtain ⟨z,iz,zb⟩ := PartialFunctional.middle d c
      (fun u v => (common_products p u v pairName).symm) (t (inPair k (Or.inr hk))).val
    have bz : c b z = c b k :=
      (common_transpose p zb.symm).trans (aligned b k hb hk marked).symm
    exact (select z bz i hi).symm.trans iz.symm
  let newName (x : Region c total) (h : ¬old (c x.val x.val)) : c x.val x.val=s :=
    ((mem_vertices _ _ _).mp x.property).resolve_left h
  let out (x : Region c total) := if h : old (c x.val x.val) then (e (inOld x.val h)).val
    else (t (inPair x.val (Or.inr (newName x h)))).val
  have all (i j : Region c total) : c i.val j.val=d (out i) (out j) := by
    by_cases hi : old (c i.val i.val) <;> by_cases hj : old (c j.val j.val)
    · simpa only [out,dif_pos hi,dif_pos hj] using he (inOld _ hi) (inOld _ hj)
    · simpa only [out,dif_pos hi,dif_neg hj] using mixed _ _ hi (newName j hj)
    · simpa only [out,dif_neg hi,dif_pos hj] using common_transpose p (mixed _ _ hj (newName i hi))
    · simpa only [out,dif_neg hi,dif_neg hj] using ht
        (inPair i.val (Or.inr (newName i hi))) (inPair j.val (Or.inr (newName j hj)))
  obtain ⟨f,hf⟩ := bundle p total out all
  exact ⟨f,fun i j => (all i j).trans (congrArg₂ d (hf i).symm (hf j).symm)⟩

end QGI.Coherent.SixSixAttachment
