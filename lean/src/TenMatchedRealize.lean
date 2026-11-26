import TenMatchedDetect
import RegionalSignatureBound

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross TenPointCross.MatchedCatalog SmallUnion SmallFiberExtension StrategyColorLaws
open SixTenCoordinates (Shore atPoint commonLaws targetLaws)
open Intertwiner (U)
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
abbrev Site := V ⊕ V
def points {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l V) (Y : Shore c r V) : Site → Fin n :=
  Sum.elim (atPoint F) (atPoint Y)
private theorem indices {n k l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l V) (Y : Shore c r V)
    (f : Fin k → Fin n) (cover : ∀ i, c (f i) (f i)=l ∨ c (f i) (f i)=r) : ∃ s : Fin k → Site, ∀ i, points F Y (s i)=f i := by
  have pick (i : Fin k) : ∃ s : Site, points F Y s=f i := by
    rcases cover i with h|h
    · obtain ⟨x,hx⟩ := (range F _).mpr h; exact ⟨.inl x,hx⟩
    · obtain ⟨x,hx⟩ := (range Y _).mpr h; exact ⟨.inr x,hx⟩
  exact Classical.axiomOfChoice pick

private def tag (a b : V → Q) : Site → Q ⊕ Q := Sum.map a b
private theorem tag_short {n k l r v : Nat} {c : Fin n → Fin n → Nat} {F : Shore c l V} {Y : Shore c r V}
    (S : Pairs F Y v) (f : Fin k → Fin n) (inj : Function.Injective f) (e : Fin k → Site)
    (he : ∀ i, points F Y (e i)=f i) (t : Q⊕Q) :
    (Finset.univ.filter (fun i => (tag S.left S.right ∘ e) i=t)).card≤3 := by
  rcases t with q|q
  · refine (RegionalSignatureBound.bound_set f inj (atPoint F) _ _ ?_).trans ((S.left_two q).le.trans (by decide))
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have eq := he i
    cases pt : e i with
    | inr x => simp [Function.comp_apply,pt,tag] at h
    | inl x =>
      rw [pt] at eq
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Sum.inl.inj (by simpa only [Function.comp_apply,pt,tag,Sum.map_inl] using h)⟩,eq⟩
  · refine (RegionalSignatureBound.bound_set f inj (atPoint Y) _ _ ?_).trans ((S.right_two q).le.trans (by decide))
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have eq := he i
    cases pt : e i with
    | inl x => simp [Function.comp_apply,pt,tag] at h
    | inr x =>
      rw [pt] at eq
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Sum.inr.inj (by simpa only [Function.comp_apply,pt,tag,Sum.map_inr] using h)⟩,eq⟩

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (F : Shore (source G) l V) (Y : Shore (source G) r V)

theorem detected (lr : l≠r) (S : Pairs F Y v) (rich : Detects F S.left) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  classical
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) l V := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let Z : Shore (targetName p) r V := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨e,_,old⟩ := SmallShore.realize_at p (by decide : 0<10) (by decide) (atPoint F) (atPoint W) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp W.injective) (range F) (range W) 0 0
  let T := e.trans W
  obtain ⟨D,dl⟩ := transport (T:=T) (Z:=Z) S (commonLaws p) (targetLaws p) old
  obtain ⟨ξ,π,rep,nz,hr,probe⟩ := fixed_labels p F Y T Z S D dl old rich
  let a := tag S.left S.right
  let b := tag (π.symm ∘ D.left) (π.symm ∘ D.right)
  have compatible (s t : Site) (act : U p (points F Y s) (points T Z t) ξ≠0) : a s=b t := by
    rcases s with i|j <;> rcases t with x|y
    · obtain ⟨z,label,h⟩ := probe _ _ act (S.left i)
      have eq := (internal S D (commonLaws p) h).mp (hr _).symm
      exact congrArg Sum.inl ((π.symm_apply_eq).mpr (eq.trans (by rw [dl,label]))).symm
    · exact (lr ((F i).property.symm.trans ((DoubledEdges.diag_of_nonzero p act).trans (Z y).property))).elim
    · exact (lr ((T x).property.symm.trans ((DoubledEdges.diag_of_nonzero p act).symm.trans (Y j).property))).elim
    · obtain ⟨z,label,h⟩ := probe _ _ act (S.right j)
      have sourceCell := (S.member_iff (rep (S.right j)) j).mpr (hr _)
      have hex := common_transpose p h
      have targetCell := (D.member_iff z y).mp (hex.symm.trans sourceCell)
      exact congrArg Sum.inr ((π.symm_apply_eq).mpr (targetCell.symm.trans (by rw [dl,label]))).symm
  refine LargeOrderBlocks.of_solver p reg ?_ rfl ?_
  · intro i h; rcases cover i h with u|u
    · rw [u,LargeFourteenRegion.large,RegionalTwoAnchor.card F]; decide
    · rw [u,LargeFourteenRegion.large,RegionalTwoAnchor.card Y]; decide
  intro f g data
  have inc (i) := cover _ ((data.src _).mp ⟨i,rfl⟩)
  obtain ⟨s,hs⟩ := indices F Y f inc
  obtain ⟨t,ht⟩ := indices T Z g (fun i => data.sameDiag i ▸ inc i)
  apply SmallVectorCells.of_partition (RegionalTernaryChoice.vector_data p data ξ nz) (a ∘ s) (b ∘ t)
  · intro i j act; apply compatible; rwa [hs,ht]
  · intro q
    refine Nat.le_trans (Nat.le_of_eq ?_) (tag_short S f data.injF s hs q)
    apply congrArg Finset.card; ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl

end QGI.Coherent.TenPointMatched
