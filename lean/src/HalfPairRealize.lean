import HalfPairOperators
import RegionalSignatureBound

noncomputable section
namespace QGI.Coherent.HalfPair
open EightTwelveHalf RegionalEightTwelveStats SixTenCoordinates StrategyColorLaws SmallUnion SmallFiberExtension
open Intertwiner (U)
open RegionalEightTwelveHalfLaws (J)
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
private theorem filter_cards {X : Type} [Fintype X] {u v : X → Prop} {du : DecidablePred u} {dv : DecidablePred v}
    (h : ∀ i, u i ↔ v i) : (@Finset.filter X u du Finset.univ).card=(@Finset.filter X v dv Finset.univ).card := by
  apply congrArg Finset.card
  ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact h i

private theorem coordinates {n k l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l P) (Y : Shore c r J)
    (f : Fin k → Fin n) (h : ∀ i, c (f i) (f i)=l ∨ c (f i) (f i)=r) :
    ∃ s : Fin k → P⊕J, ∀ i, Sum.elim (atPoint F) (atPoint Y) (s i)=f i := by
  have ex (i) : ∃ t : P⊕J, Sum.elim (atPoint F) (atPoint Y) t=f i := by
    rcases h i with hl|hr
    · obtain ⟨a,ha⟩ := (range F _).mpr hl; exact ⟨.inl a,ha⟩
    · obtain ⟨a,ha⟩ := (range Y _).mpr hr; exact ⟨.inr a,ha⟩
  exact Classical.axiomOfChoice ex

private def srcTag {A : J → C} (L : Layout A) : P⊕J → Label⊕Finset Label :=
  Sum.elim (Sum.inl ∘ L.label) (Sum.inr ∘ L.pattern)

private theorem tag_small {A : J → C} (L : Layout A) {n k l r : Nat} {c : Fin n → Fin n → Nat}
    (F : Shore c l P) (Y : Shore c r J) (f : Fin k → Fin n) (fi : Function.Injective f)
    (s : Fin k → P⊕J) (hs : ∀ i, Sum.elim (atPoint F) (atPoint Y) (s i)=f i)
    (q : Label⊕Finset Label) : (Finset.univ.filter (fun i => srcTag L (s i)=q)).card≤3 := by
  classical
  cases q with
  | inl a =>
    refine (RegionalSignatureBound.bound_set f fi (atPoint F) _ (Finset.univ.filter (fun x => L.label x=a)) ?_).trans ((L.two a).le.trans (by decide))
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have e := hs i
    cases eq : s i with
    | inl x =>
      rw [eq] at e h
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Sum.inl.inj h⟩,e⟩
    | inr x => rw [eq] at h; contradiction
  | inr w =>
    let V := Finset.univ.filter (fun j => L.pattern j=w)
    have few : V.card≤3 := by
      by_cases used : V.Nonempty
      · obtain ⟨j,hj⟩ := used
        simpa only [V,(Finset.mem_filter.mp hj).2] using L.small j
      · rw [Finset.not_nonempty_iff_eq_empty.mp used,Finset.card_empty]; decide
    apply (RegionalSignatureBound.bound_set f fi (atPoint Y) _ V ?_).trans few
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have e := hs i
    cases eq : s i with
    | inl x => rw [eq] at h; contradiction
    | inr j =>
      rw [eq] at e h
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Sum.inr.inj h⟩,e⟩

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K) (F : Shore (source G) l P) (Y : Shore (source G) r J)

theorem realize (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (L : Layout (family F Y v)) (size : ∀ j,(family F Y v j).card=4) : Realizes p reg := by
  classical
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) l P := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let Z : Shore (targetName p) r J := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨e,_,he⟩ := SmallShore.realize_at p (by decide : 0<8) (by decide) (atPoint F) (atPoint W) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp W.injective) (range F) (range W) 0 0
  let T := e.trans W
  have transport := transport p F Y T Z v L size he
  obtain ⟨ξ,π,rep,nz,hr,probe⟩ := vector_labels p F Y T Z v L transport
  let B := family T Z v
  let toSet (y : J) := Finset.univ.filter fun i => rep (π i)∈B y
  let tgtTag : P⊕J → Label⊕Finset Label := Sum.elim (fun x => Sum.inl (π.symm (L.label x))) (fun y => Sum.inr (toSet y))
  have lr : l≠r := by
    intro h; have a := RegionalTwoAnchor.card F; have b := RegionalTwoAnchor.card Y; rw [h] at a; omega
  have compatible (s t : P⊕J)
      (act : U p (Sum.elim (atPoint F) (atPoint Y) s) (Sum.elim (atPoint T) (atPoint Z) t) ξ≠0) :
      srcTag L s=tgtTag t := by
    cases s with
    | inl i =>
      cases t with
      | inl x =>
        obtain ⟨z,hz,eq⟩ := probe _ _ act (L.label i)
        have h := (transport.internal _ _ _ _ eq).mp (hr _).symm
        exact congrArg Sum.inl ((π.symm_apply_eq).mpr (h.trans hz)).symm
      | inr y => exact (lr ((F i).property.symm.trans ((DoubledEdges.diag_of_nonzero p act).trans (Z y).property))).elim
    | inr j =>
      cases t with
      | inl x => exact (lr ((T x).property.symm.trans ((DoubledEdges.diag_of_nonzero p act).symm.trans (Y j).property))).elim
      | inr y =>
        apply congrArg Sum.inr
        ext i
        obtain ⟨x,hx,eq⟩ := probe _ _ act i
        have same : rep i∈family F Y v j ↔ x∈B y := by
          simp only [B,family,Finset.mem_filter,Finset.mem_univ,true_and]
          change (source G (atPoint Y j) (atPoint F (rep i))=v ↔ targetName p (atPoint Z y) (atPoint T x)=v)
          exact ⟨fun h => eq.symm.trans h,fun h => eq.trans h⟩
        simpa only [toSet,Finset.mem_filter,Finset.mem_univ,true_and,hr] using
          (L.mark j (rep i)).symm.trans (same.trans (transport.constant (hx.trans (hr _).symm) y))
  refine LargeOrderBlocks.of_solver p reg ?_ rfl ?_
  · intro i h; rcases cover i h with a|b
    · rw [a,LargeFourteenRegion.large,RegionalTwoAnchor.card F]; decide
    · rw [b,LargeFourteenRegion.large,RegionalTwoAnchor.card Y]; decide
  intro f g data
  have included (i) := cover _ ((data.src _).mp ⟨i,rfl⟩)
  obtain ⟨s,hs⟩ := coordinates F Y f included
  obtain ⟨t,ht⟩ := coordinates T Z g (fun i => data.sameDiag i ▸ included i)
  apply SmallVectorCells.of_partition (RegionalTernaryChoice.vector_data p data ξ nz) (srcTag L ∘ s) (tgtTag ∘ t)
  · intro i j act; apply compatible; rwa [hs,ht]
  · intro q
    refine Nat.le_trans (Nat.le_of_eq ?_) (tag_small L F Y f data.injF s hs q)
    exact filter_cards (fun _ => Iff.rfl)

end QGI.Coherent.HalfPair
