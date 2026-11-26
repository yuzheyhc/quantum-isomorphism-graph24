import RegionalEightTwelveOperators

noncomputable section
namespace QGI.Coherent.RegionalEightTwelve
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates RegionalEightTwelveGeometry RegionalEightTwelveStats
open RegionalEightTwelveOperators SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private embed rows from RegionalEightTwelveEdges
open private range from RegionalSixTwelveDispatch

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem of_disconnected_simple {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) (simple : Function.Injective (family F Y v))
    (split : ¬crosses (Finset.univ.image (family F Y v))) : Realizes p reg := by
  classical
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l Point := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let W : Shore (targetName p) r Index := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨h,_,names⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide) (atPoint Y) (atPoint W) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp W.injective) (range Y) (range W) 0 0
  let Z := h.trans W
  let a := family F Y v
  let b := family T Z v
  have gram (i j) : (a i∩a j).card=(b i∩b j).card := mixed_counts (commonLaws p) F Y T Z v v (names i j)
  have st := degrees (sourceLaws _) F Y v
  have aw (j) : (a j).card=2 := (st.1 j).trans weight
  have bw (i) : (b i).card=2 := (by simpa only [Finset.inter_self] using (gram i i).symm : (b i).card=(a i).card).trans (aw i)
  have ad : (incident a 0).card=3 := by
    have z := st.2.2
    rw [weight] at z
    change 12*2=8*(incident a 0).card at z
    omega
  have bt : Function.Injective b := by
    intro j k eq
    apply simple
    have same := gram j k
    rw [eq,Finset.inter_self,bw] at same
    exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (same.trans (aw j).symm).ge).symm.trans
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (same.trans (aw k).symm).ge)
  obtain ⟨part,same,clique⟩ := disconnected_cliques a aw simple (fun i => (st.2.1 i).trans ad) split
  choose x y neq edge using fun j => Finset.card_eq_two.mp (aw j)
  have present : ∃ t i, color F Y t i=v :=
    ⟨0,x 0,(Finset.mem_filter.mp (show x 0 ∈ a 0 by rw [edge]; simp)).2⟩
  have eqSide (j) : part (x j)=part (y j) := same j _ _ (by rw [edge]; simp) (by rw [edge]; simp)
  have ll (i j : Point) (eq : part i=part j) (z w : Fin n) : Commute (U p (atPoint F i) z) (U p (atPoint F j) w) := by
    by_cases ij : i=j
    · subst j; by_cases zw : z=w
      · subst w; exact Commute.refl _
      · exact (magic_orthogonal p _ z w zw).1.trans (magic_orthogonal p _ w z (Ne.symm zw)).1.symm
    obtain ⟨k,hk⟩ := clique i j eq ij
    have h := rows (sourceLaws _) F Y v present k
    change FourTwelveCycle.neighbors (source G) v (atPoint Y k)=(a k).map (embed F) at h
    rw [hk,Finset.map_insert,Finset.map_singleton] at h
    exact adjacent_commute p ((embed F).injective.ne ij) h z w
  let pts : Point ⊕ Index → Fin n := Sum.elim (atPoint F) (atPoint Y)
  let side : Point ⊕ Index → Bool := Sum.elim part (part ∘ x)
  have lr (i : Point) (j : Index) (eq : part i=part (x j)) (z w : Fin n) :
      Commute (U p (atPoint F i) z) (U p (atPoint Y j) w) :=
    edge_commutes p F Y T Z bw bt (neq j) (edge j) _ (ll i (x j) eq z) (ll i (y j) (eq.trans (eqSide j)) z) w
  apply RegionalEightTwelveAtoms.realize p pts side (atPoint F 0) reg
  · intro s
    rcases cover _ ((mem_vertices _ _ _).mp s.property) with left|right
    · obtain ⟨i,hi⟩ := (range F _).mpr left; exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := (range Y _).mpr right; exact ⟨.inr i,hi⟩
  · intro a b eq z w
    cases a with
    | inl i => cases b with | inl j => exact ll i j eq z w | inr j => exact lr i j eq z w
    | inr i => cases b with
      | inl j => exact (lr j i eq.symm w z).symm
      | inr j =>
        change part (x i)=part (x j) at eq
        exact edge_commutes p F Y T Z bw bt (neq j) (edge j) _
          (fun a => (lr (x j) i eq.symm a z).symm) (fun a => (lr (y j) i (eq.trans (eqSide j)).symm a z).symm) w

/-- A genuine simple edge color on the eight vertices realizes all other
names in an arbitrary ambient graph, including refinements of its complement. -/
theorem of_simple {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) (simple : Function.Injective (family F Y v)) : Realizes p reg := by
  by_cases con : crosses (Finset.univ.image (family F Y v))
  · exact of_connected_simple p F Y reg cover weight simple con
  · exact of_disconnected_simple p F Y reg cover weight simple con

end QGI.Coherent.RegionalEightTwelve

