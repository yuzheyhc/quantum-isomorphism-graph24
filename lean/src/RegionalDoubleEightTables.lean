import DoubleEightQuantum
import SmallUnionRealization

noncomputable section
namespace QGI.Coherent.RegionalDoubleEight
open DoubleEight
open DoubleEight.ShoreCensus (V side Homogeneous)
open DoubleEight.MatchingExtension SmallUnion StrategyColorLaws
open private pull_products from CoherentDoubleEight
open private bank_size from DoubleEightQuantum

def Sizes (c : Table 16) := ∀ i, (Finset.univ.filter (fun j => c j j = c i i)).card=8
def Ends (c : Table 16) := ∀ i j u v, c i j=c u v → c i i=c u u ∧ c j j=c v v
def Sides (c : Table 16) (e : X ≃ Fin 16) :=
  ∀ u v, side u=side v ↔ c (e u) (e u)=c (e v) (e v)
def pull (c : Table 16) (e : X ≃ Fin 16) : Coloring := fun i j => c (e i) (e j)

private theorem frame (c : Table 16) (sizes : Sizes c) : ∃ e : X ≃ Fin 16, Sides c e := by
  classical
  let F (i : Fin 16) := Finset.univ.filter (fun j => c j j=c i i)
  let s := F 0
  have mem (i j) : i ∈ F j ↔ c i i=c j j := by simp [F]
  have lc : Fintype.card {x // x∈s}=8 := (Fintype.card_coe _).trans (sizes 0)
  have cc : sᶜ.card=8 := by rw [Finset.card_compl,Fintype.card_fin,show s.card=8 from sizes 0]
  have rc : Fintype.card {x : Fin 16 // x∉s}=8 := by
    simpa using (Fintype.card_subtype_compl (fun x => x∈s)).trans
      (show Fintype.card (Fin 16)-Fintype.card {x // x∈s}=8 by rw [lc]; decide)
  let l := Fintype.equivOfCardEq (show Fintype.card V=Fintype.card {x // x∈s} by simp [lc])
  let r := Fintype.equivOfCardEq (show Fintype.card V=Fintype.card {x : Fin 16 // x∉s} by simp [rc])
  let e := (Equiv.sumCongr l r).trans (Equiv.sumCompl (fun x => x∈s))
  have outside {a : Fin 16} (ha : a∉s) : F a=sᶜ := by
    apply Finset.eq_of_subset_of_card_le _ (by rw [sizes a,cc])
    intro z hz
    exact Finset.mem_compl.mpr fun h => ha ((mem _ _).mpr (((mem _ _).mp hz).symm.trans ((mem _ _).mp h)))
  have li (i : V) : c (l i).val (l i).val=c 0 0 := (mem _ _).mp (l i).property
  have ri (i : V) : c (r i).val (r i).val≠c 0 0 := fun h => (r i).property ((mem _ _).mpr h)
  refine ⟨e,?_⟩
  rintro (i|i) (j|j)
  · exact iff_of_true rfl ((li i).trans (li j).symm)
  · exact iff_of_false (by simp [side]) (fun h => ri j (h.symm.trans (li i)))
  · exact iff_of_false (by simp [side]) (fun h => ri i (h.trans (li j)))
  · apply iff_of_true rfl
    apply (mem _ _).mp
    change (r i).val ∈ F (r j).val
    rw [outside (r j).property]
    exact Finset.mem_compl.mpr (r i).property

private theorem left_hom {c : Table 16} (hc : Configuration c) (ends : Ends c)
    (e : X ≃ Fin 16) (sides : Sides c e) : Homogeneous (leftTable (pull c e)) := by
  let m := pull c e
  have law := pull_products _ e hc.products
  refine ⟨fun i j => ?_,fun _ _ _ _ eq => hc.reverse _ _ _ _ eq,?_⟩
  · constructor
    · intro eq; exact Sum.inl.inj (e.injective (hc.diagonal _ _ _ eq))
    · rintro rfl; exact (sides _ _).mp rfl
  intro i j x y eq a b
  by_cases occurs : ∃ u v : V, m (.inl u) (.inl v)=a
  · obtain ⟨u,v,rfl⟩ := occurs
    have forbid (i k : V) : m (.inl i) (.inr k) ≠ m (.inl u) (.inl v) := by
      intro h
      have no := (sides (.inr k) (.inl v)).mpr (ends _ _ _ _ h).2
      cases no
    have h := law (m (.inl u) (.inl v)) b (.inl i) (.inl j) (.inl x) (.inl y) eq
    change (∑ z, if m (.inl i) z = _ ∧ m z (.inl j) = b then 1 else 0 : Nat) =
      (∑ z, if m (.inl x) z = _ ∧ m z (.inl y) = b then 1 else 0 : Nat) at h
    simp only [Fintype.sum_sum_type,forbid,false_and,if_false,Finset.sum_const_zero,add_zero] at h
    exact h
  · push_neg at occurs
    change ShoreCensus.intersection (fun i j => m (.inl i) (.inl j)) a b i j =
      ShoreCensus.intersection (fun i j => m (.inl i) (.inl j)) a b x y
    simp [ShoreCensus.intersection,occurs]

structure RawInfo (m : Coloring) : Prop where
  rect : Rectangle m
  left : Homogeneous (leftTable m)
  right : Homogeneous (fun i j => m (.inr i) (.inr j))
  diag : LeftDiagonal m (m (.inl 0) (.inl 0))
  reverse : ∀ i j x y, m i j=m x y → m j i=m y x
  products : FixedInterface.HasIntersectionNumbers m

private theorem info {c : Table 16} (hc : Configuration c) (ends : Ends c)
    (e : X ≃ Fin 16) (sides : Sides c e) : RawInfo (pull c e) := by
  let swap := Equiv.sumComm V V
  have ds (i) : side (swap i)=!side i := by cases i <;> rfl
  have swapped : Sides c (swap.trans e) := by
    intro i j
    apply Iff.trans _ (sides (swap i) (swap j))
    rw [ds,ds]
    cases side i <;> cases side j <;> decide
  refine ⟨fun i j x y eq => Prod.ext ((sides _ _).mpr (ends _ _ _ _ eq).1)
    ((sides _ _).mpr (ends _ _ _ _ eq).2),left_hom hc ends e sides,
    left_hom hc ends (swap.trans e) swapped,?_,fun _ _ _ _ eq => hc.reverse _ _ _ _ eq,
    pull_products _ e hc.products⟩
  intro x y
  constructor
  · intro h
    have eq := e.injective (hc.diagonal _ _ _ h)
    subst y
    cases x with
    | inl i => exact ⟨i,rfl,rfl⟩
    | inr i => exact False.elim (by have z := (sides _ _).mpr h; cases z)
  · rintro ⟨i,rfl,rfl⟩
    exact (sides _ _).mp rfl

structure Presentation (a : Prepared.Index) (c : Table 16) where
  coordinates : Equiv.Perm (Fin 16)
  same : ∀ i j x y, Prepared.name a i j=Prepared.name a x y ↔
    c (coordinates i) (coordinates j)=c (coordinates x) (coordinates y)

private theorem models {c : Table 16} (e : X ≃ Fin 16) (I : RawInfo (pull c e)) :
    (∃ v h, Matches (pull c e) v h) ∨ ∃ a, Nonempty (Presentation a c) := by
  rcases Census.matching_or_catalog (pull c e) I.left I.right I.rect I.reverse I.products with
    ⟨v,h,hit⟩ | ⟨t,w,inside,q,hq⟩
  · exact Or.inl ⟨v,h,matches_of_rectangle I.rect hit⟩
  · have ht : t < Layers.matrices.size := by
      by_contra! no
      rw [getElem?_neg Layers.matrices t (Nat.not_lt.mpr no)] at inside
      contradiction
    let a : Prepared.Index := ⟨t,bank_size ▸ ht⟩
    have eq : w = Prepared.row a := Option.some.inj (inside.symm.trans (Prepared.row_lookup a))
    subst w
    refine Or.inr ⟨a,⟨q.symm.trans e,fun i j x y => ?_⟩⟩
    rw [← Fin.val_inj,Prepared.name_val,Prepared.name_val]
    simpa only [Equiv.trans_apply,Equiv.apply_symm_apply,pull] using
      (hq (q.symm i) (q.symm j) (q.symm x) (q.symm y)).symm

private theorem from_matching {m d : Coloring} (I : RawInfo m) (J : RawInfo d)
    (diag : m (.inl 0) (.inl 0)=d (.inl 0) (.inl 0))
    (tr : CommonTranspose m d) (common : CommonProducts m d)
    (forth : ∀ i j, ∃ x y, m i j=d x y) (back : ∀ x y, ∃ i j, d x y=m i j)
    (v : Nat) (h : Equiv.Perm V) (hit : Matches m v h) :
    ∃ t : Equiv.Perm X, ∀ i j, m i j=d (t i) (t j) := by
  obtain ⟨s,hs⟩ := left_realized I.diag (diag.symm ▸ J.diag) I.rect J.rect I.left J.left common forth back
  obtain ⟨q,hq⟩ := matching_transfers hit hs I.reverse tr common
  exact ⟨Equiv.sumCongr s (h.symm.trans (s.trans q)),extend hit hq hs tr common⟩

theorem alternatives {c d : Table 16} (hc : Configuration c) (hd : Configuration d)
    (sizes : Sizes c) (diag : ∀ i, c i i=d i i) (ce : Ends c) (de : Ends d)
    (tr : ∀ i j u v, c i j=d u v → c j i=d v u)
    (prod : ∀ a b i j u v, c i j=d u v → count c a b i j=count d a b u v)
    (used : ∀ v, (∃ i j, c i j=v) ↔ ∃ i j, d i j=v) :
    (∃ t : Equiv.Perm (Fin 16), ∀ i j, c i j=d (t i) (t j)) ∨
    ∃ a b, Nonempty (Presentation a c) ∧ Nonempty (Presentation b d) := by
  obtain ⟨e,sides⟩ := frame c sizes
  have sd : Sides d e := by intro i j; rw [←diag,←diag]; exact sides i j
  let m := pull c e
  let t := pull d e
  have I := info hc ce e sides
  have J := info hd de e sd
  have tr' : CommonTranspose m t := fun _ _ _ _ eq => tr _ _ _ _ eq
  have common : CommonProducts m t := fun a b i j x y eq =>
    (count_relabel c e a b i j).trans ((prod a b _ _ _ _ eq).trans (count_relabel d e a b x y).symm)
  have occurs (v) : (∃ i j, m i j=v) ↔ ∃ i j, t i j=v := by
    have image (C : Table 16) : (∃ i j, pull C e i j=v) ↔ ∃ i j, C i j=v :=
      ⟨fun ⟨i,j,h⟩ => ⟨_,_,h⟩,fun ⟨i,j,h⟩ => ⟨e.symm i,e.symm j,by simpa [pull] using h⟩⟩
    exact (image c).trans ((used v).trans (image d).symm)
  have forth (i j) : ∃ x y, m i j=t x y := by
    obtain ⟨x,y,h⟩ := (occurs _).mp ⟨i,j,rfl⟩; exact ⟨x,y,h.symm⟩
  have back (x y) : ∃ i j, t x y=m i j := by
    obtain ⟨i,j,h⟩ := (occurs _).mpr ⟨x,y,rfl⟩; exact ⟨i,j,h.symm⟩
  have done (u : Equiv.Perm X) (hu : ∀ i j, m i j=t (u i) (u j)) :
      ∃ q : Equiv.Perm (Fin 16), ∀ i j, c i j=d (q i) (q j) := by
    refine ⟨e.symm.trans (u.trans e),fun i j => ?_⟩
    simpa [m,t,pull] using hu (e.symm i) (e.symm j)
  rcases models e I with ⟨v,h,hit⟩ | ⟨a,A⟩
  · obtain ⟨u,hu⟩ := from_matching I J (diag _) tr' common forth back v h hit
    exact Or.inl (done u hu)
  rcases models e J with ⟨v,h,hit⟩ | ⟨b,B⟩
  · obtain ⟨u,hu⟩ := from_matching J I (diag _).symm (fun _ _ _ _ eq => (tr' _ _ _ _ eq.symm).symm)
      (fun a b _ _ _ _ eq => (common a b _ _ _ _ eq.symm).symm) back forth v h hit
    exact Or.inl (done u.symm (fun i j => by simpa using (hu (u.symm i) (u.symm j)).symm))
  · exact Or.inr ⟨a,b,A,B⟩

end QGI.Coherent.RegionalDoubleEight
