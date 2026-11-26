import RegionalEightTwelveHalfLaws
import RegionalEightTwelve

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveHalfModels
open FourTwelveFunctional (source)
open SixTenCoordinates EightTwelveHalf RegionalEightTwelveStats RegionalEightTwelveHalfLaws
open SmallUnion SmallFiberExtension StrategyColorLaws

theorem both_colors {A B v w : Nat} (left : A=v ∨ A=w) (right : B=v ∨ B=w) :
    A=B ↔ (A=v ↔ B=v) := by
  constructor
  · rintro rfl; exact Iff.rfl
  intro h
  by_cases ha : A=v
  · exact ha.trans (h.mp ha).symm
  exact (left.resolve_left ha).trans (right.resolve_left (mt h.mpr ha)).symm

theorem model_zero_twins {n l r v w : Nat} {c : Fin n → Fin n → Nat}
    (F : Shore c l P) (Y : Shore c r J) (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w)
    (e : Equiv.Perm P) (shape : (supports (family F Y v)).image (fun s => s.image e)=model 0) :
    SplitRectangle.Twins (color F Y) := by
  let a := family F Y v
  let b := fun j => (a j).image e
  have mem (j : J) : b j∈model 0 := shape ▸ Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have read (j i) : e i∈b j ↔ color F Y j i=v := by simp [b,a,family,color]
  have eq (j k i x) : color F Y j i=color F Y k x ↔ (e i∈b j ↔ e x∈b k) := by
    rw [read,read]; exact both_colors (two j i) (two k x)
  have cert : ∀ s∈model 0, ∀ t∈model 0, ∀ i j : P,
      ((i∈s ↔ i∈t) → (j∈s ↔ j∈t)) ∧ ((i∈s ↔ j∈s) → (i∈t ↔ j∈t)) := by native_decide
  exact ⟨fun j k i h x => (eq j k x x).mpr ((cert _ (mem j) _ (mem k) (e i) (e x)).1 ((eq j k i i).mp h)),
    fun j i x h k => (eq k k i x).mpr ((cert _ (mem j) _ (mem k) (e i) (e x)).2 ((eq j j i x).mp h))⟩

private theorem cube_read : ∀ f∈(model 3).powerset, (∀ s∈model 3, (s∈f ↔ sᶜ∉f)) →
    ∃ i : P, ∀ s∈model 3, (s∈f ↔ i∈s) := by
  let good (f : Family) := (∀ s∈model 3, (s∈f ↔ sᶜ∉f)) → ∃ i : P, ∀ s∈model 3, (s∈f ↔ i∈s)
  have h : ((model 3).powerset.filter (fun f => ¬good f)).card=0 := by
    dsimp only [good]; native_decide
  intro f hf
  change good f
  by_contra bad
  have mem : f∈(model 3).powerset.filter (fun f => ¬good f) := Finset.mem_filter.mpr ⟨hf,bad⟩
  have no : (model 3).powerset.filter (fun f => ¬good f)=∅ := Finset.card_eq_zero.mp h
  exact (Finset.not_mem_empty f) (no ▸ (mem : f∈(model 3).powerset.filter (fun f => ¬good f)))
private theorem cube_complements : ∀ s∈model 3, sᶜ∈model 3 := by native_decide
private theorem cube_unique : ∀ i j : P, (∀ s∈model 3, (i∈s ↔ j∈s)) → i=j := by native_decide

private theorem cube_transfer (a b : J → C) (e : Equiv.Perm P) (shape : (supports a).image (fun s => s.image e)=model 3)
    (wa : ∀ j, (a j).card=4) (wb : ∀ j, (b j).card=4)
    (common : ∀ j k, (a j∩a k).card=(b j∩b k).card) :
    Function.Injective (rowCells a) ∧ ∀ i : P, ∃ x : P, ∀ j, (i∈b j ↔ x∈a j) := by
  let c := fun j => (a j).image e
  have inside (j : J) : c j∈model 3 := shape ▸ Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have onto (s) (hs : s∈model 3) : ∃ j, c j=s := by
    rw [←shape] at hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨j,rfl⟩
  have read (j i) : e i∈c j ↔ i∈a j := by simp [c]
  have overlap (j k) : (c j∩c k).card=(b j∩b k).card := by
    change ((a j).image e ∩ (a k).image e).card=_
    rw [←Finset.image_inter _ _ e.injective,Finset.card_image_of_injective _ e.injective]; exact common j k
  have equal (j k) (hit : c j=c k) : b j=b k := by
    have hv : (c j).card=4 := (Finset.card_image_of_injective _ e.injective).trans (wa j)
    have hz : (b j∩b k).card=4 := (overlap j k).symm.trans (by rw [←hit,Finset.inter_self,hv])
    exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hz.trans (wb j).symm).ge).symm.trans
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (hz.trans (wb k).symm).ge)
  have opposite (j k) (hit : c j=(c k)ᶜ) : b j=(b k)ᶜ := by
    have none : (b j∩b k).card=0 := (overlap j k).symm.trans (by rw [hit]; apply Finset.card_eq_zero.mpr; ext i; simp [and_comm])
    apply Finset.eq_of_subset_of_card_le
    · intro i hi; apply Finset.mem_compl.mpr; intro hk
      have mem : i∈b j∩b k := Finset.mem_inter.mpr ⟨hi,hk⟩
      rw [Finset.card_eq_zero.mp none] at mem; exact Finset.not_mem_empty _ mem
    · rw [Finset.card_compl,wb,wb]; decide
  constructor
  · intro i j eq
    apply e.injective
    apply cube_unique
    intro s hs
    obtain ⟨k,rfl⟩ := onto s hs
    have same := Finset.ext_iff.mp eq k
    simpa only [read,rowCells,Finset.mem_filter,Finset.mem_univ,true_and] using same
  intro i
  let f := (model 3).filter fun s => ∃ j, c j=s ∧ i∈b j
  have mem (j) : c j∈f ↔ i∈b j := by
    constructor
    · intro h; obtain ⟨k,hk,hi⟩ := (Finset.mem_filter.mp h).2; exact equal k j hk ▸ hi
    · intro h; exact Finset.mem_filter.mpr ⟨inside j,j,rfl,h⟩
  obtain ⟨z,hz⟩ := cube_read f (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) (by
    intro s hs
    obtain ⟨j,rfl⟩ := onto s hs
    obtain ⟨k,opp⟩ := onto _ (cube_complements _ (inside j))
    rw [←opp,mem,mem,opposite k j opp,Finset.mem_compl,not_not])
  exact ⟨e.symm z,fun j => (mem j).symm.trans ((hz _ (inside j)).trans (by simpa only [Equiv.apply_symm_apply] using read j (e.symm z)))⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
open private range from RegionalSixTwelveDispatch

theorem target_two {l r v w : Nat} (F : Shore (source G) l P) (Y : Shore (source G) r J)
    (T : Shore (targetName p) l P) (Z : Shore (targetName p) r J)
    (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w) (j : J) (i : P) :
    color T Z j i=v ∨ color T Z j i=w := by
  let u := color T Z j i
  have deg := Block.degree_eq (commonLaws p) (incidence F Y T Z u) j j
  simp only [decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] at deg
  have mem : i∈family T Z u j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  obtain ⟨x,hx⟩ := Finset.card_pos.mp ((Finset.card_pos.mpr ⟨i,mem⟩).trans_eq deg.symm)
  have eq : color F Y j x=color T Z j i := (Finset.mem_filter.mp hx).2
  rw [←eq]; exact two j x

set_option maxHeartbeats 1200000 in
theorem cube {l r v w : Nat} (F : Shore (source G) l P) (Y : Shore (source G) r J)
    (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w) (wa : ∀ j, (family F Y v j).card=4)
    (names : NamedGram F (family F Y v)) (e : Equiv.Perm P) (shape : (supports (family F Y v)).image (fun s => s.image e)=model 3) :
    Realizes p reg := by
  classical
  apply RegionalEightTwelve.on_pair p F Y reg cover
  intro T Z right
  obtain ⟨z,_,hz⟩ := SmallShore.realize_at p (by decide : 0<8) (by decide) (atPoint F) (atPoint T) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp T.injective) (range F) (range T) 0 0
  let T' := z.trans T
  let a := family F Y v
  let b := family T' Z v
  have gram (j k : J) : (a j∩a k).card=(b j∩b k).card := mixed_counts (commonLaws p) F Y T' Z v v (right j k)
  have wb (j : J) : (b j).card=4 := (by simpa only [Finset.inter_self] using (gram j j).symm : (b j).card=(a j).card).trans (wa j)
  obtain ⟨mono,get⟩ := cube_transfer a b e shape wa wb gram
  choose f hf using get
  have same (i j : P) : crossGram a i j=crossGram b i j := by
    simpa only [crossGram,Block.overlap,decide_eq_true_eq] using
      Block.gram (commonLaws p) (Block.flip (commonLaws p) (incidence F Y T' Z v)) (hz i j)
  have aligned (i j : P) : crossGram b i j=crossGram a (f i) (f j) := by
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hf]
  have left (i j : P) : source G (atPoint F (f i)) (atPoint F (f j))=targetName p (atPoint T' i) (atPoint T' j) :=
    (names mono _ _ _ _ ((aligned i j).symm.trans (same i j).symm)).trans (hz i j)
  have injective : Function.Injective f := by
    intro i j ij
    have src : source G (atPoint F (f i)) (atPoint F (f i))=source G (atPoint F (f i)) (atPoint F (f j)) := by rw [ij]
    have eq := (left i i).symm.trans (src.trans (left i j))
    have copied := (hz i j).trans (eq.symm.trans (hz i i).symm)
    exact F.injective (Subtype.ext (Relations.diagonal (closure G) copied))
  let h := Equiv.ofBijective f (Finite.injective_iff_bijective.mp injective)
  refine ⟨h.symm.trans z,?_,?_⟩
  · intro i j
    simpa only [←show ∀ t, h t=f t from fun _ => rfl,Equiv.apply_symm_apply] using left (h.symm i) (h.symm j)
  · intro j i
    apply (both_colors (two j i) (target_two p F Y T' Z two j (h.symm i))).mpr
    have link : i∈a j ↔ h.symm i∈b j := by
      simpa only [←show ∀ t, h t=f t from fun _ => rfl,Equiv.apply_symm_apply] using (hf (h.symm i) j).symm
    simpa only [a,b,family,color,Finset.mem_filter,Finset.mem_univ,true_and] using link

end QGI.Coherent.RegionalEightTwelveHalfModels

