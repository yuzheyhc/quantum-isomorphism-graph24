import RegionalPairShores
import SixPointStars

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open RegionalSixTwelveGeometry

abbrev Member (f : Family) := {s // s∈f}

def star (f : Family) (i : Point) : Finset (Member f) := Finset.univ.filter fun s => i∈s.val

private theorem star_degree (f : Family) (i : Point) : (star f i).card=degree f i := by
  let v : Member f ↪ Block := ⟨Subtype.val,Subtype.val_injective⟩
  have eq : (star f i).map v=f.filter (fun s => i∈s) := by
    ext e
    constructor
    · intro h
      obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_filter.mpr ⟨s.property,(Finset.mem_filter.mp hs).2⟩
    · intro h
      obtain ⟨hs,hi⟩ := Finset.mem_filter.mp h
      exact Finset.mem_map.mpr ⟨⟨_,hs⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  exact (Finset.card_map _).symm.trans (congrArg Finset.card eq)

private theorem star_distinct {f : Family} (weights : ∀ s∈f, s.card=2) (i j : Point) (hi : 2≤(star f i).card)
    (same : star f i=star f j) : i=j := by
  by_contra diff
  have pair (x : Member f) (hx : x∈star f i) : x.val={i,j} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · have hy : x∈star f j := same ▸ hx
      have hxi : i∈x.val := (Finset.mem_filter.mp hx).2
      have hxj : j∈x.val := (Finset.mem_filter.mp hy).2
      exact Finset.insert_subset hxi (Finset.singleton_subset_iff.mpr hxj)
    · simp [weights _ x.property,diff]
  have bound : (star f i).card≤1 := Finset.card_le_one.mpr fun a ha b hb => Subtype.ext ((pair a ha).trans (pair b hb).symm)
  omega

/-- An identification of the distinct edge labels by intersection size
lifts to a point permutation whenever each vertex lies on two or four edges. -/
theorem align_degrees {f g : Family} (h : Member f ≃ Member g)
    (wf : ∀ s∈f, s.card=2) (wg : ∀ s∈g, s.card=2) {d : Nat} (ds : (d=2 ∨ d=4) ∨ d=5)
    (df : ∀ i, degree f i=d) (dg : ∀ i, degree g i=d)
    (gram : ∀ x y, (x.val∩y.val).card=((h x).val∩(h y).val).card) :
    ∃ e : Equiv.Perm Point, ∀ i x, i∈x.val ↔ e i∈(h x).val := by
  let embed : Member f ↪ Block := h.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  have corner (i : Point) : ∃ j, ∀ e : Member f, i∈e.val → j∈(h e).val := by
    let s := (star f i).map embed
    have size : s.card=d := (Finset.card_map _).trans ((star_degree f i).trans (df i))
    obtain ⟨j,hj⟩ := star_center_many s (fun a ha => by
      obtain ⟨e,_,rfl⟩ := Finset.mem_map.mp ha
      exact wg _ (h e).property) (size ▸ ds) (by
      intro a ha b hb
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
      apply Finset.card_pos.mp
      rw [show (embed x∩embed y).card=_ from (gram x y).symm]
      exact Finset.card_pos.mpr ⟨i,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩⟩)
    exact ⟨j,fun e he => hj _ (Finset.mem_map.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩)⟩
  choose m hm using corner
  have eq (i : Point) : (star f i).map h.toEmbedding=star g (m i) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm i e ((Finset.mem_filter.mp he).2)⟩
    · rw [Finset.card_map,star_degree,star_degree,df,dg]
  have inject : Function.Injective m := by
    intro i j he
    apply star_distinct wf i j
    · rw [star_degree,df]; omega
    · apply Finset.map_injective h.toEmbedding
      rw [eq,eq,he]
  let e := Equiv.ofBijective m (Finite.injective_iff_bijective.mp inject)
  refine ⟨e,fun i x => ?_⟩
  have mem : x∈star f i ↔ h x∈star g (m i) := by
    rw [←eq]
    exact (Finset.mem_map' h.toEmbedding).symm
  simpa only [star,Finset.mem_filter,Finset.mem_univ,true_and,e] using mem

theorem align {f g : Family} (h : Member f ≃ Member g)
    (wf : ∀ s∈f, s.card=2) (wg : ∀ s∈g, s.card=2) {d : Nat} (ds : d=2 ∨ d=4)
    (df : ∀ i, degree f i=d) (dg : ∀ i, degree g i=d)
    (gram : ∀ x y, (x.val∩y.val).card=((h x).val∩(h y).val).card) :
    ∃ e : Equiv.Perm Point, ∀ i x, i∈x.val ↔ e i∈(h x).val :=
  align_degrees h wf wg (Or.inl ds) df dg gram

/-- Repetitions of a two-element neighborhood are recognized by their
pairwise intersection size. The right-hand identification is kept fixed. -/
theorem label_equiv {I : Type} [Fintype I] (a b : I → Block)
    (aw : ∀ i, (a i).card=2) (bw : ∀ i, (b i).card=2)
    (gram : ∀ i j, (a i∩a j).card=(b i∩b j).card) :
    ∃ h : Member (Finset.univ.image a) ≃ Member (Finset.univ.image b),
      ∀ i, (h ⟨a i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩).val=b i := by
  classical
  let f := Finset.univ.image a
  let g := Finset.univ.image b
  let A (i : I) : Member f := ⟨a i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let B (i : I) : Member g := ⟨b i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have overlap (x y : Block) (hx : x.card=2) (hy : y.card=2) : (x∩y).card=2 ↔ x=y := by
    constructor
    · intro h
      exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hx.trans h.symm).le).symm.trans
        (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (hy.trans h.symm).le)
    · rintro rfl; simpa using hx
  have names (i j) : a i=a j ↔ b i=b j := by
    rw [←overlap _ _ (aw i) (aw j),←overlap _ _ (bw i) (bw j),gram]
  have src (s : Member f) : ∃ i, a i=s.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp s.property; exact ⟨i,hi⟩
  have dst (s : Member g) : ∃ i, b i=s.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp s.property; exact ⟨i,hi⟩
  choose u hu using src
  choose v hv using dst
  let h : Member f ≃ Member g := ⟨fun s => B (u s),fun t => A (v t),
    fun s => Subtype.ext (((names _ _).mpr (hv (B (u s)))).trans (hu s)),
    fun t => Subtype.ext (((names _ _).mp (hu (A (v t)))).trans (hv t))⟩
  exact ⟨h,fun i => (names _ _).mp (hu (A i))⟩

theorem regular_degree (f : Family) (weight : ∀ s∈f, s.card=2) (reg : Regular f) :
    6*degree f 0=f.card*2 := by
  have count (i : Point) : degree f i=∑ s∈f, if i∈s then 1 else 0 := by simp [degree]
  have total : ∑ i : Point, degree f i=∑ s∈f, s.card := by
    simp_rw [count]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    simp
  have const : ∑ s∈f, s.card=∑ _s∈f, 2 := Finset.sum_congr rfl weight
  have val (i : Point) : degree f i=degree f 0 := reg i
  simpa only [val,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using total.trans const

end QGI.Coherent.RegionalSixTwelve

