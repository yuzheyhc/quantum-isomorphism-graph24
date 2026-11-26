import RegionalPairShores

namespace QGI.Coherent.RegionalEightTwelveGeometry

abbrev Point := Fin 8
abbrev Index := Fin 12
abbrev Cell := Finset Point
abbrev Family := Finset Cell

def pool : Family := Finset.univ.powersetCard 2

def crosses (f : Family) : Prop := ∀ s : Cell, s.Nonempty → s≠Finset.univ → ∃ e∈f, (e∩s).card=1

def Determines (f : Family) : Prop := ∀ a b : Cell, (∀ e∈f, (e∩a).card=(e∩b).card) →
  (∃ i : Point, i∈a ↔ i∈b) → a=b

/-- One agreeing endpoint of a two-element probe forces agreement at the other endpoint. -/
private theorem same_pair (e a b : Cell) (weight : e.card=2) (count : (e∩a).card=(e∩b).card) :
    (e∩Finset.univ.filter (fun i => (i∈a ↔ i∈b))).card≠1 := by
  obtain ⟨x,y,ne,rfl⟩ := Finset.card_eq_two.mp weight
  have part (s : Cell) : ({x,y}∩s).card=(if x∈s then 1 else 0)+(if y∈s then 1 else 0) := by
    rw [←Finset.filter_mem_eq_inter]
    by_cases hx : x∈s <;> by_cases hy : y∈s <;> simp [Finset.filter_insert,Finset.filter_singleton,ne,hx,hy]
  rw [part,part] at count
  rw [part]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hx : x∈a <;> by_cases hy : y∈a <;> by_cases bx : x∈b <;> by_cases by' : y∈b <;> simp_all

theorem determines_connected (f : Family) (w : ∀ e∈f, e.card=2) (connected : crosses f) : Determines f := by
  intro a b h pin
  let s := Finset.univ.filter (fun i => (i∈a ↔ i∈b))
  have all : s=Finset.univ := by
    by_contra ne
    obtain ⟨i,hi⟩ := pin
    obtain ⟨e,he,cut⟩ := connected s ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩ ne
    exact same_pair e a b (w e he) (h e he) cut
  ext i
  exact (Finset.mem_filter.mp (show i∈s by rw [all]; exact Finset.mem_univ _)).2

private def unionOf (t : Family) : Cell := t.biUnion id

private def centers (t : Family) : Cell := Finset.univ.filter fun i => (t.filter fun e => i∉e).card=0

private theorem center_mem (t : Family) (i) : i∈centers t ↔ ∀ e∈t, i∈e := by
  classical
  simp [centers,Finset.filter_eq_empty_iff]

private theorem pair_at {x y : Point} {e : Cell} (xy : x≠y) (w : e.card=2) (hx : x∈e) (hy : y∈e) : e={x,y} := by
  exact (Finset.eq_of_subset_of_card_le (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
    (by rw [w,Finset.card_pair xy])).symm

private def meets (t : Family) (w : Cell) := (t.filter fun a => (a∩w).Nonempty).card
private def badCut (t : Family) := pool.filter fun w => w∉t ∧ (w∩unionOf t).card=1 ∧ meets t w≠1 ∧ (w∩centers t)=∅
private def good (t : Family) : Bool :=
  decide ((centers t=∅ ∨ ((unionOf t).card=4 ∧ badCut t=∅)) ∧
    ((t.filter (fun a => meets t a≠3))≠∅ ∨ (pool.filter (fun w => meets t w=1))=∅ ∨ centers t≠∅))

private theorem checked : ((pool.powersetCard 3).filter (fun t => good t=false)).card=0 := by native_decide

private theorem sound (t : Family) (ht : t∈pool.powersetCard 3) : good t=true := by
  by_contra bad
  exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,Bool.eq_false_of_not_eq_true bad⟩⟩)) checked

private theorem starFacts (t : Family) (ht : t∈pool.powersetCard 3) (h : ∃ i : Point, ∀ e∈t, i∈e) :
    (unionOf t).card=4 ∧ badCut t=∅ := by
  obtain ⟨i,hi⟩ := h
  have hc : (centers t).Nonempty := ⟨i,(center_mem t i).mpr hi⟩
  exact (of_decide_eq_true (sound t ht)).1.resolve_left hc.ne_empty

private theorem local_stars (t : Family) (ht : t∈pool.powersetCard 3)
    (clique : ∀ a∈t, ∀ b∈t, (a∩b).Nonempty) (mark : ∃ w∈pool, meets t w=1) :
    ∃ i : Point, ∀ e∈t, i∈e := by
  have eq : t.filter (fun a => meets t a≠3)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha ne
    have same : t.filter (fun b => (b∩a).Nonempty)=t := Finset.filter_true_of_mem (fun b hb => clique b hb a ha)
    exact ne ((congrArg Finset.card same).trans (Finset.mem_powersetCard.mp ht).2)
  obtain ⟨w,hw,h⟩ := mark
  have nz : (pool.filter (fun w => meets t w=1)).Nonempty := ⟨w,Finset.mem_filter.mpr ⟨hw,h⟩⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr (((of_decide_eq_true (sound t ht)).2.resolve_left (not_not.mpr eq)).resolve_left nz.ne_empty)
  exact ⟨i,(center_mem t i).mp hi⟩

def incident (a : Index → Cell) (i : Point) := Finset.univ.filter (fun j => i∈a j)

/-- A disconnected cubic simple graph on eight vertices is two disjoint four-cliques. -/
theorem disconnected_cliques (a : Index → Cell) (wt : ∀ j, (a j).card=2) (inj : Function.Injective a)
    (deg : ∀ i, (incident a i).card=3) (cut : ¬crosses (Finset.univ.image a)) :
    ∃ side : Point → Bool, (∀ j i k, i∈a j → k∈a j → side i=side k) ∧
      ∀ i k, side i=side k → i≠k → ∃ j, a j={i,k} := by
  classical
  unfold crosses at cut
  push_neg at cut
  obtain ⟨s,pos,proper,sep⟩ := cut
  have within (j i k) (hi : i∈a j) (hk : k∈a j) : i∈s ↔ k∈s := by
    by_cases ne : i=k
    · rw [ne]
    have eq := pair_at ne (wt j) hi hk
    have stop := sep (a j) (Finset.mem_image_of_mem a (Finset.mem_univ j))
    rw [eq] at stop
    by_cases h : i∈s <;> by_cases h' : k∈s <;> simp_all [←Finset.filter_mem_eq_inter,Finset.filter_insert,Finset.filter_singleton]
  let nb (i : Point) := unionOf ((incident a i).image a)
  have size (i) : (nb i).card=4 := by
    apply (starFacts _ ?_ ?_).1
    · refine Finset.mem_powersetCard.mpr ⟨?_,(Finset.card_image_of_injective _ inj).trans (deg i)⟩
      intro e he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,wt j⟩
    · refine ⟨i,fun e he => ?_⟩
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hj).2
  have get {i x} (h : x∈nb i) : ∃ j, i∈a j ∧ x∈a j := by
    obtain ⟨e,he,incl⟩ := Finset.mem_biUnion.mp h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    exact ⟨j,(Finset.mem_filter.mp hj).2,incl⟩
  let block (i : Point) := if i∈s then s else sᶜ
  have sub (i) : nb i⊆block i := by
    intro k hk
    obtain ⟨j,hj,mj⟩ := get hk
    have eq := within j i k hj mj
    by_cases h : i∈s <;> simp_all [block]
  obtain ⟨i,hi⟩ := pos
  obtain ⟨k,hk⟩ : ∃ k : Point, k∉s := by
    by_contra! full
    exact proper (Finset.eq_univ_iff_forall.mpr full)
  have x := Finset.card_le_card (sub i)
  have y := Finset.card_le_card (sub k)
  simp only [size,block,if_pos hi,if_neg hk,Finset.card_compl,Fintype.card_fin] at x y
  have all (i) : nb i=block i := Finset.eq_of_subset_of_card_le (sub i) (by
    rw [size]; by_cases h : i∈s <;> simp [block,h,Finset.card_compl] <;> omega)
  let side := fun i : Point => decide (i∈s)
  refine ⟨side,fun j i k hi hk => by simp only [side,within j i k hi hk],fun i k equal diff => ?_⟩
  have same : (i∈s ↔ k∈s) := by by_cases h : i∈s <;> by_cases g : k∈s <;> simp_all [side]
  have mem : k∈block i := by by_cases h : i∈s <;> simp_all [block]
  rw [←all] at mem
  obtain ⟨j,ij,kj⟩ := get mem
  exact ⟨j,pair_at diff (wt j) ij kj⟩

private theorem star_distinct (a : Index → Cell) (w : ∀ j, (a j).card=2) (inject : Function.Injective a)
    (i j : Point) (many : 2≤(incident a i).card) (eq : incident a i=incident a j) : i=j := by
  by_contra ne
  have same (k) (hk : k∈incident a i) : a k={i,j} := by
    have hj : k∈incident a j := by rw [←eq]; exact hk
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset (Finset.mem_filter.mp hk).2 (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hj).2)
    · rw [w,Finset.card_pair ne]
  have small := Finset.card_le_one.mpr (fun k hk t ht => inject ((same k hk).trans (same t ht).symm))
  omega

theorem align_connected (a b : Index → Cell) (w : ∀ j, (a j).card=2) (wt : ∀ j, (b j).card=2)
    (sa : Function.Injective a) (sb : Function.Injective b) (deg : ∀ i, (incident a i).card=3)
    (degt : ∀ i, (incident b i).card=3) (connected : crosses (Finset.univ.image a))
    (gram : ∀ j k, (a j∩a k).card=(b j∩b k).card) :
    ∃ h : Equiv.Perm Point, ∀ j i, i∈a j ↔ h i∈b j := by
  classical
  let lift (u : Index → Cell) (s : Finset Index) := s.image u
  have three (u : Index → Cell) (wu : ∀ j, (u j).card=2) (inj : Function.Injective u) (s : Finset Index) (cs : s.card=3) :
      lift u s∈pool.powersetCard 3 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_,(Finset.card_image_of_injective _ inj).trans cs⟩
    intro e he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,wu j⟩
  have common (i : Point) : ∃ t : Point, ∀ j, i∈a j → t∈b j := by
    let s := incident a i
    let A := lift a s
    let B := lift b s
    have ai (e) (h : e∈A) : i∈e := by obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hj).2
    have cut := starFacts A (three a w sa s (deg i)) ⟨i,ai⟩
    have pos := Finset.card_pos.mp ((by decide : 0<4).trans_eq cut.1.symm)
    have proper : unionOf A≠Finset.univ := fun eq => (by decide : (Finset.univ : Cell).card≠4) ((congrArg Finset.card eq).symm.trans cut.1)
    obtain ⟨e,he,out⟩ := connected (unionOf A) pos proper
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    have notmem : a j∉A := by
      intro incl
      have sub : a j⊆unionOf A := Finset.subset_biUnion_of_mem (s:=A) id incl
      exact (by decide : (2:Nat)≠1) (((w j).symm.trans (congrArg Finset.card (Finset.inter_eq_left.mpr sub)).symm).trans out)
    have marked : (A.filter (fun z => (z∩a j).Nonempty)).card=1 := by
      by_contra ne
      have empty : a j∩centers A=∅ := by
        apply Finset.eq_empty_of_forall_not_mem
        intro x mem
        obtain ⟨hx,hc⟩ := Finset.mem_inter.mp mem
        have cx := (center_mem A x).mp hc
        have eq : x=i := by
          have contain : incident a i⊆incident a x := by
            intro k hk
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cx _ (Finset.mem_image_of_mem a hk)⟩
          exact (star_distinct a w sa i x (by rw [deg]; decide) (Finset.eq_of_subset_of_card_le contain (by rw [deg,deg]))).symm
        exact notmem (Finset.mem_image_of_mem a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq ▸ hx⟩))
      have bad : a j∈badCut A := Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,w _⟩,notmem,out,ne,empty⟩
      exact (Finset.nonempty_iff_ne_empty.mp ⟨_,bad⟩) cut.2
    have transfer (k z) : (a k∩a z).Nonempty ↔ (b k∩b z).Nonempty := by rw [←Finset.card_pos,←Finset.card_pos,gram]
    have imageFilter (u : Index → Cell) (d : Cell) :
        (lift u s).filter (fun z => (z∩d).Nonempty)=(s.filter (fun k => (u k∩d).Nonempty)).image u := by
      ext e
      simp only [lift,Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨j,hj,rfl⟩,hu⟩; exact ⟨j,⟨hj,hu⟩,rfl⟩
      · rintro ⟨j,⟨hj,hu⟩,rfl⟩; exact ⟨⟨j,hj,rfl⟩,hu⟩
    have sameCount : (B.filter (fun z => (z∩b j).Nonempty)).card=1 := by
      change ((lift a s).filter _).card=1 at marked
      change ((lift b s).filter _).card=1
      rw [imageFilter,Finset.card_image_of_injective _ sb]
      rw [imageFilter,Finset.card_image_of_injective _ sa] at marked
      simpa only [transfer] using marked
    obtain ⟨z,hz⟩ := local_stars B (three b wt sb s (deg i)) (by
      intro u hu v hv
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
      exact (transfer k t).mp ⟨i,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hk).2,(Finset.mem_filter.mp ht).2⟩⟩)
      ⟨b j,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,wt _⟩,sameCount⟩
    exact ⟨z,fun k hk => hz _ (Finset.mem_image_of_mem b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩))⟩
  choose f hf using common
  have equal (i) : incident a i=incident b (f i) := Finset.eq_of_subset_of_card_le
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf i j (Finset.mem_filter.mp hj).2⟩) (by rw [deg,degt])
  have inj : Function.Injective f := fun i j eq => star_distinct a w sa i j (by rw [deg]; decide) (by rw [equal,equal,eq])
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),fun j i => ?_⟩
  have h : j∈incident a i ↔ j∈incident b (f i) := by rw [equal]
  simpa only [incident,Finset.mem_filter,Finset.mem_univ,true_and] using h

end QGI.Coherent.RegionalEightTwelveGeometry

