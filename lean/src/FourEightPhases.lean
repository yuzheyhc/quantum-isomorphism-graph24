import FourEightGeometry
import RootedTwoChoices

noncomputable section
namespace QGI.Coherent.FourEightPhases
open Relations SixTenCoordinates FourEightGeometry FourTwelveCycle

abbrev Four := Fin 4
abbrev Eight := Fin 8

private theorem bit_det (a b c : Bool) : (a=b ↔ a=c) → b=c := by cases a <;> cases b <;> cases c <;> decide

private def part (s t : Eight → Bool) (i : Eight) :=
  Finset.univ.filter (fun k => s i=s k ∧ t i=t k)

private theorem small_parts (s t : Eight → Bool)
    (balanced : ∀ k, (Finset.univ.filter fun i => s i=k).card=4)
    (balanced' : ∀ k, (Finset.univ.filter fun i => t i=k).card=4)
    (same : ∀ i, (part s t i).card=(part s t 0).card)
    (different : ¬ ∀ i j, s i=s j ↔ t i=t j) : ∀ i, (part s t i).card ≤ 2 := by
  classical
  push_neg at different
  obtain ⟨i,j,h⟩ := different
  have disj (ne : ¬(s i=s j ∧ t i=t j)) : Disjoint (part s t i) (part s t j) := by
    refine Finset.disjoint_left.mpr (fun x hi hj => ?_)
    obtain ⟨si,ti⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨sj,tj⟩ := (Finset.mem_filter.mp hj).2
    exact ne ⟨si.trans sj.symm,ti.trans tj.symm⟩
  have union (D : Disjoint (part s t i) (part s t j)) (B : Finset Eight) (size : B.card=4)
      (sub : part s t i ∪ part s t j ⊆ B) : (part s t 0).card ≤ 2 := by
    have lo := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint D,same i,same j,size] at lo
    omega
  intro x
  rw [same x]
  rcases h with ⟨eq,ne⟩|⟨eq,et⟩
  ·
    apply union (disj (fun p => ne p.2)) _ (balanced (s i))
    intro z hz
    rcases Finset.mem_union.mp hz with hi|hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(eq.trans (Finset.mem_filter.mp hj).2.1).symm⟩
  ·
    apply union (disj (fun p => eq p.1)) _ (balanced' (t i))
    intro z hz
    rcases Finset.mem_union.mp hz with hi|hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.2.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(et.trans (Finset.mem_filter.mp hj).2.2).symm⟩

private theorem four_at {G : Graph 16} {l r : Nat} (F : Shore (color (closure G)) l Four)
    (Y : Shore (color (closure G)) r Eight) (v : Nat) (b : Eight → Edge)
    (cells : ∀ i j, color (closure G) (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) (i : Four) :
    ∃ u w : V, ∀ z, color (closure G) (atPoint Y 0) z = color (closure G) (atPoint Y 0) (atPoint F i) →
      z=u ∨ z=w := by
  classical
  let U := edge (b 0)
  let S := if i∈U then U else Uᶜ
  have size : U.card=2 := (by native_decide : ∀ e : Edge, (edge e).card=2) (b 0)
  have card : S.card ≤ 2 := by by_cases h : i∈U <;> simp [S,h,Finset.card_compl,size]
  obtain ⟨u,w,short⟩ := DegreeClassRigidity.two_labels S 0 card
  refine ⟨atPoint F u,atPoint F w,fun z hz => ?_⟩
  have same := (end_colors (closure G) hz).2.trans (F i).property
  let k := F.symm ⟨z,same⟩
  have loc : atPoint F k=z := congrArg Subtype.val (F.apply_symm_apply _)
  have h : k∈U ↔ i∈U := by
    rw [←cells,←cells,loc,Relations.transpose (closure G) hz]
  have mem : k∈S := by by_cases hi : i∈U <;> simp [S,hi,h]
  rcases short k mem with eq|eq
  · exact Or.inl (loc.symm.trans (congrArg (atPoint F) eq))
  · exact Or.inr (loc.symm.trans (congrArg (atPoint F) eq))

/-- If both four-by-eight rectangles are doubled four-cycles, either
the graph is realized or their induced binary equivalence relations on
the eight-point fiber coincide. -/
theorem isomorphic_or_equal {G H : Graph 16} {l r u : Nat}
    (F : Shore (color (closure G)) l Four) (S : Shore (color (closure G)) r Four)
    (Y : Shore (color (closure G)) u Eight)
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=u)
    (v w : Nat) (b d : Eight → Edge)
    (fb : ∀ i j, color (closure G) (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j))
    (sd : ∀ i j, color (closure G) (atPoint S i) (atPoint Y j)=w ↔ i∈edge (d j))
    (B : RepeatedCycle b) (D : RepeatedCycle d) (q : QuantumIso G H) :
    Isomorphic G H ∨ ∀ i j, overlap (b i) (b j)≠1 ↔ overlap (d i) (d j)≠1 := by
  classical
  obtain ⟨s,hs,size⟩ := B.halves
  obtain ⟨t,ht,size'⟩ := D.halves
  have sLaw {i j x y} (h : color (closure G) (atPoint Y i) (atPoint Y j) = color (closure G) (atPoint Y x) (atPoint Y y)) :
      s i=s j ↔ s x=s y := by
    have eq : overlap (b i) (b j)=overlap (b x) (b y) := gram_color (sourceLaws _) F Y v b fb h
    rw [hs,hs,eq]
  have tLaw {i j x y} (h : color (closure G) (atPoint Y i) (atPoint Y j) = color (closure G) (atPoint Y x) (atPoint Y y)) :
      t i=t j ↔ t x=t y := by
    have eq : overlap (d i) (d j)=overlap (d x) (d y) := gram_color (sourceLaws _) S Y w d sd h
    rw [ht,ht,eq]
  by_cases aligned : ∀ i j, s i=s j ↔ t i=t j
  · exact Or.inr (fun i j => (hs i j).symm.trans ((aligned i j).trans (ht i j)))
  let M (i j : Eight) := if s i=s j ∧ t i=t j then 1 else 0
  have block : Block Y Y Y Y M M := by
    intro i j x y h
    simp only [M,sLaw h,tLaw h]
  have eq (i) : (part s t i).card=(part s t 0).card := by
    simpa [part,Block.hist,M] using Block.hist_eq (sourceLaws _) block i 0 1
  have bound := small_parts s t size size' eq aligned
  apply Or.inl (RootedTwoChoices.isomorphic (atPoint Y 0) ?_ q)
  intro a
  rcases cover a with h|h|h
  · let i := F.symm ⟨a,h⟩
    have loc : atPoint F i = a := congrArg Subtype.val (F.apply_symm_apply _)
    exact loc ▸ four_at F Y v b fb i
  · let i := S.symm ⟨a,h⟩
    have loc : atPoint S i = a := congrArg Subtype.val (S.apply_symm_apply _)
    exact loc ▸ four_at S Y w d sd i
  · let j := Y.symm ⟨a,h⟩
    have loc : atPoint Y j=a := congrArg Subtype.val (Y.apply_symm_apply _)
    obtain ⟨i,k,short⟩ := DegreeClassRigidity.two_labels (part s t j) 0 (bound j)
    refine ⟨atPoint Y i,atPoint Y k,fun z hz => ?_⟩
    have zz := (end_colors (closure G) hz).2.trans h
    let x := Y.symm ⟨z,zz⟩
    have pos : atPoint Y x=z := congrArg Subtype.val (Y.apply_symm_apply _)
    have compatible : color (closure G) (atPoint Y 0) (atPoint Y j)=color (closure G) (atPoint Y 0) (atPoint Y x) := by
      rw [loc,pos]; exact hz.symm
    have inClass : x∈part s t j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,bit_det _ _ _ (sLaw compatible),bit_det _ _ _ (tLaw compatible)⟩
    rcases short x inClass with eq|eq
    · exact Or.inl (pos.symm.trans (congrArg (atPoint Y) eq))
    · exact Or.inr (pos.symm.trans (congrArg (atPoint Y) eq))

end QGI.Coherent.FourEightPhases
