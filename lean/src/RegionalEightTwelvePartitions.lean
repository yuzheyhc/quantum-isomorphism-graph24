import RegionalEightTwelveStats
import RegionalEightTwelveEdges

noncomputable section
namespace QGI.Coherent.RegionalEightTwelvePartitions
open SixTenCoordinates StrategyColorLaws RegionalEightTwelveGeometry RegionalEightTwelveStats

abbrev Label := Fin 4

structure Split (a : Index → Cell) where
  point : Point → Label
  column : Index → Label
  two : ∀ s, (Finset.univ.filter (fun i => point i=s)).card=2
  three : ∀ s, (Finset.univ.filter (fun j => column j=s)).card=3
  pair : ∀ j i, i∈a j ↔ point i=column j

private theorem occurrence (a : Index → Cell) (j) : a j∈Finset.univ.image a := Finset.mem_image_of_mem _ (Finset.mem_univ j)

theorem split_repeated (a : Index → Cell) (wt : ∀ j, (a j).card=2) (deg : ∀ i, (incident a i).card=3)
    (copiesSame : ∀ j, copies a j=copies a 0) (dup : ¬Function.Injective a) : Nonempty (Split a) := by
  classical
  have dupe : ∃ i j, a i=a j ∧ i≠j := by
    by_contra! none
    exact dup (fun i j h => none i j h)
  obtain ⟨x,y,xy,ne⟩ := dupe
  have many (j) : 2≤copies a j := by
    have h : 1 < copies a x := Finset.one_lt_card.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,
      y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,xy.symm⟩,ne⟩
    rw [copiesSame x,←copiesSame j] at h
    exact h
  let cl := fun (j : Index) => Finset.univ.filter (fun t => a t=a j)
  have sharing {j k i} (hj : i∈a j) (hk : i∈a k) : a j=a k := by
    by_cases diff : a j=a k
    · exact diff
    have dj : Disjoint (cl j) (cl k) := Finset.disjoint_left.mpr fun _ hu hv =>
      diff ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2)
    have incl (q : Index) (hq : i∈a q) : cl q⊆incident a i := fun t ht =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [(Finset.mem_filter.mp ht).2]; exact hq⟩
    have bound := Finset.card_le_card (Finset.union_subset (incl j hj) (incl k hk))
    rw [Finset.card_union_of_disjoint dj,deg] at bound
    have u : 2≤(cl j).card := many j
    have v : 2≤(cl k).card := many k
    exact False.elim (by omega)
  have three (j) : copies a j=3 := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (wt j).symm)
    have eq : cl j=incident a i := by
      ext t
      simp only [cl,incident,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun h => by rw [h]; exact hi,fun h => sharing h hi⟩
    exact (congrArg Finset.card eq).trans (deg i)
  let family := Finset.univ.image a
  have every : ∀ j∈(Finset.univ : Finset Index), a j∈family := fun j _ => occurrence a j
  have cnt := Finset.sum_fiberwise_of_maps_to every (fun _ => (1:Nat))
  have each (e) (he : e∈family) : ∑ _∈(Finset.univ.filter fun j => a j=e), (1:Nat)=3 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using three j
  have total : family.card*3=12 := by
    calc _ = ∑ _ ∈ family, (3:Nat) := by simp
         _ = ∑ e∈family, ∑ _∈(Finset.univ.filter fun j => a j=e), (1:Nat) := (Finset.sum_congr rfl each).symm
         _ = 12 := cnt.trans (by simp)
  let labels : {e // e∈family} ≃ Label := Fintype.equivOfCardEq (by rw [Fintype.card_coe,Fintype.card_fin]; omega)
  let column (j : Index) := labels ⟨a j,occurrence a j⟩
  have surj : Function.Surjective column := by
    intro s
    obtain ⟨e,he⟩ := labels.surjective s
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp e.property
    exact ⟨j,(congrArg labels (Subtype.ext hj)).trans he⟩
  have hit (i : Point) : ∃ j, i∈a j := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp ((by decide : 0<3).trans_eq (deg i).symm)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  choose atI hat using hit
  let point := column ∘ atI
  have eq (j k) : column j=column k ↔ a j=a k := labels.injective.eq_iff.trans Subtype.ext_iff
  have read (j i) : i∈a j ↔ point i=column j := by
    change i∈a j ↔ column (atI i)=column j
    rw [eq]
    exact ⟨fun h => sharing (hat i) h,fun h => by rw [←h]; exact hat i⟩
  refine ⟨⟨point,column,fun s => ?_,fun s => ?_,read⟩⟩
  · obtain ⟨j,rfl⟩ := surj s
    have h : Finset.univ.filter (fun i => point i=column j)=a j := by ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,read]
    rw [h,wt]
  · obtain ⟨j,rfl⟩ := surj s
    simpa only [copies,eq] using three j

theorem transported {n l r : Nat} {c d : Fin n → Fin n → Nat} (law : Laws c d)
    (F : Shore c l Point) (Y : Shore c r Index) (T : Shore d l Point) (Z : Shore d r Index)
    (v : Nat) (src : Split (family F Y v))
    (left : ∀ i j, c (atPoint F i) (atPoint F j)=d (atPoint T i) (atPoint T j)) (wt : ∀ j, (family T Z v j).card=2)
    (degree : ∀ i, (incident (family T Z v) i).card=3) :
    ∃ b : Index → Label, (∀ j i, i∈family T Z v j ↔ src.point i=b j) ∧
      ∀ s, (Finset.univ.filter (fun j => b j=s)).card=3 := by
  classical
  let a := family F Y v
  let t := family T Z v
  have shared {i k : Point} {j : Index} (h : i∈t j) (g : k∈t j) : src.point i=src.point k := by
    have gram := Block.gram law (Block.flip law (incidence F Y T Z v)) (left i k)
    have common : 0<(Finset.univ.filter (fun j => i∈a j ∧ k∈a j)).card := by
      have hpos := Finset.card_pos.mpr (show (Finset.univ.filter (fun j => i∈t j ∧ k∈t j)).Nonempty from
        ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,g⟩⟩)
      simp only [Block.overlap,decide_eq_true_eq] at gram
      exact hpos.trans_eq gram.symm
    obtain ⟨j,hj⟩ := Finset.card_pos.mp common
    obtain ⟨hi,hk⟩ := (Finset.mem_filter.mp hj).2
    exact ((src.pair j i).mp hi).trans ((src.pair j k).mp hk).symm
  have present (j : Index) := Finset.card_pos.mp ((by decide : 0<2).trans_eq (wt j).symm)
  choose first hf using present
  let b := src.point ∘ first
  have shape (j) : t j=Finset.univ.filter (fun i => src.point i=b j) := Finset.eq_of_subset_of_card_le
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,shared hi (hf j)⟩) (by rw [src.two,wt])
  have read (j i) : i∈t j ↔ src.point i=b j := by rw [shape]; simp
  refine ⟨b,read,fun s => ?_⟩
  obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (src.two s).symm)
  have eq : src.point i=s := (Finset.mem_filter.mp hi).2
  have count : Finset.univ.filter (fun j => b j=s)=incident t i := by
    ext j
    simp only [incident,Finset.mem_filter,Finset.mem_univ,true_and,read,eq,eq_comm]
  exact (congrArg Finset.card count).trans (degree i)

end QGI.Coherent.RegionalEightTwelvePartitions

