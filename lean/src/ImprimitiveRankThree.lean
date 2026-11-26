import RowValencies

namespace QGI.RowCensus

variable {n : Nat} [NeZero n]

def palette (c : Table n Nat) := Finset.univ.image fun p : Fin n × Fin n => c p.1 p.2

/-- A nontrivial equivalence relation that is a union of basic relations. -/
structure Imprimitivity (c : Table n Nat) where
  blocks : Setoid (Fin n)
  inside : ∃ i j, i≠j ∧ blocks.r i j
  outside : ∃ i j, ¬blocks.r i j
  invariant : ∀ i j x y, c i j=c x y → (blocks.r i j ↔ blocks.r x y)

/-- A rank-three imprimitive scheme is determined by the number and size
of its blocks. The proof applies to directed schemes as well. -/
theorem imprimitive_rank_three {c : Table n Nat} (h : Laws c) (rank : (palette c).card≤3)
    (b : Imprimitivity c) :
    ∃ t d : Nat, 1<t ∧ 1<d ∧ t*d=n ∧ ∃ f : Fin n ≃ Fin t × Fin d,
    ∀ i j x y, c i j=c x y ↔ ((i=j ↔ x=y) ∧ ((f i).1=(f j).1 ↔ (f x).1=(f y).1)) := by
  classical
  obtain ⟨a,b',neq,within⟩ := b.inside
  obtain ⟨u,v,apart⟩ := b.outside
  let diag := c 0 0
  let inner := c a b'
  let outer := c u v
  have different₀ : inner≠diag := fun eq => neq ((h.diagonal _ _).mp eq)
  have different₁ : outer≠diag := fun eq => apart (((h.diagonal _ _).mp eq) ▸ b.blocks.refl _)
  have different₂ : outer≠inner := fun eq => apart ((b.invariant _ _ _ _ eq).mpr within)
  have occurs (i j : Fin n) : c i j∈palette c := Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩
  let three : Finset Nat := {outer,inner,diag}
  have subset : three ⊆ palette c := by
    intro z hz
    rcases (by simpa [three] using hz : z=outer ∨ z=inner ∨ z=diag) with rfl|rfl|rfl
    · exact occurs _ _
    · exact occurs _ _
    · exact occurs _ _
  have card : three.card=3 := by simp [three,different₀,different₁,different₂]
  have all := Finset.eq_of_subset_of_card_le subset (rank.trans_eq card.symm)
  have casesColor (i j : Fin n) : c i j=outer ∨ c i j=inner ∨ c i j=diag := by
    have it : c i j∈three := all ▸ occurs i j
    simpa [three] using it
  have inBlock (i j : Fin n) : b.blocks.r i j ↔ c i j=inner ∨ c i j=diag := by
    constructor
    · intro same
      rcases casesColor i j with out|inside|d
      · exact (apart ((b.invariant _ _ _ _ out).mp same)).elim
      · exact Or.inl inside
      · exact Or.inr d
    · rintro (eq|eq)
      · exact (b.invariant _ _ _ _ eq).mpr within
      · exact (b.invariant _ _ _ _ eq).mpr (b.blocks.refl 0)
  have shape (i j x y : Fin n) : c i j=c x y ↔
      ((i=j ↔ x=y) ∧ (b.blocks.r i j ↔ b.blocks.r x y)) := by
    constructor
    · intro eq; exact ⟨(h.diagonal _ _).symm.trans (eq ▸ (h.diagonal _ _)),b.invariant _ _ _ _ eq⟩
    · rintro ⟨hd,hb⟩
      have diagEquiv := (h.diagonal i j).trans (hd.trans (h.diagonal x y).symm)
      have innerEquiv := (inBlock i j).symm.trans (hb.trans (inBlock x y))
      rcases casesColor i j with c1|c1|c1 <;> rcases casesColor x y with c2|c2|c2 <;>
        simp_all only [diag,ne_eq] <;> aesop
  let Q := Quotient b.blocks
  let q : Fin n → Q := Quotient.mk b.blocks
  letI : Fintype Q := Fintype.ofFinite Q
  let t := Fintype.card Q
  let d := Fintype.card {x : Fin n // q x=q 0}
  have rel (i j : Fin n) : q i=q j ↔ b.blocks.r i j := Quotient.eq
  have count (i : Fin n) : Fintype.card {x : Fin n // q x=q i} =
      ((List.ofFn (c i)).filter fun z => decide (z=inner ∨ z=diag)).length := by
    rw [Fintype.card_subtype,length_filter_ofFn]
    rw [← Nat.cast_id (Finset.univ.filter (fun x => q x=q i)).card, ← Finset.sum_boole (α:=Nat)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [rel,decide_eq_true_eq]
    rw [show b.blocks.r j i ↔ c i j=inner ∨ c i j=diag from
      (show b.blocks.r j i ↔ b.blocks.r i j from ⟨b.blocks.symm,b.blocks.symm⟩).trans (inBlock i j)]
    split_ifs <;> rfl
  have uniform (s : Q) : Fintype.card {x : Fin n // q x=s}=d := Quotient.inductionOn s (fun i => by
    change Fintype.card {x : Fin n // q x=q i}=Fintype.card {x : Fin n // q x=q 0}
    rw [count i,count 0]
    exact ((h.row_perm i).filter _).length_eq)
  have tm : 1<t := Fintype.one_lt_card_iff.mpr ⟨q u,q v,fun eq => apart ((rel _ _).mp eq)⟩
  have dm : 1<d := by
    rw [← uniform (q a)]
    exact Fintype.one_lt_card_iff.mpr ⟨⟨a,rfl⟩,⟨b',(rel _ _).mpr (b.blocks.symm within)⟩,fun eq => neq (congrArg Subtype.val eq)⟩
  let index := Fintype.equivFin Q
  let coord (s : Q) := Fintype.equivFinOfCardEq (uniform s)
  let f : Fin n ≃ Fin t × Fin d :=
    (Equiv.sigmaFiberEquiv q).symm.trans ((Equiv.sigmaCongrRight coord).trans
      ((Equiv.sigmaEquivProd Q (Fin d)).trans (Equiv.prodCongr index (Equiv.refl _))))
  have first (i : Fin n) : (f i).1=index (q i) := rfl
  have cardinal := (Fintype.card_congr f).symm
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin] at cardinal
  refine ⟨t,d,tm,dm,cardinal,f,?_⟩
  intro i j x y
  simpa only [first,index.injective.eq_iff,rel] using shape i j x y

def blockSizes : Nat → List Nat
  | 16 => [2,4,8]
  | 18 => [2,3,6,9]
  | 20 => [2,4,5,10]
  | 21 => [3,7]
  | 22 => [2,11]
  | _ => []

private theorem smallFactors : ∀ n t d : Fin 24, 16≤n.val → 1<t.val → 1<d.val →
    t.val*d.val=n.val → d.val∈blockSizes n.val := by native_decide

def blockColor {n : Nat} (d : Nat) (i j : Fin n) := if i=j then 0 else if i.val/d=j.val/d then 1 else 2

/-- Explicit normal forms for every imprimitive scheme of rank at most three
at each order from sixteen through twenty-three. -/
theorem block_models {c : Table n Nat} (lo : 16≤n) (hi : n≤23) (h : Laws c)
    (rank : (palette c).card≤3) (b : Imprimitivity c) :
    ∃ d∈blockSizes n, Iso (blockColor d) c := by
  obtain ⟨t,d,ht,hd,size,f,hf⟩ := imprimitive_rank_three h rank b
  have tb : t≤n := size ▸ Nat.le_mul_of_pos_right t (by omega)
  have db : d≤n := size ▸ Nat.le_mul_of_pos_left d (by omega)
  refine ⟨d,smallFactors ⟨n,by omega⟩ ⟨t,by omega⟩ ⟨d,by omega⟩ lo ht hd size,?_⟩
  let z : Fin n ≃ Fin t × Fin d := (finCongr size.symm).trans finProdFinEquiv.symm
  let p := z.trans f.symm
  have first (i : Fin n) : (f (p i)).1.val=i.val/d := by simp only [p,Equiv.trans_apply,Equiv.apply_symm_apply]; rfl
  have blocks (i j : Fin n) : (f (p i)).1=(f (p j)).1 ↔ i.val/d=j.val/d := by rw [←first i,←first j,Fin.val_inj]
  refine ⟨p,fun i j x y => ?_⟩
  rw [hf,blocks,blocks,p.injective.eq_iff,p.injective.eq_iff]
  by_cases ij : i=j <;> by_cases xy : x=y <;> by_cases a : i.val/d=j.val/d <;>
    by_cases b' : x.val/d=y.val/d <;> simp_all [blockColor]

/-- With at most two basic relations every off-diagonal pair has the same color. -/
theorem rank_two {c : Table n Nat} (h : Laws c) (rank : (palette c).card≤2) :
    Iso (blockColor n) c := by
  have off (i j x y : Fin n) (ij : i≠j) (xy : x≠y) : c i j=c x y := by
    by_contra different
    have a : c i j≠c 0 0 := fun eq => ij ((h.diagonal _ _).mp eq)
    have b : c x y≠c 0 0 := fun eq => xy ((h.diagonal _ _).mp eq)
    have occurs (u v : Fin n) : c u v∈palette c := Finset.mem_image.mpr ⟨(u,v),Finset.mem_univ _,rfl⟩
    have incl : ({c i j,c x y,c 0 0} : Finset Nat) ⊆ palette c := by
      intro z hz
      rcases (by simpa using hz : z=c i j ∨ z=c x y ∨ z=c 0 0) with rfl|rfl|rfl <;> apply occurs
    have sz := (Finset.card_le_card incl).trans rank
    simp [different,a,b] at sz
  refine ⟨Equiv.refl _,fun i j x y => ?_⟩
  simp only [Equiv.refl_apply,blockColor,Nat.div_eq_of_lt i.isLt,Nat.div_eq_of_lt j.isLt,
    Nat.div_eq_of_lt x.isLt,Nat.div_eq_of_lt y.isLt,if_true]
  by_cases ij : i=j <;> by_cases xy : x=y
  · subst j; subst y; simp [(h.diagonal i i).mpr rfl,(h.diagonal x x).mpr rfl]
  · subst j; simp [xy,(h.diagonal i i).mpr rfl,eq_comm (a:=c 0 0),h.diagonal]
  · subst y; simp [ij,(h.diagonal x x).mpr rfl,h.diagonal]
  · simp [ij,xy,off i j x y ij xy]

end QGI.RowCensus
