import SixTenCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators
namespace QGI.Coherent.ElevenBiplane
open SixTenCoordinates
abbrev V := Fin 11
def Parameters (B : V → V → Bool) :=
  (∀ i, FiberRectangles.degree (B i)=5) ∧
  (∀ j, FiberRectangles.degree (fun i => B i j)=5) ∧ ∀ i j, i≠j → Block.overlap B i j=2

private def bit (b : Bool) : ℚ := if b then 1 else 0

private theorem sum_bit (f : V → Bool) : ∑ i, bit (f i)=(FiberRectangles.degree f : ℚ) := by
  simp [bit,FiberRectangles.degree,Finset.sum_boole]

private theorem sum_pair (B : V → V → Bool) (i j : V) :
    ∑ z, bit (B i z)*bit (B j z)=(Block.overlap B i j : ℚ) := by
  calc
    _ = ∑ z : V, if B i z=true ∧ B j z=true then (1:ℚ) else 0 := Finset.sum_congr rfl fun z _ => by
      cases h : B i z <;> cases g : B j z <;> simp [bit,h,g]
    _ = _ := by simp [Block.overlap,Finset.sum_boole]

/-- For the square incidence matrix N the matrix Nᵀ/3 - 2J/15 is a right
inverse. Its left-inverse identity gives the common size of two columns. -/
theorem dual {B : V → V → Bool} (h : Parameters B) {i j : V} (ne : i≠j) :
    Block.overlap (fun x y => B y x) i j=2 := by
  let N : Matrix V V ℚ := fun x y => bit (B x y)
  let P : Matrix V V ℚ := fun x y => bit (B y x)/3-2/15
  have mul : N*P=1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, bit (B x z)*(bit (B y z)/3-2/15))=_
    simp_rw [mul_sub,mul_div_assoc',Finset.sum_sub_distrib,←Finset.sum_div,←Finset.sum_mul]
    rw [sum_pair,sum_bit,h.1]
    by_cases eq : x=y
    · subst y
      have diag : Block.overlap B x x=5 := by simpa [Block.overlap,FiberRectangles.degree] using h.1 x
      rw [diag]; norm_num
    · rw [h.2.2 x y eq]; simp [eq]; norm_num
  have left := congrFun (congrFun (Matrix.mul_eq_one_comm.mp mul) i) j
  rw [Matrix.mul_apply,Matrix.one_apply,if_neg ne] at left
  change (∑ z, (bit (B z i)/3-2/15)*bit (B z j))=0 at left
  simp_rw [sub_mul,div_mul_eq_mul_div,Finset.sum_sub_distrib,←Finset.sum_div,←Finset.mul_sum] at left
  have sums := sum_pair (fun x y => B y x) i j
  rw [sums,sum_bit,h.2.1] at left
  exact_mod_cast (show (Block.overlap (fun x y => B y x) i j : ℚ)=2 by linarith)

/-- Through one point are five blocks. Every other point belongs to a unique
pair of these blocks. These are the eleven possible column labels. -/
private def pairLabel : V → Finset (Fin 5) :=
  ![Finset.univ,{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}]
private def labelIndex (s : Finset (Fin 5)) : V :=
  ((List.finRange 11).find? fun j => pairLabel j=s).getD 0
private theorem label_complete : ∀ s : Finset (Fin 5), s=Finset.univ ∨ s.card=2 → pairLabel (labelIndex s)=s := by native_decide

private def star (i : Fin 5) : Finset V := Finset.univ.filter fun j => i∈pairLabel j

/-- The other six blocks miss the root and use two edges through each
vertex of K₅, hence are drawn from the twelve pentagons. -/
private def isCycle (s : Finset V) : Prop :=
  0∉s ∧ s.card=5 ∧ ∀ i : Fin 5, (s ∩ star i).card=2
private instance (s : Finset V) : Decidable (isCycle s) := by unfold isCycle; infer_instance
private def cycle : Fin 12 → Finset V :=
  ![{1,4,5,8,10},{1,3,5,9,10},{1,4,6,8,9},{1,2,6,9,10},{1,3,7,8,9},{1,2,7,8,10},
    {2,4,5,6,10},{2,3,5,7,10},{2,4,6,7,8},{2,3,6,7,9},{3,4,5,6,9},{3,4,5,7,8}]
private def cycleIndex (s : Finset V) : Fin 12 := ((List.finRange 12).find? fun i => cycle i=s).getD 0
private theorem cycle_complete : ∀ s : Finset V, isCycle s → cycle (cycleIndex s)=s := by native_decide

private def compatible (F : Finset (Fin 12)) : Prop :=
  F.card=6 ∧ ∀ i ∈ F, ∀ j ∈ F, i≠j → (cycle i ∩ cycle j).card=2
private instance (F : Finset (Fin 12)) : Decidable (compatible F) := by unfold compatible; infer_instance

private def blockSet (F : Finset (Fin 12)) : Finset (Finset V) :=
  Finset.univ.image star ∪ F.image cycle

/-- The transposition of the first two base blocks exchanges the two
pentagon families. On the ten edges it swaps 02/12, 03/13 and 04/14. -/
private def switchCols : Equiv.Perm V :=
  (Equiv.swap 2 5).trans ((Equiv.swap 3 6).trans (Equiv.swap 4 7))
private def colPerm (swap : Bool) : Equiv.Perm V := if swap then switchCols else Equiv.refl V

private theorem frames_match : ∀ F : Finset (Fin 12), compatible F → ∀ G : Finset (Fin 12), compatible G →
    ∃ swap : Bool, (blockSet F).image (fun s => s.image (colPerm swap))=blockSet G := by native_decide


private def support (B : V → V → Bool) (i : V) : Finset V :=
  Finset.univ.filter fun j => B i j=true

private theorem common {B : V → V → Bool} (h : Parameters B) (i j : V) (ne : i≠j) :
    (support B i ∩ support B j).card=2 := by
  convert h.2.2 i j ne using 1
  apply congrArg Finset.card
  ext; simp [support,Block.overlap]

private theorem distinct_rows {B : V → V → Bool} (h : Parameters B) : Function.Injective (support B) := by
  intro i j eq
  by_contra ne
  have v := common h i j ne
  rw [←eq,Finset.inter_self] at v
  have sz : (support B i).card=5 := h.1 i
  omega

private theorem two_columns {B : V → V → Bool} (h : Parameters B) :
    ∃ (r : Fin 5 → V) (e : Equiv.Perm V), Function.Injective r ∧ e 0=0 ∧
      (∀ j, B j 0=true ↔ ∃ i, r i=j) ∧
      ∀ i j, B (r i) j=true ↔ i∈pairLabel (e j) := by
  classical
  let roots := (Finset.univ : Finset V).filter fun i => B i 0=true
  have rootCard : roots.card=5 := h.2.1 0
  let order := roots.orderIsoOfFin rootCard
  let r := fun i : Fin 5 => (order i).val
  have inj : Function.Injective r := fun i j eq => order.injective (Subtype.ext eq)
  have through (i : Fin 5) : B (r i) 0=true := (Finset.mem_filter.mp (order i).property).2
  have hits (j : V) : B j 0=true ↔ ∃ i, r i=j := by
    refine ⟨fun hj => ?_,fun ⟨i,hi⟩ => hi ▸ through i⟩
    let x : roots := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
    exact ⟨order.symm x,congrArg Subtype.val (order.apply_symm_apply x)⟩
  let label := fun j : V => Finset.univ.filter fun i : Fin 5 => B (r i) j=true
  have root : label 0=Finset.univ := by ext i; simp [label,through]
  have sz (j : V) (ne : j≠0) : (label j).card=2 := by
    have eq : (label j).image r=Finset.univ.filter (fun i => B i 0=true ∧ B i j=true) := by
      ext x
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,label]
      constructor
      · rintro ⟨u,hu,rfl⟩; exact ⟨through _,hu⟩
      · rintro ⟨hx,hj⟩
        obtain ⟨u,rfl⟩ := (hits _).mp hx
        exact ⟨u,hj,rfl⟩
    rw [←Finset.card_image_of_injective (label j) inj,eq]
    exact dual h (Ne.symm ne)
  have valid (j : V) : pairLabel (labelIndex (label j))=label j := by
    apply label_complete
    by_cases eq : j=0
    · exact Or.inl (eq ▸ root)
    · exact Or.inr (sz j eq)
  have same : Function.Injective label := by
    intro i j eq
    by_contra ne
    have notRoot (x y : V) (d : x≠y) (same : label x=label y) : x≠0 := by
      rintro rfl
      have small := sz y (Ne.symm d)
      rw [←same,root] at small
      simp at small
    have ni := notRoot i j ne eq
    have nj := notRoot j i (Ne.symm ne) eq.symm
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1<(label i).card by rw [sz i ni]; decide)
    have member (u : Fin 5) (hu : u∈label i) :
        0 ∈ support B (r u) ∧ i ∈ support B (r u) ∧ j ∈ support B (r u) := by
      have hv := eq ▸ hu
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,through u⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hu).2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩⟩
    have ma := member a ha
    have mb := member b hb
    have sub : ({0,i,j} : Finset V) ⊆ support B (r a) ∩ support B (r b) := by
      intro x hx
      rcases (by simpa using hx : x=0 ∨ x=i ∨ x=j) with rfl|rfl|rfl
      · exact Finset.mem_inter.mpr ⟨ma.1,mb.1⟩
      · exact Finset.mem_inter.mpr ⟨ma.2.1,mb.2.1⟩
      · exact Finset.mem_inter.mpr ⟨ma.2.2,mb.2.2⟩
    have bound := Finset.card_le_card sub
    rw [common h _ _ (inj.ne ab)] at bound
    simp [ni.symm,nj.symm,ne] at bound
  have indexInj : Function.Injective (fun j => labelIndex (label j)) := fun x y he =>
    same ((valid x).symm.trans ((congrArg pairLabel he).trans (valid y)))
  let e := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp indexInj)
  have atRoot : e 0=0 := by
    change labelIndex (label 0)=0
    rw [root]
    native_decide
  refine ⟨r,e,inj,atRoot,hits,fun i j => ?_⟩
  change _ ↔ i∈pairLabel (labelIndex (label j))
  simp [valid,label]

private structure Frame (B : V → V → Bool) where
  cols : Equiv.Perm V
  family : Finset (Fin 12)
  admissible : compatible family
  rows : Finset.univ.image (fun i => (support B i).image cols)=blockSet family

private theorem frame {B : V → V → Bool} (h : Parameters B) : Nonempty (Frame B) := by
  classical
  obtain ⟨r,e,inj,root,hits,labels⟩ := two_columns h
  let S (i : V) := (support B i).image e
  have entry (i j : V) : e j ∈ S i ↔ B i j=true := by simp [S,support]
  have size (i : V) : (S i).card=5 := (Finset.card_image_of_injective _ e.injective).trans (h.1 i)
  have sec (i j : V) (ne : i≠j) : (S i ∩ S j).card=2 := by
    change ((support B i).image e ∩ (support B j).image e).card=2
    have image : (support B i).image e ∩ (support B j).image e=(support B i ∩ support B j).image e := by
      ext x
      obtain ⟨z,rfl⟩ := e.surjective x
      simp
    rw [image,Finset.card_image_of_injective _ e.injective]
    exact common h i j ne
  have starEq (u : Fin 5) : S (r u)=star u := by
    ext x
    obtain ⟨j,rfl⟩ := e.surjective x
    simpa [star] using (entry (r u) j).trans (labels u j)
  let rest := Finset.univ.filter fun i => B i 0≠true
  have restSize : rest.card=6 := by
    have total := Finset.filter_card_add_filter_neg_card_eq_card (s:=Finset.univ) (fun i : V => B i 0=true)
    have five := h.2.1 0
    change (Finset.univ.filter (fun i => B i 0=true)).card=5 at five
    change (Finset.univ.filter (fun i => B i 0=true)).card+rest.card=_ at total
    simp only [Finset.card_univ,Fintype.card_fin] at total
    omega
  have cyc (i : V) (mem : i∈rest) : isCycle (S i) := by
    have away := (Finset.mem_filter.mp mem).2
    refine ⟨fun atZero => away ((entry i 0).mp (root.symm ▸ atZero)),size i,fun u => ?_⟩
    rw [←starEq]
    exact sec i (r u) (fun eq => away ((hits i).mpr ⟨u,eq.symm⟩))
  let number := fun i => cycleIndex (S i)
  have decode (i : V) (hi : i∈rest) : cycle (number i)=S i := cycle_complete _ (cyc i hi)
  have unique : Function.Injective S := fun i j eq => distinct_rows h
    ((Finset.image_injective e.injective) eq)
  let F := rest.image number
  have count : F.card=6 := by
    rw [←restSize]
    apply Finset.card_image_iff.mpr
    intro i hi j hj eq
    exact unique ((decode _ hi).symm.trans ((congrArg cycle eq).trans (decode _ hj)))
  have ok : compatible F := by
    refine ⟨count,?_⟩
    intro u hu v hv ne
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    rw [decode _ hi,decode _ hj]
    exact sec i j (fun eq => ne (congrArg number eq))
  refine ⟨⟨e,F,ok,?_⟩⟩
  change Finset.univ.image S=_
  ext s
  simp only [blockSet,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases through : B i 0=true
    · obtain ⟨u,rfl⟩ := (hits i).mp through
      exact Or.inl ⟨u,(starEq u).symm⟩
    · have hi : i∈rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _,through⟩
      exact Or.inr ⟨number i,Finset.mem_image_of_mem _ hi,decode _ hi⟩
  · rintro (⟨u,rfl⟩|⟨v,hv,rfl⟩)
    · exact ⟨r u,starEq u⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i,(decode _ hi).symm⟩

theorem unique_design (A B : V → V → Bool) (ha : Parameters A) (hb : Parameters B) :
    ∃ e f : Equiv.Perm V, ∀ i j, A i j=B (e i) (f j) := by
  classical
  obtain ⟨a⟩ := frame ha
  obtain ⟨b⟩ := frame hb
  obtain ⟨sw,hs⟩ := frames_match _ a.admissible _ b.admissible
  let f := a.cols.trans ((colPerm sw).trans b.cols.symm)
  have hits (i : V) : ∃ j, (support A i).image f=support B j := by
    have hi := Finset.mem_image_of_mem (fun v => (support A v).image a.cols) (Finset.mem_univ i)
    rw [a.rows] at hi
    have hs' := Finset.mem_image_of_mem (fun s : Finset V => s.image (colPerm sw)) hi
    rw [hs,←b.rows] at hs'
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hs'
    refine ⟨j,Finset.ext fun x => ?_⟩
    have hx := Finset.ext_iff.mp eq (b.cols x)
    simpa [f,Finset.mem_image,Equiv.trans_apply,Equiv.symm_apply_eq] using hx.symm
  choose g hg using hits
  have inj : Function.Injective g := by
    intro i j eq
    apply distinct_rows ha
    apply Finset.image_injective f.injective
    rw [hg,hg,eq]
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp inj),f,fun i j => ?_⟩
  have same := Finset.ext_iff.mp (hg i) (f j)
  change A i j=B (g i) (f j)
  have bitEq : (A i j=true ↔ B (g i) (f j)=true) := by simpa [support] using same
  cases ha : A i j <;> cases hb : B (g i) (f j) <;> simp_all

end QGI.Coherent.ElevenBiplane
