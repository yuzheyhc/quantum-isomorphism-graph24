import NineTwelveDesign
import NineNinePartition
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.NineTwelvePartition
open NineTwelveDesign SixTenCoordinates
open private disjoint_degrees from FiberRectangles
abbrev Tri := Fin 3
structure Split (b : Inc) where
  pt : P → Tri
  ln : L → Tri
  onto : Function.Surjective ln
  three : ∀ t, (Finset.univ.filter (fun i => pt i=t)).card=3
  flag : ∀ r x, b r x=true ↔ ln r=pt x

/-- Concurrence four implies that any two points of one triple have
identical columns. The distinct triples therefore partition nine points. -/
theorem split {b : Inc} (rd : ∀ r, (line b r).card=3)
    (cd : ∀ x, FiberRectangles.degree (fun i => b i x)=4)
    (pair : ∀ i x y, b i x=true → b i y=true → x≠y → concurrence b x y=4) : Nonempty (Split b) := by
  classical
  let col := fun x : P => Finset.univ.filter (fun r : L => b r x)
  have colCard (x) : (col x).card=4 := cd x
  have touch {r x y} (hx : b r x=true) (hy : b r y=true) : col x=col y := by
    by_cases eq : x=y
    · rw [eq]
    have h := pair r x y hx hy eq
    have both : (col x ∩ col y).card=4 := by
      have z : col x ∩ col y=Finset.univ.filter (fun i => b i x && b i y) := by
        ext i; simp only [col,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,Bool.and_eq_true]
      simpa only [z,concurrence,Finset.card_filter] using h
    have l : col x ∩ col y=col x := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [both,colCard])
    have r' : col x ∩ col y=col y := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [both,colCard])
    exact l.symm.trans r'
  have lineContains (x) : ∃ r, b r x=true := by
    obtain ⟨r,h⟩ := Finset.card_pos.mp ((by decide : 0<4).trans_eq (colCard x).symm)
    exact ⟨r,(Finset.mem_filter.mp h).2⟩
  have rep (r) : ∃ x, b r x=true := by
    obtain ⟨x,h⟩ := Finset.card_pos.mp ((by decide : 0<3).trans_eq (rd r).symm)
    exact ⟨x,(Finset.mem_filter.mp h).2⟩
  choose point hp using rep
  have hit (r x) : b r x=true ↔ col (point r)=col x := by
    refine ⟨fun hx => touch (hp r) hx,fun eq => ?_⟩
    have h : r∈col (point r) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp r⟩
    have hx : r∈col x := eq ▸ h
    change r∈Finset.univ.filter (fun j => b j x) at hx
    exact (Finset.mem_filter.mp hx).2
  let family := Finset.univ.image col
  have splits (f) (hf : f∈family) : (Finset.univ.filter (fun x => col x=f)).card=3 := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨r,hx⟩ := lineContains x
    have eq : Finset.univ.filter (fun y => col y=col x)=line b r := by
      ext y
      simp only [line,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [hit r y,(hit r x).mp hx]
      exact eq_comm
    rw [eq,rd]
  have total := Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=family)
    (fun x _ => Finset.mem_image_of_mem col (Finset.mem_univ x)) (fun _ => (1:Nat))
  have card : family.card=3 := by
    have h : family.card*3=9 := by
      calc _ = ∑ _ ∈family,(3:Nat) := by simp
           _ = ∑ f ∈family, ∑ _∈Finset.univ.filter (fun x => col x=f),(1:Nat) := by
             apply Finset.sum_congr rfl; intro f hf; simp [splits f hf]
           _ = 9 := total.trans (by simp)
    omega
  let E : {c // c∈family} ≃ Fin 3 := Fintype.equivOfCardEq (by rw [Fintype.card_coe,card,Fintype.card_fin])
  let pt := fun x => E ⟨col x,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have eq (x y) : pt x=pt y ↔ col x=col y := E.injective.eq_iff.trans Subtype.ext_iff
  have onto : Function.Surjective pt := by
    intro t
    obtain ⟨f,rfl⟩ := E.surjective t
    obtain ⟨x,_,ex⟩ := Finset.mem_image.mp f.property
    exact ⟨x,congrArg E (Subtype.ext ex)⟩
  refine ⟨⟨pt,pt ∘ point,?_,?_,fun r x => (hit r x).trans (eq _ _).symm⟩⟩
  · intro tag
    obtain ⟨x,rfl⟩ := onto tag
    obtain ⟨r,flag⟩ := lineContains x
    exact ⟨r,(eq _ _).mpr ((hit r x).mp flag)⟩
  · intro tag
    obtain ⟨x,rfl⟩ := onto tag
    exact (by simpa only [eq] using splits (col x) (Finset.mem_image_of_mem col (Finset.mem_univ x)))

variable {n : Nat} {c : Fin n → Fin n → Nat} {a d : Nat}
abbrev cells (A : Shore c a P) (Y : Shore c d L) := fun r i => c (atPoint Y r) (atPoint A i)
abbrev mark (A : Shore c a P) (Y : Shore c d L) (v : Nat) : Inc := fun r i => decide (cells A Y r i=v)

theorem pointOnto {b : Inc} (s : Split b) : Function.Surjective s.pt := by
  intro t
  obtain ⟨i,h⟩ := Finset.card_pos.mp ((by decide : 0<3).trans_eq (s.three t).symm)
  exact ⟨i,(Finset.mem_filter.mp h).2⟩

theorem named (law : Laws c c) (A : Shore c a P) (Y : Shore c d L) (u : Nat) (s : Split (mark A Y u)) :
    Block A A A A (fun i j => decide (s.pt i=s.pt j)) (fun i j => decide (s.pt i=s.pt j)) := by
  have B : Block Y Y A A (mark A Y u) (mark A Y u) := Block.map Block.names (fun t => decide (t=u))
  have gram := Block.gram law (Block.flip law B)
  have pos (i j : P) : 0<Block.overlap (fun i r => mark A Y u r i) i j ↔ s.pt i=s.pt j := by
    rw [Block.overlap,Finset.card_pos]
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨x,y⟩ := (Finset.mem_filter.mp hr).2
      exact ((s.flag _ _).mp x).symm.trans ((s.flag _ _).mp y)
    · intro eq
      obtain ⟨r,hr⟩ := s.onto (s.pt i)
      exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(s.flag _ _).mpr hr,(s.flag _ _).mpr (hr.trans eq)⟩⟩
  intro i j x y h
  exact Bool.decide_congr ((pos i j).symm.trans ((by rw [gram h] : _ ↔ _).trans (pos x y)))

/-- Independent triple labels for the second color may be re-indexed by
ordering the three point blocks of the first color. A missed pair of
blocks then forces equality of the two partitions. -/
theorem compatible (law : Laws c c) (A : Shore c a P) (Y : Shore c d L)
    {u v : Nat} (uv : u≠v) (s : Split (mark A Y u)) (t : Split (mark A Y v)) :
    ∀ i j, s.pt i=s.pt j → t.pt i=t.pt j := by
  classical
  let tag := QGI.NineNine.Partition.tag
  have cards (z : Tri) : Fintype.card {i : P // tag i=z}=Fintype.card {i : P // s.pt i=z} := by
    simp only [Fintype.card_subtype,tag,QGI.NineNine.Partition.three_each,s.three]
  let h := Equiv.ofFiberEquiv (fun z => Fintype.equivOfCardEq (cards z))
  have labels (i : P) : s.pt (h i)=tag i := Equiv.ofFiberEquiv_map _ i
  let f := t.pt ∘ h
  have count (pred : P → Prop) [DecidablePred pred] :
      (Finset.univ.filter (fun i => pred (h i))).card=(Finset.univ.filter pred).card := by
    simp only [Finset.card_filter]
    exact Equiv.sum_comp h (fun i => if pred i then (1:Nat) else 0)
  have three (z) : (Finset.univ.filter (fun i => f i=z)).card=3 :=
    (count (fun i => t.pt i=z)).trans (t.three z)
  have both := Block.map₂ (named law A Y u s) (named law A Y v t) (fun i j => i && j)
  have uniform (i j : P) : (Finset.univ.filter (fun z => s.pt i=s.pt z ∧ t.pt i=t.pt z)).card=
       (Finset.univ.filter (fun z => s.pt j=s.pt z ∧ t.pt j=t.pt z)).card := by
    simpa only [FiberRectangles.degree,Bool.and_eq_true,decide_eq_true_eq] using Block.degree_eq law both i j
  have joint (j : P) : (Finset.univ.filter (fun i => tag j=tag i ∧ f j=f i)).card=
      (Finset.univ.filter (fun i => tag 0=tag i ∧ f 0=f i)).card := by
    simp only [f,Function.comp_apply,←labels]
    exact (count (fun i => s.pt (h j)=s.pt i ∧ t.pt (h j)=t.pt i)).trans
      ((uniform (h j) (h 0)).trans (count (fun i => s.pt (h 0)=s.pt i ∧ t.pt (h 0)=t.pt i)).symm)
  have miss : ∃ k l, ∀ i : P, tag i=k → f i≠l := by
    refine ⟨s.ln 0,t.ln 0,fun i hi eq => uv ?_⟩
    have su := (s.flag 0 (h i)).mpr (hi.symm.trans (labels i).symm)
    have sv := (t.flag 0 (h i)).mpr eq.symm
    exact (of_decide_eq_true su).symm.trans (of_decide_eq_true sv)
  have same := QGI.NineNine.Partition.same f three joint miss
  intro i j eq
  obtain ⟨i,rfl⟩ := h.surjective i
  obtain ⟨j,rfl⟩ := h.surjective j
  exact same i j ((labels i).symm.trans (eq.trans (labels j)))

theorem palette (law : Laws c c) (A : Shore c a P) (Y : Shore c d L) {u : Nat} (s : Split (mark A Y u))
    (other : ∀ r i, FiberRectangles.degree (mark A Y (cells A Y r i) r) ≤ 4 → Nonempty (Split (mark A Y (cells A Y r i)))) :
    ∀ i j, s.pt i=s.pt j → ∀ r, cells A Y r i=cells A Y r j := by
  intro i j eq r
  by_contra different
  have bounded := disjoint_degrees (cells A Y r) different
  have keeps (x y : P) (sxy : s.pt x=s.pt y)
      (small : FiberRectangles.degree (mark A Y (cells A Y r x) r)≤4) : cells A Y r y=cells A Y r x := by
    let v := cells A Y r x
    by_cases same : u=v
    · have h := (s.flag r x).mp (decide_eq_true same.symm)
      exact of_decide_eq_true ((s.flag r y).mpr (h.trans sxy)) |>.trans same
    · obtain ⟨t⟩ := other r x small
      have h := (t.flag r x).mp (by exact decide_eq_true rfl)
      exact of_decide_eq_true ((t.flag r y).mpr (h.trans (compatible law A Y same s t x y sxy)))
  change FiberRectangles.degree (mark A Y (cells A Y r i) r)+
    FiberRectangles.degree (mark A Y (cells A Y r j) r)≤9 at bounded
  by_cases small : FiberRectangles.degree (mark A Y (cells A Y r i) r)≤4
  · exact different (keeps i j eq small).symm
  · exact different (keeps j i eq.symm (by omega))


end QGI.Coherent.NineTwelvePartition



