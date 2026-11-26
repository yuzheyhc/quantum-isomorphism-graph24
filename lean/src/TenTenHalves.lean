import TenTenMoments

namespace QGI.Coherent.TenTenHalves
open SixTenCoordinates hiding V
open TenTenMoments

private theorem grouped (t : V → Fin 6) (w : Fin 6 → Nat) :
    (∑ k, (Finset.univ.filter (fun j => t j=k)).card*w k)=∑ j, w (t j) := by
  have one (k) : (Finset.univ.filter (fun j => t j=k)).card*w k=∑ j, if t j=k then w k else 0 := by
    rw [←Finset.sum_filter,Finset.sum_const,Nat.nsmul_eq_mul]
  simp_rw [one]; rw [Finset.sum_comm]; simp

private theorem profile {h : Fin 6 → Nat}
    (sum : ∑ k, h k=10) (mass : ∑ k : Fin 6, h k*k.val=25) (pos : 0<h 5)
    (div : ∀ k : Fin 6, 5 ∣ h k*k.val) :
    0<h 0 ∧ ∀ s t : Fin 6, 0<s.val → s.val<5 → 0<t.val → t.val<5 → 0<h s → 0<h t → s=t := by
  have prime : Nat.Prime 5 := by decide
  have multiple (k : Fin 6) (ok : ¬5∣k.val) : 5∣h k := (prime.dvd_mul.mp (div k)).resolve_right ok
  obtain ⟨a,e1⟩ := multiple 1 (by decide)
  obtain ⟨b,e2⟩ := multiple 2 (by decide)
  obtain ⟨c,e3⟩ := multiple 3 (by decide)
  obtain ⟨d,e4⟩ := multiple 4 (by decide)
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty] at sum mass
  change h 0+(h 1+(h 2+(h 3+(h 4+(h 5+0)))))=10 at sum
  change h 0*0+(h 1*1+(h 2*2+(h 3*3+(h 4*4+(h 5*5+0)))))=25 at mass
  constructor
  · omega
  · intro s t hs st ht tl sp tp
    have choose : ∀ k : Fin 6, 0<k.val → k.val<5 → k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by decide
    rcases choose s hs st with rfl|rfl|rfl|rfl <;> rcases choose t ht tl with rfl|rfl|rfl|rfl <;> first | rfl | omega

/-- In a regular ten-by-ten rectangle of valency five, all rows of a
single named color are equal to the first row or its complement. -/
theorem parallel {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) (X : Shore c l V) (Y : Shore c r V)
    (a : Nat) (base : c (atPoint X 0) (atPoint Y 0)=a)
    (B : Inc) (bits : ∀ i j, B i j=true ↔ c (atPoint X i) (atPoint Y j)=a)
    (rows : ∀ i, FiberRectangles.degree (B i)=5) (cols : ∀ j, FiberRectangles.degree (fun i => B i j)=5) :
    ∀ i, (∀ j, B i j=B 0 j) ∨ (∀ j, B i j= !(B 0 j)) := by
  classical
  let U (i : V) := Finset.univ.filter (fun j => B i j=true)
  let H := Block.overlap B
  have card (i) : (U i).card=5 := rows i
  have meet (i j) : (U i∩U j).card=H i j := by
    apply congrArg Finset.card; ext k; simp [H,U,Block.overlap]
  have diag (i) : H i i=5 := (meet i i).symm.trans (by rw [Finset.inter_self,card])
  have bound (i j) : H i j≤5 := (meet i j) ▸ ((Finset.card_le_card Finset.inter_subset_left).trans (card i).le)
  let t (i j) : Fin 6 := ⟨H i j,by have := bound i j; omega⟩
  let h (k : Fin 6) := Block.hist H 0 k.val
  have eqFilter (i : V) (k : Fin 6) : Finset.univ.filter (fun j => t i j=k)=Finset.univ.filter (fun j => H i j=k.val) := by
    ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.ext_iff]; rfl
  have sum : ∑ k, h k=10 := by
    have e := grouped (t 0) (fun _ => 1)
    simpa only [eqFilter,Nat.mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,h,Block.hist] using e
  have mass : ∑ k : Fin 6, h k*k.val=25 := by
    have e := grouped (t 0) Fin.val
    simp only [eqFilter] at e
    exact e.trans (by simpa only [gram_overlap] using gram_sum rows cols 0)
  have positive (i j : V) : 0<Block.hist H i (H i j) := Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have found := profile (h:=h) sum mass (by simpa only [h,diag] using positive 0 0)
    (fun k => HalfRectangle.overlap_dvd law X Y a 5 base B bits rows 0 k.val)
  have named : Block X X Y Y B B := by
    intro i j k t e; apply Bool.eq_iff_iff.mpr; rw [bits,bits,e]
  have hist (i : V) (k : Fin 6) : Block.hist H i k.val=h k := Block.hist_eq law (Block.gram law named) i 0 k.val
  obtain ⟨z,hz⟩ := Finset.card_pos.mp found.1
  have dis : Disjoint (U 0) (U z) := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ((meet 0 z).trans (Finset.mem_filter.mp hz).2))
  have comp : U z=(U 0)ᶜ := Finset.eq_of_subset_of_card_le
    (fun v hv => Finset.mem_compl.mpr (fun h₀ => Finset.disjoint_left.mp dis h₀ hv)) (by rw [Finset.card_compl,card,card]; decide)
  have total (i : V) : H 0 i+H z i=5 := by
    have ha : U 0∩U i=(U i).filter (fun k => k∈U 0) := by ext k; simp [and_comm]
    have hb : U z∩U i=(U i).filter (fun k => k∉U 0) := by rw [comp]; ext k; simp [and_comm]
    rw [←meet,←meet,ha,hb,Finset.filter_card_add_filter_neg_card_eq_card,card]
  have pos (i j : V) : 0<h (t i j) := by rw [←hist i]; exact positive i j
  intro i
  have ends : H 0 i=0 ∨ H 0 i=5 := by
    by_contra wrong
    have nz : H 0 i≠0 := fun h => wrong (Or.inl h)
    have nf : H 0 i≠5 := fun h => wrong (Or.inr h)
    have eq := found.2 (t 0 i) (t z i) (by change 0<H 0 i; omega) (by change H 0 i<5; have := bound 0 i; omega)
      (by change 0<H z i; have := total i; have := bound 0 i; omega) (by change H z i<5; have := total i; omega) (pos _ _) (pos _ _)
    have same : H 0 i=H z i := congrArg Fin.val eq
    have := total i; omega
  rcases ends with zero|full
  · right
    have ds := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ((meet 0 i).trans zero))
    have eq : U i=(U 0)ᶜ := Finset.eq_of_subset_of_card_le
      (fun v hv => Finset.mem_compl.mpr (fun h₀ => Finset.disjoint_left.mp ds h₀ hv)) (by rw [Finset.card_compl,card,card]; decide)
    intro j; apply Bool.eq_iff_iff.mpr
    simpa [U] using Finset.ext_iff.mp eq j
  · left
    have eq := (Finset.eq_of_subset_of_card_le Finset.inter_subset_right ((card i).trans ((meet 0 i).trans full).symm).le).symm.trans
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_left ((card 0).trans ((meet 0 i).trans full).symm).le)
    intro j; apply Bool.eq_iff_iff.mpr; simpa [U] using Finset.ext_iff.mp eq j

end QGI.Coherent.TenTenHalves
