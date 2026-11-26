import SevenSevenCatalog
import SixTenCoordinates

namespace QGI.Coherent.SevenSevenFano
open SevenSevenCatalog
open SixTenCoordinates (Laws Shore atPoint Block)

private theorem obstruct (d : V → Nat) (total : ∑ j, d j=9)
    (unique : ∀ j k, d j=3 → d k=3 → j=k) (m : M)
    (stable : ∀ j k, m 0 j=m 0 k → d j=d k) (out : Uniform m ∨ Strong m) : False := by
  classical
  rcases out with all|⟨i,j,x,y,pal,row,_,_⟩
  · have con (j) : d j=d 0 := stable j 0 (all 0 j)
    rw [Finset.sum_congr rfl (fun j _ => con j)] at total
    simp only [Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul] at total
    omega
  let R := Finset.univ.filter (fun k => m 0 k=m i j)
  let B := Finset.univ.filter (fun k => m 0 k≠m i j)
  have red : R.card=3 := by simpa only [R,Finset.sum_boole] using row 0
  have both : R.card+B.card=7 := Finset.filter_card_add_filter_neg_card_eq_card _
  have blue : B.card=4 := by omega
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0<R.card)
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0<B.card)
  have hr' := (Finset.mem_filter.mp hr).2
  have hb' := (Finset.mem_filter.mp hb).2
  have covered (k) : d k=if m 0 k=m i j then d r else d b := by
    split_ifs with hit
    · exact stable k r (hit.trans hr'.symm)
    · exact stable k b (((pal 0 k).resolve_left hit).trans ((pal 0 b).resolve_left hb').symm)
  have mass : 3*d r+4*d b=9 := by
    rw [Finset.sum_congr rfl (fun k _ => covered k),Finset.sum_ite] at total
    simpa only [Finset.sum_const,smul_eq_mul,←red,←blue] using total
  have r3 : d r=3 := by omega
  have card : R.card≤1 := Finset.card_le_one.mpr (by
    intro k hk l hl
    apply unique
    · exact (stable k r ((Finset.mem_filter.mp hk).2.trans hr'.symm)).trans r3
    · exact (stable l r ((Finset.mem_filter.mp hl).2.trans hr'.symm)).trans r3)
  omega

/-- Two ternary Fano incidences cannot meet in a seven-point shore when
the outer rectangle is uniform or again has the Fano two-color palette. -/
theorem no_chain {n} {c : Fin n → Fin n → Nat} {a b s}
    (law : Laws c c) (A : Shore c a V) (B : Shore c b V) (Y : Shore c s V)
    (h₁ : Strong (fun i j => c (atPoint A i) (atPoint B j)))
    (h₂ : Strong (fun i j => c (atPoint B i) (atPoint Y j)))
    (out : Uniform (fun i j => c (atPoint A i) (atPoint Y j)) ∨
      Strong (fun i j => c (atPoint A i) (atPoint Y j))) : False := by
  classical
  let l := fun i j => c (atPoint A i) (atPoint B j)
  let r := fun i j => c (atPoint B i) (atPoint Y j)
  obtain ⟨i,j,x,y,_,rows,_,_⟩ := h₁
  obtain ⟨k,z,u,w,_,row,col,sep⟩ := h₂
  let L := Finset.univ.filter (fun t => l 0 t=l i j)
  let N := fun q => Finset.univ.filter (fun t => r t q=r k z)
  let d := fun q => (L∩N q).card
  have left : L.card=3 := by simpa only [L,l,Finset.sum_boole] using rows 0
  have right (q) : (N q).card=3 := by simpa only [N,r,Finset.sum_boole] using col q
  have term (q) : d q=∑ t, if l 0 t=l i j ∧ r t q=r k z then (1:Nat) else 0 := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext t; simp [L,N]
  have total : ∑ q, d q=9 := by
    rw [Finset.sum_congr rfl (fun q _ => term q),Finset.sum_comm]
    have along (t) : (∑ q, if l 0 t=l i j ∧ r t q=r k z then (1:Nat) else 0)=
        if l 0 t=l i j then 3 else 0 := by
      by_cases h : l 0 t=l i j
      · simpa only [h,true_and,if_true] using row t
      · simp [h]
    rw [Finset.sum_congr rfl (fun t _ => along t),Finset.sum_ite]
    simp only [Finset.sum_const,smul_eq_mul,Finset.sum_const_zero,add_zero]
    change L.card*3=9; rw [left]
  have eqset (q) (hq : d q=3) : L=N q := by
    have e : L∩N q=L := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by change L.card≤d q; omega)
    exact e.symm.trans (Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      (by change (N q).card≤d q; rw [right,hq]))
  have unique (q t) (hq : d q=3) (ht : d t=3) : q=t := by
    apply sep
    intro v
    have setEq := (eqset q hq).symm.trans (eqset t ht)
    simpa only [N,r,Finset.mem_filter,Finset.mem_univ,true_and] using
      (show v∈N q ↔ v∈N t from setEq ▸ Iff.rfl)
  apply obstruct d total unique _ _ out
  intro q t eq
  rw [term,term]
  exact Block.fold (L:=A) (L':=A) (M:=B) (M':=B) (R:=Y) (R':=Y) law
    Block.names Block.names (fun v w => if v=l i j ∧ w=r k z then 1 else 0) eq

end QGI.Coherent.SevenSevenFano



