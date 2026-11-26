import HighRowExtensions
import TwelveRowCensus
import TwelveThinCensus
import data.RowCensus12High

namespace QGI.TwelveHighCensus
open RowCensus

/-- All nonthin relations have valency two; exactly two or four colors have valency one. -/
def quasi (r : List Nat) := (∀ a∈r, r.count a≤2) ∧ (thinCount r=2 ∨ thinCount r=4)

private def high (w : Nat) : Bool :=
  let r := wordDigits 12 w
  decide (5<r.toFinset.card ∧ thinCount r∣12 ∧ thinCount r<12 ∧
    ¬((r.all (fun a => r.count a≤2))=true ∧ (thinCount r=2 ∨ thinCount r=4)))

def Remaining (c : Table 12 Nat) : Prop :=
  ∃ m : Matrix 12, Laws m ∧ RowCensus.Iso m c ∧ word m 0 ∈ blockRoots 12 ∧ quasi (wordDigits 12 (word m 0))

private def certificates := decode raw12High
private def useUnit (rs : List Nat) := (List.range rs.length).any fun i =>
  (wordDigits 12 (rs.getD 0 0)).count (entry 12 rs i rs.length)==1

private def options (rs : List Nat) := if rs.isEmpty then (blockRoots 12).filter high else
  if capacity (wordDigits 12 (rs.getD 0 0)) then
    (if useUnit rs then unitRows 12 rs else highRows 12 rs)
  else []

set_option maxRecDepth 100000 in
private theorem checked : (List.range certificates.size).all
    (fun i => verifiedBy TwelveRowCensus.cells options certificates i)=true := by native_decide

private theorem casesOfRoot : (blockRoots 12).all (fun w =>
    let r := wordDigits 12 w
    decide (r.toFinset.card≤5) || decide (∀ i j : Fin 12, digit 12 w i.val=digit 12 w j.val → i=j) ||
      !(decide (thinCount r∣12)) || high w ||
      ((r.all (fun a => r.count a≤2)) && decide (thinCount r=2 ∨ thinCount r=4)))=true := by native_decide

theorem catalog_or_remaining (c : Table 12 Nat) (h : Laws c) :
    (∃ a, RowCensus.Iso (TwelveRowCensus.cells a) c) ∨ Remaining c := by
  obtain ⟨m,p,g,hm,root,acts,names⟩ := normalize_blocks c h
  let natM : Table 12 Nat := fun i j => (m i j).val
  have inRoot : TwelveRowCensus.rank natM=(wordDigits 12 (word m 0)).toFinset.card := by
    apply congrArg Finset.card
    ext a
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Prod.exists,wordDigits,digit_word,
      List.mem_toFinset,List.mem_ofFn,natM]
    constructor
    · rintro ⟨i,j,e⟩
      obtain ⟨z,hz⟩ := List.mem_ofFn.mp ((hm.row_perm i).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
      exact ⟨z,(congrArg Fin.val hz).trans e⟩
    · rintro ⟨i,e⟩; exact ⟨0,i,e⟩
  have finish (proof : ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) m) :
      ∃ a, RowCensus.Iso (TwelveRowCensus.cells a) c := by
    obtain ⟨a,e,iso⟩ := proof
    exact ⟨a,e.trans p,fun i j x y => (iso i j x y).trans (names _ _ _ _)⟩
  have optionsRoot := List.all_eq_true.mp casesOfRoot _ root
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not,
    List.all_eq_true] at optionsRoot
  rcases optionsRoot with (((low|thin)|bad)|easy)|residual
  · have nh : Laws natM := hm.transport (Equiv.refl _) Fin.val (fun _ _ _ _ e => Fin.ext e)
    obtain ⟨a,e,iso⟩ := TwelveRowCensus.rank_five natM nh (inRoot ▸ low)
    exact Or.inl (finish ⟨a,e,fun i j x y => (iso i j x y).trans Fin.val_inj⟩)
  · have first : Function.Injective (m 0) := fun i j eq => thin i j (by simpa using congrArg Fin.val eq)
    have th (i : Fin 12) := List.nodup_ofFn.mp ((hm.row_perm i).nodup_iff.mpr (List.nodup_ofFn.mpr first))
    exact Or.inl (finish (twelve_thin hm th))
  · exact (bad (by simpa [wordDigits] using thinCount_dvd hm)).elim
  · left
    apply finish
    exact census_from TwelveRowCensus.cells certificates (by native_decide) (by native_decide) options
      (fun mat law rs f pos k hk => by
        have nz := List.length_pos_iff.mp pos
        have base : wordDigits 12 (rs.getD 0 0)=wordDigits 12 (word mat 0) :=
          congrArg List.ofFn (funext (fun j => (f 0 j pos).trans (digit_word mat 0 j).symm))
        simp only [options,List.isEmpty_eq_false_iff.mpr nz,Bool.false_eq_true,if_false,base,capacity_sound mat law,if_true]
        split
        · exact unit_complete mat law rs f pos k hk
        · exact high_complete mat law rs f pos k hk)
      (fun _ => false) (fun i => by simpa using List.all_eq_true.mp checked i.val (List.mem_range.mpr i.isLt))
      (fun _ _ absurd => by cases absurd) m hm (by simp [options,root,easy])
  · right
    exact ⟨m,hm,⟨p,names⟩,root,residual.1,residual.2⟩

end QGI.TwelveHighCensus
