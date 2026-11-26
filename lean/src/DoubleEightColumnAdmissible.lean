import DoubleEightColumnEnum
import DoubleEightColumnLaws
import DoubleEightColumnProfiles
import Mathlib.Data.List.FinRange

namespace QGI.DoubleEight.ColumnBridge
open ShoreCensus (V Coloring seed)
open ColumnEnum
open Finset
open scoped BigOperators

private theorem count_sum {α : Type} (f : α → Bool) (l : List α) :
    l.countP f = (l.map (fun a => (if f a then 1 else 0 : Nat))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases e : f a <;> simp [List.countP_cons, e, ih, Nat.add_comm]

private theorem eight_sum (f : Nat → Bool) :
    (List.range 8).countP f = ∑ i : V, (if f i.val then 1 else 0 : Nat) := by
  rw [← List.map_coe_finRange, List.countP_map, count_sum, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

private theorem cols_sum (cols : List Nat) (sz : cols.length = 8) (f : Nat → Bool) :
    cols.countP f = ∑ j : V, (if f (cols.getD j.val 0) then 1 else 0 : Nat) := by
  have e : cols = List.ofFn (fun j : V => cols.getD j.val 0) := by
    apply List.ext_getElem
    · simpa using sz
    · intro j hj _
      simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        Option.getD_some]
  conv_lhs => rw [e, List.ofFn_eq_map,List.countP_map,count_sum,← List.ofFn_eq_map,List.sum_ofFn]
  rfl

private def shore (a : Fin 21) := UniformInput.shores.getD a.val #[]

private theorem seed_facts : ∀ a : Fin 21,
    (∀ i j : V, relation (shore a) i.val j.val = seed a i j ∧
      relation (shore a) i.val j.val < rank (shore a)) ∧
    ∀ r : Fin (rank (shore a)), 0 < valency (shore a) r.val := by native_decide

private theorem shape {ds : List Nat} (h : ds ∈ ColumnProfiles.profiles) :
    (ds.length = 2 ∨ ds.length = 3 ∨ ds.length = 4) ∧ ∀ s : Fin ds.length, 0 < ds.get s := by
  have check : ColumnProfiles.profiles.all (fun ps => decide ((ps.length = 2 ∨ ps.length = 3 ∨
      ps.length = 4) ∧ ∀ s : Fin ps.length, 0 < ps.get s)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp check _ h)

private theorem pack_at {r k n s t : Nat} (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (hn : n < r) (hs : s < k) (ht : t < k) (f : Nat → Nat → Nat → Nat) :
    entry (pack r k f) k n s t = f n s t := by
  have hidx : (n*k+s)*k+t < r*k*k := by rcases hk with rfl|rfl|rfl <;> omega
  have h₁ : ((n*k+s)*k+t)/(k*k) = n := by rcases hk with rfl|rfl|rfl <;> omega
  have h₂ : (((n*k+s)*k+t)/k)%k = s := by rcases hk with rfl|rfl|rfl <;> omega
  have h₃ : ((n*k+s)*k+t)%k = t := by rcases hk with rfl|rfl|rfl <;> omega
  simp [entry,pack,Array.getD,hidx,h₁,h₂,h₃]

private theorem pack_congr {r k : Nat} (hk : k = 2 ∨ k = 3 ∨ k = 4)
    {f g : Nat → Nat → Nat → Nat} (h : ∀ n < r, ∀ s < k, ∀ t < k, f n s t = g n s t) :
    pack r k f = pack r k g := by
  apply Array.ext
  · simp [pack]
  · intro i hi _
    simp only [pack,Array.size_map,Array.size_range] at hi
    simp only [pack,Array.getElem_map,Array.getElem_range]
    apply h <;> rcases hk with rfl|rfl|rfl <;> omega

private theorem first_correct {z s : Nat} (existsI : ∃ i : V, letter z i.val = s) :
    firstPoint z s < 8 ∧ letter z (firstPoint z s) = s := by
  obtain ⟨i,hi⟩ := existsI
  unfold firstPoint
  cases e : (List.range 8).find? (fun x => letter z x == s) with
  | none => exact ((List.find?_eq_none.mp e) i.val (List.mem_range.mpr i.isLt) (beq_iff_eq.mpr hi)).elim
  | some w =>
    change w < 8 ∧ letter z w = s
    exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some e),
      beq_iff_eq.mp (List.find?_some (p := fun x => letter z x == s) e)⟩

/-- Semantic completeness bridge for the column search. All count and
packing conventions here are those of the actual executable enumerator. -/
theorem admissible (a : Fin 21) (ds cols : List Nat) (c : Coloring)
    (hds : ds ∈ ColumnProfiles.profiles) (sz : cols.length = 8) (order : cols.Pairwise (· ≤ ·))
    (bound : ∀ z ∈ cols, z < 65536)
    (digits : ∀ i j : V, letter (cols.getD j.val 0) i.val = c i j)
    (colors : ∀ i j, c i j < ds.length)
    (rows : ∀ (s : Fin ds.length) (i : V), ((univ : Finset V).filter (fun j => c i j = s.val)).card = ds.get s)
    (columns : ∀ (s : Fin ds.length) (j : V), ((univ : Finset V).filter (fun i => c i j = s.val)).card = ds.get s)
    (compat : FixedInterface.Compatible c (seed a)) :
    ∃ q, Admissible (UniformInput.shores.getD a.val #[]) ds q cols := by
  let L := seed a
  let S := shore a
  let q := pack (rank S) ds.length (ColumnLaws.quota L c)
  obtain ⟨shapeK,positive⟩ := shape hds
  have seeds := (seed_facts a).1
  have eqL (i j : V) : relation S i.val j.val = L i j := (seeds i j).1
  have inCol {z : Nat} (hz : z ∈ cols) : ∃ j : V, cols.getD j.val 0 = z := by
    obtain ⟨k,e⟩ := List.mem_iff_get.mp hz
    refine ⟨⟨k.val,sz ▸ k.isLt⟩,?_⟩
    simpa [List.get_eq_getElem, List.getElem?_eq_getElem k.isLt] using e
  have valEq (r : Nat) : valency S r = BareLaws.rowHistogram L r 0 := by
    simp only [valency,eight_sum,BareLaws.rowHistogram,beq_iff_eq]
    exact sum_congr rfl fun i _ => by rw [show relation S 0 i.val = L 0 i from eqL 0 i]
  have sizes (s : Fin ds.length) : ds[s.val]! = BareLaws.rowHistogram c s.val 0 := by
    simpa [getElem!_pos, s.isLt,BareLaws.rowHistogram] using (rows s 0).symm
  have getQ {r s t : Nat} (hr : r < rank S) (hs : s < ds.length) (ht : t < ds.length) :
      entry q ds.length r s t = ColumnLaws.quota L c r s t := pack_at shapeK hr hs ht _
  have neighborEq (j i : V) (r t : Nat) : neighbor S (cols.getD j.val 0) r i.val t =
      ColumnLaws.quota L c r (c i j) t := by
    simpa only [neighbor,eight_sum,Bool.and_eq_true,beq_iff_eq,eqL,digits] using
      (ColumnLaws.column_quota compat r t i j rfl)
  have first (j : V) (s : Fin ds.length) : ∃ i : V,
      firstPoint (cols.getD j.val 0) s.val = i.val ∧ c i j = s.val := by
    have pos := positive s
    rw [← columns s j] at pos
    obtain ⟨x,hx⟩ := Finset.card_pos.mp pos
    have found := first_correct (z := cols.getD j.val 0) (s := s.val)
      ⟨x,(digits x j).trans (mem_filter.mp hx).2⟩
    let i : V := ⟨_,found.1⟩
    exact ⟨i,rfl,(digits i j).symm.trans found.2⟩
  change ∃ q, Admissible S ds q cols
  refine ⟨q, sz, order, bound, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨j,rfl⟩ := inCol hz
    refine ⟨fun i => (digits i j) ▸ colors i j, fun s => ?_⟩
    simp only [eight_sum,digits,beq_iff_eq,getElem!_pos ds s.val s.isLt]
    simpa using columns s j
  · intro z hz
    obtain ⟨j,rfl⟩ := inCol hz
    apply pack_congr shapeK
    intro r _ s hs t _
    obtain ⟨i,e,cell⟩ := first j ⟨s,hs⟩
    rw [e,neighborEq,cell]
  · intro z hz r i t
    obtain ⟨j,rfl⟩ := inCol hz
    rw [neighborEq,digits,getQ r.isLt (colors i j) t.isLt]
  · intro r s t
    rw [sizes s,getQ r.isLt s.isLt t.isLt,valEq]
    exact ColumnLaws.gram_integral compat r s t
  · intro i j _ s t
    have exactGram : ColumnEnum.gram cols i j s t =
        FixedInterface.product c (FixedInterface.transpose c) s t i j := by
      simp only [ColumnEnum.gram,cols_sum cols sz,digits,Bool.and_eq_true,beq_iff_eq,
        FixedInterface.product,FixedInterface.transpose,List.sum_ofFn]
    have hr : L i j < rank S := eqL i j ▸ (seeds i j).2
    have hv : 0 < BareLaws.rowHistogram L (L i j) 0 := by
      rw [← valEq]
      exact (seed_facts a).2 ⟨_,hr⟩
    rw [exactGram,target,eqL,sizes s,getQ hr s.isLt t.isLt,valEq,ColumnLaws.gram_recovered compat _ _ _ hv,
      ColumnLaws.gram_at compat]

end QGI.DoubleEight.ColumnBridge
