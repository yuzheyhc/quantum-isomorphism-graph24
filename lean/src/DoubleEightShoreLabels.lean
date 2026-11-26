import DoubleEightShoreCensus
import DoubleEightShoreCertificate
import Mathlib.Data.List.FinRange

namespace QGI.DoubleEight.ShoreLabels

open ShoreCensus (V Coloring Homogeneous)
open ShoreCheck (Word bank relabel colorAt)

private def raw (s p : Word) : Word :=
  (Array.range 64).map fun k => s[8 * p[k / 8]! + p[k % 8]!]!

private def rowMap (s t : Word) : Word := Id.run do
  let mut table := Array.replicate 8 0
  for j in [:8] do table := table.set! s[j]! t[j]!
  return table

/-- Two explicitly reconstructed color maps certify that the point-reordered
word and its normalized word define exactly the same partition. -/
private def checkNames (s p : Word) : Bool :=
  let old := raw s p
  let w := ShoreCheck.normalize old
  let f := rowMap old w
  let g := rowMap w old
  w.size == 64 && (Array.range 64).all fun k =>
    let u := old[k]!
    let v := w[k]!
    v < 8 && f[u]! == v && g[v]! == u

private def nameChecks : Bool :=
  let perms := (List.range 8).permutations.map List.toArray
  UniformInput.shores.all fun s => perms.all fun p => checkNames s p

private theorem all_names : nameChecks = true := by native_decide

private theorem names_of_perm {s : Word} (hs : s ∈ UniformInput.shores.toList)
    {p : List Nat} (hp : p.Perm (List.range 8)) : checkNames s p.toArray = true := by
  have h := Array.all_eq_true_iff_forall_mem.mp all_names _ (Array.mem_def.mpr hs)
  exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨p, List.mem_permutations.mpr hp, rfl⟩)

private theorem raw_at (s p : Word) (i j : V) :
    (raw s p)[8*i.val+j.val]! = s[8*p[i.val]!+p[j.val]!]! := by
  have bound : 8*i.val + j.val < 64 := by omega
  have lo : (8*i.val+j.val) / 8 = i.val := by omega
  have hi : (8*i.val+j.val) % 8 = j.val := by omega
  simp [raw, getElem!_pos, bound, lo, hi]

private def order (e : V ≃ V) : List Nat := List.ofFn (Fin.val ∘ e)

private theorem order_perm (e : V ≃ V) : (order e).Perm (List.range 8) := by
  simpa [order, List.ofFn_eq_map] using Equiv.Perm.ofFn_comp_perm e Fin.val

private theorem order_at (e : V ≃ V) (i : V) : (order e).toArray[i.val]! = (e i).val := by
  have hi : i.val < (order e).toArray.size := by simpa only [order, List.size_toArray,
    List.length_ofFn] using i.isLt
  rw [getElem!_pos (order e).toArray i.val hi, List.getElem_toArray]
  simp only [order, List.getElem_ofFn, Function.comp_apply]

private theorem dimensions :
    UniformInput.shores.size = 21 ∧ ∀ s ∈ UniformInput.shores.toList, s.size = 64 := by
  native_decide

private def bank_word_coordinates (c : Coloring) (w : Word) : Prop :=
  (∀ i j : V, w[8*i.val+j.val]! < 8) ∧
  ∀ i j k l : V, c i j = c k l ↔ w[8*i.val+j.val]! = w[8*k.val+l.val]!

private theorem exact_coordinates (c : Coloring) (hc : Homogeneous c) :
    ∃ w ∈ bank, bank_word_coordinates c w := by
  obtain ⟨a, e, he⟩ := ShoreCensus.every_shore c hc
  have ha : a.val < UniformInput.shores.size := dimensions.1.symm ▸ a.isLt
  let s := UniformInput.shores[a.val]
  have hs : s ∈ UniformInput.shores.toList := Array.getElem_mem_toList ha
  have hsize : s.size = 64 := dimensions.2 s hs
  let p := order e.symm
  have hp : p.Perm (List.range 8) := order_perm _
  let w := relabel s p.toArray
  have hw : w ∈ bank := ShoreCheck.bank_iff_relabeling.mpr ⟨s, hs, p, hp, rfl⟩
  have key (i j : V) : (raw s p.toArray)[8*i.val+j.val]! =
      ShoreCensus.seed a (e.symm i) (e.symm j) := by
    rw [raw_at, order_at, order_at]
    have bound : 8*(e.symm i).val + (e.symm j).val < s.size := by rw [hsize]; omega
    simp [ShoreCensus.seed, Array.getD, ha, s, getElem!_pos, bound] at *
  have passed := names_of_perm hs hp
  simp only [checkNames, Bool.and_eq_true, beq_iff_eq] at passed
  let old := raw s p.toArray
  let f := rowMap old w
  let g := rowMap w old
  have facts (i j : V) : w[8*i.val+j.val]! < 8 ∧
      f[ShoreCensus.seed a (e.symm i) (e.symm j)]! = w[8*i.val+j.val]! ∧
      g[w[8*i.val+j.val]!]! = ShoreCensus.seed a (e.symm i) (e.symm j) := by
    have hn : 8*i.val+j.val ∈ Array.range 64 := by simp; omega
    have z := Array.all_eq_true_iff_forall_mem.mp passed.2 _ hn
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at z
    rw [← key i j]
    exact ⟨z.1.1, z.1.2, z.2⟩
  refine ⟨w, hw, fun i j => (facts i j).1, ?_⟩
  intro i j k l
  have partition := he (e.symm i) (e.symm j) (e.symm k) (e.symm l)
  simp only [Equiv.apply_symm_apply] at partition
  constructor
  · intro equal
    exact (facts i j).2.1.symm.trans
      ((congrArg (fun n : Nat => f[n]!) (partition.mpr equal)).trans (facts k l).2.1)
  · intro equal
    exact partition.mp ((facts i j).2.2.symm.trans
      ((congrArg (fun n : Nat => g[n]!) equal).trans (facts k l).2.2))

/-- Arbitrary eight-point schemes have an actual bank word in their current
point coordinates. Only the numeric names of the colors can differ. -/
theorem exists_bank_word_raw (c : Coloring) (hc : Homogeneous c) :
    ∃ w ∈ bank, ∀ i j k l : V,
      c i j = c k l ↔ w[8*i.val+j.val]! = w[8*k.val+l.val]! := by
  obtain ⟨w, hw, _, h⟩ := exact_coordinates c hc
  exact ⟨w, hw, h⟩

theorem exists_bank_word (c : Coloring) (hc : Homogeneous c) :
    ∃ w ∈ bank, ∀ i j k l : V,
      c i j = c k l ↔ colorAt w i j = colorAt w k l := by
  obtain ⟨w, hw, bound, h⟩ := exact_coordinates c hc
  refine ⟨w, hw, fun i j k l => (h i j k l).trans ?_⟩
  rw [Fin.ext_iff]
  change _ ↔ w[8*i.val+j.val]! % 8 = w[8*k.val+l.val]! % 8
  rw [Nat.mod_eq_of_lt (bound i j), Nat.mod_eq_of_lt (bound k l)]

end QGI.DoubleEight.ShoreLabels
