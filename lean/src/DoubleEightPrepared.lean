import SixteenMapComplete
import DoubleEightLayerCheck
import DoubleEightPlacementCheck
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace QGI.DoubleEight.Prepared
open SixteenMapSearch
open private digest sorted from SixteenMapSearch

abbrev Index := Fin 636
abbrev Vertex := Fin 16

def row (a : Index) := Layers.matrices.getD a.val #[]

private theorem get_ofFn {n : Nat} {α : Type} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  simp

private def cache : Vector (Option Scheme) 636 :=
  Vector.ofFn fun a => prepare [8,8] (a.val + 1) (row a)

def scheme (a : Index) : Scheme :=
  (cache.get a).getD ⟨0,#[],0,#[],#[],#[],[]⟩

private theorem present : ∀ a : Index, (cache.get a).isSome = true := by native_decide

theorem prepare_row (a : Index) : prepare [8,8] (a.val+1) (row a) = some (scheme a) := by
  have eq : cache.get a = prepare [8,8] (a.val+1) (row a) := by simp only [cache,get_ofFn]
  rw [← eq,scheme]
  cases e : cache.get a with
  | none => have h := present a; simp [e] at h
  | some v => rfl

attribute [local irreducible] scheme row

private structure Table (r : Nat) where
  trans : Fin r → Fin r
  p : Fin r → Fin r → Fin r → Nat

private def diagonalFlag {r} (a : Table r) (k : Fin r) : Bool :=
  decide (∀ i j : Fin r, i ≠ j → a.p j k i = 0)

private def initial {r} (a : Table r) : Vector Nat r :=
  let diag := Vector.ofFn (diagonalFlag a)
  Vector.ofFn fun k =>
    let d := (List.ofFn fun i => if diag.get i then a.p i k (a.trans k) else 0).sum
    digest [(diag.get k).toNat, (decide (a.trans k = k)).toNat, 8*d, 8, 8]

private def triples {r} (a : Table r) (keys : Vector Nat r) (k : Fin r) (z : Fin (r*r)) : Option Nat :=
  let ij : Fin r × Fin r := finProdFinEquiv.symm z
  let mult := a.p k ij.1 ij.2
  if 0 < mult then some (digest [keys.get ij.1,keys.get ij.2,mult]) else none

private def step {r} (a : Table r) (keys : Vector Nat r) : Vector Nat r :=
  Vector.ofFn fun k => digest (keys.get k :: keys.get (a.trans k) ::
    sorted ((List.ofFn (triples a keys k)).filterMap id))

private def stages {r} (a : Table r) : Nat → Vector Nat r
  | 0 => initial a
  | n+1 => step a (stages a n)

private theorem perm_of_equiv {r s : Nat} {α : Type} (e : Fin r ≃ Fin s) (f : Fin r → α)
    (g : Fin s → α) (h : ∀ i, f i = g (e i)) : (List.ofFn f).Perm (List.ofFn g) := by
  have rs : r = s := by simpa using Fintype.card_congr e
  subst s
  have fg : f = g ∘ e := funext h
  rw [fg]
  exact Equiv.Perm.ofFn_comp_perm e g

private theorem sorted_eq {xs ys : List Nat} (h : xs.Perm ys) : sorted xs = sorted ys := by
  exact List.eq_of_perm_of_sorted (((List.mergeSort_perm _ _).trans h).trans (List.mergeSort_perm _ _).symm)
    (List.sorted_mergeSort' (· ≤ ·) xs) (List.sorted_mergeSort' (· ≤ ·) ys)

private theorem stage_congr {r s : Nat} (a : Table r) (b : Table s) (e : Fin r ≃ Fin s)
    (tr : ∀ i, e (a.trans i) = b.trans (e i))
    (mul : ∀ k i j, a.p k i j = b.p (e k) (e i) (e j)) :
    ∀ n i, (stages a n).get i = (stages b n).get (e i) := by
  have flags (k : Fin r) : diagonalFlag a k = diagonalFlag b (e k) := by
    unfold diagonalFlag
    apply decide_eq_decide.mpr
    constructor
    · intro h i j ne
      obtain ⟨i,rfl⟩ := e.surjective i
      obtain ⟨j,rfl⟩ := e.surjective j
      rw [← mul]
      exact h i j (fun eq => ne (congrArg e eq))
    · intro h i j ne
      rw [mul]
      exact h (e i) (e j) (fun eq => ne (e.injective eq))
  intro n
  induction n with
  | zero =>
    intro k
    have weights := perm_of_equiv e (fun i => if diagonalFlag a i then a.p i k (a.trans k) else 0)
      (fun i => if diagonalFlag b i then b.p i (e k) (b.trans (e k)) else 0) (fun i => by
        dsimp only
        rw [flags, mul, tr])
    have refl : (a.trans k = k) ↔ b.trans (e k) = e k := by rw [← tr,e.injective.eq_iff]
    simp only [stages,initial,get_ofFn]
    rw [weights.sum_eq, flags, decide_eq_decide.mpr refl]
  | succ n ih =>
    intro k
    let prod : Fin (r*r) ≃ Fin (s*s) := finProdFinEquiv.symm.trans ((e.prodCongr e).trans finProdFinEquiv)
    have terms : ∀ z, triples a (stages a n) k z = triples b (stages b n) (e k) (prod z) := by
      intro z
      obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective z
      simp [triples, prod, mul, ih]
    have hs := sorted_eq ((perm_of_equiv prod _ _ terms).filterMap id)
    simp only [stages,step,get_ofFn, ih, tr, hs]

private def tab (a : Scheme) : Table a.rank where
  trans k := if h : transposeName a k.val < a.rank then ⟨_,h⟩ else k
  p k i j := coefficient a k.val i.val j.val

private def Good (s : Scheme) : Prop :=
  (∀ k : Fin s.rank, transposeName s k.val < s.rank) ∧
  Vector.ofFn (fun k : Fin s.rank => refinedKey s k.val) = stages (tab s) 3 ∧
  s.profile = sorted (List.ofFn (fun k : Fin s.rank => refinedKey s k.val))

private instance (s : Scheme) : Decidable (Good s) := by unfold Good; infer_instance
private theorem good : ∀ a : Index, Good (scheme a) := by native_decide

/-- Every genuine palette isomorphism passes both levels of the actual catalog search:
the initial scheme-pair bucket and the individual recursive map search. -/
theorem eligible (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (tr : ∀ i j, transposeName (scheme a) i.val = j.val ↔
      transposeName (scheme b) (e i).val = (e j).val)
    (mul : ∀ k i j, coefficient (scheme a) k.val i.val j.val =
      coefficient (scheme b) (e k).val (e i).val (e j).val) :
    (scheme a).rank = (scheme b).rank ∧ (scheme a).profile = (scheme b).profile ∧
    List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (scheme a) (scheme b) := by
  obtain ⟨atBound,ak,ap⟩ := good a
  obtain ⟨btBound,bk,bp⟩ := good b
  have rev (i : Fin (scheme a).rank) : e ((tab (scheme a)).trans i) = (tab (scheme b)).trans (e i) := by
    apply Fin.ext
    simp only [tab, dif_pos (atBound i), dif_pos (btBound (e i))]
    exact ((tr i ⟨_,atBound i⟩).mp rfl).symm
  have ks (i : Fin (scheme a).rank) : refinedKey (scheme a) i.val = refinedKey (scheme b) (e i).val :=
    (by
      have left := congrArg (fun v => Vector.get v i) ak
      have right := congrArg (fun v => Vector.get v (e i)) bk
      simpa only [get_ofFn] using left.trans ((stage_congr _ _ e rev mul 3 i).trans right.symm))
  exact ⟨by simpa using Fintype.card_congr e,
    ap.trans ((sorted_eq (perm_of_equiv e _ _ ks)).trans bp.symm),
    mem_of_palette_equiv _ _ e ks tr mul⟩

private theorem metadata : ∀ a : Index, (scheme a).colors = row a ∧ (scheme a).id = a.val+1 ∧
    Layers.matrices[a.val]? = some (row a) ∧
    (∀ i j : Vertex, Placements.color (row a) i j < (scheme a).rank) := by native_decide

theorem scheme_row (a : Index) : (scheme a).colors = row a := (metadata a).1
theorem scheme_id (a : Index) : (scheme a).id = a.val+1 := (metadata a).2.1
theorem row_lookup (a : Index) : Layers.matrices[a.val]? = some (row a) := (metadata a).2.2.1

def name (a : Index) (i j : Vertex) : Fin (scheme a).rank :=
  ⟨Placements.color (row a) i j, (metadata a).2.2.2 i j⟩

theorem name_val (a : Index) (i j : Vertex) :
    (name a i j).val = Placements.color (row a) i j := rfl

set_option maxRecDepth 10000 in
private theorem cell_facts : ∀ a : Index,
    (∀ k : Fin (scheme a).rank, ∃ i j : Vertex, name a i j = k) ∧
    ∀ i j : Vertex, transposeName (scheme a) (name a i j).val = (name a j i).val := by
  native_decide

theorem name_surjective (a : Index) (k : Fin (scheme a).rank) : ∃ i j, name a i j = k := (cell_facts a).1 k
theorem transpose_at (a : Index) (i j : Vertex) :
    transposeName (scheme a) (name a i j).val = (name a j i).val := (cell_facts a).2 i j

/-- Count a whole row of the intersection tensor in one traversal of the sixteen middle points. -/
private def histogram {n : Nat} : List (Fin n) → Vector Nat n
  | [] => Vector.replicate n 0
  | k :: xs => let h := histogram xs; h.set k.val (h.get k + 1) k.isLt

private theorem histogram_at {n : Nat} (xs : List (Fin n)) (j : Fin n) :
    (histogram xs).get j = (xs.map (fun i => if i = j then 1 else 0)).sum := by
  induction xs with
  | nil => change (Vector.replicate n 0)[j.val] = 0; simp
  | cons k xs ih =>
    simp only [histogram, List.map_cons, List.sum_cons]
    change ((histogram xs).set k.val ((histogram xs).get k + 1) k.isLt)[j.val] = _
    rw [Vector.getElem_set]
    by_cases e : k = j
    · subst k; simp [ih, Nat.add_comm]
    · have ne : k.val ≠ j.val := fun eq => e (Fin.ext eq)
      simp [ne,e]
      exact ih

private def pairAt (a : Index) (x y z : Vertex) : Fin ((scheme a).rank * (scheme a).rank) :=
  finProdFinEquiv (name a x z,name a z y)

private def histAt (a : Index) (x y : Vertex) := histogram (List.ofFn (pairAt a x y))

private def coefficients (s : Scheme) (k : Fin s.rank) : Vector Nat (s.rank*s.rank) :=
  Vector.ofFn fun t => let p := finProdFinEquiv.symm t
                       coefficient s k.val p.1.val p.2.val

private theorem histograms : ∀ a : Index, ∀ x y : Vertex,
    coefficients (scheme a) (name a x y) = histAt a x y := by native_decide

theorem coefficient_at (a : Index) (x y : Vertex) (i j : Fin (scheme a).rank) :
    coefficient (scheme a) (name a x y).val i.val j.val =
      ∑ z : Vertex, if name a x z = i ∧ name a z y = j then 1 else 0 := by
  have h := congrArg (fun v => Vector.get v (finProdFinEquiv (i,j))) (histograms a x y)
  simpa only [coefficients,get_ofFn,Equiv.symm_apply_apply,histAt,histogram_at,List.map_ofFn,
    Function.comp_apply,pairAt,Equiv.apply_eq_iff_eq,Prod.mk.injEq,List.sum_ofFn] using h

/-- The intersection counts on vertices suffice directly. In particular, no
assumption about the hashed color keys used by the executable is needed. -/
theorem eligible_of_cells (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (tr : ∀ x y u v, e (name a x y) = name b u v → e (name a y x) = name b v u)
    (mul : ∀ x y u v, e (name a x y) = name b u v → ∀ i j : Fin (scheme a).rank,
      (∑ z : Vertex, if name a x z = i ∧ name a z y = j then 1 else 0 : Nat) =
      ∑ z : Vertex, if name b u z = e i ∧ name b z v = e j then 1 else 0) :
    (scheme a).rank = (scheme b).rank ∧ (scheme a).profile = (scheme b).profile ∧
    List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (scheme a) (scheme b) := by
  apply eligible a b e
  · intro k j
    obtain ⟨x,y,hxy⟩ := name_surjective a k
    obtain ⟨u,v,huv⟩ := name_surjective b (e k)
    have et := tr x y u v ((congrArg e hxy).trans huv.symm)
    rw [← hxy, transpose_at, hxy, ← huv, transpose_at, ← et]
    exact (Fin.val_inj.trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm))
  · intro k i j
    obtain ⟨x,y,hxy⟩ := name_surjective a k
    obtain ⟨u,v,huv⟩ := name_surjective b (e k)
    rw [← hxy, coefficient_at, hxy, ← huv, coefficient_at]
    exact mul _ _ _ _ ((congrArg e hxy).trans huv.symm) _ _

end QGI.DoubleEight.Prepared
