import FourPointInterface
import PartialFunctional

namespace QGI.Coherent.FourPointCycleGlue
open FourTwelveCycle FourTwelveTypes StrategyColorLaws

/-- The three positions on the cycle, including the ordered diagonal. -/
def position (i j : Fin 4) : Nat := if i=j then 0 else if i=j+2 then 2 else 1

/-- These four equations include the incident-edge sum and the next-edge
sum. Together with the known diagonal they recover even a directed row. -/
private theorem read_cycle (row : Fin 4 → Nat) (j : Fin 4) (δ α β : Nat) (diag : row j=δ)
    (sums : ∀ k, ∑ i ∈ edge (cycle k), row i = if j ∈ edge (cycle k) then α else β) (i : Fin 4) :
    row i = if position i j=0 then δ else if position i j=1 then α-δ else β-(α-δ) := by
  have endpoints : ∀ k : Fin 4, edge (cycle k) = {k,k+1} := by decide
  have distinct : ∀ k : Fin 4, k ≠ k+1 := by decide
  have next (k : Fin 4) : row k + row (k+1) = if j ∈ edge (cycle k) then α else β := by
    simpa only [endpoints,Finset.sum_pair (distinct k)] using sums k
  have wrap : ∀ k : Fin 4, k+3+1=k ∧ k+1+1=k+2 := by decide
  have slots : ∀ k : Fin 4, k ∈ edge (cycle k) ∧ k ∈ edge (cycle (k+3)) ∧
      k ∉ edge (cycle (k+1)) := by decide
  have h₀ := next j
  have h₁ := next (j+1)
  have h₃ := next (j+3)
  rw [if_pos (slots j).1] at h₀
  rw [(wrap j).2,if_neg (slots j).2.2] at h₁
  rw [(wrap j).1,if_pos (slots j).2.1] at h₃
  have positions : ∀ k : Fin 4, position k k=0 ∧ position (k+1) k=1 ∧
      position (k+2) k=2 ∧ position (k+3) k=1 := by decide
  rcases (show ∀ i j : Fin 4, i=j ∨ i=j+1 ∨ i=j+2 ∨ i=j+3 by decide) i j with h|h|h|h
  all_goals subst i; simp only [(positions j).1,(positions j).2.1,(positions j).2.2.1,
    (positions j).2.2.2,reduceCtorEq,ite_true,ite_false] <;> norm_num <;> omega

/-- Four representative columns of an interface with exactly two cross
colors. The active neighborhoods are the four cycle edges in these coordinates. -/
structure Frame {n : Nat} (c : Fin n → Fin n → Nat) (F : Fin 4 ↪ Fin n)
    (Y : Fin 4 → Fin n) (a b : Nat) : Prop where
  cells : ∀ k, neighbors c a (Y k) = (edge (cycle k)).map F
  names : ∀ k i, c (Y k) (F i) = if i ∈ edge (cycle k) then a else b

private theorem read_product {n} {c : Fin n → Fin n → Nat} {F Y a b}
    (P : Frame c F Y a b) (s : Nat) (j k : Fin 4) :
    count c a s (Y k) (F j) = ∑ i ∈ edge (cycle k), if c (F i) (F j)=s then 1 else 0 := by
  classical
  calc
    _ = ∑ z ∈ neighbors c a (Y k), if c z (F j)=s then 1 else 0 := by
      simp only [count,neighbors,Finset.sum_filter,ite_and]
    _ = _ := by rw [P.cells,Finset.sum_map]

/-- The matching of representatives identifies every internal relation by
position (diagonal, neighbor or opposite), with its original color name. -/
theorem internal_names {n} {c d : Fin n → Fin n → Nat} {F T Y Z a b}
    (P : Frame c F Y a b) (Q : Frame d T Z a b)
    (src : ∀ s t i j x y, c i j=c x y → count c s t i j=count c s t x y)
    (paired : ∀ s t i j x y, c i j=d x y → count c s t i j=count d s t x y)
    (diagonal : ∀ j y, c (F j) (F j)=d (T y) (T y))
    {i j x y : Fin 4} (pos : position i j=position x y) :
    c (F i) (F j)=d (T x) (T y) := by
  classical
  let s := c (F i) (F j)
  let left := fun z => if c (F z) (F j)=s then 1 else 0
  let right := fun z => if d (T z) (T y)=s then 1 else 0
  let inside := count c a s (Y j) (F j)
  let outside := count c a s (Y (j+1)) (F j)
  have yes : j ∈ edge (cycle j) := (show ∀ k : Fin 4, k ∈ edge (cycle k) by decide) j
  have no : j ∉ edge (cycle (j+1)) := (show ∀ k : Fin 4, k ∉ edge (cycle (k+1)) by decide) j
  have ls (k) : ∑ z ∈ edge (cycle k), left z = if j ∈ edge (cycle k) then inside else outside := by
    rw [←read_product P]
    by_cases h : j ∈ edge (cycle k)
    · rw [if_pos h]; apply src; simp only [P.names,if_pos h,if_pos yes]
    · rw [if_neg h]; apply src; simp only [P.names,if_neg h,if_neg no]
  have rs (k) : ∑ z ∈ edge (cycle k), right z = if y ∈ edge (cycle k) then inside else outside := by
    rw [←read_product Q]
    by_cases h : y ∈ edge (cycle k)
    · rw [if_pos h]; symm; apply paired; simp only [P.names,Q.names,if_pos yes,if_pos h]
    · rw [if_neg h]; symm; apply paired; simp only [P.names,Q.names,if_neg no,if_neg h]
  have diag : right y = left j := by simp [left,right,diagonal j y]
  have l := read_cycle left j (left j) inside outside rfl ls i
  have r := read_cycle right y (left j) inside outside diag rs x
  rw [pos] at l
  have eq : right x = left i := r.trans l.symm
  by_contra ne
  have diff : d (T x) (T y) ≠ s := Ne.symm ne
  simp [right,left,s,diff] at eq

end QGI.Coherent.FourPointCycleGlue

namespace QGI.Coherent.FourPointCycleGlue
open FourTwelveCycle FourTwelveTypes StrategyColorLaws
open private align from FourTwelveCycle

/-- A neighborhood on the four vertices, in the coordinates of that fiber. -/
def sectionAt {n : Nat} (c : Fin n → Fin n → Nat) (F : Fin 4 ↪ Fin n) (v : Nat) (z : Fin n) :=
  Finset.univ.filter (fun i => c z (F i) = v)

private theorem mixed_entry {n : Nat} (c : Fin n → Fin n → Nat) (a b : Nat) (i j : Fin n) :
    (mark c a * (mark c b).conjTranspose) i j =
      (((neighbors c a i) ∩ (neighbors c b j)).card : ℂ) := by
  classical
  have filt : (neighbors c a i) ∩ (neighbors c b j) =
      Finset.univ.filter (fun z => c i z = a ∧ c j z = b) := by ext z; simp [neighbors]
  rw [filt,← Finset.sum_boole]
  simp only [Matrix.mul_apply,mark,Matrix.conjTranspose_apply,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

private theorem mixed {a b : Nat} {i j x y : Fin n}
    (h : Relations.color (closure G) i j = targetName p x y) :
    ((neighbors (Relations.color (closure G)) a i) ∩ (neighbors (Relations.color (closure G)) b j)).card =
    ((neighbors (targetName p) a x) ∩ (neighbors (targetName p) b y)).card := by
  have eq := entries p h ((closure H).mul_mem (target_mark_mem p a) ((closure H).adjoint_mem (target_mark_mem p b)))
    (Intertwiner.matrix_mul p (mark_intertwines p a) (Intertwiner.conjugate_transpose p (mark_intertwines p b)))
  simp only [mixed_entry] at eq
  exact_mod_cast eq

/-- The only two distinct subsets that cannot be distinguished by intersection
with the four cycle edges are the two pairs of opposite vertices. -/
def ambiguous (s : Finset (Fin 4)) : Prop := s = {0,2} ∨ s = {1,3}

private theorem distinguish : ∀ s t : Finset (Fin 4), ¬ambiguous s →
    (∀ k, (edge (cycle k) ∩ s).card = (edge (cycle k) ∩ t).card) → s=t := by
  unfold ambiguous
  decide

private theorem section_inter {c : Fin n → Fin n → Nat} {F : Fin 4 ↪ Fin n}
    (v : Nat) (z : Fin n) (E : Finset (Fin 4)) :
    ((E.map F) ∩ neighbors c v z).card = (E ∩ sectionAt c F v z).card := by
  have eq : E.map F ∩ neighbors c v z = (E ∩ sectionAt c F v z).map F := by
    ext u
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp (Finset.mem_inter.mp h).1
      exact Finset.mem_map.mpr ⟨i,Finset.mem_inter.mpr ⟨hi,by simpa [neighbors,sectionAt] using (Finset.mem_inter.mp h).2⟩,rfl⟩
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_inter.mpr ⟨Finset.mem_map.mpr ⟨i,(Finset.mem_inter.mp hi).1,rfl⟩,by simpa [sectionAt,neighbors] using (Finset.mem_inter.mp hi).2⟩
  rw [eq,Finset.card_map]

/-- Once four reference edges agree, all unambiguous source sections are
recovered simultaneously, with no shape restriction on the target sections. -/
theorem recover_section {F T : Fin 4 ↪ Fin n} {Y Z : Fin 4 → Fin n} {a b : Nat}
    (P : Frame (Relations.color (closure G)) F Y a b) (Q : Frame (targetName p) T Z a b)
    (s : Nat) {u v : Fin n}
    (named : ∀ k, Relations.color (closure G) (Y k) u = targetName p (Z k) v)
    (shape : ¬ambiguous (sectionAt (Relations.color (closure G)) F s u)) :
    sectionAt (Relations.color (closure G)) F s u = sectionAt (targetName p) T s v := by
  apply distinguish _ _ shape
  intro k
  have eq := mixed p (a:=a) (b:=s) (named k)
  rwa [P.cells,Q.cells,section_inter,section_inter] at eq

/-- Four corresponding exterior representatives canonically determine a
compatible labeling of the target fiber up to symmetries fixing every edge.
All inputs describe only the source interface and the named fibers. -/
theorem align_frame {F T : Fin 4 ↪ Fin n} {Y Z : Fin 4 → Fin n} {a b l : Nat}
    (P : Frame (Relations.color (closure G)) F Y a b)
    (srcFiber : ∀ z, z ∈ Set.range F ↔ Relations.color (closure G) z z=l)
    (dstFiber : ∀ z, z ∈ Set.range T ↔ targetName p z z=l)
    (named : ∀ i j, Relations.color (closure G) (Y i) (Y j) = targetName p (Z i) (Z j)) :
    ∃ e : Equiv.Perm (Fin 4), Frame (targetName p) (e.toEmbedding.trans T) Z a b := by
  classical
  let c := Relations.color (closure G)
  let d := targetName p
  have pull (k : Fin 4) (z : Fin n) : ∃ x, c (Y k) x = d (Z k) z ∧ c x x = d z z := by
    obtain ⟨x,h,_⟩ := PartialFunctional.middle d c (fun s t => (common_products p s t (named k k)).symm) z
    exact ⟨x,h.symm,(SmallShore.endpoints p h.symm).2⟩
  have desc (k : Fin 4) : ∃ t : Edge, neighbors d a (Z k) = (edge t).map T := by
    let S := sectionAt d T a (Z k)
    have es : S.map T = neighbors d a (Z k) := by
      ext z
      constructor
      · intro h
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
        simpa [S,sectionAt,neighbors] using hi
      · intro hz
        obtain ⟨x,h,hd⟩ := pull k z
        have hx : x ∈ neighbors c a (Y k) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.trans (Finset.mem_filter.mp hz).2⟩
        rw [show neighbors c a (Y k) = _ from P.cells k] at hx
        obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hx
        obtain ⟨j,rfl⟩ := (dstFiber z).mpr (hd.symm.trans ((srcFiber x).mp ⟨i,hi⟩))
        exact Finset.mem_map.mpr ⟨j,by simpa [S,sectionAt,neighbors] using hz,rfl⟩
    have cnt := (shared_counts p a (named k k)).1
    change (neighbors (Relations.color (closure G)) a (Y k) ∩ neighbors (Relations.color (closure G)) a (Y k)).card =
      (neighbors d a (Z k) ∩ neighbors d a (Z k)).card at cnt
    simp only [Finset.inter_self,P.cells,←es,Finset.card_map] at cnt
    have two : ∀ i, (edge (cycle i)).card=2 := by decide
    obtain ⟨t,ht⟩ := (show ∀ s : Finset (Fin 4), s.card=2 → ∃ t : Edge, edge t=s by decide) S
      (cnt.symm.trans (two k))
    exact ⟨t,ht.symm ▸ es.symm⟩
  choose t ht using desc
  obtain ⟨e,he⟩ := align t (by
    intro i j
    have g := (shared_counts p a (named i j)).1
    change ((neighbors c a (Y i)) ∩ (neighbors c a (Y j))).card =
      ((neighbors d a (Z i)) ∩ (neighbors d a (Z j))).card at g
    simpa only [c,P.cells,ht,←Finset.map_inter,Finset.card_map,overlap] using g)
  let E := e.toEmbedding.trans T
  have cells (k) : neighbors d a (Z k) = (edge (cycle k)).map E := by
    rw [ht,←he,Finset.map_map]
  refine ⟨e,cells,?_⟩
  intro k j
  have iffA : d (Z k) (E j)=a ↔ j ∈ edge (cycle k) := by
    have h : E j ∈ neighbors d a (Z k) ↔ j ∈ edge (cycle k) := by rw [cells]; simp
    simpa [neighbors] using h
  by_cases h : j ∈ edge (cycle k)
  · exact (iffA.mpr h).trans (if_pos h).symm
  · rw [if_neg h]
    obtain ⟨x,hx,hd⟩ := pull k (E j)
    obtain ⟨i,rfl⟩ := (srcFiber x).mpr (hd.trans ((dstFiber _).mp ⟨e j,rfl⟩))
    have hs := P.names k i
    by_cases hi : i ∈ edge (cycle k)
    · exact False.elim ((iffA.not.mpr h) (hx.symm.trans (hs.trans (if_pos hi))))
    · exact hx.symm.trans (hs.trans (if_neg hi))

end QGI.Coherent.FourPointCycleGlue
