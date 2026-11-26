import StrategyColorLaws

noncomputable section
open scoped BigOperators
namespace QGI.Coherent.FourTwelveCycle

abbrev Vertex := Fin 4
abbrev Edge := Fin 6

def ends : Edge → Vertex × Vertex := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def edge (a : Edge) : Finset Vertex := {(ends a).1,(ends a).2}
def cycle : Fin 4 → Edge := ![0,3,5,2]

def overlap (a b : Edge) : Nat := ((edge a) ∩ (edge b)).card

def moment {X : Type} (C : X → X → Bool) (a b : Finset X) : Nat :=
  ∑ i ∈ a, ∑ j ∈ b, if C i j then 1 else 0

private theorem same_edge : ∀ a b : Edge, overlap a b = 2 ↔ a = b := by native_decide

/-- All permutations of four consecutive edge labels preserving intersections
come from relabeling the four vertices. The target is free to use any of the
six two-element subsets. -/
private theorem align : ∀ t : Fin 4 → Edge,
    (∀ i j, overlap (cycle i) (cycle j) = overlap (t i) (t j)) →
    ∃ e : Equiv.Perm Vertex, ∀ i, (edge (cycle i)).map e.toEmbedding = edge (t i) := by
  native_decide

private def slot : Vertex → Vertex → Edge :=
  ![![0,0,1,2],![0,0,3,4],![1,3,0,5],![2,4,5,0]]
private def entry (a : Edge → Bool) (i j : Vertex) := if i = j then false else a (slot i j)

private theorem endpoints : ∀ i j : Vertex, i ≠ j →
    (ends (slot i j) = (i,j) ∨ ends (slot i j) = (j,i)) := by native_decide

private theorem encodes (G : Graph 4) (i j : Vertex) :
    entry (fun a => G.edge (ends a).1 (ends a).2) i j = G.edge i j := by
  by_cases h : i=j
  · subst j; simp [entry,G.loopless]
  simp only [entry,if_neg h]
  rcases endpoints i j h with e|e <;> rw [e]
  exact G.symm _ _

/-- The sixteen edge-to-edge adjacency sums distinguish all sixty-four
labeled simple graphs on four vertices, including nonregular ones. -/
private theorem recover_bits : ∀ a b : Edge → Bool,
  (∀ i j, moment (entry a) (edge (cycle i)) (edge (cycle j)) =
    moment (entry b) (edge (cycle i)) (edge (cycle j))) → ∀ i j, entry a i j = entry b i j := by
  native_decide

theorem recover (G H : Graph 4)
    (equal : ∀ i j, moment G.edge (edge (cycle i)) (edge (cycle j)) =
      moment H.edge (edge (cycle i)) (edge (cycle j))) : ∀ i j, G.edge i j = H.edge i j := by
  let bits := fun (D : Graph 4) a => D.edge (ends a).1 (ends a).2
  have decode (D : Graph 4) : entry (bits D) = D.edge := by funext i j; exact encodes D i j
  have eq := recover_bits (bits G) (bits H) (by simpa only [decode] using equal)
  simpa only [decode] using eq

/-- Suppose the twelve-point side has already been realized. When its
source columns are exactly the four edges of a cycle, its intersection
counts and its adjacency sums across the other side extend the realization
to the four-point side. The second set of columns can be arbitrary. -/
theorem realize {R : Type} (a b : R → Edge) (h : Equiv.Perm R)
    (G H : Graph 4) (only : ∀ y, ∃ i, a y = cycle i) (all : ∀ i, ∃ y, a y = cycle i)
    (gram : ∀ y z, overlap (a y) (a z) = overlap (b (h y)) (b (h z)))
    (pulled : ∀ y z, moment G.edge (edge (a y)) (edge (a z)) =
      moment H.edge (edge (b (h y))) (edge (b (h z)))) :
    ∃ e : Equiv.Perm Vertex, (∀ i j, G.edge i j = H.edge (e i) (e j)) ∧
      ∀ y, (edge (a y)).map e.toEmbedding = edge (b (h y)) := by
  choose rep hr using all
  obtain ⟨e,he⟩ := align (fun i => b (h (rep i))) (by
    intro i j
    simpa only [hr] using gram (rep i) (rep j))
  have cross (y : R) : (edge (a y)).map e.toEmbedding = edge (b (h y)) := by
    obtain ⟨i,hi⟩ := only y
    have src : a (rep i) = a y := (hr i).trans hi.symm
    have self := (same_edge _ _).mpr src
    have dst := (same_edge _ _).mp ((gram _ _).symm.trans self)
    rw [hi,he,dst]
  let D : Graph 4 := ⟨fun i j => H.edge (e i) (e j),fun i j => H.symm _ _,fun i => H.loopless _⟩
  refine ⟨e,recover G D ?_,cross⟩
  intro i j
  have eq := pulled (rep i) (rep j)
  rw [hr,hr,←he,←he] at eq
  simpa only [moment,D,Finset.sum_map,Equiv.coe_toEmbedding] using eq

end QGI.Coherent.FourTwelveCycle


namespace QGI.Coherent.FourTwelveCycle
open StrategyColorLaws

def neighbors {n : Nat} (c : Fin n → Fin n → Nat) (v : Nat) (i : Fin n) :=
  Finset.univ.filter (fun k => c i k = v)

private theorem gram_entry {n : Nat} (c : Fin n → Fin n → Nat) (v : Nat) (i j : Fin n) :
    (mark c v * (mark c v).conjTranspose) i j =
      (((neighbors c v i) ∩ (neighbors c v j)).card : ℂ) := by
  classical
  have filt : (neighbors c v i) ∩ (neighbors c v j) =
      Finset.univ.filter (fun z => c i z = v ∧ c j z = v) := by ext z; simp [neighbors]
  rw [filt,← Finset.sum_boole]
  simp only [Matrix.mul_apply,mark,Matrix.conjTranspose_apply,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

private theorem moment_entry {n : Nat} (G : Graph n) (c : Fin n → Fin n → Nat) (v : Nat) (i j : Fin n) :
    (mark c v * (Intertwiner.adjacency G * (mark c v).conjTranspose)) i j =
      (moment G.edge (neighbors c v i) (neighbors c v j) : ℂ) := by
  classical
  simp only [moment,neighbors,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Matrix.mul_apply,mark,Intertwiner.adjacency,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : c i k = v
  · simp only [hk,if_true,one_mul]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp_all
  · simp [hk]

/-- Every named right-shore map preserves both inputs of cycle reconstruction.
The two sums count all common neighbors, and all graph edges between the
two named neighborhoods, respectively. -/
theorem shared_counts {n : Nat} {G H : Graph n} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
    (v : Nat) {i j x y : Fin n} (same : Relations.color (closure G) i j = targetName p x y) :
    let c := Relations.color (closure G)
    let d := targetName p
    ((neighbors c v i) ∩ (neighbors c v j)).card = ((neighbors d v x) ∩ (neighbors d v y)).card ∧
      moment G.edge (neighbors c v i) (neighbors c v j) =
      moment H.edge (neighbors d v x) (neighbors d v y) := by
  dsimp only
  have markMem := target_mark_mem p v
  have markLaw := mark_intertwines p v
  have conjugate := (closure H).adjoint_mem markMem
  have conjugateLaw := Intertwiner.conjugate_transpose p markLaw
  have eq := entries p same ((closure H).mul_mem markMem conjugate)
    (Intertwiner.matrix_mul p markLaw conjugateLaw)
  have adj := entries p same ((closure H).mul_mem markMem ((closure H).mul_mem (adjacency_mem H) conjugate))
    (Intertwiner.matrix_mul p markLaw (Intertwiner.matrix_mul p (Intertwiner.initial_adjacency p) conjugateLaw))
  simp only [gram_entry] at eq
  simp only [moment_entry] at adj
  exact ⟨by exact_mod_cast eq,by exact_mod_cast adj⟩

end QGI.Coherent.FourTwelveCycle

