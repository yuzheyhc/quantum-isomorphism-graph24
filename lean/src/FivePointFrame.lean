import FourPointCycleGlue
import Mathlib.Data.Fin.VecNotation

noncomputable section
namespace QGI.Coherent.FivePointFrame
open StrategyColorLaws
open FourTwelveCycle (neighbors shared_counts)
open private mixed from FourPointCycleGlue
abbrev V := Fin 5
abbrev Edge := Fin 10

def ends : Edge → V × V := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def edge (i : Edge) : Finset V := {(ends i).1,(ends i).2}
def cycle (i : V) : Finset V := {i,i+1}

theorem edge_injective : Function.Injective edge := by
  change ∀ i j : Edge, edge i=edge j → i=j
  native_decide

/-- A nonempty regular simple graph on five points of degree at least
two contains a spanning five-cycle. Regular supports here are unions of
ordinary unordered pairs, with no loops or multiple edges. -/
theorem contains_cycle : ∀ s : Finset Edge, s.Nonempty →
    (∀ i : V, (s.filter (fun k => i∈edge k)).card=(s.filter (fun k => 0∈edge k)).card) →
    ∃ e : Equiv.Perm V, ∀ i, ∃ b∈s, edge b=(cycle i).map e.toEmbedding := by native_decide

structure Frame {n : Nat} (c : Fin n → Fin n → Nat) (F : V ↪ Fin n)
    (Y : V → Fin n) (a b : Nat) : Prop where
  cells : ∀ k, neighbors c a (Y k) = (cycle k).map F
  names : ∀ k i, c (Y k) (F i)=if i∈cycle k then a else b

private theorem gram_test : ∀ a b c d e : Edge, let t := ![a,b,c,d,e]
    (∀ i j, (cycle i ∩ cycle j).card=(edge (t i) ∩ edge (t j)).card) →
    ∃ q : Equiv.Perm V, ∀ i, (cycle i).map q.toEmbedding=edge (t i) := by native_decide

theorem align (t : V → Edge) (h : ∀ i j, (cycle i ∩ cycle j).card=(edge (t i) ∩ edge (t j)).card) :
    ∃ q : Equiv.Perm V, ∀ i, (cycle i).map q.toEmbedding=edge (t i) := by
  have eq : (![t 0,t 1,t 2,t 3,t 4] : V → Edge)=t := by funext i; fin_cases i <;> rfl
  have g := gram_test (t 0) (t 1) (t 2) (t 3) (t 4)
  dsimp only at g
  rw [eq] at g
  exact g h

def sectionAt {n : Nat} (c : Fin n → Fin n → Nat) (F : Fin 5 ↪ Fin n) (v : Nat) (z : Fin n) :=
  Finset.univ.filter (fun i => c z (F i)=v)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

private theorem section_inter {c : Fin n → Fin n → Nat} {F : Fin 5 ↪ Fin n}
    (v : Nat) (z : Fin n) (E : Finset (Fin 5)) :
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

/-- On an odd cycle the intersections with its five edges distinguish
every subset of the shore. -/
theorem recover {F T : V ↪ Fin n} {Y Z : V → Fin n} {a b : Nat}
    (P : Frame (Relations.color (closure G)) F Y a b) (Q : Frame (targetName p) T Z a b)
    {u v : Fin n} (named : ∀ k, Relations.color (closure G) (Y k) u=targetName p (Z k) v) :
    ∀ i, Relations.color (closure G) u (F i)=targetName p v (T i) := by
  intro i
  let s := Relations.color (closure G) u (F i)
  have unique : ∀ x y : Finset V, (∀ k, (cycle k ∩ x).card=(cycle k ∩ y).card) → x=y := by native_decide
  have eq : sectionAt (Relations.color (closure G)) F s u=sectionAt (targetName p) T s v := by
    apply unique; intro k
    have h := mixed p (a:=a) (b:=s) (named k)
    rwa [P.cells,Q.cells,section_inter,section_inter] at h
  have hit : i∈sectionAt (Relations.color (closure G)) F s u := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  exact (Finset.mem_filter.mp (eq ▸ hit)).2.symm

end QGI.Coherent.FivePointFrame
