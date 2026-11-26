import FourPointCycleGlue

noncomputable section
namespace QGI.Coherent.RegionalPairShores
open FourTwelveCycle StrategyColorLaws
open FourTwelveFunctional (source)
open private mixed from FourPointCycleGlue

def sectionAt {n k : Nat} (c : Fin n → Fin n → Nat) (F : Fin k ↪ Fin n) (s : Nat) (x : Fin n) :=
  Finset.univ.filter fun i => c x (F i)=s

theorem section_inter {n k} (c : Fin n → Fin n → Nat) (F : Fin k ↪ Fin n) (s : Nat) (x : Fin n) (e : Finset (Fin k)) :
    ((e.map F)∩neighbors c s x).card=(e∩sectionAt c F s x).card := by
  have eq : e.map F ∩ neighbors c s x=(e∩sectionAt c F s x).map F := by
    ext z
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp (Finset.mem_inter.mp h).1
      exact Finset.mem_map.mpr ⟨i,Finset.mem_inter.mpr ⟨hi,by simpa [neighbors,sectionAt] using (Finset.mem_inter.mp h).2⟩,rfl⟩
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_inter.mpr ⟨Finset.mem_map.mpr ⟨i,(Finset.mem_inter.mp hi).1,rfl⟩,
        by simpa [sectionAt,neighbors] using (Finset.mem_inter.mp hi).2⟩
  rw [eq,Finset.card_map]

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

/-- Matching the named probe neighborhoods recovers any row when their
intersection counts and one known point distinguish subsets. Probe colors may vary. -/
theorem recover {I : Type} (F T : Fin k ↪ Fin n) (Y Z : I → Fin n) (v : I → Nat) (sets : I → Finset (Fin k))
    (src : ∀ j, neighbors (source G) (v j) (Y j)=(sets j).map F)
    (tgt : ∀ j, neighbors (targetName p) (v j) (Z j)=(sets j).map T)
    (dist : ∀ a b : Finset (Fin k), (∀ j, (sets j∩a).card=(sets j∩b).card) →
      (∃ i : Fin k, i∈a ↔ i∈b) → a=b)
    {x y : Fin n} (same : ∀ j, source G (Y j) x=targetName p (Z j) y)
    (pin : ∃ i, source G x (F i)=targetName p y (T i)) :
    ∀ i, source G x (F i)=targetName p y (T i) := by
  obtain ⟨a,ha⟩ := pin
  intro i
  let s := source G x (F i)
  have eq : sectionAt (source G) F s x=sectionAt (targetName p) T s y := by
    apply dist
    · intro j
      have counts := mixed p (a:=v j) (b:=s) (same j)
      rwa [src,tgt,section_inter,section_inter] at counts
    · exact ⟨a,by simp only [sectionAt,Finset.mem_filter,Finset.mem_univ,true_and,ha]⟩
  have inc : i∈sectionAt (targetName p) T s y := eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  exact (Finset.mem_filter.mp inc).2.symm

end QGI.Coherent.RegionalPairShores

