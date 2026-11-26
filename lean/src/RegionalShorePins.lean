import SixEightGeometry
import RegionalSignatureBound
import RegionalFourFourEight

noncomputable section
namespace QGI.Coherent.RegionalShorePins
open SixTenCoordinates SixEightGeometry SmallUnion SmallFiberExtension Intertwiner Synchrony
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)
open Classical

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

def Short {J : Type*} {k l : Nat} (A : Shore (source G) l (Fin k)) (s : J → Fin n) : Prop :=
  ∀ i : Fin k, (Finset.univ.filter fun t => ∀ j, source G (atPoint A t) (s j)=source G (atPoint A i) (s j)).card≤3

theorem pinned {k l : Nat} (A : Shore (source G) l (Fin k)) : Short A (atPoint A) := by
  intro i
  apply (Finset.card_le_card (t:=({i} : Finset (Fin k))) ?_).trans (by simp)
  intro t ht
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ht
  exact Finset.mem_singleton.mpr (A.injective (Subtype.ext (Relations.diagonal _ (ht i))))

theorem one {k l : Nat} (A : Shore (source G) l (Fin k)) (x : Fin n)
    (small : ∀ i, (Finset.univ.filter fun t => source G (atPoint A t) x=source G (atPoint A i) x).card≤3) :
    Short A (fun _ : Unit => x) := by
  intro i
  apply (Finset.card_le_card ?_).trans (small i)
  intro t h
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
  exact h ()

attribute [local instance 2000] Classical.propDecidable in
theorem realize {l r w k m o : Nat} {J : Type*}
    (A : Shore (source G) l (Fin k)) (B : Shore (source G) r (Fin m)) (Y : Shore (source G) w (Fin o))
    (reg : Nat → Prop) (large : ∀ i, reg (source G i i) → LargeFourteenRegion.large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=w)
    (ξ : cyclic p) (nz : ξ≠0) (s t : J → Fin n) (fixed : ∀ j, U p (s j) (t j) ξ=ξ)
    (sa : Short A s) (sb : Short B s) (sy : Short Y s) : Realizes p reg := by
  apply LargeOrderBlocks.of_solver p reg large rfl
  intro f g D
  apply RegionalTernaryChoice.source_pins p D ξ nz s t fixed
  intro i
  have bound {q h : Nat} (S : Shore (source G) q (Fin h)) (small : Short S s) (tag : source G (f i) (f i)=q) :
      (Finset.univ.filter (fun b => source G (f b) (f b)=source G (f i) (f i) ∧ ∀ j, source G (f b) (s j)=source G (f i) (s j))).card≤3 := by
    obtain ⟨a,ha⟩ := (range_emb S (f i)).mpr tag
    apply (RegionalSignatureBound.bound_set f D.injF (atPoint S) _ _ ?_).trans (small a)
    intro b hb
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb
    obtain ⟨z,hz⟩ := (range_emb S (f b)).mpr (hb.1.trans tag)
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hz⟩
    intro j
    rw [show atPoint S z=f b from hz,show atPoint S a=f i from ha]
    exact hb.2 j
  rcases cover _ ((D.src _).mp ⟨i,rfl⟩) with h|h|h
  · exact bound A sa h
  · exact bound B sb h
  · exact bound Y sy h

theorem root {l r w k m o : Nat} (A : Shore (source G) l (Fin k)) (B : Shore (source G) r (Fin m))
    (Y : Shore (source G) w (Fin o)) (reg : Nat → Prop)
    (large : ∀ i, reg (source G i i) → LargeFourteenRegion.large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=w)
    (x : Fin n) (sa : Short A (fun _ : Unit => x)) (sb : Short B (fun _ : Unit => x))
    (sy : Short Y (fun _ : Unit => x)) : Realizes p reg := by
  let ψ : cyclic p := ⟨p.psi,psi_mem p⟩
  have nz : ψ≠0 := fun h => psi_ne_zero p (congrArg Subtype.val h)
  obtain ⟨y,hy⟩ := DoubledEdges.nonzero_row p ψ nz x
  let ξ := U p x y ψ
  have fix : U p x y ξ=ξ := congrArg (fun Z : Module.End ℂ (cyclic p) => Z ψ) (restricted_projection p _ _).1
  exact realize p A B Y reg large cover ξ hy (fun _ : Unit => x) (fun _ => y) (fun _ => fix) sa sb sy

end QGI.Coherent.RegionalShorePins
