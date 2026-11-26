import SixShoreExtension
import LargeOrderSingle
import RegionalDoubleEight
import LargeOrderSixteenShapes

noncomputable section
namespace QGI.Coherent.RegionalSixExterior
open SixShoreExtension (keep)
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private shore from RegionalFourFourEight
variable {n l r z : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

private theorem combine {h : Nat} [NeZero (2*h)] {tags : Fin 2 → Nat} (bound : n≤23) (half : h=4 ∨ h=8)
    (A : Shore (source G) l (Fin 6)) (Y : ∀ i, Shore (source G) (tags i) (Fin (2*h))) (apart : ∀ i, l≠tags i)
    (old : Realizes p (keep tags)) (size : (vertices (source G) (keep tags)).card=16) : Isomorphic G H := by
  let main := fun v => keep tags v ∨ v=l
  have eq : vertices (source G) main=vertices (source G) (keep tags) ∪ vertices (source G) (·=l) := by
    ext i; simp only [mem_vertices,Finset.mem_union,main]
  have dj : Disjoint (vertices (source G) (keep tags)) (vertices (source G) (·=l)) := by
    apply Finset.disjoint_left.mpr; intro i hi hl
    obtain ⟨j,hj⟩ := (mem_vertices _ _ _).mp hi
    exact apart j (((mem_vertices _ _ _).mp hl).symm.trans hj)
  apply AlmostFullRegion.isomorphic p main _ (SixShoreExtension.extend p half A Y apart old)
  rw [eq,Finset.card_union_of_disjoint dj,size,RegionalTwoAnchor.card A]; omega

include p in
theorem sixteen (bound : n≤23) (A : Shore (source G) l (Fin 6)) (Y : Shore (source G) r (Fin 16)) : Isomorphic G H := by
  let tags (_ : Fin 2) := r
  have keepSpec (w) : keep tags w ↔ w=r := ⟨fun ⟨_,h⟩ => h,fun h => ⟨0,h⟩⟩
  have size : (vertices (source G) (keep tags)).card=16 := by
    rw [show keep tags=(·=r) from funext fun i => propext (keepSpec i)]; exact RegionalTwoAnchor.card Y
  have old : Realizes p (keep tags) := by
    apply LargeOrderBlocks.of_solver p _ (fun i h => by rw [(keepSpec _).mp h,large,RegionalTwoAnchor.card Y]; decide) size
    intro f g D; apply LargeOrderSingle.solve p f g D
    intro i j; exact ((keepSpec _).mp ((D.src _).mp ⟨i,rfl⟩)).trans ((keepSpec _).mp ((D.src _).mp ⟨j,rfl⟩)).symm
  apply combine p (tags:=tags) bound (h:=8) (Or.inr rfl) A (fun _ => Y) _ old size
  intro _ hr; have card := RegionalTwoAnchor.card A
  change l=r at hr; rw [hr,RegionalTwoAnchor.card Y] at card; contradiction

include p in
theorem eights (bound : n≤23) (A : Shore (source G) l (Fin 6)) (B : Shore (source G) r (Fin 8)) (C : Shore (source G) z (Fin 8))
    (rz : r≠z) : Isomorphic G H := by
  let tags : Fin 2 → Nat := ![r,z]
  let Y : ∀ i, Shore (source G) (tags i) (Fin 8) := fun i => by
    by_cases h : i=0
    · subst i; exact B
    · have e : i=1 := by omega
      subst i; exact C
  have keepSpec (w) : keep tags w ↔ w=r ∨ w=z := by
    constructor
    · rintro ⟨i,h⟩; fin_cases i
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h|h); exact ⟨0,h⟩; exact ⟨1,h⟩
  have size : (vertices (source G) (keep tags)).card=16 := by
    rw [show keep tags=(fun t => t=r ∨ t=z) from funext fun i => propext (keepSpec i)]
    exact RegionalFourSixEight.pair_card rz B C
  have old : Realizes p (keep tags) := by
    apply RegionalDoubleEight.realize p _ size
    intro i hi
    obtain ⟨j,hj⟩ := hi
    have eq : fiber G i=vertices (source G) (·=tags j) := by ext x; rw [fiber_eq,mem_vertices,hj]
    rw [eq,RegionalTwoAnchor.card (Y j)]
  apply combine p (h:=4) (tags:=tags) bound (Or.inl rfl) A Y _ old size
  intro j h; have card := RegionalTwoAnchor.card A
  rw [h,RegionalTwoAnchor.card (Y j)] at card; contradiction

open LargeOrderSixteenShapes CoprimeProfiles
def accepted (xs : List Nat) := let ids : Finset (Fin xs.length) := Finset.univ
  decide (Has ids 6 ∧ (Has ids 16 ∨ Twice ids 8))

theorem by_profile {xs : List Nat} (bound : n≤23) (P : Profile G xs) (hit : accepted xs=true) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,cs,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := cs
  let reg := fun _ : Nat => True
  have tags (x) : reg (source G x x) ↔ P.tag x∈(Finset.univ : Finset (Fin xs.length)) := by simp [reg]
  obtain ⟨hs,other⟩ := of_decide_eq_true hit
  obtain ⟨a,_,sa⟩ := single P tags (by decide) hs
  obtain ⟨A⟩ := shore a sa
  rcases other with h|h
  · obtain ⟨y,_,sy⟩ := single P tags (by decide) h
    obtain ⟨Y⟩ := shore y sy; exact sixteen p bound A Y
  · obtain ⟨b,c,_,_,sb,sc,diff⟩ := two P tags (by decide) h
    obtain ⟨B⟩ := shore b sb; obtain ⟨C⟩ := shore c sc
    exact eights p bound A B C diff
end QGI.Coherent.RegionalSixExterior
