import FiberPairProfiles
import FivePointExtension

namespace QGI.Coherent.FivePointProfiles
open FourTwelveFunctional (source fiber_eq)
open LargeFourteenRegion LargeOrderProfiles CoprimeProfiles SmallFiberExtension SmallUnion StrategyColorLaws

def core (xs : List Nat) (ids : Finset (Fin xs.length)) :=
  ids.filter (fun i => xs[i.val]≠5)

def base (xs : List Nat) (ids : Finset (Fin xs.length)) := accepted 15 xs ids || FiberPairProfiles.triple xs ids

def covered (xs : List Nat) := checkWith xs (fun ids => base xs ids || base xs (core xs ids))

private theorem solve {n} (nineteen : NineteenSolver n) {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    (ids : Finset (Fin xs.length)) (ok : base xs ids=true) (reg : Nat → Prop)
    (tags : ∀ i, reg (source G i i) ↔ P.tag i∈ids) (active : ∀ i, reg (source G i i) → large G (source G i i)) :
    Realizes p reg := by
  classical
  simp only [base,Bool.or_eq_true] at ok
  rcases ok with small|pair
  · have sz : (vertices (source G) reg).card=weight xs ids := by
      have eq : vertices (source G) reg=Finset.univ.filter (fun i => P.tag i∈ids) := by
        ext i; simp only [mem_vertices,Finset.mem_filter,Finset.mem_univ,true_and,tags]
      rw [eq,←Finset.sum_card_fiberwise_eq_card_filter Finset.univ ids P.tag]
      simp_rw [P.size]; rfl
    exact solveAccepted15With nineteen P p ids small reg tags active sz
  · exact FiberPairProfiles.solveWith nineteen P p ids pair reg tags active

theorem isomorphicWith {n : Nat} (nineteen : NineteenSolver n) {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (ok : covered xs=true) (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  obtain ⟨e,he⟩ := LargeOrderProfiles.named P _ ok p (fun ids yes reg shape active _ => by
    simp only [Bool.or_eq_true] at yes
    rcases yes with old|smaller
    · exact solve nineteen P p ids old reg shape active
    let c := source G
    let size := fun t => (vertices c (·=t)).card
    let keep := fun t => reg t ∧ size t≠5
    have atSize (i) : size (c i i)=xs[(P.tag i).val] := by
      have eq : vertices c (·=c i i)=fiber G i := by ext z; exact (mem_vertices _ _ z).trans (fiber_eq i z).symm
      exact (congrArg Finset.card eq).trans (P.fiber_size i)
    have tags (i) : keep (c i i) ↔ P.tag i∈core xs ids := by
      simp only [keep,core,Finset.mem_filter,atSize]
      exact and_congr_left' (shape i)
    have map := solve nineteen P p _ smaller keep tags (fun i h => active i h.1)
    let names := (Finset.univ.filter (fun i => reg (c i i) ∧ size (c i i)=5)).image (fun i => c i i)
    have sz (t) (ht : t∈names) : size t=5 := by
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hj).2.2
    apply RegionalFourFourEight.restrict_map p (FivePointExtension.extend_names p keep names sz map)
    intro i h
    by_cases s : size (c i i)=5
    · exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,s⟩,rfl⟩)
    · exact Or.inl ⟨h,s⟩)
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩

theorem isomorphic {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (ok : covered xs=true) (q : QuantumIso G H) : Isomorphic G H :=
  isomorphicWith (unrestrictedNineteen n) P ok q

end QGI.Coherent.FivePointProfiles
