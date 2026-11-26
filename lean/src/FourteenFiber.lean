import SmallFiberExtension
import ZivAvCoreQuantum
import CoherentCoprime
import ComponentReduction

noncomputable section

namespace QGI.Literature
open Coherent.SmallShore
open Coherent.StrategyColorLaws (count)

/-- Ziv-Av, *Enumeration of coherent configurations of order at most 15*,
§2.2, Tables 2 and 3 (pp. 67–68). Fourteen does not occur in either list
for association schemes. Thus every specified algebraic isomorphism between
two homogeneous 14-point schemes is induced by a point permutation.
https://actamath.savbb.sk/pdf/aumb2605.pdf -/
theorem zivAv_named_fourteen_scheme {c b : Table 14} {d : Nat} (hc : Local c d) (hb : Local b d)
    (used : ∀ s, (∃ i j, c i j=s) ↔ ∃ x y, b x y=s)
    (products : ∀ s t i j x y, c i j=b x y → count c s t i j=count b s t x y) :
    ∃ e : Equiv.Perm (Fin 14), ∀ i j, c i j = b (e i) (e j) :=
  ZivAv.named_of_homogeneous hc hb used products

end QGI.Literature

namespace QGI.Coherent.FourteenFiber
open SmallFiberExtension SmallUnion StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private theorem set_eq (b : Fin n) :
    vertices (source G) (fun s => s=source G b b) = fiber G b := by
  ext x; simp [fiber_eq]

/-- Named realization of an induced homogeneous fourteen-point fiber inside
a perfect commuting strategy on any total vertex set. -/
theorem realize (p : PerfectStrategy G H K) (b : Fin n) (size : (fiber G b).card = 14) :
    Realizes p (fun w => w=source G b b) := by
  classical
  let c := source G
  let d := targetName p
  let s := c b b
  let reg := fun w : Nat => w=s
  let X := Region c reg
  let Y := Region d reg
  have card : Fintype.card X=14 := (Fintype.card_coe _).trans ((congrArg Finset.card (set_eq b)).trans size)
  let F : Fin 14 ≃ X := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using card.symm)
  obtain ⟨u,hu⟩ := diagonal_names p
  let m : X ≃ Y := Equiv.subtypeEquiv u (fun x => by simp only [mem_vertices,c,source,hu x,d])
  let T := F.trans m
  let f := fun i : Fin 14 => (F i).val
  let t := fun i : Fin 14 => (T i).val
  have enumerate {a : Fin n → Fin n → Nat} (e : Fin 14 ≃ Region a reg) (x : Fin n) :
      (∃ i, (e i).val=x) ↔ a x x=s := by
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (e i).property
    · intro h
      let z : Region a reg := ⟨x,(mem_vertices a reg x).mpr h⟩
      exact ⟨e.symm z,congrArg Subtype.val (e.apply_symm_apply z)⟩
  have fi : Function.Injective f := fun _ _ eq => F.injective (Subtype.ext eq)
  have ti : Function.Injective t := fun _ _ eq => T.injective (Subtype.ext eq)
  obtain ⟨srcCfg,tgtCfg,used,prod⟩ := SmallShore.correspondence p f t s fi ti (enumerate F) (enumerate T)
  obtain ⟨perm,name⟩ := Literature.zivAv_named_fourteen_scheme srcCfg tgtCfg used prod
  refine ⟨(F.symm.trans perm).trans T,fun x y => ?_⟩
  simpa only [SmallShore.restrict,f,t,Equiv.apply_symm_apply,Equiv.trans_apply] using name (F.symm x) (F.symm y)

/-- The whole fourteen-point fiber and only fibers of sizes at most three
may occur on the source. -/
theorem isomorphic_of_small_exterior (p : PerfectStrategy G H K) (b : Fin n) (size : (fiber G b).card=14)
    (other : ∀ v, v ≠ source G b b → (vertices (source G) (fun w => w=v)).card ≤ 3) :
    Isomorphic G H := by
  have eq : (fun v => 3 < (vertices (source G) (fun w => w=v)).card) = (fun v => v=source G b b) := by
    funext v; apply propext
    constructor
    · intro h; by_contra neq; exact (Nat.not_lt.mpr (other v neq)) h
    · rintro rfl; rw [set_eq,size]; decide
  obtain ⟨e,he⟩ := of_large_region p (eq.symm ▸ realize p b size)
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun x y => common_edge p (he x y)⟩

theorem isomorphic_of_fourteen {G H : Graph 16} (b : Fin 16) (size : (fiber G b).card=14)
    (qc : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,_,⟨p⟩⟩ := qc
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  apply isomorphic_of_small_exterior p b size
  intro v ne
  have sub : vertices (source G) (fun w => w=v) ⊆ (fiber G b)ᶜ := by
    intro x hx; exact Finset.mem_compl.mpr (fun h =>
      ne (((mem_vertices _ _ _).mp hx).symm.trans ((fiber_eq b x).mp h)))
  have card := Finset.card_le_card sub
  rw [Finset.card_compl,Fintype.card_fin,size] at card
  omega

/-- With 15 points in one fiber, the remaining vertex has a constant
adjacency to that fiber. Disconnecting the graph or its complement
gives the graph result without a named claim for all 15-point schemes. -/
theorem isomorphic_of_fifteen {G H : Graph 16} (b : Fin 16) (size : (fiber G b).card=15)
    (qc : QuantumIso G H) : Isomorphic G H := by
  classical
  let X := fiber G b
  have sz : Xᶜ.card = 1 := by rw [Finset.card_compl,Fintype.card_fin,size]
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp sz
  have eq (i : Fin 16) : i ∉ X ↔ i=a := by
    rw [←Finset.mem_compl,ha,Finset.mem_singleton]
  have out : a ∉ X := (eq a).mpr rfl
  have only : fiber G a = {a} := by
    ext i
    simp only [Finset.mem_singleton]
    constructor
    · intro h; apply (eq i).mp; intro hi
      exact out ((fiber_eq b a).mpr (((fiber_eq a i).mp h).symm.trans ((fiber_eq b i).mp hi)))
    · intro h; exact (fiber_eq a i).mpr (congrArg (fun x => source G x x) h)
  have cross (i : Fin 16) (hi : i∈X) : G.edge i a = G.edge b a := by
    have color := CoprimeFibers.monochromatic G b a (by rw [size,only,Finset.card_singleton]; decide)
      hi ((fiber_eq a a).mpr rfl)
    have edge := (Relations.same _ _ _ _ _).mp color _ (adjacency_mem G)
    cases h : G.edge i a <;> cases k : G.edge b a <;> first | rfl | simp [Intertwiner.adjacency,h,k] at edge
  let side := fun i : Fin 16 => decide (i∈X)
  have both : Function.Surjective side := by
    intro t
    cases t with
    | true => exact ⟨b,decide_eq_true ((fiber_eq b b).mpr rfl)⟩
    | false => exact ⟨a,decide_eq_false out⟩
  apply Components.uniform_cut_sixteen side both (G.edge b a) _ qc
  intro i j diff
  by_cases hi : i∈X <;> by_cases hj : j∈X
  · simp [side,hi,hj] at diff
  · exact ((eq j).mp hj) ▸ cross i hi
  · rw [(eq i).mp hi,G.symm]; exact cross j hj
  · simp [side,hi,hj] at diff

end QGI.Coherent.FourteenFiber
