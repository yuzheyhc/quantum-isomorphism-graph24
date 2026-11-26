import SmallFiberExtension
import CoprimeProfiles

noncomputable section
namespace QGI.Coherent.LargeFourteenRegion
open SmallFiberExtension SmallUnion StrategyColorLaws CoprimeProfiles
open FourTwelveFunctional (source fiber_eq)

def large {n : Nat} (G : Graph n) (name : Nat) : Prop :=
  3 < (vertices (source G) (fun w => w=name)).card

abbrev restricted {n k : Nat} (c : Fin n → Fin n → Nat) (f : Fin k → Fin n) := SmallShore.restrict c f

/-- Every local datum is supplied in the original strategy's common names.
The two indexings also identify the diagonal name at each index. -/
structure DataFor {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (region : Nat → Prop) (f g : Fin k → Fin n) : Prop where
  injF : Function.Injective f
  injG : Function.Injective g
  src : ∀ z, (∃ i, f i=z) ↔ region (source G z z)
  tgt : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z)
  srcConfig : Configuration (restricted (source G) f)
  tgtConfig : Configuration (restricted (targetName p) g)
  used : ∀ s, (∃ i j, source G (f i) (f j)=s) ↔ ∃ x y, targetName p (g x) (g y)=s
  products : ∀ s t i j x y, source G (f i) (f j)=targetName p (g x) (g y) →
    count (restricted (source G) f) s t i j=count (restricted (targetName p) g) s t x y
  sameDiag : ∀ i, source G (f i) (f i)=targetName p (g i) (g i)
  srcLarge : ∀ i, 4 ≤ (Finset.univ.filter (fun j => source G (f j) (f j)=source G (f i) (f i))).card
  tgtLarge : ∀ i, 4 ≤ (Finset.univ.filter (fun j => targetName p (g j) (g j)=targetName p (g i) (g i))).card

abbrev Data {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (f g : Fin 14 → Fin n) := DataFor p (large G) f g

private theorem sum_if (xs : List Nat) :
    (xs.map (fun k => if 3 < k then k else 0)).sum = (xs.filter (fun k => 3 < k)).sum := by
  induction xs with
  | nil => rfl
  | cons k xs ih => by_cases h : 3 < k <;> simp [h,ih]

private theorem card_core {n : Nat} {G : Graph n} {xs : List Nat} (P : Profile G xs) :
    (vertices (source G) (large G)).card=(xs.filter (fun k => 3 < k)).sum := by
  classical
  let active := Finset.univ.filter (fun j : Fin xs.length => 3 < xs[j.val])
  have named (z : Fin n) : vertices (source G) (fun w => w=source G z z) = fiber G z := by
    ext t; simp [fiber_eq]
  have whole : vertices (source G) (large G) = Finset.univ.filter (fun i => P.tag i ∈ active) := by
    ext i
    simp [active,large,named,P.fiber_size]
  have eq := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) active P.tag
  rw [whole,←eq]
  simp_rw [P.size]
  rw [Finset.sum_filter]
  exact (Fin.sum_univ_fun_getElem xs (fun k => if 3 < k then k else 0)).trans (sum_if xs)

private theorem local_large {n : Nat} {G : Graph n} (f : Fin 14 → Fin n) (fi : Function.Injective f)
    (range : ∀ z, (∃ i, f i=z) ↔ large G (source G z z)) (i : Fin 14) :
    4 ≤ (Finset.univ.filter (fun j => source G (f j) (f j) = source G (f i) (f i))).card := by
  classical
  let e : Fin 14 ↪ Fin n := ⟨f,fi⟩
  let C := Finset.univ.filter (fun j => source G (f j) (f j) = source G (f i) (f i))
  have all : C.map e = vertices (source G) (fun w => w=source G (f i) (f i)) := by
    ext z
    simp only [C,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,mem_vertices]
    constructor
    · rintro ⟨j,h,rfl⟩; exact h
    · intro h
      have hi := (range _).mp ⟨i,rfl⟩
      obtain ⟨j,rfl⟩ := (range z).mpr (h ▸ hi)
      exact ⟨j,h,rfl⟩
  have size := (range _).mp ⟨i,rfl⟩
  change 4 ≤ (vertices (source G) (fun w => w=source G (f i) (f i))).card at size
  simpa only [←all,Finset.card_map,C] using size

/-- A named fourteen-point solver may use the actual complete-space perfect
strategy, its placements, or solely their local configurations. Solving those
tables suffices for the entire graph, in any ambient order. -/
theorem isomorphic_via_core_fourteen {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (sum : (xs.filter (fun k => 3 < k)).sum=14)
    (solve : ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (p : PerfectStrategy G H K) (f g : Fin 14 → Fin n), Data p f g →
      ∃ e : Equiv.Perm (Fin 14), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)))
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  let c := source G
  let d := targetName p
  let reg := large G
  let X := Region c reg
  let Y := Region d reg
  have card : Fintype.card X=14 := (Fintype.card_coe _).trans ((card_core P).trans sum)
  let F : Fin 14 ≃ X := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using card.symm)
  obtain ⟨u,hu⟩ := diagonal_names p
  let m : X ≃ Y := Equiv.subtypeEquiv u (fun i => by simp only [mem_vertices,c,source,hu i,d])
  let T := F.trans m
  let f := fun i : Fin 14 => (F i).val
  let g := fun i : Fin 14 => (T i).val
  have enumerate {a : Fin n → Fin n → Nat} (e : Fin 14 ≃ Region a reg) (x : Fin n) :
      (∃ i, (e i).val=x) ↔ reg (a x x) := by
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (e i).property
    · intro h
      let z : Region a reg := ⟨x,(mem_vertices _ _ _).mpr h⟩
      exact ⟨e.symm z,congrArg Subtype.val (e.apply_symm_apply z)⟩
  have fi : Function.Injective f := fun _ _ eq => F.injective (Subtype.ext eq)
  have gi : Function.Injective g := fun _ _ eq => T.injective (Subtype.ext eq)
  have diag (i : Fin 14) : c (f i) (f i)=d (g i) (g i) := hu (f i)
  have L := local_large f fi (enumerate F)
  have R (i : Fin 14) : 4 ≤ (Finset.univ.filter (fun j => d (g j) (g j)=d (g i) (g i))).card := by
    simp_rw [←diag]
    exact L i
  obtain ⟨src,tgt,used,prod⟩ := SmallUnion.correspondence p reg f g fi gi (enumerate F) (enumerate T)
  obtain ⟨e,h⟩ := solve p f g ⟨fi,gi,enumerate F,enumerate T,src,tgt,used,prod,diag,L,R⟩
  have localReal : Realizes p reg := by
    refine ⟨(F.symm.trans e).trans T,fun i j => ?_⟩
    simpa only [f,g,Equiv.trans_apply,Equiv.apply_symm_apply] using h (F.symm i) (F.symm j)
  obtain ⟨m',hm⟩ := of_large_region p localReal
  exact ⟨⟨m',m'.symm,m'.symm_apply_apply,m'.apply_symm_apply,fun i j => common_edge p (hm i j)⟩⟩

end QGI.Coherent.LargeFourteenRegion
