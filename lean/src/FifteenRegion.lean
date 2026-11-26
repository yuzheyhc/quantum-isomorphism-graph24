import LargeFourteenRegion

noncomputable section
namespace QGI.Coherent.LargeFifteenRegion
open SmallFiberExtension SmallUnion StrategyColorLaws CoprimeProfiles LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private card_core from LargeFourteenRegion

private theorem local_large {n : Nat} {G : Graph n} (f : Fin 15 → Fin n) (fi : Function.Injective f)
    (range : ∀ z, (∃ i, f i=z) ↔ large G (source G z z)) (i : Fin 15) :
    4 ≤ (Finset.univ.filter (fun j => source G (f j) (f j) = source G (f i) (f i))).card := by
  classical
  let e : Fin 15 ↪ Fin n := ⟨f,fi⟩
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

/-- A named fifteen-point solver may use the actual complete-space perfect
strategy, its placements, or solely their local configurations. Solving those
tables suffices for the entire graph, in any ambient order. -/
theorem isomorphic_via_core_fifteen {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (sum : (xs.filter (fun k => 3 < k)).sum=15)
    (solve : ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (p : PerfectStrategy G H K) (f g : Fin 15 → Fin n), DataFor p (large G) f g →
      ∃ e : Equiv.Perm (Fin 15), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)))
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
  have card : Fintype.card X=15 := (Fintype.card_coe _).trans ((card_core P).trans sum)
  let F : Fin 15 ≃ X := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using card.symm)
  obtain ⟨u,hu⟩ := diagonal_names p
  let m : X ≃ Y := Equiv.subtypeEquiv u (fun i => by simp only [mem_vertices,c,source,hu i,d])
  let T := F.trans m
  let f := fun i : Fin 15 => (F i).val
  let g := fun i : Fin 15 => (T i).val
  have enumerate {a : Fin n → Fin n → Nat} (e : Fin 15 ≃ Region a reg) (x : Fin n) :
      (∃ i, (e i).val=x) ↔ reg (a x x) := by
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (e i).property
    · intro h
      let z : Region a reg := ⟨x,(mem_vertices _ _ _).mpr h⟩
      exact ⟨e.symm z,congrArg Subtype.val (e.apply_symm_apply z)⟩
  have fi : Function.Injective f := fun _ _ eq => F.injective (Subtype.ext eq)
  have gi : Function.Injective g := fun _ _ eq => T.injective (Subtype.ext eq)
  have diag (i : Fin 15) : c (f i) (f i)=d (g i) (g i) := hu (f i)
  have L := local_large f fi (enumerate F)
  have R (i : Fin 15) : 4 ≤ (Finset.univ.filter (fun j => d (g j) (g j)=d (g i) (g i))).card := by
    simp_rw [←diag]
    exact L i
  obtain ⟨src,tgt,used,prod⟩ := SmallUnion.correspondence p reg f g fi gi (enumerate F) (enumerate T)
  obtain ⟨e,h⟩ := solve p f g ⟨fi,gi,enumerate F,enumerate T,src,tgt,used,prod,diag,L,R⟩
  have localReal : Realizes p reg := by
    refine ⟨(F.symm.trans e).trans T,fun i j => ?_⟩
    simpa only [f,g,Equiv.trans_apply,Equiv.apply_symm_apply] using h (F.symm i) (F.symm j)
  obtain ⟨m',hm⟩ := of_large_region p localReal
  exact ⟨⟨m',m'.symm,m'.symm_apply_apply,m'.apply_symm_apply,fun i j => common_edge p (hm i j)⟩⟩

end QGI.Coherent.LargeFifteenRegion
