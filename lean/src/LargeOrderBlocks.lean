import LargeFourteenRegion

noncomputable section
namespace QGI.Coherent.LargeOrderBlocks
open LargeFourteenRegion SmallFiberExtension SmallUnion StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
open private bundle small_map from SmallFiberExtension

variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Every diagonal class that meets a named region is present there in full. -/
theorem fiber_card {reg : Nat → Prop} (f : Fin k → Fin n) (hf : Function.Injective f)
    (range : ∀ z, (∃ i, f i=z) ↔ reg (source G z z)) (i : Fin k) :
    (Finset.univ.filter (fun j => source G (f j) (f j)=source G (f i) (f i))).card =
      (fiber G (f i)).card := by
  classical
  let e : Fin k ↪ Fin n := ⟨f,hf⟩
  let C := Finset.univ.filter (fun j => source G (f j) (f j)=source G (f i) (f i))
  have all : C.map e = fiber G (f i) := by
    ext x
    simp only [C,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,fiber_eq]
    constructor
    · rintro ⟨j,h,rfl⟩; exact h
    · intro h
      obtain ⟨j,rfl⟩ := (range x).mpr (h ▸ (range _).mp ⟨i,rfl⟩)
      exact ⟨j,h,rfl⟩
  exact (Finset.card_map _).symm.trans (congrArg Finset.card all)

theorem large_iff (i : Fin n) : large G (source G i i) ↔ 4 ≤ (fiber G i).card := by
  have h : vertices (source G) (fun w => w=source G i i) = fiber G i := by
    ext j; simp [fiber_eq]
  rw [large,h]
  omega

theorem small (p : PerfectStrategy G H K) (reg : Nat → Prop)
    (bound : (vertices (source G) reg).card ≤ 13) : Realizes p reg := small_map p reg bound

/-- Provide the given solver with the original strategy and coordinates for
exactly this union of fibers, including the multiplication table in common names. -/
theorem of_solver (p : PerfectStrategy G H K) (reg : Nat → Prop)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=k)
    (solve : ∀ (f g : Fin k → Fin n), DataFor p reg f g →
      ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j))) :
    Realizes p reg := by
  classical
  let c := source G
  let d := targetName p
  let X := Region c reg
  let Y := Region d reg
  have card : Fintype.card X=k := (Fintype.card_coe _).trans size
  let F : Fin k ≃ X := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using card.symm)
  obtain ⟨u,hu⟩ := diagonal_names p
  let m : X ≃ Y := Equiv.subtypeEquiv u (fun i => by simp only [mem_vertices,c,source,hu i,d])
  let T := F.trans m
  let f := fun i : Fin k => (F i).val
  let g := fun i : Fin k => (T i).val
  have enumerate {a : Fin n → Fin n → Nat} (e : Fin k ≃ Region a reg) (x : Fin n) :
      (∃ i, (e i).val=x) ↔ reg (a x x) := by
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (e i).property
    · intro h
      let z : Region a reg := ⟨x,(mem_vertices _ _ _).mpr h⟩
      exact ⟨e.symm z,congrArg Subtype.val (e.apply_symm_apply z)⟩
  have fi : Function.Injective f := fun _ _ eq => F.injective (Subtype.ext eq)
  have gi : Function.Injective g := fun _ _ eq => T.injective (Subtype.ext eq)
  have diag (i : Fin k) : c (f i) (f i)=d (g i) (g i) := hu (f i)
  have L (i : Fin k) : 4 ≤ (Finset.univ.filter (fun j => c (f j) (f j)=c (f i) (f i))).card := by
    rw [fiber_card f fi (enumerate F)]
    exact (large_iff _).mp (active _ ((enumerate F _).mp ⟨i,rfl⟩))
  have R (i : Fin k) : 4 ≤ (Finset.univ.filter (fun j => d (g j) (g j)=d (g i) (g i))).card := by
    simp_rw [←diag]; exact L i
  obtain ⟨src,tgt,used,prod⟩ := correspondence p reg f g fi gi (enumerate F) (enumerate T)
  obtain ⟨e,h⟩ := solve f g ⟨fi,gi,enumerate F,enumerate T,src,tgt,used,prod,diag,L,R⟩
  refine ⟨(F.symm.trans e).trans T,fun i j => ?_⟩
  simpa only [f,g,Equiv.trans_apply,Equiv.apply_symm_apply] using h (F.symm i) (F.symm j)

/-- Compatible local bijections on blocks of arbitrary cardinality glue whenever
each rectangle between fibers in different blocks is monochromatic. -/
theorem glue (p : PerfectStrategy G H K) (reg : Nat → Prop) (block : Nat → Nat)
    (maps : ∀ t, Realizes p (fun v => reg v ∧ block v=t))
    (apart : ∀ x y, reg (source G x x) → reg (source G y y) → block (source G x x) ≠ block (source G y y) →
      ∀ i ∈ fiber G x, ∀ j ∈ fiber G y, source G i j = source G x y) : Realizes p reg := by
  classical
  choose e he using maps
  let c := source G
  let d := targetName p
  let zone := fun (i : Region c reg) => block (c i.val i.val)
  let pt (i : Region c reg) : Region c (fun v => reg v ∧ block v = zone i) :=
    ⟨i.val,(mem_vertices _ _ _).mpr ⟨(mem_vertices _ _ _).mp i.property,rfl⟩⟩
  let f (i : Region c reg) := (e (zone i) (pt i)).val
  have localMap (i j : Region c reg) (h : zone i=zone j) : c i.val j.val=d (f i) (f j) := by
    let y : Region c (fun v => reg v ∧ block v = zone i) :=
      ⟨j.val,(mem_vertices _ _ _).mpr ⟨(mem_vertices _ _ _).mp j.property,h.symm⟩⟩
    have transport (t s : Nat) (eq : t=s) (x : Region c (fun v => reg v ∧ block v=t))
        (z : Region c (fun v => reg v ∧ block v=s)) (xz : x.val=z.val) :
        (e t x).val=(e s z).val := by
      subst s
      rw [show x=z from Subtype.ext xz]
    have ey : (e (zone i) y).val=f j := transport _ _ h _ _ rfl
    exact (he (zone i) (pt i) y).trans (congrArg (d (f i)) ey)
  have names (i j : Region c reg) : c i.val j.val=d (f i) (f j) := by
    by_cases h : zone i=zone j
    · exact localMap i j h
    · obtain ⟨x,y,hit⟩ := StrategyColors.exists_source p (f i) (f j)
      have matchColor := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨hx,hy⟩ := SmallShore.endpoints p matchColor
      have dx := hx.trans (localMap i i rfl).symm
      have dy := hy.trans (localMap j j rfl).symm
      have uniform := apart i.val j.val ((mem_vertices _ _ _).mp i.property)
        ((mem_vertices _ _ _).mp j.property) h x ((fiber_eq _ _).mpr dx) y ((fiber_eq _ _).mpr dy)
      exact uniform.symm.trans matchColor
  obtain ⟨E,points⟩ := bundle p reg f names
  exact ⟨E,fun i j => by rw [points,points]; exact names i j⟩

theorem named (p : PerfectStrategy G H K) (block : Nat → Nat)
    (maps : ∀ t, Realizes p (fun v => large G v ∧ block v=t))
    (apart : ∀ i j, 4 ≤ (fiber G i).card → 4 ≤ (fiber G j).card →
      block (source G i i) ≠ block (source G j j) → (fiber G i).card.Coprime (fiber G j).card) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, source G i j=targetName p (e i) (e j) :=
  of_large_region p (glue p (large G) block maps (fun i j hi hj h _ hx _ hy =>
    CoprimeFibers.monochromatic G i j (apart _ _ ((large_iff _).mp hi) ((large_iff _).mp hj) h) hx hy))

end QGI.Coherent.LargeOrderBlocks
