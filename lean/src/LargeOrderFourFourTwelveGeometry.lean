import RegionalFourTwelve
import LargeOrderFourFourSixSix
import LargeOrderEightAnchors

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourTwelveGeometry
open SixTenCoordinates FourTwelveCycle FourTwelveCycleGraph FourTwelveTypes LargeOrderSquareInterface
open SmallUnion SmallFiberExtension FiberPairExtension
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)
open private induce from SmallUnionRealization
open private twins reverse from RegionalFourFourEight

abbrev Twelve := Fin 12
variable {n l v : Nat} {G : Graph n}
local notation "c₀" => source G

structure Layout (F : Shore c₀ l I) (Y : Shore c₀ v Twelve) where
  mark : Nat
  other : Nat
  different : mark≠other
  palette : ∀ j i, c₀ (atPoint Y j) (atPoint F i)=mark ∨ c₀ (atPoint Y j) (atPoint F i)=other
  col : Twelve → Edge
  cells : ∀ j i, c₀ (atPoint Y j) (atPoint F i)=mark ↔ i∈edge (col j)

structure Around {F : Shore c₀ l I} {Y : Shore c₀ v Twelve} (B : Layout F Y) where
  points : Equiv.Perm I
  label : Twelve → I
  pattern : ∀ j, edge (B.col j)=(edge (cycle (label j))).map points.toEmbedding
  onto : Function.Surjective label

variable {F : Shore (source G) l I} {Y : Shore (source G) v Twelve}

theorem Layout.gram (B : Layout F Y) : Block Y Y Y Y (fun i j => overlap (B.col i) (B.col j))
    (fun i j => overlap (B.col i) (B.col j)) := by
  let A := fun j i => decide (c₀ (atPoint Y j) (atPoint F i)=B.mark)
  have named : Block Y Y F F A A := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=B.mark)) h
  have eq (j k) : Block.overlap A j k=overlap (B.col j) (B.col k) := by
    apply congrArg Finset.card
    ext i; simp [A,B.cells]
  intro i j x y h
  simpa only [eq] using Block.gram (sourceLaws (closure G)) named h

theorem Layout.columns (B : Layout F Y) (j) : neighbors c₀ B.mark (atPoint Y j)=(edge (B.col j)).map (emb F) := by
  have inside : ∃ i, c₀ (atPoint Y j) (atPoint F i)=B.mark := ⟨(FourTwelveCycle.ends (B.col j)).1,(B.cells j _).mpr (by simp [edge])⟩
  obtain ⟨i,hi⟩ := inside
  ext z
  constructor
  · intro hz
    have hit := (Finset.mem_filter.mp hz).2
    obtain ⟨s,rfl⟩ := (range_emb F z).mpr ((Relations.end_colors (closure G) (hit.trans hi.symm)).2.trans (F i).property)
    exact Finset.mem_map.mpr ⟨s,(B.cells j s).mp hit,rfl⟩
  · rintro hz
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(B.cells j s).mpr hs⟩

private theorem same (B : Layout F Y) (j k : Twelve) : mult B.col (B.col j)=mult B.col (B.col k) := by
  have h := Block.hist_eq (sourceLaws (closure G)) B.gram j k 2
  have rule (a b : Twelve) : overlap (B.col a) (B.col b)=2 ↔ B.col b=B.col a := (edge_overlap _ _).trans eq_comm
  simpa only [Block.hist,rule,mult] using h

theorem classify (F : Shore c₀ l I) (Y : Shore c₀ v Twelve) (ne : l≠v) :
    MapsOne c₀ v l ∨ FiberPairExtension.twins c₀ l v ∨
    ∃ B : Layout F Y, Nonempty (Around B) ∨ ∀ e, mult B.col e=2 := by
  classical
  let c := c₀
  let q : I ⊕ Twelve ≃ Fin 16 := finSumFinEquiv
  let join : I ⊕ Twelve → Fin n := Sum.elim (atPoint F) (atPoint Y)
  let u := join ∘ q.symm
  have lf (i) : u (q (.inl i))=atPoint F i := by simp [u,join]
  have yr (i) : u (q (.inr i))=atPoint Y i := by simp [u,join]
  have inj : Function.Injective u := by
    intro x y h
    obtain ⟨x,rfl⟩ := q.surjective x; obtain ⟨y,rfl⟩ := q.surjective y
    cases x with
    | inl x => cases y with
      | inl y => rw [lf,lf] at h; exact congrArg (fun z => q (.inl z)) ((emb F).injective h)
      | inr y => rw [lf,yr] at h; exact (ne ((F x).property.symm.trans ((congrArg (fun z => c z z) h).trans (Y y).property))).elim
    | inr x => cases y with
      | inl y => rw [yr,lf] at h; exact (ne ((F y).property.symm.trans ((congrArg (fun z => c z z) h.symm).trans (Y x).property))).elim
      | inr y => rw [yr,yr] at h; exact congrArg (fun z => q (.inr z)) ((emb Y).injective h)
  have range (z) : (∃ i,u i=z) ↔ c z z=l ∨ c z z=v := by
    constructor
    · rintro ⟨i,rfl⟩; obtain ⟨i,rfl⟩ := q.surjective i
      cases i with | inl i => rw [lf]; exact Or.inl (F i).property | inr i => rw [yr]; exact Or.inr (Y i).property
    · rintro (h|h)
      · obtain ⟨i,rfl⟩ := (range_emb F z).mpr h; exact ⟨q (.inl i),lf i⟩
      · obtain ⟨i,rfl⟩ := (range_emb Y z).mpr h; exact ⟨q (.inr i),yr i⟩
  let d := SmallShore.restrict c u
  let f : Frame d := ⟨q,l,v,ne,fun i => by change c (u _) (u _)=l; rw [lf]; exact (F i).property,
    fun j => by change c (u _) (u _)=v; rw [yr]; exact (Y j).property⟩
  have cross (j i) : crosses f j i=c₀ (atPoint Y j) (atPoint F i) := by
    change c (u (q (.inr j))) (u (q (.inl i)))=_
    rw [yr,lf]
  have cc : Configuration c := ⟨fun _ _ _ h => Relations.diagonal _ h,fun _ _ _ _ h => Relations.transpose _ h,Relations.products _⟩
  have induced := induce cc (fun h => (Relations.end_colors (closure G) h).2) (keep:=fun s => s=l ∨ s=v) u inj range
  have law : Laws d d := ⟨fun h => Relations.transpose _ h,fun h => (Relations.end_colors (closure G) h).2,
    fun a b i j x y eq => induced.products a b i j x y eq⟩
  rcases RegionalFourTwelve.classify f law with tw|⟨j,i,thin⟩|⟨B⟩
  · apply Or.inr (Or.inl (reverse (twins Y F ?_)))
    simpa only [show crosses f=(fun j i => c (atPoint Y j) (atPoint F i)) from funext (fun j => funext (cross j))] using tw
  · refine Or.inl ⟨atPoint Y j,atPoint F i,(Y j).property,(F i).property,fun z hz => ?_⟩
    obtain ⟨a,rfl⟩ := (range_emb F z).mpr ((Relations.end_colors (closure G) hz).2.trans (F i).property)
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp thin
    have hit (a) (ha : crosses f j a=crosses f j i) : a=k := by
      have h : a∈RegionalFourTwelve.line f (crosses f j i) j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
      simpa only [hk,Finset.mem_singleton] using h
    exact congrArg (atPoint F) ((hit a (by rw [cross,cross]; exact hz)).trans (hit i rfl).symm)
  · obtain ⟨B⟩ := B
    let D : Layout F Y := ⟨B.v,B.w,B.vw,fun j i => by rw [←cross]; exact B.palette j i,B.col,fun j i => by
      rw [←cross,B.cells]; simp only [RegionalFourTwelve.line,Finset.mem_filter,Finset.mem_univ,true_and]⟩
    have data : FourPointInterface.PairColumns (closure G) D.mark (emb F) (emb Y) D.col :=
      ⟨fun i => (F i).property.trans (F 0).property.symm,
        fun z => (range_emb Y z).trans (Iff.of_eq (congrArg (c z z=·) (Y 0).property.symm)),D.columns⟩
    rcases shapes D.col (FourPointInterface.of_coherent data).1 with ⟨e,split⟩|⟨o,within,every⟩|full
    · apply Or.inr (Or.inl (reverse (twins Y F ?_)))
      have tw := RegionalFourTwelve.matching B e split
      simpa only [show crosses f=(fun j i => c (atPoint Y j) (atPoint F i)) from funext (fun j => funext (cross j))] using tw
    · choose label hl using within
      have sur : Function.Surjective label := by
        intro i
        obtain ⟨j,hj⟩ := every i
        exact ⟨j,(show Function.Injective cycle by decide) (edge_inj (Finset.map_injective _ ((hl j).symm.trans hj)))⟩
      exact Or.inr (Or.inr ⟨D,Or.inl ⟨⟨o,label,hl,sur⟩⟩⟩)
    · have eq (a) : mult D.col a=mult D.col (D.col 0) := by obtain ⟨j,rfl⟩ := full a; exact same D j 0
      have total : ∑ e, mult D.col e=12 := by
        simpa [mult] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Twelve) (Finset.univ : Finset Edge) D.col
      simp only [eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
      exact Or.inr (Or.inr ⟨D,Or.inr (fun a => (eq a).trans (by omega))⟩)

theorem few (B : Layout F Y) (strong : Nonempty (Around B) ∨ ∀ e, mult B.col e=2) (j : Twelve) :
    mult B.col (B.col j) ≤3 := by
  rcases strong with cycleCase|full
  · obtain ⟨C⟩ := cycleCase
    choose rep hr using C.onto
    have rule (i : I) (q : Twelve) : C.label q=i ↔ B.col q=B.col (rep i) := by
      have h := C.pattern (rep i)
      rw [hr] at h
      constructor
      · intro e; exact edge_inj ((C.pattern q).trans (e ▸ h.symm))
      · intro e
        have eq := (C.pattern q).symm.trans ((congrArg edge e).trans h)
        exact (show Function.Injective cycle by decide) (edge_inj (Finset.map_injective _ eq))
    have count (i : I) : (Finset.univ.filter (fun z => C.label z=i)).card=mult B.col (B.col j) := by
      simpa only [rule,mult] using same B (rep i) j
    have total := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset Twelve) (Finset.univ : Finset I) C.label
    simp [count] at total
    omega
  · rw [full]; decide

end QGI.Coherent.LargeOrderFourFourTwelveGeometry
