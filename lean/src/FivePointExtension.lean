import FivePointInterface
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.FivePointExtension
open SixTenCoordinates hiding V
open FivePointFrame SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
open FourTwelveCycle (neighbors shared_counts)
open RegionalCycleExtension (emb range_emb)
open private uniform_merge bundle from SmallFiberExtension
open private shore from RegionalFourFourEight

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

private def cell (c : Table n) (s : Nat) : ThreeRectangleExtension.Cell c s ≃ {x // c x x=s} :=
  Equiv.subtypeEquivRight (fun x => mem_vertices c (·=s) x)

/-- Five representative pairs of a pentagon determine every internal
and mixed color once their exterior vertices have been placed. -/
theorem align_frame {F T : Fin 5 ↪ Fin n} {Y Z : Fin 5 → Fin n} {a b l : Nat}
    (P : Frame (Relations.color (closure G)) F Y a b)
    (srcFiber : ∀ z, z ∈ Set.range F ↔ Relations.color (closure G) z z=l)
    (dstFiber : ∀ z, z ∈ Set.range T ↔ targetName p z z=l)
    (named : ∀ i j, Relations.color (closure G) (Y i) (Y j) = targetName p (Z i) (Z j)) :
    ∃ e : Equiv.Perm (Fin 5), Frame (targetName p) (e.toEmbedding.trans T) Z a b := by
  classical
  let c := Relations.color (closure G)
  let d := targetName p
  have pull (k : Fin 5) (z : Fin n) : ∃ x, c (Y k) x = d (Z k) z ∧ c x x = d z z := by
    obtain ⟨x,h,_⟩ := PartialFunctional.middle d c (fun s t => (common_products p s t (named k k)).symm) z
    exact ⟨x,h.symm,(SmallShore.endpoints p h.symm).2⟩
  have desc (k : Fin 5) : ∃ t : Edge, neighbors d a (Z k) = (edge t).map T := by
    let S := sectionAt d T a (Z k)
    have es : S.map T = neighbors d a (Z k) := by
      ext z
      constructor
      · intro h
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
        simpa [S,sectionAt,neighbors] using hi
      · intro hz
        obtain ⟨x,h,hd⟩ := pull k z
        have hx : x ∈ neighbors c a (Y k) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.trans (Finset.mem_filter.mp hz).2⟩
        rw [show neighbors c a (Y k) = _ from P.cells k] at hx
        obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hx
        obtain ⟨j,rfl⟩ := (dstFiber z).mpr (hd.symm.trans ((srcFiber x).mp ⟨i,hi⟩))
        exact Finset.mem_map.mpr ⟨j,by simpa [S,sectionAt,neighbors] using hz,rfl⟩
    have cnt := (shared_counts p a (named k k)).1
    change (neighbors (Relations.color (closure G)) a (Y k) ∩ neighbors (Relations.color (closure G)) a (Y k)).card =
      (neighbors d a (Z k) ∩ neighbors d a (Z k)).card at cnt
    simp only [Finset.inter_self,P.cells,←es,Finset.card_map] at cnt
    have two : ∀ i, (cycle i).card=2 := by decide
    obtain ⟨t,ht⟩ := (show ∀ s : Finset (Fin 5), s.card=2 → ∃ t : Edge, edge t=s by decide) S
      (cnt.symm.trans (two k))
    exact ⟨t,ht.symm ▸ es.symm⟩
  choose t ht using desc
  obtain ⟨e,he⟩ := align t (by
    intro i j
    have g := (shared_counts p a (named i j)).1
    change ((neighbors c a (Y i)) ∩ (neighbors c a (Y j))).card =
      ((neighbors d a (Z i)) ∩ (neighbors d a (Z j))).card at g
    simpa only [c,P.cells,ht,←Finset.map_inter,Finset.card_map] using g)
  let E := e.toEmbedding.trans T
  have cells (k) : neighbors d a (Z k) = (cycle k).map E := by
    rw [ht,←he,Finset.map_map]
  refine ⟨e,cells,?_⟩
  intro k j
  have iffA : d (Z k) (E j)=a ↔ j ∈ cycle k := by
    have h : E j ∈ neighbors d a (Z k) ↔ j ∈ cycle k := by rw [cells]; simp
    simpa [neighbors] using h
  by_cases h : j ∈ cycle k
  · exact (iffA.mpr h).trans (if_pos h).symm
  · rw [if_neg h]
    obtain ⟨x,hx,hd⟩ := pull k (E j)
    obtain ⟨i,rfl⟩ := (srcFiber x).mpr (hd.trans ((dstFiber _).mp ⟨e j,rfl⟩))
    have hs := P.names k i
    by_cases hi : i ∈ cycle k
    · exact False.elim ((iffA.not.mpr h) (hx.symm.trans (hs.trans (if_pos hi))))
    · exact hx.symm.trans (hs.trans (if_neg hi))


theorem pentagon {l : Nat} (F : Shore (source G) l V) (reg : Nat → Prop) (old : Realizes p reg)
    (Y : V → Region (source G) reg) (q : Equiv.Perm V) {a b : Nat}
    (P : Frame (source G) (q.toEmbedding.trans (emb F)) (fun i => (Y i).val) a b) :
    Realizes p (fun t => reg t ∨ t=l) := by
  classical
  let c := source G
  let d := targetName p
  obtain ⟨e,he⟩ := old
  let left := q.trans F
  let sl := q.toEmbedding.trans (emb F)
  obtain ⟨m,hm⟩ := diagonal_names p
  let T : Shore d l V := F.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
  have rangeS (x) : x∈Set.range sl ↔ c x x=l := by
    refine Iff.trans ?_ (range_emb F x)
    exact ⟨fun ⟨i,h⟩ => ⟨q i,h⟩,fun ⟨i,h⟩ => ⟨q.symm i,by simpa [sl] using h⟩⟩
  let Z := fun i => (e (Y i)).val
  obtain ⟨k,Q⟩ := align_frame p P rangeS (range_emb T) (fun i j => he (Y i) (Y j))
  let right := k.trans T
  let L := left.trans (cell c l).symm
  let R := right.trans (cell d l).symm
  let g := L.symm.trans R
  have image (i) : g (L i)=R i := by simp [g]
  apply ThreeRectangleExtension.merge_maps p reg l e g he
  · intro x y; obtain ⟨x,rfl⟩ := L.surjective x; obtain ⟨y,rfl⟩ := L.surjective y
    rw [image,image]
    apply recover p P Q (u:=sl x) (v:=(emb T) (k x)) _ y
    intro i; exact (P.names i x).trans (Q.names i x).symm
  · intro x y; obtain ⟨y,rfl⟩ := L.surjective y; rw [image]
    exact recover p P Q (fun i => he (Y i) x) y

/-- A named realization on any union of old fibers extends across one
whole five-point fiber in the original strategy. -/
theorem extend {l : Nat} (F : Shore (source G) l V) (reg : Nat → Prop) (old : Realizes p reg) :
    Realizes p (fun t => reg t ∨ t=l) := by
  classical
  let c := source G
  let total := fun t => reg t ∨ t=l
  by_cases uniform : ∀ a b i j, reg (c a a) → c b b=l → c i i=c a a → c j j=l → c a b=c i j
  · obtain ⟨e,he⟩ := old
    obtain ⟨f,hf⟩ := LargeOrderBlocks.small p (·=l) ((RegionalTwoAnchor.card F).trans_le (by decide))
    obtain ⟨g,hg,_⟩ := uniform_merge p reg l e he f hf uniform
    obtain ⟨u,hu⟩ := bundle p total g hg
    exact ⟨u,fun i j => by rw [hu,hu]; exact hg i j⟩
  push_neg at uniform
  obtain ⟨a,b,i,j,inA,lb,ai,lj,ne⟩ := uniform
  let m := (fiber G a).card
  have pos : 0 < m := Finset.card_pos.mpr ⟨a,(fiber_eq _ _).mpr rfl⟩
  letI : NeZero m := ⟨Nat.ne_of_gt pos⟩
  obtain ⟨Y⟩ := shore a (rfl : (fiber G a).card=m)
  rcases FivePointInterface.classify F Y with same|⟨x,y,one⟩|⟨q,rep,s,t,P⟩
  · have constant (u z : Fin n) (hu : c u u=c a a) (hz : c z z=l) : c u z=c (atPoint Y 0) (atPoint F 0) := by
      simpa only [atPoint,Equiv.apply_symm_apply] using same (F.symm ⟨z,hz⟩) (Y.symm ⟨u,hu⟩)
    exact (ne ((constant a b rfl lb).trans (constant i j ai lj).symm)).elim
  · exact RegionalFourFourEight.functional p old (fun i h => h) (atPoint Y y) (atPoint F x)
      ((congrArg reg (Y y).property).mpr inA) (F x).property one
  · let W (i : V) : Region c reg := ⟨atPoint Y (rep i),(mem_vertices _ _ _).mpr (by
      change reg (source G (atPoint Y (rep i)) (atPoint Y (rep i)))
      rw [show source G (atPoint Y (rep i)) (atPoint Y (rep i))=c a a from (Y (rep i)).property]
      exact inA)⟩
    exact pentagon p F reg old W q P

theorem extend_names (reg : Nat → Prop) (names : Finset Nat)
    (size : ∀ t∈names, (vertices (source G) (·=t)).card=5) (old : Realizes p reg) :
    Realizes p (fun v => reg v ∨ v∈names) := by
  classical
  induction names using Finset.induction_on with
  | empty => exact RegionalFourFourEight.restrict_map p old (fun i h => by simpa using h)
  | @insert t names ht ih =>
    have sz := size t (Finset.mem_insert_self _ _)
    let e := Fintype.equivOfCardEq (show Fintype.card V=Fintype.card (ThreeRectangleExtension.Cell (source G) t) by
      simpa only [Fintype.card_fin,Fintype.card_coe] using sz.symm)
    let F := e.trans (cell (source G) t)
    have next := extend p F _ (ih (fun u hu => size u (Finset.mem_insert_of_mem hu)))
    apply RegionalFourFourEight.restrict_map p next
    intro i h
    rcases h with h|h
    · exact Or.inl (Or.inl h)
    rcases Finset.mem_insert.mp h with h|h
    · exact Or.inr h
    · exact Or.inl (Or.inr h)

end QGI.Coherent.FivePointExtension
