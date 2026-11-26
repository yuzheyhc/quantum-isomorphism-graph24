import LargeOrderFourDirections
import LargeOrderEighteenFour
import LargeOrderSixteen

noncomputable section
namespace QGI.Coherent.LargeOrderFiveFours
open SixTenCoordinates LargeOrderSquareInterface LargeOrderStrongPaths CoprimeProfiles SmallUnion SmallFiberExtension
open FiberPairExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private reverse from RegionalFourFourEight
open private card_shore from LargeOrderEighteenFour
open private maps_one from LargeOrderSquareInterface

private def group : Fin 3 → Fin 2 → Fin 5 := ![![0,1],![2,3],![4,4]]

private theorem regroup : ∀ m : Fin 5 → Fin 5, (∀ i, m (m i)=i) →
    ∃ e : Equiv.Perm (Fin 5),
      (∀ q r : Fin 3, q≠r → ∀ i j, m (e (group q i))≠e (group r j)) ∧ m (e 4)=e 4 := by native_decide

private theorem partition {T : Fin 5 → Fin 5 → Prop} (rev : ∀ i j, T i j → T j i)
    (degree : ∀ i j k, i≠j → i≠k → j≠k → T i j ∨ T i k) :
    ∃ e : Equiv.Perm (Fin 5), (∀ q r : Fin 3, q≠r → ∀ i j, T (e (group q i)) (e (group r j))) ∧
      ∀ i : Fin 4, T (e 4) (e i.castSucc) := by
  classical
  let bad := fun i j => i≠j ∧ ¬T i j
  let mate := fun i => if h : ∃ j, bad i j then h.choose else i
  have chosen {i j} (h : bad i j) : mate i=j := by
    let ex : ∃ j, bad i j := ⟨j,h⟩
    have s := ex.choose_spec
    rw [show mate i=ex.choose from dif_pos ex]
    by_contra ne
    exact (degree i _ j s.1 h.1 ne).elim s.2 h.2
  have inv (i) : mate (mate i)=i := by
    by_cases ex : ∃ j, bad i j
    · have s := ex.choose_spec
      rw [chosen s]
      exact chosen ⟨Ne.symm s.1,fun t => s.2 (rev _ _ t)⟩
    · simp [mate,ex]
  obtain ⟨e,pair,free⟩ := regroup mate inv
  have disj : ∀ (q r : Fin 3), q≠r → ∀ i j, group q i≠group r j := by decide
  refine ⟨e,fun q r qr i j => ?_,fun i => ?_⟩
  · by_contra h
    exact pair q r qr i j (chosen ⟨fun h => disj q r qr i j (e.injective h),h⟩)
  · have ne := (by decide : ∀ i : Fin 4, (4 : Fin 5)≠i.castSucc) i
    exact Classical.byContradiction (fun h => ne (e.injective (free.symm.trans
      (chosen (i:=e 4) (j:=e i.castSucc) ⟨fun s => ne (e.injective s),h⟩))))

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem four_remaining {l : Fin 5 → Nat} (F : ∀ i : Fin 5, Shore c₀ (l i) (Fin 4))
    (distinct : Function.Injective l) (reg : Nat → Prop) (inside : ∀ i, reg (l i))
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=20)
    (cover : ∀ x, reg (c₀ x x) → ∃ i, c₀ x x=l i) (j : Fin 5) :
    Realizes p (fun s => reg s ∧ s≠l j) := by
  classical
  let c := c₀
  let keep := fun s => reg s ∧ s≠l j
  have diff : vertices c keep=vertices c reg \ vertices c (·=l j) := by
    ext z; simp only [mem_vertices,Finset.mem_sdiff,keep]
  have sub : vertices c (·=l j) ⊆ vertices c reg := fun z h =>
    (mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp h).symm ▸ inside j)
  have card : (vertices c keep).card=16 := by rw [diff,Finset.card_sdiff sub,size,card_shore (F j)]
  apply LargeOrderBlocks.of_solver p keep (fun z hz => active z hz.1) card
  intro f g D
  have actual (i : Fin 16) : keep (c (f i) (f i)) := (D.src _).mp ⟨i,rfl⟩
  have other (t : Fin 4) : ∃ i, f i=atPoint (F (j.succAbove t)) 0 := by
    apply (D.src _).mpr
    rw [(F (j.succAbove t) 0).property]
    exact ⟨inside _,fun h => Fin.succAbove_ne j t (distinct h)⟩
  choose u hu using other
  refine LargeOrderSixteen.four_cells p f g D ?_ u ?_
  · intro i
    obtain ⟨t,ht⟩ := cover _ (actual i).1
    have same : fiber G (f i)=vertices c (·=l t) := by
      ext x; simp only [FourTwelveFunctional.fiber_eq,mem_vertices]; exact (congrArg (c x x=·) ht).to_iff
    rw [same,card_shore (F t)]
  · intro i
    obtain ⟨t,ht⟩ := cover _ (actual i).1
    have ne : t≠j := fun h => (actual i).2 (ht.trans (congrArg l h))
    obtain ⟨s,rfl⟩ := Fin.exists_succAbove_eq ne
    exact ⟨s,by rw [hu]; exact ht.trans (F (j.succAbove s) 0).property.symm⟩

theorem frames {l : Fin 5 → Nat} (F : ∀ i : Fin 5, Shore c₀ (l i) (Fin 4))
    (distinct : Function.Injective l) (reg : Nat → Prop) (inside : ∀ i, reg (l i))
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=20)
    (cover : ∀ x, reg (c₀ x x) → ∃ i, c₀ x x=l i) : Realizes p reg := by
  classical
  let c := c₀
  let law := sourceLaws (closure G)
  let u := fun i => atPoint (F i) 0
  by_contra bad
  have no (i j : Fin 5) (ne : i≠j) : ¬MapsOne c (l i) (l j) := by
    rintro ⟨x,y,hx,hy,pin⟩
    have old := four_remaining p F distinct reg inside active size cover j
    apply bad (RegionalFourFourEight.functional p old _ x y
      ⟨by change reg (c x x); rw [hx]; exact inside i,fun h => ne (distinct (hx.symm.trans h))⟩ hy pin)
    intro z hz
    by_cases h : c z z=l j
    · exact Or.inr h
    · exact Or.inl ⟨hz,h⟩
  have nop (i j : Fin 5) (ne : i≠j) : ¬Pin (F i) (F j) := fun h => no i j ne (maps_one law _ _ h)
  have cycle' {i j : Fin 5} (ne : i≠j) (miss : ¬twins c (l i) (l j)) : CycleAt c (l j) (l i) :=
    cycle_reverse law (((square law (F i) (F j)).resolve_left (no i j ne)).resolve_left miss)
  obtain ⟨e,paired,free⟩ := partition (T:=fun i j => twins c (l i) (l j)) (fun _ _ h => reverse h)
    (fun i j k ij ik jk => by
      by_cases h : twins c (l i) (l j)
      · exact Or.inl h
      · exact Or.inr (by by_contra h'; exact no j k jk (cycles_force law (cycle' ij h) (cycle' ik h'))))
  have anchors : ∃ v : Fin 5 → Fin n, ∀ i j, c (u i) (u j)=targetName p (v i) (v j) := by
    by_cases uniform : ∃ i j : Fin 5, i≠j ∧ ∀ x y, colors (F i) (F j) x y=colors (F i) (F j) 0 0
    · obtain ⟨i,j,ne,all⟩ := uniform
      have third : ∀ i j : Fin 5, ∃ k, i≠k ∧ j≠k := by decide
      obtain ⟨k,ik,jk⟩ := third i j
      exact LargeOrderFiveAnchors.complete p u i j k ne ik jk (LargeOrderFourDirections.uniform_forces law _ _ all _)
    · have nonu (i j : Fin 5) (ne : i≠j) : ¬∀ x y, colors (F i) (F j) x y=colors (F i) (F j) 0 0 :=
        fun h => uniform ⟨i,j,ne,h⟩
      let idx := fun i : Fin 4 => e i.castSucc
      have diff (i : Fin 4) : e 4≠idx i := fun h => (by decide : ∀ i : Fin 4, (4 : Fin 5)≠i.castSucc) i (e.injective h)
      have inj : Function.Injective idx := fun _ _ h => Fin.castSucc_injective _ (e.injective h)
      obtain ⟨i,j,ne,forced⟩ := LargeOrderFourDirections.four_neighbors law (F (e 4)) (fun i => F (idx i))
        (fun i => nop _ _ (diff i)) (fun i => nonu _ _ (diff i)) free
        (fun _ _ ne => nop _ _ (fun h => ne (inj h))) (fun _ _ ne => nonu _ _ (fun h => ne (inj h)))
      exact LargeOrderFiveAnchors.complete p u _ _ (e 4) (fun h => ne (inj h)) (diff i).symm (diff j).symm forced
  obtain ⟨v,hv⟩ := anchors
  let idx := fun q j => e (group q j)
  let a := fun q j => u (idx q j)
  have diag (q j) : source G (a q j) (a q j)=l (idx q j) := (F (idx q j) 0).property
  apply bad (LargeOrderFourPairs.synchronized p reg a (fun q j => v (idx q j)) (fun _ _ _ _ => hv _ _) ?_ ?_ ?_)
  · intro q
    rw [diag,diag]
    exact (RegionalTwoAnchor.pair_bound (F (idx q 0)) (F (idx q 1))).trans (by decide)
  · intro x hx
    obtain ⟨i,h⟩ := cover x hx
    obtain ⟨t,rfl⟩ := e.surjective i
    obtain ⟨q,j,rfl⟩ := (by decide : ∀ t : Fin 5, ∃ q j, group q j=t) t
    exact ⟨q,j,h.trans (diag q j).symm⟩
  · intro q r ne i j
    rw [diag,diag]; exact paired q r ne i j

theorem solve {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)}
    (num : ids.card=5) (parts : ∀ i∈ids, xs[i.val]=4)
    (reg : Nat → Prop) (shape : ∀ x, reg (c₀ x x) ↔ P.tag x ∈ ids)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=20) : Realizes p reg := by
  classical
  let tags : Fin 5 ≃ {i // i∈ids} := Fintype.equivOfCardEq (by simp [num])
  choose a ha using fun i : Fin 5 => P.occurs (tags i).val (by rw [parts _ (tags i).property]; decide)
  let l := fun i => c₀ (a i) (a i)
  let F (i : Fin 5) : Shore c₀ (l i) (Fin 4) :=
    (Fintype.equivOfCardEq (show Fintype.card (Fin 4)=Fintype.card {z // z∈fiber G (a i)} by
      simp [P.fiber_size,ha,parts _ (tags i).property])).trans (Equiv.subtypeEquivRight (FourTwelveFunctional.fiber_eq _))
  apply frames p F (fun i j h => tags.injective (Subtype.ext ((ha i).symm.trans (((P.same _ _).mpr h).trans (ha j)))))
    reg (fun i => (shape _).mpr ((ha i).symm ▸ (tags i).property)) active size
  intro x hx
  obtain ⟨i,hi⟩ := tags.surjective ⟨P.tag x,(shape _).mp hx⟩
  exact ⟨i,(P.same _ _).mp ((congrArg Subtype.val hi).symm.trans (ha i).symm)⟩

end QGI.Coherent.LargeOrderFiveFours
