import LargeOrderFourPairs
import LargeOrderSquareInterface
import LargeOrderFourteen

noncomputable section
namespace QGI.Coherent.LargeOrderEighteenFour
open SixTenCoordinates LargeOrderSquareInterface LargeOrderStrongPaths CoprimeProfiles SmallUnion SmallFiberExtension
open FiberPairExtension StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private reverse from RegionalFourFourEight

private theorem pair_partition : ∀ (b : Fin 3 → Fin 3 → Bool) (s : Fin 3 → Bool),
    (∀ i j, b i j=b j i) →
    (∀ i j k, i≠j → i≠k → j≠k → b i j=true ∨ b i k=true) →
    (∀ i j, i≠j → b i j=true ∨ s i=true) →
    (∀ i j, i≠j → s i=true ∨ s j=true) →
    ∃ e : Equiv.Perm (Fin 3), b (e 0) (e 2)=true ∧ b (e 1) (e 2)=true ∧ s (e 0)=true ∧ s (e 1)=true := by
  intro b s sym deg mixed six
  have choose : ∀ A B C D E F : Bool,
      (A=true ∨ B=true) → (A=true ∨ C=true) → (B=true ∨ C=true) →
      (A=true ∨ D=true) → (A=true ∨ E=true) → (B=true ∨ D=true) → (B=true ∨ F=true) →
      (C=true ∨ E=true) → (C=true ∨ F=true) → (D=true ∨ E=true) → (D=true ∨ F=true) → (E=true ∨ F=true) →
      (B=true ∧ C=true ∧ D=true ∧ E=true) ∨ (A=true ∧ C=true ∧ D=true ∧ F=true) ∨
      (B=true ∧ A=true ∧ F=true ∧ E=true) := by
    intro A B C D E F
    cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> cases F <;> simp
  have h := choose (b 0 1) (b 0 2) (b 1 2) (s 0) (s 1) (s 2)
    (deg 0 1 2 (by decide) (by decide) (by decide))
    (by rw [←sym 1 0]; exact deg 1 0 2 (by decide) (by decide) (by decide))
    (by rw [←sym 2 0,←sym 2 1]; exact deg 2 0 1 (by decide) (by decide) (by decide))
    (mixed 0 1 (by decide)) (by rw [sym 0 1]; exact mixed 1 0 (by decide))
    (mixed 0 2 (by decide)) (by rw [sym 0 2]; exact mixed 2 0 (by decide))
    (mixed 1 2 (by decide)) (by rw [sym 1 2]; exact mixed 2 1 (by decide))
    (six 0 1 (by decide)) (six 0 2 (by decide)) (six 1 2 (by decide))
  rcases h with h|h|h
  · exact ⟨Equiv.refl _,h⟩
  · exact ⟨Equiv.swap 1 2,by simpa [Equiv.swap_apply_def,sym 2 1] using h⟩
  · exact ⟨Equiv.swap 0 2,by simpa [Equiv.swap_apply_def,sym 2 0,sym 1 0] using h⟩

private theorem card_shore {n l k : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l (Fin k)) :
    (vertices c (·=l)).card=k := by
  have e := Equiv.subtypeEquivRight (fun i => mem_vertices c (·=l) i)
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (F.trans e.symm)).symm

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

/-- A thin cross color removes a four-point fiber. Otherwise any two
non-twin interfaces meeting at one shore would violate the common-neighbor
histograms or give a thin color between their other ends. The remaining
non-twin interfaces fit inside two disjoint pairs of fibers. -/
theorem frames {l : Fin 3 → Nat} {v : Nat} (F : ∀ i : Fin 3, Shore c₀ (l i) (Fin 4))
    (Y : Shore c₀ v (Fin 6)) (distinct : Function.Injective l) (reg : Nat → Prop)
    (inside : ∀ i, reg (l i)) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (size : (vertices c₀ reg).card=18) (cover : ∀ x, reg (c₀ x x) → (∃ i, c₀ x x=l i) ∨ c₀ x x=v) :
    Realizes p reg := by
  classical
  by_contra bad
  let c := c₀
  have no (i j : Fin 3) (ne : i≠j) : ¬MapsOne c (l i) (l j) := by
    rintro ⟨x,y,hx,hy,pin⟩
    let keep := fun s => reg s ∧ s≠l j
    have diff : vertices c keep=vertices c reg \ vertices c (·=l j) := by
      ext z; simp only [mem_vertices,Finset.mem_sdiff,keep]
    have sub : vertices c (·=l j) ⊆ vertices c reg := fun z h =>
      (mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp h).symm ▸ inside j)
    have old := LargeOrderBlocks.fourteen p keep (fun z hz => active z hz.1)
      (by rw [diff,Finset.card_sdiff sub,size,card_shore (F j)])
    apply bad (RegionalFourFourEight.functional p old _ x y
      ⟨by change reg (c x x); rw [hx]; exact inside i,fun h => ne (distinct (hx.symm.trans h))⟩ hy pin)
    intro z hz
    by_cases h : c z z=l j
    · exact Or.inr h
    · exact Or.inl ⟨hz,h⟩
  let law := sourceLaws (closure G)
  let b := fun i j => decide (twins c (l i) (l j))
  let s := fun i => decide (twins c (l i) v)
  have square' (i j : Fin 3) (ne : i≠j) (miss : ¬twins c (l i) (l j)) : CycleAt c (l i) (l j) :=
    ((square law (F i) (F j)).resolve_left (no i j ne)).resolve_left miss
  have tetra' (i : Fin 3) (miss : ¬twins c (l i) v) : TetraAt c (l i) v :=
    (four_six law (F i) Y).resolve_left miss
  have either {U W : Prop} (fails : ¬U → ¬W → False) : U ∨ W := by tauto
  obtain ⟨e,eq₀,eq₁,eq₂,eq₃⟩ := pair_partition b s (fun i j => Bool.decide_congr
    ⟨fun h => reverse h,fun h => reverse h⟩) (fun i j k ij ik jk => by
      simp only [b,decide_eq_true_eq]
      exact either (fun a b => no j k jk (cycles_force law (cycle_reverse law (square' i j ij a)) (cycle_reverse law (square' i k ik b)))))
    (fun i j ij => by
      simp only [b,s,decide_eq_true_eq]
      exact either (fun a b => mixed_false law (tetra' i b) (cycle_reverse law (square' i j ij a))))
    (fun i j ij => by
      simp only [s,decide_eq_true_eq]
      exact either (fun a b => no i j ij (tetra_force law (tetra' i a) (tetra' j b))))
  simp only [b,s,decide_eq_true_eq] at eq₀ eq₁ eq₂ eq₃
  let a : Fin 2 → Fin 2 → Fin n := ![![atPoint (F (e 0)) 0,atPoint (F (e 1)) 0],![atPoint (F (e 2)) 0,atPoint Y 0]]
  let label : Fin 2 → Fin 2 → Nat := ![![l (e 0),l (e 1)],![l (e 2),v]]
  have diag (q j : Fin 2) : source G (a q j) (a q j)=label q j := by
    fin_cases q <;> fin_cases j
    · exact (F (e 0) 0).property
    · exact (F (e 1) 0).property
    · exact (F (e 2) 0).property
    · exact (Y 0).property
  apply bad (LargeOrderFourPairs.realize p reg a ?_ ?_ ?_)
  · intro q
    rw [diag,diag]
    have union : vertices c (fun w => w=label q 0 ∨ w=label q 1) =
        vertices c (·=label q 0) ∪ vertices c (·=label q 1) := by ext z; simp only [mem_vertices,Finset.mem_union]
    rw [union]
    refine (Finset.card_union_le _ _).trans ?_
    fin_cases q
    · change (vertices c (·=l (e 0))).card+(vertices c (·=l (e 1))).card≤13
      rw [card_shore (F _),card_shore (F _)]; decide
    · change (vertices c (·=l (e 2))).card+(vertices c (·=v)).card≤13
      rw [card_shore (F _),card_shore Y]; decide
  · intro x inc
    rcases cover x inc with ⟨i,h⟩|h
    · obtain ⟨i,rfl⟩ := e.surjective i
      fin_cases i
      · exact ⟨0,0,h.trans (diag 0 0).symm⟩
      · exact ⟨0,1,h.trans (diag 0 1).symm⟩
      · exact ⟨1,0,h.trans (diag 1 0).symm⟩
    · exact ⟨1,1,h.trans (diag 1 1).symm⟩
  · intro q r ne i j
    simp only [diag]
    fin_cases q <;> fin_cases r <;> fin_cases i <;> fin_cases j <;>
      first | exact (ne rfl).elim | exact eq₀ | exact eq₁ | exact eq₂ | exact eq₃ |
              exact reverse eq₀ | exact reverse eq₁ | exact reverse eq₂ | exact reverse eq₃

def accepted {xs : List Nat} (ids : Finset (Fin xs.length)) := decide (ids.card=4 ∧
  (ids.filter (fun i => xs[i.val]=4)).card=3 ∧ ∃ i ∈ ids, xs[i.val]=6)

theorem solve {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)} (ok : accepted ids=true)
    (reg : Nat → Prop) (shape : ∀ x, reg (c₀ x x) ↔ P.tag x ∈ ids)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=18) : Realizes p reg := by
  classical
  obtain ⟨count,three,y,iny,sy⟩ := of_decide_eq_true ok
  let A := ids.filter (fun i => xs[i.val]=4)
  have out : y∉A := fun h => (by decide : 6≠4) (sy.symm.trans (Finset.mem_filter.mp h).2)
  have all : insert y A=ids := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset iny (Finset.filter_subset _ _)) (by rw [Finset.card_insert_of_not_mem out,three,count])
  let tags : Fin 3 ≃ {i // i∈A} := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using three.symm)
  choose a ha using fun i : Fin 3 => P.occurs (tags i).val (by rw [(Finset.mem_filter.mp (tags i).property).2]; decide)
  obtain ⟨b,hb⟩ := P.occurs y (by rw [sy]; decide)
  let l := fun i => c₀ (a i) (a i)
  let v := c₀ b b
  have shore (x : Fin n) {k : Nat} (h : (fiber G x).card=k) : Nonempty (Shore c₀ (c₀ x x) (Fin k)) := by
    let e := Fintype.equivOfCardEq (show Fintype.card (Fin k) = Fintype.card {z // z∈fiber G x} by simp [h])
    exact ⟨e.trans (Equiv.subtypeEquivRight (FourTwelveFunctional.fiber_eq x))⟩
  let F := fun i => Classical.choice (shore (a i) (k:=4) (by rw [P.fiber_size,ha,(Finset.mem_filter.mp (tags i).property).2]))
  obtain ⟨Y⟩ := shore b (k:=6) (by rw [P.fiber_size,hb,sy])
  have injective : Function.Injective l := fun i j h => tags.injective
    (Subtype.ext ((ha i).symm.trans (((P.same _ _).mpr h).trans (ha j))))
  apply frames p (l:=l) (v:=v) F Y injective reg
    (fun i => (shape _).mpr ((ha i).symm ▸ (Finset.mem_filter.mp (tags i).property).1)) active size
  intro x hx
  have inc := (shape _).mp hx
  rw [←all,Finset.mem_insert] at inc
  rcases inc with h|h
  · exact Or.inr ((P.same _ _).mp (h.trans hb.symm))
  · obtain ⟨i,hi⟩ := tags.surjective ⟨P.tag x,h⟩
    exact Or.inl ⟨i,(P.same _ _).mp ((congrArg Subtype.val hi).symm.trans (ha i).symm)⟩

end QGI.Coherent.LargeOrderEighteenFour
