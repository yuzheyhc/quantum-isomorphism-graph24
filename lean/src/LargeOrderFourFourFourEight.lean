import LargeOrderEightBinary
import LargeOrderEightAnchors
import LargeOrderEighteenFour
import LargeOrderFourDirections

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourFourEight
open SixTenCoordinates LargeOrderSquareInterface LargeOrderEightCycles LargeOrderEightAnchors SmallUnion SmallFiberExtension
open FiberPairExtension StrategyColorLaws LargeFourteenRegion CoprimeProfiles
open FourEightGeometry (Eight)
open FourTwelveFunctional (source)
open private twins reverse from RegionalFourFourEight

set_option synthInstance.maxSize 2000 in
private theorem groups : ∀ (w : Fin 3 → Fin 3 → Bool) (t : Fin 3 → Bool),
    (∀ i j, w i j=w j i) → (∀ i j k, i≠j → i≠k → j≠k → w i j=true ∨ w i k=true) →
    (∀ i j, i≠j → w i j=true ∨ t i=true) →
    (∃ e : Equiv.Perm (Fin 3), w (e 0) (e 2)=true ∧ w (e 1) (e 2)=true ∧ t (e 0)=true ∧ t (e 1)=true) ∨
    (∀ i j, i≠j → w i j=true) := by native_decide

set_option synthInstance.maxSize 2000 in
private theorem needs : ∀ (u : Fin 3 → Fin 3 → Bool) (t : Fin 3 → Bool), (∀ i j, u i j=u j i) →
    (∀ i, t i=false → ∃ j, i≠j ∧ u i j=true) →
    ∃ s d : Fin 3, ∀ i, t i=false → (∃ j, i≠j ∧ u i j=false) → i=s ∨ i=d := by native_decide

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

theorem frames {l : Fin 3 → Nat} {v : Nat} (F : ∀ i : Fin 3, Shore c₀ (l i) I) (Y : Shore c₀ v Eight)
    (ld : Function.Injective l) (apart : ∀ i, l i≠v) (reg : Nat → Prop)
    (inF : ∀ i, reg (l i)) (inY : reg v) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (cover : ∀ x, reg (c₀ x x) → (∃ i, c₀ x x=l i) ∨ c₀ x x=v) : Realizes p reg := by
  classical
  let c := c₀
  let law := sourceLaws (closure G)
  let keep := fun i s => reg s ∧ s≠l i
  have old (j : Fin 3) : Realizes p (keep j) := by
    apply RegionalFourFourEight.solve p (fun h => (by decide : (0 : Fin 2)≠1) (Fin.succAbove_right_injective (p:=j) (ld h)))
      (apart (j.succAbove 0)) (apart (j.succAbove 1)) (F (j.succAbove 0)) (F (j.succAbove 1)) Y
      (keep j) (fun i h => active i h.1)
    intro x hx
    rcases cover x hx.1 with ⟨s,h⟩|h
    · have ne : s≠j := fun hs => hx.2 (h.trans (congrArg l hs))
      obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq ne
      fin_cases i
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  by_contra bad
  have no (s : Nat) (j : Fin 3) (inside : reg s) (distinct : s≠l j) : ¬MapsOne c s (l j) := by
    rintro ⟨x,y,hx,hy,one⟩
    apply bad (RegionalFourFourEight.functional p (old j) _ x y
      ⟨by change reg (c x x); rw [hx]; exact inside,fun h => distinct (hx.symm.trans h)⟩ hy one)
    intro z hz; by_cases h : c z z=l j
    · exact Or.inr h
    · exact Or.inl ⟨hz,h⟩
  have sq {i j : Fin 3} (ne : i≠j) (miss : ¬FiberPairExtension.twins c (l i) (l j)) : CycleAt c (l j) (l i) :=
    cycle_reverse law (((square law (F i) (F j)).resolve_left (no _ _ (inF i) (fun h => ne (ld h)))).resolve_left miss)
  have cy (i) (miss : ¬FiberPairExtension.twins c (l i) v) : Nonempty (CycleData (F i) Y) := by
    rcases FourEightGeometry.interface (F i) Y with ⟨s,t,ht⟩|tw|⟨a,b,pal,code,cells,⟨C⟩⟩
    · exact (no _ i inY (Ne.symm (apart i)) ⟨atPoint Y t,atPoint (F i) s,(Y t).property,(F i s).property,ht⟩).elim
    · exact (miss (twins (F i) Y tw)).elim
    · exact ⟨⟨a,b,pal,code,cells,C⟩⟩
  let w := fun i j => decide (FiberPairExtension.twins c (l i) (l j))
  let t := fun i => decide (FiberPairExtension.twins c (l i) v)
  have pair := groups w t (fun i j => Bool.decide_congr ⟨fun h => reverse h,fun h => reverse h⟩)
    (fun i j k ij ik jk => by
      simp only [w,decide_eq_true_eq]
      by_cases h : FiberPairExtension.twins c (l i) (l j)
      · exact Or.inl h
      · exact Or.inr (by by_contra h'; exact no _ _ (inF j) (fun h => jk (ld h)) (cycles_force law (sq ij h) (sq ik h'))))
    (fun i j ne => by
      simp only [w,t,decide_eq_true_eq]
      by_cases h : FiberPairExtension.twins c (l i) (l j)
      · exact Or.inl h
      · exact Or.inr (by by_contra h'; exact no _ j inY (Ne.symm (apart j)) (conflict (Classical.choice (cy i h')) (sq ne h))))
  by_cases grouped : ∃ e : Equiv.Perm (Fin 3), w (e 0) (e 2)=true ∧ w (e 1) (e 2)=true ∧ t (e 0)=true ∧ t (e 1)=true
  · obtain ⟨e,w₀,w₁,t₀,t₁⟩ := grouped
    simp only [w,t,decide_eq_true_eq] at w₀ w₁ t₀ t₁
    let a : Fin 2 → Fin 2 → Fin n := ![![atPoint (F (e 0)) 0,atPoint (F (e 1)) 0],![atPoint (F (e 2)) 0,atPoint Y 0]]
    let label : Fin 2 → Fin 2 → Nat := ![![l (e 0),l (e 1)],![l (e 2),v]]
    have diag (q j : Fin 2) : source G (a q j) (a q j)=label q j := by
      fin_cases q <;> fin_cases j
      · exact (F (e 0) 0).property
      · exact (F (e 1) 0).property
      · exact (F (e 2) 0).property
      · exact (Y 0).property
    apply bad (LargeOrderFourPairs.realize p reg a ?_ ?_ ?_)
    · intro q; rw [diag,diag]; fin_cases q
      · exact (RegionalTwoAnchor.pair_bound (F (e 0)) (F (e 1))).trans (by decide)
      · exact (RegionalTwoAnchor.pair_bound (F (e 2)) Y).trans (by decide)
    · intro x hx; rcases cover x hx with ⟨i,h⟩|h
      · obtain ⟨i,rfl⟩ := e.surjective i
        fin_cases i
        · exact ⟨0,0,h.trans (diag 0 0).symm⟩
        · exact ⟨0,1,h.trans (diag 0 1).symm⟩
        · exact ⟨1,0,h.trans (diag 1 0).symm⟩
      · exact ⟨1,1,h.trans (diag 1 1).symm⟩
    · intro q r ne i j; simp only [diag]
      fin_cases q <;> fin_cases r <;> fin_cases i <;> fin_cases j <;> first
        | exact (ne rfl).elim | exact w₀ | exact w₁ | exact t₀ | exact t₁
        | exact reverse w₀ | exact reverse w₁ | exact reverse t₀ | exact reverse t₁
  have allSquare := pair.resolve_left grouped
  simp only [w,decide_eq_true_eq] at allSquare
  let un := fun i j => Uniform (F i) (F j)
  have either (i) (miss : ¬FiberPairExtension.twins c (l i) v) : ∃ j, i≠j ∧ un i j := by
    by_contra h
    push_neg at h
    have mixed (j : Fin 3) (ne : i≠j) : ∃ s t, c (atPoint (F i) s) (atPoint (F j) t)≠c (atPoint (F i) 0) (atPoint (F j) 0) := by
      by_contra! no
      exact h j ne (fun a b x y => (no a b).trans (no x y).symm)
    have one : ∃ j : Fin 3, i≠j := (by decide : ∀ i : Fin 3, ∃ j, i≠j) i
    obtain ⟨j,ne⟩ := one
    apply bad (LargeOrderEightBinary.realize p (F i) Y (Classical.choice (cy i miss)) reg active ?_)
    intro x hx; rcases cover x hx with ⟨k,hk⟩|hv
    · by_cases same : i=k
      · subst k; exact ⟨_,F j,Or.inl hk,mixed j ne⟩
      · exact ⟨_,F k,Or.inr (Or.inl hk),mixed k same⟩
    · exact ⟨_,F j,Or.inr (Or.inr hv),mixed j ne⟩
  have missing : ∃ i j : Fin 3, i≠j ∧ un i j := by
    by_contra h
    have all (i) : t i=true := by
      apply decide_eq_true
      by_contra tw
      obtain ⟨j,ne,u⟩ := either i tw
      exact h ⟨i,j,ne,u⟩
    exact grouped ⟨Equiv.refl _,decide_eq_true (allSquare 0 2 (by decide)),decide_eq_true (allSquare 1 2 (by decide)),all 0,all 1⟩
  have sym (i j : Fin 3) : un i j ↔ un j i :=
    ⟨fun h a b x y => law.rev (h b a y x),fun h a b x y => law.rev (h b a y x)⟩
  obtain ⟨s,d,needed⟩ := needs (fun i j => decide (un i j)) t (fun i j => Bool.decide_congr (sym i j))
    (fun i no => by simpa only [decide_eq_true_eq] using either i (of_decide_eq_false no))
  have directions (i : Fin 3) : ∃ f : Eight → Bool, (∀ z, (Finset.univ.filter (fun k => f k=z)).card=4) ∧
      (¬FiberPairExtension.twins c (l i) v → ∀ a b, f a≠f b → sharp (F i) Y a b) := by
    by_cases h : FiberPairExtension.twins c (l i) v
    · exact ⟨fun z => decide (z.val<4),by decide,fun no => (no h).elim⟩
    · obtain ⟨f,bal,sep⟩ := direction (Classical.choice (cy i h)); exact ⟨f,bal,fun _ => sep⟩
  choose cut balance sharp' using directions
  obtain ⟨a,b,sd,dd⟩ := two_cuts (cut s) (cut d) (balance s) (balance d)
  obtain ⟨u,z,ne,empty⟩ := missing
  let embed (i : Fin 3) : Fin 5 := i.castLE (by decide)
  have equal (i) : anchors F Y a b (embed i)=atPoint (F i) 0 := by fin_cases i <;> rfl
  have force := LargeOrderFourDirections.uniform_forces law (F u) (F z) (fun i j => empty i j 0 0) (atPoint Y a)
  have below (i : Fin 3) : embed i≠3 := by
    intro h
    have val := congrArg Fin.val h
    change i.val=3 at val
    omega
  obtain ⟨target,matched⟩ := LargeOrderFiveAnchors.complete p (anchors F Y a b) (embed u) (embed z) 3
    (fun h => ne (Fin.castLE_injective (show 3≤5 by decide) h)) (below u) (below z)
    (by rw [equal,equal]; exact force)
  apply bad (LargeOrderEightAnchors.solve p F Y reg cover a b target matched allSquare ?_)
  intro i; by_cases h : FiberPairExtension.twins c (l i) v
  · exact Or.inl h
  · refine Or.inr ⟨cy i h,?_⟩
    by_cases isolate : ∀ j, i≠j → un i j
    · exact Or.inr isolate
    push_neg at isolate
    have eq := needed i (decide_eq_false h) (by simpa only [decide_eq_false_iff_not] using isolate)
    rcases eq with rfl|rfl
    · exact Or.inl (sharp' _ h a b sd)
    · exact Or.inl (sharp' _ h a b dd)

def accepted {xs : List Nat} (ids : Finset (Fin xs.length)) := decide (ids.card=4 ∧
  (ids.filter (fun i => xs[i.val]=4)).card=3 ∧ ∃ i ∈ ids, xs[i.val]=8)

theorem solve {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)} (ok : accepted ids=true)
    (reg : Nat → Prop) (shape : ∀ x, reg (c₀ x x) ↔ P.tag x ∈ ids)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) : Realizes p reg := by
  classical
  obtain ⟨count,three,y,iny,sy⟩ := of_decide_eq_true ok
  let A := ids.filter (fun i => xs[i.val]=4)
  have out : y∉A := fun h => (by decide : 8≠4) (sy.symm.trans (Finset.mem_filter.mp h).2)
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
  obtain ⟨Y⟩ := shore b (k:=8) (by rw [P.fiber_size,hb,sy])
  have injective : Function.Injective l := fun i j h => tags.injective
    (Subtype.ext ((ha i).symm.trans (((P.same _ _).mpr h).trans (ha j))))
  have apart (i) : l i≠v := fun eq => out ((ha i).symm.trans (((P.same _ _).mpr eq).trans hb) ▸ (tags i).property)
  apply frames p (l:=l) (v:=v) F Y injective apart reg
    (fun i => (shape _).mpr ((ha i).symm ▸ (Finset.mem_filter.mp (tags i).property).1)) ((shape _).mpr (hb.symm ▸ iny)) active
  intro x hx
  have inc := (shape _).mp hx
  rw [←all,Finset.mem_insert] at inc
  rcases inc with h|h
  · exact Or.inr ((P.same _ _).mp (h.trans hb.symm))
  · obtain ⟨i,hi⟩ := tags.surjective ⟨P.tag x,h⟩
    exact Or.inl ⟨i,(P.same _ _).mp ((congrArg Subtype.val hi).symm.trans (ha i).symm)⟩

end QGI.Coherent.LargeOrderFourFourFourEight
