import LargeOrderSixDirections
import LargeOrderFiveFours
import LargeOrderThreeClassGlue

noncomputable section
namespace QGI.Coherent.LargeOrderTwentyTwoFours
open SixTenCoordinates LargeOrderSquareInterface LargeOrderStrongPaths LargeOrderTetraInterfaces LargeOrderSixDirections
open LargeOrderFiveAnchors FiberPairExtension StrategyColorLaws SmallUnion SmallFiberExtension LargeFourteenRegion CoprimeProfiles
open FourSixSix (E)
open FourTwelveFunctional (source)
open private partition group from LargeOrderFiveFours
open private maps_one from LargeOrderSquareInterface
open private twins reverse from RegionalFourFourEight

private def uniform {n} (c : Fin n → Fin n → Nat) (l r : Nat) := ∀ x y z t,
  c x x=l → c y y=r → c z z=l → c t t=r → c x y=c z t

private theorem point {n l X} {c : Fin n → Fin n → Nat} (F : Shore c l X) (x : Fin n) (h : c x x=l) :
    ∃ i, atPoint F i=x := ⟨F.symm ⟨x,h⟩,congrArg Subtype.val (F.apply_symm_apply _)⟩

private theorem lift_uniform {n l r a b} [NeZero a] [NeZero b] {c : Fin n → Fin n → Nat}
    (F : Shore c l (Fin a)) (S : Shore c r (Fin b)) (h : ∀ i j, raw F S i j=raw F S 0 0) : uniform c l r := by
  intro x y z t hx hy hz ht
  obtain ⟨i,rfl⟩ := point F x hx; obtain ⟨j,rfl⟩ := point S y hy
  obtain ⟨a,rfl⟩ := point F z hz; obtain ⟨b,rfl⟩ := point S t ht
  exact (h i j).trans (h a b).symm

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

theorem frames {l : I → Nat} {v : Nat} (F : ∀ i : I, Shore c₀ (l i) I) (Y : Shore c₀ v E)
    (ld : Function.Injective l) (apart : ∀ i, l i≠v) (reg : Nat → Prop) (inF : ∀ i, reg (l i))
    (inY : reg v) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=22)
    (cover : ∀ x, reg (c₀ x x) → (∃ i, c₀ x x=l i) ∨ c₀ x x=v) : Realizes p reg := by
  classical
  let c := c₀
  let law := sourceLaws (closure G)
  let keep := fun i s => reg s ∧ s≠l i
  have old (i) : Realizes p (keep i) := by
    have diff : vertices c (keep i)=vertices c reg \ vertices c (·=l i) := by ext z; simp only [mem_vertices,Finset.mem_sdiff,keep]
    have sub : vertices c (·=l i) ⊆ vertices c reg := fun z h => (mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp h).symm ▸ inF i)
    apply LargeOrderEighteenFour.frames p (fun j => F (i.succAbove j)) Y (ld.comp Fin.succAbove_right_injective) (keep i)
      (fun j => ⟨inF _,fun h => Fin.succAbove_ne _ _ (ld h)⟩) (fun x h => active x h.1)
      (by rw [diff,Finset.card_sdiff sub,size,RegionalTwoAnchor.card (F i)])
    intro x hx
    rcases cover x hx.1 with ⟨j,h⟩|h
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq (show j≠i from fun eq => hx.2 (h.trans (congrArg l eq)))
      exact Or.inl ⟨k,h⟩
    · exact Or.inr h
  apply Classical.byContradiction
  intro bad
  have no (i j : I) (ne : i≠j) : ¬MapsOne c (l i) (l j) := by
    rintro ⟨x,y,hx,hy,one⟩
    apply bad (RegionalFourFourEight.functional p (old j) _ x y
      ⟨(congrArg reg hx).mpr (inF i),fun h => ne (ld (hx.symm.trans h))⟩ hy one)
    intro x owned; by_cases h : c x x=l j
    · exact Or.inr h
    · exact Or.inl ⟨owned,h⟩
  have nop (i j : I) (ne : i≠j) : ¬Pin (F i) (F j) := fun h => no i j ne (maps_one law _ _ h)
  have tetra (i : I) (T : Shore c v E) (inc : Shape (F i) T FourSixSix.Interfaces.flag) : False := by
    have full (j : I) (ne : i≠j) := uniform_four law (F i) T (F j) inc (nop i j ne)
    have exterior (z) (hz : keep i (c z z)) (nv : c z z≠v) : ∃ j, i≠j ∧ c z z=l j := by
      obtain ⟨j,h⟩ := (cover z hz.1).resolve_right nv
      exact ⟨j,fun h' => hz.2 (h.trans (congrArg l h'.symm)),h⟩
    apply bad (LargeOrderThreeClassGlue.overlap p reg (keep i) ⟨inY,(Ne.symm (apart i))⟩
      (fun z hz => by by_cases h : c z z=l i; exact Or.inl h; exact Or.inr ⟨hz,h⟩)
      (old i) ((RegionalTwoAnchor.pair_bound (F i) T).trans (by decide))
      (atPoint T 0) (atPoint T 1) (T 0).property (T 1).property ?_ ?_)
    · intro x y s t hx hy ny hs ht
      obtain ⟨j,ne,h⟩ := exterior y hy ny
      exact lift_uniform (F i) (F j) (full j ne) x y s t hx h hs (ht.trans h)
    · intro x x' y hx hx' hy ny ha hb
      obtain ⟨j,ne,h⟩ := exterior y hy ny
      obtain ⟨a,rfl⟩ := point T x hx; obtain ⟨b,rfl⟩ := point T x' hx'; obtain ⟨z,rfl⟩ := point (F j) y h
      exact anchored_rows law (F i) T (F j) inc (fun a b => (full j ne a b).trans (full j ne 0 b).symm) a b z ha hb
  have sy (i : I) : FiberPairExtension.twins c (l i) v := by
    rcases FourSixSix.Interfaces.classify law (F i) Y with ⟨s,full⟩|tw|⟨s,q,hit⟩
    · exact twins (F i) Y ⟨fun a b _ _ j => (full a j).trans (full b j).symm,fun _ j k _ a => (full a j).trans (full a k).symm⟩
    · exact tw
    · let T := q.symm.trans Y
      apply (tetra i T ?_).elim
      intro a b x y h
      have raw' (i' j') : FourSixSix.Interfaces.cells (F i) T i' j'=s ↔ FourSixSix.incident i' j' := by
        simpa only [T,Equiv.apply_symm_apply] using hit i' (q.symm j')
      apply Bool.decide_congr
      exact (raw' a b).symm.trans ((Iff.of_eq (congrArg (·=s) h)).trans (raw' x y))
  let label : Fin 5 → Nat := ![l 0,l 1,l 2,l 3,v]
  let u : Fin 5 → Fin n := ![atPoint (F 0) 0,atPoint (F 1) 0,atPoint (F 2) 0,atPoint (F 3) 0,atPoint Y 0]
  have lf (i : I) : label i.castSucc=l i := by fin_cases i <;> rfl
  have uf (i : I) : u i.castSucc=atPoint (F i) 0 := by fin_cases i <;> rfl
  have loc (j : Fin 5) : (∃ i : I, j=i.castSucc) ∨ j=4 := (by decide : ∀ j : Fin 5, (∃ i : I, j=i.castSucc) ∨ j=4) j
  have diag (i) : c₀ (u i) (u i)=label i := by
    rcases loc i with ⟨j,rfl⟩|rfl
    · rw [lf,uf]; exact (F j 0).property
    · exact (Y 0).property
  have sm (i) : (vertices c₀ (·=label i)).card≤6 := by
    rcases loc i with ⟨j,rfl⟩|rfl
    · rw [lf,RegionalTwoAnchor.card (F j)]; decide
    · exact (RegionalTwoAnchor.card Y).le
  have deg (i j k : Fin 5) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
      FiberPairExtension.twins c (label i) (label j) ∨ FiberPairExtension.twins c (label i) (label k) := by
    rcases loc i with ⟨a,rfl⟩|rfl
    · rcases loc j with ⟨b,rfl⟩|rfl
      · rcases loc k with ⟨d,rfl⟩|rfl
        · simp only [lf]
          have strong (b : I) (ne : a≠b) (h : ¬FiberPairExtension.twins c (l a) (l b)) :=
            cycle_reverse law (((square law (F a) (F b)).resolve_left (no a b ne)).resolve_left h)
          by_cases h : FiberPairExtension.twins c (l a) (l b)
          · exact Or.inl h
          · right
            by_contra z
            apply no b d (fun h => jk (congrArg Fin.castSucc h))
            exact cycles_force law (strong b (fun h => ij (congrArg Fin.castSucc h)) h)
              (strong d (fun h => ik (congrArg Fin.castSucc h)) z)
        · rw [lf]; exact Or.inr (sy a)
      · rw [lf]; exact Or.inl (sy a)
    · rcases loc j with ⟨b,rfl⟩|rfl
      · rw [lf]; exact Or.inl (reverse (sy b))
      · exact (ij rfl).elim
  obtain ⟨e,paired,_⟩ := partition (T:=fun i j => FiberPairExtension.twins c (label i) (label j)) (fun _ _ h => reverse h) deg
  have anchors : ∃ z : Fin 5 → Fin n, ∀ i j, c (u i) (u j)=targetName p (z i) (z j) := by
    by_cases ex : ∃ i j : Fin 5, i≠j ∧ uniform c (label i) (label j)
    · obtain ⟨i,j,ne,same⟩ := ex
      obtain ⟨k,ik,jk⟩ := (by decide : ∀ i j : Fin 5, ∃ k, i≠k ∧ j≠k) i j
      apply LargeOrderFiveAnchors.complete p u i j k ne ik jk
      intro x y t h k
      exact same x y _ _ ((law.last (law.rev h)).trans (diag i)) ((law.last k).trans (diag j)) (diag i) (diag j)
    have dif (i j : Fin 5) (ne : i≠j) : ¬uniform c (label i) (label j) := fun h => ex ⟨i,j,ne,h⟩
    have not6 (i : I) : ¬∀ a b, raw (F i) Y a b=raw (F i) Y 0 0 := by
      intro h
      apply dif i.castSucc 4 ((by decide : ∀ i : I, i.castSucc≠4) i)
      rw [lf]; exact lift_uniform _ _ h
    let dir := fun i => Classical.choice (form law (F i) Y (sy i) (not6 i))
    have across (i j : I) (ne : i≠j) :=
      square_names law (F i) (F j) Y (dir i) (dir j) (nop i j ne) (by
        intro h; apply dif i.castSucc j.castSucc (fun h => ne (Fin.castSucc_injective _ h))
        rw [lf,lf]; exact lift_uniform _ _ h)
    apply LargeOrderFiveAnchors.complete p u 0 1 2 (by decide) (by decide) (by decide)
    intro x y t h k
    obtain ⟨a,rfl⟩ := point (F 0) x ((law.last (law.rev h)).trans (F 0 0).property)
    obtain ⟨b,rfl⟩ := point (F 1) y ((law.last k).trans (F 1 0).property)
    obtain ⟨d,rfl⟩ := point (F 2) t ((law.last h).trans (F 2 0).property)
    have ad := ((across 0 2 (by decide) a d 0 0).mp h).mpr ((dir 0).lzero.trans (dir 2).lzero.symm)
    have db := ((across 2 1 (by decide) d b 0 0).mp k).mpr ((dir 2).lzero.trans (dir 1).lzero.symm)
    exact (across 0 1 (by decide) a b 0 0).mpr (iff_of_true (ad.trans db) ((dir 0).lzero.trans (dir 1).lzero.symm))
  obtain ⟨z,hz⟩ := anchors
  let ix := fun q j => e (group q j)
  apply bad (LargeOrderFourPairs.synchronized p reg (fun q j => u (ix q j)) (fun q j => z (ix q j))
    (fun _ _ _ _ => hz _ _) ?_ ?_ ?_)
  · intro q; simp only [diag]
    have eq : vertices c₀ (fun w => w=label (ix q 0) ∨ w=label (ix q 1)) =
        vertices c₀ (·=label (ix q 0)) ∪ vertices c₀ (·=label (ix q 1)) := by ext x; simp only [mem_vertices,Finset.mem_union]
    rw [eq]
    exact (Finset.card_union_le _ _).trans (by have := sm (ix q 0); have := sm (ix q 1); omega)
  · intro x hx
    obtain ⟨i,hi⟩ : ∃ i, c x x=label i := by
      rcases cover x hx with ⟨a,h⟩|h
      · exact ⟨a.castSucc,h.trans (lf a).symm⟩
      · exact ⟨4,h⟩
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨q,j,rfl⟩ := (by decide : ∀ i : Fin 5, ∃ q j, group q j=i) i
    exact ⟨q,j,hi.trans (diag _).symm⟩
  · intro q r ne i j
    simp only [diag]
    exact paired q r ne i j

def accepted {xs : List Nat} (ids : Finset (Fin xs.length)) := decide (ids.card=5 ∧
  (ids.filter (fun i => xs[i.val]=4)).card=4 ∧ ∃ i ∈ ids, xs[i.val]=6)

theorem solve {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)} (ok : accepted ids=true)
    (reg : Nat → Prop) (shape : ∀ x, reg (c₀ x x) ↔ P.tag x ∈ ids)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=22) : Realizes p reg := by
  classical
  obtain ⟨count,three,y,iny,sy⟩ := of_decide_eq_true ok
  let A := ids.filter (fun i => xs[i.val]=4)
  have out : y∉A := fun h => (by decide : 6≠4) (sy.symm.trans (Finset.mem_filter.mp h).2)
  have all : insert y A=ids := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset iny (Finset.filter_subset _ _)) (by rw [Finset.card_insert_of_not_mem out,three,count])
  let tags : Fin 4 ≃ {i // i∈A} := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using three.symm)
  choose a ha using fun i : Fin 4 => P.occurs (tags i).val (by rw [(Finset.mem_filter.mp (tags i).property).2]; decide)
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
  have apart (i) : l i≠v := fun eq => out ((ha i).symm.trans (((P.same _ _).mpr eq).trans hb) ▸ (tags i).property)
  apply frames p (l:=l) (v:=v) F Y injective apart reg
    (fun i => (shape _).mpr ((ha i).symm ▸ (Finset.mem_filter.mp (tags i).property).1)) ((shape _).mpr (hb.symm ▸ iny)) active size
  intro x hx
  have inc := (shape _).mp hx
  rw [←all,Finset.mem_insert] at inc
  rcases inc with h|h
  · exact Or.inr ((P.same _ _).mp (h.trans hb.symm))
  · obtain ⟨i,hi⟩ := tags.surjective ⟨P.tag x,h⟩
    exact Or.inl ⟨i,(P.same _ _).mp ((congrArg Subtype.val hi).symm.trans (ha i).symm)⟩

end QGI.Coherent.LargeOrderTwentyTwoFours
