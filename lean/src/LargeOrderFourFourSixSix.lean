import LargeOrderThreeClassGlue
import LargeOrderTetraInterfaces
import LargeOrderEighteenFour
import LargeOrderFourSixSix

noncomputable section
namespace QGI.Coherent.LargeOrderFourFourSixSix
open SixTenCoordinates LargeOrderSquareInterface LargeOrderTetraInterfaces CoprimeProfiles SmallUnion SmallFiberExtension
open FiberPairExtension StrategyColorLaws LargeFourteenRegion
open FourSixSix (E incident)
open FourSixSix.Interfaces (flag cells)
open FourTwelveFunctional (source fiber_eq)
open private maps_one from LargeOrderSquareInterface
open private twins reverse from RegionalFourFourEight

private def oth : Fin 2 → Fin 2 := ![1,0]
private theorem other (i j : Fin 2) : i=j ∨ i=oth j := by decide +revert
private theorem neq (j : Fin 2) : oth j≠j := by decide +revert

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G

private theorem card {s k : Nat} (S : Shore c₀ s (Fin k)) (i : Fin k) : (fiber G (atPoint S i)).card=k := by
  have same : fiber G (atPoint S i)=vertices c₀ (·=s) := by ext z; simp only [fiber_eq,mem_vertices,(S i).property]
  rw [same,RegionalTwoAnchor.card S]

theorem frames {l v : Fin 2 → Nat} (F : ∀ i : Fin 2, Shore c₀ (l i) I) (Y : ∀ j : Fin 2, Shore c₀ (v j) E)
    (ld : Function.Injective l) (vd : Function.Injective v) (apart : ∀ i j, l i≠v j)
    (reg : Nat → Prop) (inF : ∀ i, reg (l i)) (inY : ∀ j, reg (v j))
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=20)
    (cover : ∀ x, reg (c₀ x x) → (∃ i, c₀ x x=l i) ∨ ∃ j, c₀ x x=v j) : Realizes p reg := by
  classical
  let c := c₀
  let law := sourceLaws (closure G)
  let keep := fun s w => reg w ∧ w≠s
  have rest {s k : Nat} (S : Shore c s (Fin k)) (inside : reg s) : (vertices c (keep s)).card=20-k := by
    have diff : vertices c (keep s)=vertices c reg \ vertices c (·=s) := by ext z; simp only [mem_vertices,Finset.mem_sdiff,keep]
    have sub : vertices c (·=s) ⊆ vertices c reg := fun z h =>
      (mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp h).symm ▸ inside)
    rw [diff,Finset.card_sdiff sub,size,RegionalTwoAnchor.card S]
  have old (i) : Realizes p (keep (l i)) := by
    apply LargeOrderFourSixSix.realize p _ (fun x h => active x h.1) (rest (F i) (inF i))
    · refine ⟨atPoint (F (oth i)) 0,?_,card (F (oth i)) 0⟩
      change keep (l i) (c₀ (atPoint _ _) (atPoint _ _)); rw [(F (oth i) 0).property]
      exact ⟨inF _,fun h => neq i (ld h)⟩
    · refine ⟨atPoint (Y 0) 0,atPoint (Y 1) 0,?_,?_,card (Y 0) 0,card (Y 1) 0,?_⟩
      · rw [(Y 0 0).property]; exact ⟨inY 0,Ne.symm (apart _ _)⟩
      · rw [(Y 1 0).property]; exact ⟨inY 1,Ne.symm (apart _ _)⟩
      · rw [(Y 0 0).property,(Y 1 0).property]; exact fun h => (by decide : (0 : Fin 2)≠1) (vd h)
  apply Classical.byContradiction
  intro bad
  have no {s t : Nat} (dif : s≠t) (ins : reg s) (map : Realizes p (keep t)) : ¬MapsOne c s t := by
    rintro ⟨x,y,hx,hy,pin⟩
    apply bad (RegionalFourFourEight.functional p map _ x y
      ⟨by change reg (c x x); rw [hx]; exact ins,fun h => dif (hx.symm.trans h)⟩ hy pin)
    intro z hz
    by_cases h : c z z=t
    · exact Or.inr h
    · exact Or.inl ⟨hz,h⟩
  have noF (i) : ¬Pin (F i) (F (oth i)) := fun h =>
    no (fun eq => neq i (ld eq.symm)) (inF i) (old (oth i)) (maps_one law _ _ h)
  have noY (j) : ¬MapsOne c (v j) (v (oth j)) :=
    no (fun h => neq j (vd h.symm)) (inY j) (LargeOrderBlocks.fourteen p _
      (fun i hz => active i hz.1) (rest (Y (oth j)) (inY _)))
  have tetra (i j : Fin 2) (T : Shore c (v j) E) (s : Nat)
      (truth : ∀ x y, cells (F i) T x y=s ↔ incident x y) : False := by
    have inc : Shape (F i) T flag := fun ⦃a b x y⦄ h => Bool.decide_congr ((truth a b).symm.trans
      ((show cells (F i) T a b=s ↔ cells (F i) T x y=s by rw [show cells (F i) T a b=cells (F i) T x y from h]).trans (truth x y)))
    have fu := uniform_four law (F i) T (F (oth i)) inc (noF i)
    rcases FourSixSix.Interfaces.next_to_tetra law (F i) T (Y (oth j)) truth with ⟨u,yu⟩|⟨u,q,more⟩
    swap
    · let Z := q.symm.trans (Y (oth j))
      have m (a b) : cells (F i) Z a b=u ↔ incident a b := by simpa only [Z,Equiv.apply_symm_apply] using more a (q.symm b)
      have bl : Shape (F i) Z flag := fun ⦃a b x y⦄ h => Bool.decide_congr ((m a b).symm.trans
        ((show cells (F i) Z a b=u ↔ cells (F i) Z x y=u by rw [show cells (F i) Z a b=cells (F i) Z x y from h]).trans (m x y)))
      exact noY j (dual_tetra law (F i) T Z inc bl)
    let old' := keep (l i)
    have ext (z : Fin n) (oldz : old' (c z z)) (nv : c z z≠v j) : c z z=l (oth i) ∨ c z z=v (oth j) := by
      rcases cover z oldz.1 with ⟨t,h⟩|⟨t,h⟩
      · rcases other t i with rfl|rfl
        · exact (oldz.2 h).elim
        · exact Or.inl h
      · rcases other t j with rfl|rfl
        · exact (nv h).elim
        · exact Or.inr h
    have coord {t : Nat} {X : Type} (S : Shore c t X) (x : Fin n) (h : c x x=t) : ∃ k, atPoint S k=x :=
      ⟨S.symm ⟨x,h⟩,congrArg Subtype.val (S.apply_symm_apply _)⟩
    apply bad (LargeOrderThreeClassGlue.overlap p reg old' ⟨inY _,Ne.symm (apart _ _)⟩
      (fun x hx => by by_cases h : c x x=l i; exact Or.inl h; exact Or.inr ⟨hx,h⟩)
      (old i) ((RegionalTwoAnchor.pair_bound (F i) T).trans (by decide))
      (atPoint T 0) (atPoint T 1) (T 0).property (T 1).property ?_ ?_)
    · intro x y x' y' hx hy ny hx' hy'
      obtain ⟨a,rfl⟩ := coord (F i) x hx
      obtain ⟨a',rfl⟩ := coord (F i) x' hx'
      rcases ext y hy ny with h|h
      · obtain ⟨b,rfl⟩ := coord (F (oth i)) y h
        obtain ⟨b',rfl⟩ := coord (F (oth i)) y' (hy'.trans h)
        exact (fu a b).trans (fu a' b').symm
      · obtain ⟨b,rfl⟩ := coord (Y (oth j)) y h
        obtain ⟨b',rfl⟩ := coord (Y (oth j)) y' (hy'.trans h)
        exact (yu a b).trans (yu a' b').symm
    · intro x x' z hx hx' hz nz ha hb
      obtain ⟨a,rfl⟩ := coord T x hx
      obtain ⟨a',rfl⟩ := coord T x' hx'
      rcases ext z hz nz with h|h
      · obtain ⟨b,rfl⟩ := coord (F (oth i)) z h
        exact anchored_rows law (F i) T (F (oth i)) inc (fun i j => (fu i j).trans (fu 0 j).symm) a a' b ha hb
      · obtain ⟨b,rfl⟩ := coord (Y (oth j)) z h
        exact anchored_rows law (F i) T (Y (oth j)) inc (fun i j => (yu i j).trans (yu 0 j).symm) a a' b ha hb
  have allTwin (i j) : FiberPairExtension.twins c (l i) (v j) := by
    rcases FourSixSix.Interfaces.classify law (F i) (Y j) with ⟨s,h⟩|tw|⟨s,q,ht⟩
    · exact twins (F i) (Y j) ⟨fun a b _ _ z => (h a z).trans (h b z).symm,fun _ b z _ a => (h a b).trans (h a z).symm⟩
    · exact tw
    · let T := q.symm.trans (Y j)
      exact (tetra i j T s (fun a b => by simpa only [T,Equiv.apply_symm_apply] using ht a (q.symm b))).elim
  let a : Fin 2 → Fin 2 → Fin n := ![fun i => atPoint (F i) 0, fun j => atPoint (Y j) 0]
  have left (i : Fin 2) : c₀ (a 0 i) (a 0 i)=l i := (F i 0).property
  have right (i : Fin 2) : c₀ (a 1 i) (a 1 i)=v i := (Y i 0).property
  let labels : Fin 2 → Fin 2 → Nat := ![l,v]
  have diag (q i : Fin 2) : c₀ (a q i) (a q i)=labels q i := by
    fin_cases q
    · exact left i
    · exact right i
  apply bad (LargeOrderFourPairs.realize p reg a ?_ ?_ ?_)
  · intro q; rw [diag,diag]; fin_cases q
    · exact (RegionalTwoAnchor.pair_bound (F 0) (F 1)).trans (by decide)
    · exact (RegionalTwoAnchor.pair_bound (Y 0) (Y 1)).trans (by decide)
  · intro x hx; rcases cover x hx with ⟨i,h⟩|⟨i,h⟩
    · exact ⟨0,i,h.trans (left i).symm⟩
    · exact ⟨1,i,h.trans (right i).symm⟩
  · intro q r ne i j
    rw [diag,diag]
    fin_cases q <;> fin_cases r <;> first | exact (ne rfl).elim | exact allTwin _ _ | exact reverse (allTwin _ _)

def accepted {xs : List Nat} (ids : Finset (Fin xs.length)) := decide (
  (ids.filter (fun i => xs[i.val]=4)).card=2 ∧ (ids.filter (fun i => xs[i.val]=6)).card=2 ∧
  ∀ i∈ids, xs[i.val]=4 ∨ xs[i.val]=6)

theorem solve {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)} (ok : accepted ids=true)
    (reg : Nat → Prop) (shape : ∀ x, reg (c₀ x x) ↔ P.tag x ∈ ids)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=20) : Realizes p reg := by
  classical
  obtain ⟨four,six,all⟩ := of_decide_eq_true ok
  have frames' (k : Nat) (pos : 0<k) (num : (ids.filter (fun i => xs[i.val]=k)).card=2) :
      ∃ l : Fin 2 → Nat, Function.Injective l ∧ (∀ i, reg (l i)) ∧
      (∀ i, Nonempty (Shore c₀ (l i) (Fin k))) ∧ ∀ x, reg (c₀ x x) → xs[(P.tag x).val]=k → ∃ i, c₀ x x=l i := by
    let A := ids.filter (fun i => xs[i.val]=k)
    let tags : Fin 2 ≃ {j // j∈A} := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using num.symm)
    choose z hz using fun i : Fin 2 => P.occurs (tags i).val (by rw [(Finset.mem_filter.mp (tags i).property).2]; exact pos)
    let l := fun i => c₀ (z i) (z i)
    refine ⟨l,fun i j h => tags.injective (Subtype.ext ((hz i).symm.trans (((P.same _ _).mpr h).trans (hz j)))),
      fun i => (shape _).mpr ((hz i).symm ▸ (Finset.mem_filter.mp (tags i).property).1),fun i => ?_,fun x hx hk => ?_⟩
    · let p := Fintype.equivOfCardEq (show Fintype.card (Fin k)=Fintype.card {x // x∈fiber G (z i)} by
        simp [P.fiber_size,hz,(Finset.mem_filter.mp (tags i).property).2])
      exact ⟨p.trans (Equiv.subtypeEquivRight (fiber_eq _))⟩
    · obtain ⟨i,h⟩ := tags.surjective ⟨P.tag x,Finset.mem_filter.mpr ⟨(shape x).mp hx,hk⟩⟩
      exact ⟨i,(P.same _ _).mp ((congrArg Subtype.val h).symm.trans (hz i).symm)⟩
  obtain ⟨l,ld,inF,Fs,left⟩ := frames' 4 (by decide) four
  obtain ⟨v,vd,inY,Ys,right⟩ := frames' 6 (by decide) six
  let F := fun i => Classical.choice (Fs i)
  let Y := fun j => Classical.choice (Ys j)
  refine frames p F Y ld vd (fun i j h => ?_) reg inF inY active size ?_
  · have num := RegionalTwoAnchor.card (F i)
    rw [h,RegionalTwoAnchor.card (Y j)] at num
    contradiction
  · intro x hx
    exact (all _ ((shape x).mp hx)).imp (left x hx) (right x hx)

end QGI.Coherent.LargeOrderFourFourSixSix
