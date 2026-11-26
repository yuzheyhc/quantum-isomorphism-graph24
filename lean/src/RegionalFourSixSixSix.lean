import FourSixSixSixRoot
import SixSixRegion

noncomputable section
namespace QGI.Coherent.RegionalFourSixSixSix
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws LargeFourteenRegion
open LargeOrderSquareInterface LargeOrderTetraInterfaces CoprimeProfiles
open FourSixSix (E incident)
open FourSixSix.Interfaces (flag cells)
open FourTwelveFunctional (source fiber_eq)
open SixSixEightPins (Flat flat_twins)
open private twins from RegionalFourFourEight
variable {n l : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G
private theorem other : ∀ i j : Fin 3, j=i ∨ j=i+1 ∨ j=i+2 := by decide
private theorem ne : ∀ i : Fin 3, i+1≠i ∧ i+2≠i ∧ i+1≠i+2 := by decide
private theorem card {s k : Nat} (X : Shore c₀ s (Fin k)) (i : Fin k) : (fiber G (atPoint X i)).card=k := by
  have eq : fiber G (atPoint X i)=vertices c₀ (·=s) := by ext y; simp only [fiber_eq,mem_vertices,(X i).property]
  rw [eq,RegionalTwoAnchor.card X]

theorem frames {v : Fin 3 → Nat} (F : Shore c₀ l I) (Y : ∀ j, Shore c₀ (v j) E)
    (vd : Function.Injective v) (apart : ∀ j, l≠v j)
    (reg : Nat → Prop) (inF : reg l) (inY : ∀ j, reg (v j))
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=22)
    (cover : ∀ i, reg (c₀ i i) → c₀ i i=l ∨ ∃ j, c₀ i i=v j) : Realizes p reg := by
  classical
  let c := c₀
  let law := sourceLaws (closure G)
  let ext := fun w => ∃ j, w=v j
  have old : Realizes p ext := by
    apply RegionalFourFourEight.restrict_map p (SixSixRegion.realize p (Y 0) (Y 1) (Y 2) (vd.ne (by decide)) (vd.ne (by decide)) (vd.ne (by decide)))
    rintro x ⟨j,h⟩
    fin_cases j <;> tauto
  let keep := fun s w => reg w ∧ w≠s
  have kept (j : Fin 3) : Realizes p (keep (v j)) := by
    have diff : vertices c (keep (v j))=vertices c reg \ vertices c (·=v j) := by ext x; simp only [mem_vertices,Finset.mem_sdiff,keep]
    have sub : vertices c (·=v j)⊆vertices c reg := fun x h => (mem_vertices _ _ _).mpr (((mem_vertices _ _ _).mp h).symm ▸ inY j)
    apply LargeOrderFourSixSix.realize p _ (fun x h => active x h.1) (by rw [diff,Finset.card_sdiff sub,size,RegionalTwoAnchor.card (Y j)])
    · exact ⟨atPoint F 0,by change keep (v j) (c₀ (atPoint F 0) (atPoint F 0)); rw [(F 0).property]; exact ⟨inF,apart j⟩,card F 0⟩
    · refine ⟨atPoint (Y (j+1)) 0,atPoint (Y (j+2)) 0,?_,?_,card _ _,card _ _,?_⟩
      · rw [(Y (j+1) 0).property]; exact ⟨inY _,vd.ne (ne j).1⟩
      · rw [(Y (j+2) 0).property]; exact ⟨inY _,vd.ne (ne j).2.1⟩
      · rw [(Y (j+1) 0).property,(Y (j+2) 0).property]; exact vd.ne (ne j).2.2
  by_contra bad
  have no (i j : Fin 3) (ij : i≠j) : ¬MapsOne c (v i) (v j) := by
    rintro ⟨x,y,hx,hy,pin⟩
    apply bad (RegionalFourFourEight.functional p (kept j) _ x y ⟨(congrArg reg hx).mpr (inY i),fun h => vd.ne ij (hx.symm.trans h)⟩ hy pin)
    intro z hz; by_cases h : c z z=v j
    · exact Or.inr h
    · exact Or.inl ⟨hz,h⟩
  have coord {b k : Nat} (X : Shore c b (Fin k)) (z : Fin n) (h : c z z=b) : ∃ i, atPoint X i=z :=
    ⟨X.symm ⟨z,h⟩,congrArg Subtype.val (X.apply_symm_apply _)⟩
  have noTet (j : Fin 3) (T : Shore c (v j) E) (s : Nat)
      (names : ∀ i t, cells F T i t=s ↔ incident i t) : False := by
    have marked : Shape F T flag := fun ⦃a b x y⦄ h => Bool.decide_congr ((names a b).symm.trans
      ((show cells F T a b=s ↔ cells F T x y=s by rw [show cells F T a b=cells F T x y from h]).trans (names x y)))
    have flat (k : Fin 3) (jk : j≠k) : Flat F (Y k) := by
      rcases FourSixSix.Interfaces.next_to_tetra law F T (Y k) names with ⟨u,h⟩|⟨u,q,more⟩
      · exact fun a b => (h a b).trans (h 0 0).symm
      let Z := q.symm.trans (Y k)
      have m (a b) : cells F Z a b=u ↔ incident a b := by simpa only [Z,Equiv.apply_symm_apply] using more a (q.symm b)
      have mark : Shape F Z flag := fun ⦃a b x y⦄ h => Bool.decide_congr ((m a b).symm.trans
        ((show cells F Z a b=u ↔ cells F Z x y=u by rw [show cells F Z a b=cells F Z x y from h]).trans (m x y)))
      exact (no j k jk (dual_tetra law F T Z marked mark)).elim
    apply bad (LargeOrderThreeClassGlue.overlap p reg ext ⟨j,rfl⟩ cover old ((RegionalTwoAnchor.pair_bound F T).trans (by decide))
      (atPoint T 0) (atPoint T 1) (T 0).property (T 1).property ?_ ?_)
    · intro i x a b hi hx nx ha hb
      obtain ⟨k,hk⟩ := hx
      obtain ⟨i,rfl⟩ := coord F i hi; obtain ⟨a,rfl⟩ := coord F a ha
      obtain ⟨b,rfl⟩ := coord (Y k) b (hb.trans hk); obtain ⟨x,rfl⟩ := coord (Y k) x hk
      have jk : j≠k := fun e => nx (hk.trans (congrArg v e.symm))
      exact (flat k jk i x).trans (flat k jk a b).symm
    · intro i x y hi hx hy ny ha hb
      obtain ⟨k,hk⟩ := hy
      obtain ⟨i,rfl⟩ := coord T i hi; obtain ⟨x,rfl⟩ := coord T x hx
      have jk : j≠k := fun e => ny (hk.trans (congrArg v e.symm))
      obtain ⟨b,rfl⟩ := coord (Y k) y hk
      exact anchored_rows law F T (Y k) marked (fun i z => (flat k jk i z).trans (flat k jk 0 z).symm) i x b ha hb
  have allTwin (j : Fin 3) : FiberPairExtension.twins c l (v j) := by
    rcases FourSixSix.Interfaces.classify law F (Y j) with ⟨u,h⟩|tw|⟨u,q,ht⟩
    · exact twins F (Y j) ⟨fun a b _ _ z => (h a z).trans (h b z).symm,fun _ b z _ a => (h a b).trans (h a z).symm⟩
    · exact tw
    · let T := q.symm.trans (Y j)
      exact (noTet j T u (fun a b => by simpa only [T,Equiv.apply_symm_apply] using ht a (q.symm b))).elim
  by_cases simple : ∃ k, Flat F (Y k)
  · obtain ⟨k,flat⟩ := simple
    let a (i : Fin 3) : Region c ext := ⟨atPoint (Y i) 0,(mem_vertices _ _ _).mpr ⟨i,(Y i 0).property⟩⟩
    have da (i) : c (a i).val (a i).val=v i := (Y i 0).property
    apply bad (RegionalFourFourEight.restrict_map p (FiberPairExtension.attach p F 0 (by decide) ext old (a (k+1)) (a (k+2)) ?_
      ((congrArg (FiberPairExtension.twins c l) (da (k+1))).mpr (allTwin _)) ((congrArg (FiberPairExtension.twins c l) (da (k+2))).mpr (allTwin _))) (fun x h => (cover x h).symm))
    intro z; obtain ⟨j,hj⟩ := (mem_vertices _ _ _).mp z.property
    rcases other k j with rfl|rfl|rfl
    · right; right; intro i x w hw
      obtain ⟨u,hu⟩ := coord F i.val i.property; obtain ⟨b,hb⟩ := coord F x.val x.property
      obtain ⟨y,hy⟩ := coord (Y _) z.val hj; obtain ⟨t,ht⟩ := coord (Y _) w (hw.trans hj)
      rw [←hu,←hb,←hy,←ht]; exact (flat u y).trans (flat b t).symm
    · exact Or.inl (hj.trans (da _).symm)
    · exact Or.inr (Or.inl (hj.trans (da _).symm))
  · exact bad (FourSixSixSixRoot.realize p F Y reg active cover (fun j h => simple ⟨j,h⟩))

def accepted {xs : List Nat} (ids : Finset (Fin xs.length)) := decide (
  (ids.filter (fun i => xs[i.val]=4)).card=1 ∧ (ids.filter (fun i => xs[i.val]=6)).card=3 ∧
  ∀ i∈ids, xs[i.val]=4 ∨ xs[i.val]=6)

theorem solve {xs : List Nat} (P : Profile G xs) {ids : Finset (Fin xs.length)} (ok : accepted ids=true)
    (reg : Nat → Prop) (shape : ∀ x, reg (c₀ x x) ↔ P.tag x ∈ ids)
    (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (size : (vertices c₀ reg).card=22) : Realizes p reg := by
  classical
  obtain ⟨four,six,all⟩ := of_decide_eq_true ok
  have frames' (m k : Nat) (pos : 0<k) (num : (ids.filter (fun i => xs[i.val]=k)).card=m) :
      ∃ l : Fin m → Nat, Function.Injective l ∧ (∀ i, reg (l i)) ∧
      (∀ i, Nonempty (Shore c₀ (l i) (Fin k))) ∧ ∀ x, reg (c₀ x x) → xs[(P.tag x).val]=k → ∃ i, c₀ x x=l i := by
    let A := ids.filter (fun i => xs[i.val]=k)
    let tags : Fin m ≃ {j // j∈A} := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using num.symm)
    choose z hz using fun i : Fin m => P.occurs (tags i).val (by rw [(Finset.mem_filter.mp (tags i).property).2]; exact pos)
    let l := fun i => c₀ (z i) (z i)
    refine ⟨l,fun i j h => tags.injective (Subtype.ext ((hz i).symm.trans (((P.same _ _).mpr h).trans (hz j)))),
      fun i => (shape _).mpr ((hz i).symm ▸ (Finset.mem_filter.mp (tags i).property).1),fun i => ?_,fun x hx hk => ?_⟩
    · let p := Fintype.equivOfCardEq (show Fintype.card (Fin k)=Fintype.card {x // x∈fiber G (z i)} by
        simp [P.fiber_size,hz,(Finset.mem_filter.mp (tags i).property).2])
      exact ⟨p.trans (Equiv.subtypeEquivRight (fiber_eq _))⟩
    · obtain ⟨i,h⟩ := tags.surjective ⟨P.tag x,Finset.mem_filter.mpr ⟨(shape x).mp hx,hk⟩⟩
      exact ⟨i,(P.same _ _).mp ((congrArg Subtype.val h).symm.trans (hz i).symm)⟩
  obtain ⟨u,_,iu,Fu,left⟩ := frames' 1 4 (by decide) four
  obtain ⟨v,vd,iv,Ys,right⟩ := frames' 3 6 (by decide) six
  let F := Classical.choice (Fu 0)
  let Y := fun j => Classical.choice (Ys j)
  refine frames p F Y vd (fun j h => ?_) reg (iu 0) iv active size ?_
  · have num := RegionalTwoAnchor.card F
    rw [h,RegionalTwoAnchor.card (Y j)] at num; contradiction
  · intro x hx
    rcases all _ ((shape x).mp hx) with h|h
    · obtain ⟨j,hh⟩ := left x hx h
      exact Or.inl (hh.trans (congrArg u (Subsingleton.elim j 0)))
    · exact Or.inr (right x hx h)

end QGI.Coherent.RegionalFourSixSixSix
