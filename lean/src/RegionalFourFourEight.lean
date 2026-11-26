import RegionalCycleSupport
import RegionalTwoAnchor
import TwoCycleMatchings
import FiberPairExtension

noncomputable section
namespace QGI.Coherent.RegionalFourFourEight
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle SmallUnion SmallFiberExtension LargeFourteenRegion
open FourTwelveFunctional (source transport_thin)
open private bundle from SmallFiberExtension

private theorem twins {n k t l v} {c : Fin n → Fin n → Nat}
    (F : Shore c l (Fin k)) (Y : Shore c v (Fin t))
    (h : SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint Y j))) :
    FiberPairExtension.twins c l v := by
  constructor
  · intro i x j he y
    simpa only [atPoint,Equiv.apply_symm_apply] using h.1 (F.symm i) (F.symm x) (Y.symm j)
      (by simpa only [atPoint,Equiv.apply_symm_apply] using he) (Y.symm y)
  · intro i j y he x
    simpa only [atPoint,Equiv.apply_symm_apply] using h.2 (F.symm i) (Y.symm j) (Y.symm y)
      (by simpa only [atPoint,Equiv.apply_symm_apply] using he) (F.symm x)

private theorem reverse {n l r} {G : Graph n}
    (h : FiberPairExtension.twins (source G) l r) :
    FiberPairExtension.twins (source G) r l := by
  exact ⟨fun i x j e y => transpose _ (h.2 j i x (transpose _ e) y),
    fun i j y e x => transpose _ (h.1 j y i (transpose _ e) x)⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

theorem restrict_map {s t : Nat → Prop} (map : Realizes p s)
    (inside : ∀ i, t (source G i i) → s (source G i i)) : Realizes p t := by
  obtain ⟨e,he⟩ := map
  let inc (x : Region (source G) t) : Region (source G) s := ⟨x.val,(mem_vertices _ _ _).mpr (inside _ ((mem_vertices _ _ _).mp x.property))⟩
  obtain ⟨f,hf⟩ := bundle p t (fun x => (e (inc x)).val) (fun x y => he (inc x) (inc y))
  exact ⟨f,fun i j => by rw [hf,hf]; exact he (inc i) (inc j)⟩

theorem functional {s : Nat} {reg keep : Nat → Prop} (old : Realizes p keep)
    (inside : ∀ i, reg (source G i i) → keep (source G i i) ∨ source G i i=s)
    (x y : Fin n) (hx : keep (source G x x)) (hy : source G y y=s)
    (one : ∀ z, source G x z=source G x y → z=y) : Realizes p reg := by
  let c := source G
  obtain ⟨e,he⟩ := old
  let X := Region c reg
  have cover (k : X) : ∃ i : Region c keep, ∀ z, c i.val z=c i.val k.val → z=k.val := by
    rcases inside k.val ((mem_vertices _ _ _).mp k.property) with kept|h
    · exact ⟨⟨k.val,(mem_vertices _ _ _).mpr kept⟩,fun z eq => (Relations.diagonal _ eq).symm⟩
    have diag := hy.trans h.symm
    obtain ⟨w,_,hit⟩ := PartialFunctional.middle c c (fun a b => Relations.products (closure G) a b _ _ _ _ diag) x
    have row := (Relations.end_colors (closure G) hit).1
    exact ⟨⟨w,(mem_vertices _ _ _).mpr ((congrArg keep row).mp hx)⟩,
      fun z hz => transport_thin row one z k.val (hz.trans hit.symm) hit.symm⟩
  obtain ⟨f,_,names,_⟩ := PartialFunctional.extend p (fun i : X => i.val) Subtype.val_injective
    (fun i : Region c keep => i.val) (fun i => (e i).val) he cover
  obtain ⟨E,hE⟩ := bundle p reg f names
  exact ⟨E,fun i j => by rw [hE,hE]; exact names i j⟩

theorem centered {k m t l r v : Nat} [NeZero k] [NeZero m] [NeZero t] (F : Shore (source G) l (Fin k))
    (S : Shore (source G) r (Fin m)) (Y : Shore (source G) v (Fin t)) (small : k≤13)
    (old : Realizes p (fun z => z=r ∨ z=v)) {reg : Nat → Prop}
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v)
    (fs : FiberPairExtension.twins (source G) l r) (fy : FiberPairExtension.twins (source G) l v) : Realizes p reg := by
  let c := source G
  let keep := fun z => z=r ∨ z=v
  let b : Region c keep := ⟨atPoint S 0,(mem_vertices _ _ _).mpr (Or.inl (S 0).property)⟩
  let d : Region c keep := ⟨atPoint Y 0,(mem_vertices _ _ _).mpr (Or.inr (Y 0).property)⟩
  have sb : source G b.val b.val=r := (S 0).property
  have yd : source G d.val d.val=v := (Y 0).property
  apply restrict_map p (FiberPairExtension.attach p F 0 small keep old b d (fun j => ?_) (by rw [sb]; exact fs) (by rw [yd]; exact fy))
  · intro i h; rcases cover i h with h|h|h
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · rw [sb,yd]
    exact ((mem_vertices _ _ _).mp j.property).imp_right Or.inl

theorem solve {l r v : Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (F : Shore (source G) l (Fin 4)) (S : Shore (source G) r (Fin 4)) (Y : Shore (source G) v (Fin 8))
    (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r ∨ source G i i=v) : Realizes p reg := by
  classical
  let c := source G
  have coverS (i) (hi : reg (c i i)) : c i i=r ∨ c i i=l ∨ c i i=v := by
    rcases cover i hi with h|h|h <;> tauto
  have coverY (i) (hi : reg (c i i)) : c i i=v ∨ c i i=l ∨ c i i=r := by
    rcases cover i hi with h|h|h <;> tauto
  have fy := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound F Y).trans (by decide))
  have sy := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound S Y).trans (by decide))
  have fs := LargeOrderBlocks.small p _ ((RegionalTwoAnchor.pair_bound F S).trans (by decide))
  have thinF (i : Fin 4) (j : Eight) (one : ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) : Realizes p reg :=
    functional p sy (fun z h => Or.symm (cover z h)) (atPoint Y j) (atPoint F i) (Or.inr (Y j).property) (F i).property one
  have thinS (i : Fin 4) (j : Eight) (one : ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint S i) → z=atPoint S i) : Realizes p reg :=
    functional p fy (fun z h => Or.symm (coverS z h)) (atPoint Y j) (atPoint S i) (Or.inr (Y j).property) (S i).property one
  have cycleCase {l' r'} (A : Shore c l' (Fin 4)) (B : Shore c r' (Fin 4))
      (cov : ∀ i, reg (c i i) → c i i=l' ∨ c i i=r' ∨ c i i=v)
      (mix : ∃ i j, c (atPoint A i) (atPoint B j)≠c (atPoint A 0) (atPoint B 0))
      (u : Nat) (b : Eight → Edge) (cells : ∀ i j, c (atPoint A i) (atPoint Y j)=u ↔ i∈edge (b j))
      (C : RepeatedCycle b) : Realizes p reg := by
    apply LargeOrderBlocks.of_solver p reg active rfl
    intro f g data
    exact RegionalCycleSupport.solve p data A B Y (fun i => cov _ ((data.src _).mp ⟨i,rfl⟩)) mix u b cells C
  rcases FourEightGeometry.interface F Y with ⟨i,j,thin⟩|ft|⟨u,_,_,b,fb,⟨B⟩⟩
  · exact thinF i j thin
  · rcases FourEightGeometry.interface S Y with ⟨i,j,thin⟩|st|⟨w,_,_,d,sd,⟨D⟩⟩
    · exact thinS i j thin
    · exact centered p Y F S (by decide) fs coverY (reverse (twins F Y ft)) (reverse (twins S Y st))
    · by_cases mixed : ∃ i j, c (atPoint S i) (atPoint F j)≠c (atPoint S 0) (atPoint F 0)
      · exact cycleCase S F coverS mixed w d sd D
      · push_neg at mixed
        have un : SplitRectangle.Twins (fun i j => c (atPoint S i) (atPoint F j)) :=
          ⟨fun i x _ _ y => (mixed i y).trans (mixed x y).symm,fun _ j y _ x => (mixed x j).trans (mixed x y).symm⟩
        exact centered p F S Y (by decide) sy cover (reverse (twins S F un)) (twins F Y ft)
  · by_cases mixed : ∃ i j, c (atPoint F i) (atPoint S j)≠c (atPoint F 0) (atPoint S 0)
    · exact cycleCase F S cover mixed u b fb B
    · push_neg at mixed
      rcases FourEightGeometry.interface S Y with ⟨i,j,thin⟩|st|⟨w,_,_,d,sd,⟨D⟩⟩
      · exact thinS i j thin
      · have un : SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint S j)) :=
          ⟨fun i x _ _ y => (mixed i y).trans (mixed x y).symm,fun _ j y _ x => (mixed x j).trans (mixed x y).symm⟩
        exact centered p S F Y (by decide) fy coverS (reverse (twins F S un)) (twins S Y st)
      · exact restrict_map p (RegionalTwoAnchor.solve p lr lv rv F S Y mixed
          (TwoCycleMatchings.two_base (sourceLaws _) F S Y mixed u w b d fb sd B D)) cover

theorem three_cover {a b d : Fin n} {reg : Nat → Prop}
    (ha : reg (source G a a)) (hb : reg (source G b b)) (hd : reg (source G d d))
    (ab : source G a a≠source G b b) (ad : source G a a≠source G d d) (bd : source G b b≠source G d d)
    (size : (vertices (source G) reg).card=(fiber G a).card+(fiber G b).card+(fiber G d).card) :
    ∀ i, reg (source G i i) → source G i i=source G a a ∨ source G i i=source G b b ∨ source G i i=source G d d := by
  classical
  have dj {i j : Fin n} (diff : source G i i ≠ source G j j) : Disjoint (fiber G i) (fiber G j) :=
    Finset.disjoint_left.mpr fun _ h k => diff (((FourTwelveFunctional.fiber_eq _ _).mp h).symm.trans ((FourTwelveFunctional.fiber_eq _ _).mp k))
  have eq : (fiber G a ∪ fiber G b) ∪ fiber G d = vertices (source G) reg := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      simp only [Finset.mem_union,FourTwelveFunctional.fiber_eq] at hi
      exact (mem_vertices _ _ _).mpr (hi.elim (fun h => h.elim (fun h => h ▸ ha) (fun h => h ▸ hb)) (fun h => h ▸ hd))
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dj ad,dj bd⟩),Finset.card_union_of_disjoint (dj ab),size]
  intro i hi
  have inc := (mem_vertices _ _ _).mpr hi
  rw [←eq] at inc
  simp only [Finset.mem_union,FourTwelveFunctional.fiber_eq] at inc
  exact or_assoc.mp inc

private theorem shore (x : Fin n) {k : Nat} (h : (fiber G x).card=k) :
    Nonempty (Shore (source G) (source G x x) (Fin k)) := by
  let e := Fintype.equivOfCardEq (show Fintype.card (Fin k)=Fintype.card {z // z∈fiber G x} by simp [h])
  exact ⟨e.trans (Equiv.subtypeEquivRight (FourTwelveFunctional.fiber_eq x))⟩

theorem realize (reg : Nat → Prop) (active : ∀ i, reg (source G i i) → large G (source G i i))
    (total : (vertices (source G) reg).card=16)
    (eight : ∃ y, reg (source G y y) ∧ (fiber G y).card=8)
    (fours : ∃ a b, reg (source G a a) ∧ reg (source G b b) ∧ (fiber G a).card=4 ∧ (fiber G b).card=4 ∧ source G a a≠source G b b) : Realizes p reg := by
  obtain ⟨y,hy,sy⟩ := eight
  obtain ⟨a,b,ha,hb,sa,sb,ab⟩ := fours
  obtain ⟨F⟩ := shore a sa
  obtain ⟨S⟩ := shore b sb
  obtain ⟨Y⟩ := shore y sy
  have diff (z : Fin n) (sz : (fiber G z).card=4) : source G z z≠source G y y := by
    intro eq
    have same : fiber G z=fiber G y := by ext i; rw [FourTwelveFunctional.fiber_eq,FourTwelveFunctional.fiber_eq,eq]
    rw [same,sy] at sz
    contradiction
  exact solve p ab (diff a sa) (diff b sb) F S Y reg active
    (three_cover ha hb hy ab (diff a sa) (diff b sb) (by rw [sa,sb,sy,total]))

end QGI.Coherent.RegionalFourFourEight
