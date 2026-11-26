import RegionalTwoAnchor
import SixTenCoordinates

noncomputable section
namespace QGI.Coherent.RegionalThreeClasses
open SmallUnion SmallFiberExtension SixTenCoordinates StrategyColorLaws
open FourTwelveFunctional (source)

private def coords {n k d} {c : Fin n → Fin n → Nat} (F : Shore c d (Fin k)) :
    Fin k ≃ Region c (·=d) := F.trans (Equiv.subtypeEquivRight (fun i => (mem_vertices c (·=d) i).symm))

private theorem range {n k d} {c : Fin n → Fin n → Nat} (F : Shore c d (Fin k)) (x : Fin n) :
    (∃ i, atPoint F i=x) ↔ c x x=d :=
  ⟨fun ⟨i,hi⟩ => hi ▸ (F i).property,fun h => ⟨F.symm ⟨x,h⟩,congrArg Subtype.val (F.apply_symm_apply ⟨x,h⟩)⟩⟩

variable {n k m : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

theorem small_pair {l : Nat} (F : Shore (source G) l (Fin k)) (T : Shore (targetName p) l (Fin k))
    (small : k≤13) (i j x y : Fin k) (hit : source G (atPoint F i) (atPoint F j)=targetName p (atPoint T x) (atPoint T y)) :
    ∃ e : Equiv.Perm (Fin k), e i=x ∧ e j=y ∧
      ∀ a b, source G (atPoint F a) (atPoint F b)=targetName p (atPoint T (e a)) (atPoint T (e b)) := by
  let S := coords F
  let D := coords T
  have card := RegionalTwoAnchor.card F
  obtain ⟨e,ei,ej,he⟩ := realize_region_pair p (·=l) ((Nat.zero_lt_of_lt i.isLt).trans_eq card.symm)
    (card.le.trans small) (S i) (S j) (D x) (D y) hit
  let t := S.trans (e.trans D.symm)
  have map (s) : D (t s)=e (S s) := D.apply_symm_apply _
  refine ⟨t,D.injective ((map _).trans ei),D.injective ((map _).trans ej),fun a b => ?_⟩
  have names := he (S a) (S b)
  rw [←map,←map] at names
  exact names

/-- The classes on the small shore are visible as named neighborhoods of
the prescribed exterior vertices. Two ordered anchors determine the entire
permutation of three classes. -/
theorem align {l r v : Nat} (F : Shore (source G) l (Fin k)) (Y : Shore (source G) r (Fin m))
    (T : Shore (targetName p) l (Fin k)) (Z : Shore (targetName p) r (Fin m)) (small : k≤13)
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (a b : Fin k → Fin 3) (tag : Fin m → Fin 3) (onto : Function.Surjective a) (full : Function.Surjective tag)
    (src : ∀ j i, source G (atPoint Y j) (atPoint F i)=v ↔ a i=tag j)
    (tgt : ∀ j i, targetName p (atPoint Z j) (atPoint T i)=v ↔ b i=tag j)
    (constant : ∀ j i t, a i=a t → source G (atPoint Y j) (atPoint F i)=source G (atPoint Y j) (atPoint F t)) :
    ∃ e : Equiv.Perm (Fin k), (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) := by
  classical
  let law := commonLaws p
  let A := fun j i => decide (a i=tag j)
  let B := fun j i => decide (b i=tag j)
  have inc : Block Y Z F T A B := by
    intro j i w x eq
    simp only [A,B,←src,←tgt,eq]
  have pair {i j x y} (hit : source G (atPoint F i) (atPoint F j)=targetName p (atPoint T x) (atPoint T y)) :
      a i=a j ↔ b x=b y := by
    have g := Block.gram law (Block.flip law inc) hit
    have pos (u w : Fin 3) : 0 < (Finset.univ.filter (fun j => u=tag j ∧ w=tag j)).card ↔ u=w := by
      rw [Finset.card_pos]
      constructor
      · rintro ⟨j,h⟩
        obtain ⟨z,t⟩ := (Finset.mem_filter.mp h).2; exact z.trans t.symm
      · rintro rfl
        obtain ⟨j,hj⟩ := full u
        exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj.symm,hj.symm⟩⟩
    simpa only [Block.overlap,A,B,decide_eq_true_eq,pos] using Iff.of_eq (congrArg (0<·) g)
  obtain ⟨j,hj⟩ := full 0
  obtain ⟨t,ht⟩ := full 1
  obtain ⟨i,hi⟩ := onto 0
  obtain ⟨u,hu⟩ := onto 1
  obtain ⟨q,hq⟩ := law.middle (right j t)
  obtain ⟨x,hx⟩ := (range T _).mpr (((SmallShore.endpoints p (hq (atPoint F i)).1).2).symm.trans (F i).property)
  have xzero : b x=0 := by
    refine ((tgt j x).mp ?_).trans hj
    rw [hx,←(hq (atPoint F i)).1]
    exact (src j i).mpr (hi.trans hj.symm)
  obtain ⟨z,hz⟩ := law.middle (hq (atPoint F i)).2
  obtain ⟨y,hy⟩ := (range T _).mpr (((SmallShore.endpoints p (hz (atPoint F u)).1).2).symm.trans (F u).property)
  have yone : b y=1 := by
    refine ((tgt t y).mp ?_).trans ht
    rw [hy,←common_transpose p (hz (atPoint F u)).2]
    exact (src t u).mpr (hu.trans ht.symm)
  have hit : source G (atPoint F i) (atPoint F u)=targetName p (atPoint T x) (atPoint T y) := by
    rw [hx,hy]; exact (hz (atPoint F u)).1
  obtain ⟨e,ei,eu,ll⟩ := small_pair p F T small i u x y hit
  have agree (o : Fin k) : a o=b (e o) := by
    have z := pair (ll o i)
    have one := pair (ll o u)
    rw [hi,ei,xzero] at z
    rw [hu,eu,yone] at one
    exact (show ∀ s t : Fin 3, (s=0 ↔ t=0) → (s=1 ↔ t=1) → s=t by decide) _ _ z one
  refine ⟨e,ll,fun j i => ?_⟩
  obtain ⟨t,cls⟩ := full (a i)
  obtain ⟨q,hq⟩ := law.middle (right t j)
  let z := q.symm (atPoint T (e i))
  have qz : q z=atPoint T (e i) := q.apply_symm_apply _
  have left := (hq z).1
  have other := common_transpose p (hq z).2
  rw [qz] at left other
  obtain ⟨s,hs⟩ := (range F z).mpr (((SmallShore.endpoints p left).2).trans (T (e i)).property)
  rw [←hs] at left other
  have row : source G (atPoint Y t) (atPoint F s)=v := left.trans ((tgt t (e i)).mpr ((agree i).symm.trans cls.symm))
  exact (constant j i s (cls.symm.trans ((src t s).mp row).symm)).trans other

end QGI.Coherent.RegionalThreeClasses

