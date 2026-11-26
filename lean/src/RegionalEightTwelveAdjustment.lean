import RegionalEightTwelveCatalog
import RegionalThreeClasses
import RegionalEightTwelveEdges

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveAdjustment
open SixTenCoordinates SmallUnion StrategyColorLaws
open FourTwelveFunctional (source)
open QGI.EightTwelveCatalog (Label Closed)
open private range from RegionalSixTwelveDispatch

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem adjust_closed {k l r v : Nat} (F : Shore (source G) l (Fin 12)) (Y : Shore (source G) r (Fin k))
    (T : Shore (targetName p) l (Fin 12)) (Z : Shore (targetName p) r (Fin k))
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (a b : Fin 12 → Label) (tag : Fin k → Label) (onto : Function.Surjective a) (ontoB : Function.Surjective b)
    (full : Function.Surjective tag)
    (src : ∀ j i, source G (atPoint Y j) (atPoint F i)=v ↔ a i=tag j)
    (tgt : ∀ j i, targetName p (atPoint Z j) (atPoint T i)=v ↔ b i=tag j)
    (constant : ∀ j i t, a i=a t → source G (atPoint Y j) (atPoint F i)=source G (atPoint Y j) (atPoint F t))
    (closed : Closed (fun i j => targetName p (atPoint T i) (atPoint T j)) b) :
    ∃ e : Equiv.Perm (Fin 12), (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
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
    have pos (u w : Label) : 0 < (Finset.univ.filter (fun j => u=tag j ∧ w=tag j)).card ↔ u=w := by
      rw [Finset.card_pos]
      constructor
      · rintro ⟨j,h⟩
        obtain ⟨z,t⟩ := (Finset.mem_filter.mp h).2; exact z.trans t.symm
      · rintro rfl
        obtain ⟨j,hj⟩ := full u
        exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj.symm,hj.symm⟩⟩
    simpa only [Block.overlap,A,B,decide_eq_true_eq,pos] using Iff.of_eq (congrArg (0<·) g)
  have two (s t : Label) : ∃ f : Equiv.Perm (Fin 12),
      (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (f i)) (atPoint T (f j))) ∧
      ∀ i, a i=s ∨ a i=t → b (f i)=a i := by
    obtain ⟨j,hj⟩ := full s
    obtain ⟨m,hm⟩ := full t
    obtain ⟨i,hi⟩ := onto s
    obtain ⟨u,hu⟩ := onto t
    obtain ⟨q,hq⟩ := law.middle (right j m)
    obtain ⟨x,hx⟩ := (range T _).mpr (((SmallShore.endpoints p (hq (atPoint F i)).1).2).symm.trans (F i).property)
    have first : b x=s := by
      refine ((tgt j x).mp ?_).trans hj
      rw [hx,←(hq (atPoint F i)).1]
      exact (src j i).mpr (hi.trans hj.symm)
    obtain ⟨z,hz⟩ := law.middle (hq (atPoint F i)).2
    obtain ⟨y,hy⟩ := (range T _).mpr (((SmallShore.endpoints p (hz (atPoint F u)).1).2).symm.trans (F u).property)
    have second : b y=t := by
      refine ((tgt m y).mp ?_).trans hm
      rw [hy,←common_transpose p (hz (atPoint F u)).2]
      exact (src m u).mpr (hu.trans hm.symm)
    have hit : source G (atPoint F i) (atPoint F u)=targetName p (atPoint T x) (atPoint T y) := by
      rw [hx,hy]; exact (hz (atPoint F u)).1
    obtain ⟨e,ei,eu,names⟩ := RegionalThreeClasses.small_pair p F T (by decide) i u x y hit
    refine ⟨e,names,fun k hk => ?_⟩
    rcases hk with one|one
    · have h := (pair (names k i)).mp (one.trans hi.symm); rw [ei,first] at h; exact h.trans one.symm
    · have h := (pair (names k u)).mp (one.trans hu.symm); rw [eu,second] at h; exact h.trans one.symm
  obtain ⟨e₀,h₀,_⟩ := two 0 0
  obtain ⟨d,hd⟩ := EightTwelveCatalog.label_equiv a (b ∘ e₀) onto (ontoB.comp e₀.surjective) (fun i j => pair (h₀ i j))
  have inv (i) : d.symm (b (e₀ i))=a i := by rw [←show d (a i)=b (e₀ i) from hd i,d.symm_apply_apply]
  obtain ⟨g,part,gn⟩ := closed d.symm (by
    intro x y
    obtain ⟨i,rfl⟩ := e₀.surjective x
    obtain ⟨j,rfl⟩ := e₀.surjective y
    obtain ⟨f,names,match'⟩ := two (a i) (a j)
    exact ⟨f i,f j,(match' i (Or.inl rfl)).trans (inv i).symm,(match' j (Or.inr rfl)).trans (inv j).symm,
      (h₀ i j).symm.trans (names i j)⟩)
  let e := e₀.trans g
  have agree (i) : a i=b (e i) := ((part (e₀ i)).trans (inv i)).symm
  refine ⟨e,fun i j => (h₀ i j).trans (gn _ _),fun j i => ?_⟩
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

end QGI.Coherent.RegionalEightTwelveAdjustment

