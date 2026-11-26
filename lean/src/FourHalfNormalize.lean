import FourHalfAlignment
import FourHalfCov
import FourHalfOrientation

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog
open SixTenCoordinates SmallUnion StrategyColorLaws
open FourTwelveFunctional (source)
open private twins from RegionalFourFourEight

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
   (p : PerfectStrategy G H K)

theorem normalize {X : Shore (source G) r Eight} {TX : Shore (targetName p) r Eight} {q : Eight → Four}
    (h : balanced q) (D : Aligned p X TX l q) :
    ∃ q' : Eight → Four, balanced q' ∧ canonical q' ∧ Nonempty (Aligned p X TX l q') := by
  obtain ⟨f,k,can⟩ := change_chart q h
  obtain ⟨eb,pb,hit',_,pos'⟩ := transform_ok f k
  let e := Equiv.ofBijective (pointTransform f k) pb
  let t := Equiv.ofBijective (transform f k) eb
  let q' := transform f k ∘ q
  have bal (u : Four) : (Finset.univ.filter (fun i => q' i=u)).card=2 := by
    have test (i : Eight) : q' i=u ↔ q i=t.symm u := t.apply_eq_iff_eq_symm_apply
    simpa only [test] using h (t.symm u)
  have back (i j) : hit (e.symm i) (q j)=hit i (q' j) := by
    have eq := hit' (e.symm i) (q j)
    change hit (e (e.symm i)) (q' j)=_ at eq
    simpa only [Equiv.apply_symm_apply] using eq.symm
  have loc (i j : Four) : pos (e.symm i) (e.symm j)=pos i j := by
    have eq := pos' (e.symm i) (e.symm j)
    change pos (e (e.symm i)) (e (e.symm j))=_ at eq
    simpa only [Equiv.apply_symm_apply] using eq.symm
  refine ⟨q',bal,can,⟨⟨e.symm.trans D.F,e.symm.trans D.T,D.active,D.rest,D.distinct,?_,?_,?_⟩⟩⟩
  · intro j i; simpa only [back] using D.sourceRow j (e.symm i)
  · intro j i; simpa only [back] using D.targetRow j (e.symm i)
  · intro i j x y eq; exact D.four _ _ _ _ ((loc i j).trans (eq.trans (loc x y).symm))

theorem nonTwin {c : Fin n → Fin n → Nat} (P : Chart c r v) (nt : ¬FiberPairExtension.twins c r v) :
    ¬Twin (FourHalfCatalog.cross P.key P.swap) := by
  intro h
  apply nt (twins P.X P.Y ?_)
  have named (i j x y : Eight) : FourHalfCatalog.cross P.key P.swap i j=FourHalfCatalog.cross P.key P.swap x y ↔
      c (atPoint P.X i) (atPoint P.Y j)=c (atPoint P.X x) (atPoint P.Y y) := by
    simpa only [index_val.1,index_val.2,vertex,Sum.elim_inl,Sum.elim_inr,FourHalfCatalog.cross]
      using P.names (.inl i) (.inr j) (.inl x) (.inr y)
  exact ⟨fun i j x eq y => (named _ _ _ _).mp (h.1 i j x ((named _ _ _ _).mpr eq) y),
    fun x i j eq y => (named _ _ _ _).mp (h.2 x i j ((named _ _ _ _).mpr eq) y)⟩

theorem mark_iff {a z : Nat} (az : a≠z) (s t : Bool) :
    (if s then a else z)=(if t then a else z) ↔ s=t := by cases s <;> cases t <;> simp [az,Ne.symm az]

theorem named_cycle {X : Shore (source G) r Eight} {TX : Shore (targetName p) r Eight} {q : Eight → Four}
    (D : Aligned p X TX l q) : Block X TX D.F D.T (fun j i => hit i (q j)) (fun j i => hit i (q j)) := by
  intro i j a b eq
  rw [D.sourceRow,D.targetRow] at eq
  exact (mark_iff D.distinct _ _).mp eq

end QGI.Coherent.FourHalfModel
