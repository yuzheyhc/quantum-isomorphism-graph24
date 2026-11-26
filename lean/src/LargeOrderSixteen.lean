import LargeOrderBlocks
import SeventeenHard

noncomputable section
namespace QGI.Coherent.LargeOrderSixteen
open SmallUnion StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open private middle from FourTwelveFunctional
open private tetra from SeventeenHard

/-- In local coordinates, singleton colors from jointly realized anchors
determine the image of every vertex and every relation between them. -/
theorem anchored {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {reg : Nat → Prop} {f g : Fin k → Fin n} (D : DataFor p reg f g)
    {I : Type} (a b : I → Fin k)
    (pair : ∀ i j, source G (f (a i)) (f (a j))=targetName p (g (b i)) (g (b j)))
    (thin : ∀ x, ∃ i, ∀ z, source G (f (a i)) (f z) = source G (f (a i)) (f x) → z=x) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  have forward {i j x y : Fin k} (eq : c i j=d x y) (z : Fin k) :=
    middle c d (fun s t => D.products s t i j x y eq) z
  have backward {i j x y : Fin k} (eq : c i j=d x y) (z : Fin k) :=
    middle d c (fun s t => (D.products s t i j x y eq).symm) z
  choose idx unique using thin
  have pick (x : Fin k) : ∃ y, c (a (idx x)) x=d (b (idx x)) y := by
    obtain ⟨z,h,_⟩ := forward (pair (idx x) (idx x)) x
    exact ⟨z,h⟩
  choose t ht using pick
  have onAnchor (x : Fin k) (i : I) : c x (a i)=d (t x) (b i) := by
    obtain ⟨z,h,l⟩ := backward (pair (idx x) i) (t x)
    exact (unique x z (h.symm.trans (ht x).symm)) ▸ l.symm
  have names (x y : Fin k) : c x y = d (t x) (t y) := by
    obtain ⟨z,h,l⟩ := backward (onAnchor x (idx y)) (t y)
    exact (unique y z ((common_transpose p l.symm).trans (ht y).symm)) ▸ h.symm
  have inj : Function.Injective t := by
    intro x y eq
    apply D.srcConfig.diagonal x y x
    exact (names x y).trans ((congrArg (d (t x)) eq.symm).trans (names x x).symm)
  exact ⟨Equiv.ofBijective t (Finite.injective_iff_bijective.mp inj),names⟩

theorem four_cells {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {reg : Nat → Prop} (f g : Fin 16 → Fin n)
    (D : DataFor p reg f g) (small : ∀ i, (fiber G (f i)).card ≤ 4)
    (u : Fin 4 → Fin 16) (cover : ∀ i, ∃ j, source G (f i) (f i)=source G (f (u j)) (f (u j))) :
    ∃ e : Equiv.Perm (Fin 16), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  let c := restricted (source G) f
  have four (i) : (Finset.univ.filter (fun j => c j j=c i i)).card ≤ 4 :=
    (LargeOrderBlocks.fiber_card f D.injF D.src i).trans_le (small i)
  rcases Literature.fkv_sixteen_small_configuration D.srcConfig D.tgtConfig four D.used D.products with
    yes | thin
  · exact yes
  · obtain ⟨v,hv⟩ := tetra p reg f g D.injF D.injG D.src D.tgt u
    apply anchored p D u v hv
    intro i
    obtain ⟨j,hj⟩ := cover i
    exact ⟨j,fun z eq => thin (u j) z i (((Relations.end_colors (closure G) eq).2).trans hj) hj eq⟩

end QGI.Coherent.LargeOrderSixteen
