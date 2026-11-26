import EightFourteenWords
import data.EightFourteenPlacements
import ZivAvCoreCheck

namespace QGI.EightFourteenPlacement
open EightFourteenWords
abbrev Key := Fin 3
abbrev Rep := Fin 10
def model (k : Key) : ZivAv.Index := if k=0 then 1 else if k=1 then 7 else 13
def rightName (k : Key) (i j : J) := ZivAv.color (model k) i j
def key (r : Rep) : Key := Fin.ofNat' 3 ((EightFourteenInput.reps[r.val]?).getD (0,0)).1
def shape (r : Rep) : Shape := Fin.ofNat' 30 ((EightFourteenInput.reps[r.val]?).getD (0,0)).2
def inside (r : Rep) (i : I) (j : J) := incident (word (shape r) i) j
def point (a : Axis) (b : Bool) : J := ⟨2*a.val+b.toNat,by cases b <;> simp <;> omega⟩
def axisTag (k : Key) (s : Shape) := (EightFourteenInput.placements[30*k.val+s.val]?).getD (0,0,0)
def rep (k : Key) (s : Shape) : Rep := Fin.ofNat' 10 (axisTag k s).1
def row (k : Key) (s : Shape) (i : I) : I := Fin.ofNat' 8 ((axisTag k s).2.1 >>> (3*i.val))
def coord (k : Key) (s : Shape) (j : Axis) : Axis := Fin.ofNat' 7 (((axisTag k s).2.2 >>> (3*j.val))%8)
def col (k : Key) (s : Shape) (j : J) := point (coord k s (axis j)) (side j)
def swap (t : Word) (j : J) := point (axis j) (side j ^^ bit t (axis j))

attribute [local irreducible] ZivAv.cores14 EightFourteenInput.reps EightFourteenInput.placements EightFourteenInput.families
theorem swapped : ∀ t j, swap t (swap t j)=j := by native_decide
theorem swap_names : ∀ k t i j, rightName k (swap t i) (swap t j)=rightName k i j := by native_decide
theorem swap_incidence : ∀ t u j, incident u (swap t j)=incident (shift u t) j := by native_decide
theorem placed : ∀ k s, key (rep k s)=k ∧ Function.Injective (row k s) ∧ Function.Injective (col k s) ∧
    (∀ i j, inside (rep k s) i j=incident (word s (row k s i)) (col k s j)) ∧
    ∀ i j, rightName k (col k s i) (col k s j)=rightName k i j := by
  unfold Function.Injective; native_decide
def swapPerm (t : Word) : Equiv.Perm J := ⟨swap t,swap t,swapped t,swapped t⟩
noncomputable def rowPerm (k : Key) (s : Shape) : Equiv.Perm I := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (placed k s).2.1)
noncomputable def colPerm (k : Key) (s : Shape) : Equiv.Perm J := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (placed k s).2.2.1)

/-- Simultaneous numbering of the eight points and fourteen columns, including all independent pair flips. -/
theorem present (k : Key) (B : I → J → Bool) (rows : ∀ i, ∃ w : Word, ∀ j, B i j=incident w j)
    (gram : ∀ i j, i≠j → (Finset.univ.filter (fun y => B i y=true ∧ B j y=true)).card=3) :
    ∃ r : Rep, key r=k ∧ ∃ e : Equiv.Perm I, ∃ g : Equiv.Perm J,
      (∀ i j, B (e i) (g j)=inside r i j) ∧ ∀ i j, rightName k (g i) (g j)=rightName k i j := by
  choose w hw using rows
  let u (i : I) := shift (w i) (w 0)
  obtain ⟨s,f,hf⟩ := classify u (shift_self _) (by
    intro i j ne
    rw [show dist (u i) (u j)=dist (w i) (w j) from shift_dist _ _ _]
    have eq := distance_from_common (w i) (w j)
    have h := gram i j ne
    simp_rw [hw] at h
    omega)
  let r := rep k s
  have pp := placed k s
  refine ⟨r,pp.1,(rowPerm k s).trans f,(colPerm k s).trans (swapPerm (w 0)),?_,?_⟩
  · intro i j
    change B (f (row k s i)) (swap (w 0) (col k s j))=inside r i j
    rw [hw,swap_incidence,pp.2.2.2.1]
    exact congrArg (fun t => incident t (col k s j)) (hf (row k s i))
  · intro i j
    exact (swap_names k _ _ _).trans (pp.2.2.2.2 i j)
end QGI.EightFourteenPlacement
