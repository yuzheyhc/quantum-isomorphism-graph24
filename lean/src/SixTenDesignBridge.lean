import SixTenDesignGraph
import SixTenCoordinates

noncomputable section

namespace QGI.Coherent.SixTenDesignBridge

open SixTenCoordinates StrategyColorLaws
open QGI.SixTen.Cross (design colGram rowGram)

private theorem same_name {a b v w : Nat} (ha : a=v ∨ a=w) (hb : b=v ∨ b=w)
    (same : decide (a=v) = decide (b=v)) : a=b := by
  by_cases h : a=v
  · subst a; exact Eq.symm (of_decide_eq_true (by simpa using same.symm))
  · have ne : b ≠ v := by intro e; simp [e,h] at same
    exact (ha.resolve_left h).trans (hb.resolve_left ne).symm

private theorem incidence {c d l r v} (f : Frame c l r) (g : Frame d l r)
    (src : ∀ i j, basic f v i j = design i j) (tgt : ∀ i j, basic g v i j = design i j) :
    Block f.leftShore g.leftShore f.rightShore g.rightShore design design := by
  intro i j x y h
  exact (src i j).symm.trans ((basic_block f g v h).trans (tgt x y))

private theorem countBlock {c d : Coloring} {u v w : Nat} {X Y Z : Type} [Fintype Y]
    {L : Shore c u X} {L' : Shore d u X} {M : Shore c v Y} {M' : Shore d v Y}
    {R : Shore c w Z} {R' : Shore d w Z} {T U : X → Y → Bool} {P Q : Y → Z → Bool}
    (law : Laws c d) (h : Block L L' M M' T U) (k : Block M M' R R' P Q) :
    Block L L' R R' (fun i j => (Finset.univ.filter fun x => T i x = true ∧ P x j = true).card)
      (fun i j => (Finset.univ.filter fun x => U i x = true ∧ Q x j = true).card) := by
  intro i j x y eq
  simpa using
    Block.fold law h k (fun a b => if a = true ∧ b = true then 1 else 0) eq

private theorem sample {c d : Coloring} {u v : Nat} {X Y : Type} (law : Laws c d)
    (L : Shore c u X) (L' : Shore d u X) (R : Shore c v Y) (R' : Shore d v Y) (i : X) (j : Y) :
    ∃ y : Y, c (atPoint L i) (atPoint R j) = d (atPoint L' i) (atPoint R' y) := by
  obtain ⟨e,he⟩ := law.middle ((L i).property.trans (L' i).property.symm)
  have hit := (he (atPoint R j)).1
  let t : {z : V // d z z = v} := ⟨_,(law.last hit).symm.trans (R j).property⟩
  refine ⟨R'.symm t,?_⟩
  simpa only [atPoint,Equiv.apply_symm_apply,t] using hit

private theorem rowDiagonal : ∀ i j : A, rowGram design i j = rowGram design i i ↔ j=i := by
  native_decide

private theorem canonical {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l r : Nat} (f : Frame (Relations.color (closure G)) l r)
    (g : Frame (targetName p) l r) (v w : Nat)
    (twoG : ∀ i j, cross f i j = v ∨ cross f i j = w)
    (twoH : ∀ i j, cross g i j = v ∨ cross g i j = w)
    (src : ∀ i j, basic f v i j = design i j) (tgt : ∀ i j, basic g v i j = design i j) :
    Isomorphic G H := by
  let L := g.leftShore
  let R := g.rightShore
  let AL := fun i j : A => H.edge (atPoint L i) (atPoint L j)
  let AR := fun i j : B => H.edge (atPoint R i) (atPoint R j)
  have law := targetLaws p
  have crossLaw := commonLaws p
  have dsg := incidence g g tgt tgt
  have common := incidence f g src tgt
  have inner {i j x y : V} (eq : targetName p i j = targetName p x y) : H.edge i j = H.edge x y := by
    obtain ⟨a,b,h⟩ := StrategyColors.exists_source p i j
    have z := (associated p).mpr (StrategyColors.maps_support p h)
    exact (common_edge p z).symm.trans (common_edge p (z.trans eq))
  have leftEdge : Block L L L L AL AL := fun ⦃_ _ _ _⦄ h => inner h
  have rightEdge : Block R R R R AR AR := fun ⦃_ _ _ _⦄ h => inner h
  have names {i j x y} (eq : design i j = design x y) : cross g i j = cross g x y :=
    same_name (twoH i j) (twoH x y) ((tgt i j).trans (eq.trans (tgt x y).symm))
  have leftRows := QGI.SixTen.Cross.left_graph AL (fun i j => H.symm _ _) (fun i => H.loopless _)
    (fun i j k eq => countBlock law leftEdge dsg (names eq))
  have gram : Block R R R R (colGram design) (colGram design) :=
    Block.gram law (Block.flip law dsg)
  let sel := fun k (j w : B) => AR j w && decide (colGram design j w = k)
  have selLaw (k : Nat) : Block R R R R (sel k) (sel k) :=
    Block.map₂ rightEdge gram (fun b n => b && decide (n=k))
  have regular (k : Nat) (j x : B) : QGI.SixTen.Cross.selectedDegree AR k j = QGI.SixTen.Cross.selectedDegree AR k x := by
    simpa only [sel,Bool.and_eq_true,decide_eq_true_eq,QGI.SixTen.Cross.selectedDegree] using
      Block.degree_eq law (selLaw k) j x
  have mixed (k : Nat) (i x : A) (j : B) (eq : design i j = design x j) :
      QGI.SixTen.Cross.mixedDegree AR k i j = QGI.SixTen.Cross.mixedDegree AR k x j := by
    simpa only [sel,Bool.and_eq_true,decide_eq_true_eq,QGI.SixTen.Cross.mixedDegree] using
      countBlock law dsg (Block.flip law (selLaw k)) (names eq)
  have rightRows := QGI.SixTen.Cross.right_graph AR (fun i j => H.symm _ _) (fun i => H.loopless _) regular mixed
  have gramL : Block f.leftShore L f.leftShore L (rowGram design) (rowGram design) :=
    Block.gram crossLaw common
  have gramR : Block f.rightShore R f.rightShore R (colGram design) (colGram design) :=
    Block.gram crossLaw (Block.flip crossLaw common)
  have ll (i j : A) : G.edge (f.e (.inl i)) (f.e (.inl j)) = H.edge (g.e (.inl i)) (g.e (.inl j)) := by
    obtain ⟨y,hy⟩ := sample crossLaw f.leftShore L f.leftShore L i j
    have z := gramL hy
    refine (common_edge p hy).trans ?_
    change AL i y = AL i j
    by_cases h : j=i
    · subst j; rw [(rowDiagonal i y).mp z.symm]
    · have hyi : y ≠ i := by intro e; rw [e] at z; exact h ((rowDiagonal i j).mp z)
      exact leftRows i y i j (Ne.symm hyi) (Ne.symm h)
  have rr (i j : B) : G.edge (f.e (.inr i)) (f.e (.inr j)) = H.edge (g.e (.inr i)) (g.e (.inr j)) := by
    obtain ⟨y,hy⟩ := sample crossLaw f.rightShore R f.rightShore R i j
    exact (common_edge p hy).trans (rightRows i y i j (gramR hy).symm)
  have lr (i : A) (j : B) : G.edge (f.e (.inl i)) (f.e (.inr j)) = H.edge (g.e (.inl i)) (g.e (.inr j)) :=
    common_edge p (same_name (twoG i j) (twoH i j) ((src i j).trans (tgt i j).symm))
  let e := f.e.symm.trans g.e
  refine ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,?_⟩⟩
  intro x y
  obtain ⟨s,rfl⟩ := f.e.surjective x
  obtain ⟨t,rfl⟩ := f.e.surjective y
  simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]
  cases s with
  | inl s => cases t with | inl t => exact ll s t | inr t => exact lr s t
  | inr s =>
    cases t with
    | inl t => exact (G.symm _ _).trans ((lr t s).trans (H.symm _ _))
    | inr t => exact rr s t

private def renumber {c l r} (f : Frame c l r) (a : Equiv.Perm A) (b : Equiv.Perm B) : Frame c l r :=
  ⟨(Equiv.sumCongr a.symm b.symm).trans f.e, fun i => f.left (a.symm i), fun i => f.right (b.symm i),f.distinct⟩

theorem isomorphic {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l r : Nat} (f : Frame (Relations.color (closure G)) l r)
    (g : Frame (targetName p) l r) (v w : Nat)
    (twoG : ∀ i j, cross f i j = v ∨ cross f i j = w)
    (twoH : ∀ i j, cross g i j = v ∨ cross g i j = w)
    (a a' : Equiv.Perm A) (b b' : Equiv.Perm B)
    (src : ∀ i j, basic f v i j = design (a i) (b j))
    (tgt : ∀ i j, basic g v i j = design (a' i) (b' j)) : Isomorphic G H := by
  apply canonical p (renumber f a b) (renumber g a' b') v w
  · exact fun i j => twoG (a.symm i) (b.symm j)
  · exact fun i j => twoH (a'.symm i) (b'.symm j)
  · intro i j; change basic f v (a.symm i) (b.symm j) = _
    simpa only [Equiv.apply_symm_apply] using src (a.symm i) (b.symm j)
  · intro i j; change basic g v (a'.symm i) (b'.symm j) = _
    simpa only [Equiv.apply_symm_apply] using tgt (a'.symm i) (b'.symm j)

end QGI.Coherent.SixTenDesignBridge
