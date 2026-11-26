import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.LargeOrderHomogeneous
open SmallUnion StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)

private def Agrees {k} (c d : Table k) (M N : Mat k) : Prop :=
  ∀ i j x y, c i j=d x y → M i j=N x y

private theorem mul_agrees {k} {c d : Table k}
    (numbers : ∀ a b i j x y, c i j=d x y → count c a b i j=count d a b x y)
    {A B C D : Mat k} (ac : Agrees c d A C) (bd : Agrees c d B D) : Agrees c d (A*B) (C*D) := by
  classical
  intro i j x y hit
  let left := fun z => (c i z,c z j)
  let right := fun z => (d x z,d z y)
  have card (s : Nat × Nat) :
      Fintype.card {z // left z=s} = Fintype.card {z // right z=s} := by
    rcases s with ⟨a,b⟩
    simpa only [Fintype.card_subtype,left,right,Prod.mk.injEq,count,Finset.sum_boole] using numbers a b i j x y hit
  let mid := fun s => Fintype.equivOfCardEq (card s)
  let e := Equiv.ofFiberEquiv mid
  simp only [Matrix.mul_apply]
  apply Fintype.sum_equiv e
  intro z
  have h : (c i z,c z j)=(d x (e z),d (e z) y) := (Equiv.ofFiberEquiv_map mid z).symm
  exact congrArg₂ (· * ·) (ac _ _ _ _ (congrArg Prod.fst h)) (bd _ _ _ _ (congrArg Prod.snd h))

private theorem diag_eq {k} {c d : Table k} (hc : Configuration c) (hd : Configuration d)
    (diag : ∀ i, c i i=d i i) {i j x y} (eq : c i j=d x y) : i=j ↔ x=y := by
  constructor
  · rintro rfl; exact hd.diagonal _ _ _ (eq.symm.trans (diag _))
  · rintro rfl; exact hc.diagonal _ _ _ (eq.trans (diag _).symm)

private def algebra {k} (c : Table k) (hc : Configuration c) : CoherentAlgebra k where
  space := {
    carrier := {M | Agrees c c M M}
    zero_mem' := fun _ _ _ _ _ => rfl
    add_mem' := fun ha hb i j x y eq => congrArg₂ (· + ·) (ha _ _ _ _ eq) (hb _ _ _ _ eq)
    smul_mem' := fun u _ ha i j x y eq => congrArg (u • ·) (ha _ _ _ _ eq) }
  one_mem := fun i j x y eq => by simp only [Matrix.one_apply,diag_eq hc hc (fun _ => rfl) eq]
  ones_mem := fun _ _ _ _ _ => rfl
  mul_mem := mul_agrees hc.products
  schur_mem := fun ha hb i j x y eq => congrArg₂ (· * ·) (ha _ _ _ _ eq) (hb _ _ _ _ eq)
  adjoint_mem := fun ha i j x y eq => congrArg star (ha _ _ _ _ (hc.reverse _ _ _ _ eq))

private theorem homogeneous {k} {c : Table k} (hc : Configuration c) (pos : 0 < k)
    (uniform : ∀ i j, c i i=c j j) : (algebra c hc).Homogeneous := by
  intro M hm
  let o : Fin k := ⟨0,pos⟩
  refine ⟨M o o,?_⟩
  ext i j
  by_cases h : i=j
  · subst j
    simpa [schur,Matrix.one_apply] using hm i i o o (uniform _ _)
  · simp [schur,Matrix.one_apply,h]

private def transport {k} {c d : Table k} (fromC : ∀ x y, ∃ i j, c i j=d x y) (M : Mat k) : Mat k :=
  fun x y => M (fromC x y).choose (fromC x y).choose_spec.choose

private theorem paired {k} {c d : Table k} (fromC : ∀ x y, ∃ i j, c i j=d x y) {M : Mat k}
    (hc : Agrees c c M M) : Agrees c d M (transport fromC M) :=
  fun _ _ x y eq => hc _ _ _ _ (eq.trans (fromC x y).choose_spec.choose_spec.symm)

private theorem unique_map {k} {c d : Table k} (fromC : ∀ x y, ∃ i j, c i j=d x y) {M N : Mat k}
    (h : Agrees c d M N) : transport fromC M=N := by
  ext x y
  exact h _ _ _ _ (fromC x y).choose_spec.choose_spec

private def equivalence {k} {c d : Table k} (hc : Configuration c) (hd : Configuration d)
    (used : ∀ a, (∃ i j, c i j=a) ↔ ∃ x y, d x y=a)
    (numbers : ∀ a b i j x y, c i j=d x y → count c a b i j=count d a b x y)
    (diag : ∀ i, c i i=d i i)
    (rev : ∀ i j x y, c i j=d x y → c j i=d y x) : AlgebraIso (algebra c hc) (algebra d hd) := by
  let fromC := fun x y => (used _).mpr ⟨x,y,rfl⟩
  let fromD := fun i j => (used _).mp ⟨i,j,rfl⟩
  have inverse {N : Mat k} (h : Agrees d d N N) : Agrees c d (transport fromD N) N :=
    fun i j x y eq => (paired fromD h x y i j eq.symm).symm
  refine {
    map := transport fromC
    mapsTo := fun M h i j x y eq =>
      h _ _ _ _ ((fromC i j).choose_spec.choose_spec.trans (eq.trans (fromC x y).choose_spec.choose_spec.symm))
    injectiveOn := ?_
    surjectiveOn := ?_
    map_one := unique_map fromC (fun i j x y eq => by simp only [Matrix.one_apply,diag_eq hc hd diag eq])
    map_ones := rfl
    map_add := fun _ _ _ _ => rfl
    map_smul := fun _ _ _ => rfl
    map_mul := fun _ ha _ hb => unique_map fromC (mul_agrees numbers (paired fromC ha) (paired fromC hb))
    map_schur := fun _ _ _ _ => rfl
    map_adjoint := fun _ ha => unique_map fromC (fun i j x y eq => congrArg star (paired fromC ha _ _ _ _ (rev _ _ _ _ eq))) }
  · intro M hm N hn eq
    ext i j
    obtain ⟨x,y,h⟩ := fromD i j
    exact (paired fromC hm i j x y h.symm).trans ((congrFun (congrFun eq x) y).trans (paired fromC hn i j x y h.symm).symm)
  · intro N hn
    refine ⟨transport fromD N,?_,unique_map fromC (inverse hn)⟩
    intro i j x y eq
    exact hn _ _ _ _ ((fromD i j).choose_spec.choose_spec.trans (eq.trans (fromD x y).choose_spec.choose_spec.symm))

/-- On a homogeneous region of a separable order, transport the full local
matrix algebra in the original common names, including all directed relations. -/
theorem solve {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (ord : k=17 ∨ k=20 ∨ k=21 ∨ k=22) {reg : Nat → Prop}
    (f g : Fin k → Fin n) (D : DataFor p reg f g)
    (single : ∀ i j, source G (f i) (f i)=source G (f j) (f j)) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  let a := equivalence (c:=c) (d:=d) D.srcConfig D.tgtConfig D.used D.products D.sameDiag
    (fun _ _ _ _ h => common_transpose p h)
  have other (i j) : d i i=d j j := (D.sameDiag i).symm.trans ((single i j).trans (D.sameDiag j))
  obtain ⟨e,h⟩ := Literature.zivAv_schemeIso_realized ord (homogeneous D.srcConfig (by omega) single)
    (homogeneous D.tgtConfig (by omega) other) a
  refine ⟨e,fun i j => ?_⟩
  let v := c i j
  have mem : mark c v ∈ (algebra c D.srcConfig).space := fun x y u w eq => by simp only [mark,eq]
  have both : Agrees c d (mark c v) (mark d v) := fun x y u w eq => by simp only [mark,eq]
  have im : a.map (mark c v)=mark d v := unique_map (fun x y => (D.used _).mpr ⟨x,y,rfl⟩) both
  have one := h _ mem i j
  rw [im] at one
  change v = d (e i) (e j)
  by_cases eq : d (e i) (e j)=v
  · exact eq.symm
  · have no : (1:ℂ)=0 := by simpa only [mark,eq,if_false,show c i j=v from rfl,if_true] using one
    exact (one_ne_zero no).elim

end QGI.Coherent.LargeOrderHomogeneous
