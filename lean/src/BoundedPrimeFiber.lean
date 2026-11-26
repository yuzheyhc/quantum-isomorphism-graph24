import LargeOrderHomogeneous
import CoherentCoprime

noncomputable section
namespace QGI.Coherent.BoundedPrimeFiber
open SmallUnion StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private algebra equivalence homogeneous unique_map Agrees from LargeOrderHomogeneous

/-- A graph automorphism fixes every entry color under simultaneous transport. -/
theorem fixed_color {n : Nat} (G : Graph n) (e : Equiv.Perm (Fin n))
    (aut : ∀ i j, Intertwiner.adjacency G i j = Intertwiner.adjacency G (e i) (e j)) (i j : Fin n) :
    source G i j = source G (e i) (e j) := by
  let C : CoherentAlgebra n := {
    space := {
      carrier := {M | ∀ i j, M i j = M (e i) (e j)}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun hx hy i j => congrArg₂ (· + ·) (hx i j) (hy i j)
      smul_mem' := fun r _ hx i j => congrArg (r • ·) (hx i j) }
    one_mem := fun i j => by simp [Matrix.one_apply]
    ones_mem := fun _ _ => rfl
    schur_mem := fun hx hy i j => congrArg₂ (· * ·) (hx i j) (hy i j)
    adjoint_mem := fun hx i j => congrArg star (hx j i)
    mul_mem := fun hx hy i j => by
      simp only [Matrix.mul_apply]
      exact Fintype.sum_equiv e _ _ (fun z => congrArg₂ (· * ·) (hx i z) (hy z j)) }
  exact (Relations.same _ _ _ _ _).mpr (fun M hm => hm C aut i j)

/-- Vertices with the same neighbors off the selected pair can be exchanged
without changing any coherent color of the ambient undirected graph. -/
theorem reverse_of_twins {n} (G : Graph n) (x y : Fin n)
    (twins : ∀ z, z ≠ x → z ≠ y → Intertwiner.adjacency G x z = Intertwiner.adjacency G y z) :
    source G x y = source G y x := by
  classical
  let A := Intertwiner.adjacency G
  have sym (i j) : A i j=A j i := by simp only [A,Intertwiner.adjacency,G.symm i j]
  have diag (i) : A i i=0 := by simp [A,Intertwiner.adjacency,G.loopless]
  have left (j) : A x j = A y (Equiv.swap x y j) := by
    by_cases jx : j=x
    · subst j; simp only [Equiv.swap_apply_left,diag]
    by_cases jy : j=y
    · subst j; simpa only [Equiv.swap_apply_right] using sym x y
    rw [Equiv.swap_apply_of_ne_of_ne jx jy]
    exact twins j jx jy
  have right (j) : A y j = A x (Equiv.swap x y j) := by
    simpa using (left (Equiv.swap x y j)).symm
  have h := fixed_color G (Equiv.swap x y) (fun i j => by
    change A i j = A (Equiv.swap x y i) (Equiv.swap x y j)
    by_cases ix : i=x
    · subst i; simpa only [Equiv.swap_apply_left] using left j
    by_cases iy : i=y
    · subst i; simpa only [Equiv.swap_apply_right] using right j
    rw [Equiv.swap_apply_of_ne_of_ne ix iy]
    exact (Equiv.apply_swap_eq_self (v := A i) ((sym i x).trans ((twins i ix iy).trans (sym y i))) j).symm) x y
  simpa using h

variable {n k : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K) {reg : Nat → Prop}
  (f g : Fin k → Fin n) (D : DataFor p reg f g)
  (single : ∀ i j, source G (f i) (f i)=source G (f j) (f j))

include D single in
private theorem fiber_range (i : Fin k) :
    fiber G (f i) = Finset.univ.image f := by
  ext z
  simp only [Finset.mem_image,Finset.mem_univ,true_and,fiber_eq]
  constructor
  · intro eq
    exact (D.src z).mpr (eq.symm ▸ (D.src (f i)).mp ⟨i,rfl⟩)
  · rintro ⟨j,rfl⟩
    exact single j i

include D single in
/-- A prime fiber bigger than its complement sends just one color to each
outside vertex, independently of the chosen point on the fiber. -/
theorem external (prime : k.Prime) (small : n < k+k) (i j : Fin k) (z : Fin n)
    (outside : ¬ ∃ a, f a=z) : source G (f i) z=source G (f j) z := by
  classical
  have eq := fiber_range p f g D single j
  have sz : (fiber G (f j)).card=k := by rw [eq,Finset.card_image_of_injective _ D.injF]; simp
  have dis : fiber G z ⊆ (fiber G (f j))ᶜ := by
    intro u hu; apply Finset.mem_compl.mpr
    intro both
    have same := ((fiber_eq _ _).mp hu).symm.trans ((fiber_eq _ _).mp both)
    apply outside
    have mem := (fiber_eq _ _).mpr same
    rw [eq] at mem
    simpa using mem
  have bound := Finset.card_le_card dis
  rw [Finset.card_compl,Fintype.card_fin,sz] at bound
  have pos := Finset.card_pos.mpr (show (fiber G z).Nonempty from ⟨z,(fiber_eq _ _).mpr rfl⟩)
  have cop := prime.coprime_iff_not_dvd.mpr (show ¬ k ∣ (fiber G z).card by
    intro h; have := Nat.le_of_dvd pos h; omega)
  exact CoprimeFibers.monochromatic G (f j) z (sz ▸ cop)
    ((fiber_eq _ _).mpr (single i j)) ((fiber_eq _ _).mpr rfl)

private theorem off_diagonal {m} {C : CoherentAlgebra m} (ht : C.HasTournamentBasis)
    {M : Mat m} (hm : M ∈ C.space) (sym : ∀ i j, M i j=M j i) :
    ∃ b, ∀ i j, i ≠ j → M i j=b := by
  obtain ⟨arc,flip,uniform⟩ := ht
  obtain ⟨_,b,c,entries⟩ := uniform M hm
  refine ⟨b,fun i j ne => ?_⟩
  cases orient : arc i j with
  | true => simp [entries,ne,orient]
  | false =>
    have rev : arc j i=true := by
      have h := flip i j ne
      cases e : arc j i <;> simp_all
    rw [sym i j,entries]
    simp [ne.symm,rev]

include D single in
/-- In a prime fiber larger than its exterior, an undirected adjacency which
is constant on each orientation of a tournament makes all its vertices twins. -/
theorem symmetric_of_tournament (prime : k.Prime) (small : n < k+k)
    (ht : (algebra (restricted (source G) f) D.srcConfig).HasTournamentBasis) (i j : Fin k) :
    source G (f i) (f j)=source G (f j) (f i) := by
  let A := Intertwiner.adjacency G
  let M : Mat k := fun x y => A (f x) (f y)
  have inC : M ∈ (algebra (restricted (source G) f) D.srcConfig).space :=
    fun x y a b h => (Relations.same _ _ _ _ _).mp h _ (adjacency_mem G)
  have sym (x y) : M x y=M y x := by simp only [M,A,Intertwiner.adjacency,G.symm (f x) (f y)]
  obtain ⟨b,hb⟩ := off_diagonal ht inC sym
  apply reverse_of_twins
  intro z hi hj
  by_cases inside : ∃ a, f a=z
  · obtain ⟨a,rfl⟩ := inside
    exact (hb i a (fun h => hi (congrArg f h.symm))).trans
      (hb j a (fun h => hj (congrArg f h.symm))).symm
  · exact (Relations.same _ _ _ _ _).mp (external p f g D single prime small i j z inside) _ (adjacency_mem G)

/-- On the bounded nineteen-point fiber, tournament exceptions to algebraic
separability need neither a catalog placement nor a quantum tournament test. -/
theorem nineteen {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (bound : n<38) {reg : Nat → Prop} (f g : Fin 19 → Fin n)
    (D : DataFor p reg f g) (hom : ∀ i j, source G (f i) (f i)=source G (f j) (f j)) :
    ∃ e : Equiv.Perm (Fin 19), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  let L := equivalence (c:=c) (d:=d) D.srcConfig D.tgtConfig D.used D.products D.sameDiag
    (fun _ _ _ _ h => common_transpose p h)
  have hc := homogeneous D.srcConfig (by decide) hom
  have real : L.Realized := by
    rcases Literature.zivAv_tournament_exceptions (Or.inl rfl) hc (L.homogeneous_target hc) L with h | ht
    · exact h
    · refine ⟨Equiv.refl _,fun M hm i j => ?_⟩
      have sym (a b) : M a b=M b a := hm a b b a
        (symmetric_of_tournament p f g D hom (by decide) bound ht a b)
      rw [L.fixes_tournament_symmetric ht hm sym]
      rfl
  obtain ⟨e,he⟩ := real
  refine ⟨e,fun i j => ?_⟩
  let v := c i j
  have mem : mark c v ∈ (algebra c D.srcConfig).space := fun x y u w eq => by simp only [mark,eq]
  have both : Agrees c d (mark c v) (mark d v) := fun x y u w eq => by simp only [mark,eq]
  have im : L.map (mark c v)=mark d v := unique_map (fun x y => (D.used _).mpr ⟨x,y,rfl⟩) both
  have h := he _ mem i j
  rw [im] at h
  change c i j=d (e i) (e j)
  by_cases eq : d (e i) (e j)=v
  · exact eq.symm
  · have no : (1:ℂ)=0 := by simpa only [mark,eq,if_false,show c i j=v from rfl,if_true] using h
    exact (one_ne_zero no).elim

end QGI.Coherent.BoundedPrimeFiber

