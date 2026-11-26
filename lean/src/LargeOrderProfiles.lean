import LargeOrderFourteen
import LargeOrderHomogeneous
import LargeOrderSixteen
import LargeOrderSingle
import LargeOrderEighteen
import LargeOrderNineteen
import BoundedPrimeFiber
import RegionalDoubleEight
import RegionalSixTen
import FifteenNamed
import LargeOrderSixteenShapes
import SixSixRegion
import NineNineMain
import RegionalFourSixEight
import LargeOrderEighteenFour
import LargeOrderTwentyMixed
import FourSixteenRegion
import RegionalFourSixNine
import LargeOrderFiveFours
import RegionalSixEightNine
import RegionalFourFourFourteen
import RegionalFourFourSixNine
import SevenSevenRegion
import LargeOrderFourFourSixSix
import OddShoreAttachment
import RegionalSixFifteen
import RegionalElevenEleven
import RegionalSixTwelveComplete
import RegionalEightTwelveSigned
import RegionalTenTenComplete
import RegionalTenTwelve
import RegionalSixSixTen
import RegionalFourSixSixSix
import LargeOrderFourFourFourEight
import LargeOrderTwentyTwoFours
import FourEighteenRegion
import NineTwelveRegion
import RegionalFourEightEight
import LargeOrderFourFourSixEight
import RegionalSixSixNine
import SevenFourteenRegion
import RegionalSixSixEight
import LargeOrderFourFourTwelve

namespace QGI.Coherent.LargeOrderProfiles
open CoprimeProfiles SmallUnion LargeFourteenRegion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private labels from CoprimeProfiles

def label (xs : List Nat) (i : Fin xs.length) : Nat := (labels 4 xs).getD i.val 0

def members (xs : List Nat) (t : Nat) : Finset (Fin xs.length) :=
  Finset.univ.filter (fun i => 4 ≤ xs[i.val] ∧ label xs i=t)

def weight (xs : List Nat) (ids : Finset (Fin xs.length)) : Nat := ∑ i ∈ ids, xs[i.val]

/-- Independently check the coprime cuts and the solver condition on every
nonempty block. Isolated small fibers are attached after gluing. -/
def checkWith (xs : List Nat) (accept : Finset (Fin xs.length) → Bool) : Bool :=
  decide ((∀ i : Fin xs.length, 4 ≤ xs[i.val] → accept (members xs (label xs i)) = true) ∧
    ∀ i j : Fin xs.length, 4 ≤ xs[i.val] → 4 ≤ xs[j.val] → label xs i ≠ label xs j →
      xs[i.val].Coprime xs[j.val])

/-- A predicate on the actual profile indices also applies to repeated parts.
The callback gets the complete-space strategy, the common named region, its
cardinality, and the exact correspondence between the region and profile tags. -/
theorem named {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (accept : Finset (Fin xs.length) → Bool) (checked : checkWith xs accept=true)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)
    (solve : ∀ ids : Finset (Fin xs.length), accept ids=true → ∀ reg : Nat → Prop,
      (∀ i, reg (source G i i) ↔ P.tag i ∈ ids) →
      (∀ i, reg (source G i i) → large G (source G i i)) →
      (vertices (source G) reg).card=weight xs ids → Realizes p reg) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, source G i j=targetName p (e i) (e j) := by
  classical
  have valid : (∀ i : Fin xs.length, 4 ≤ xs[i.val] → accept (members xs (label xs i))=true) ∧
      ∀ i j : Fin xs.length, 4 ≤ xs[i.val] → 4 ≤ xs[j.val] → label xs i ≠ label xs j →
        xs[i.val].Coprime xs[j.val] := of_decide_eq_true checked
  let block := fun v => if h : ∃ i, source G i i=v then label xs (P.tag h.choose) else 0
  have atPoint (i : Fin n) : block (source G i i)=label xs (P.tag i) := by
    let h : ∃ j, source G j j = source G i i := ⟨i,rfl⟩
    simp only [block,dif_pos h]
    exact congrArg _ ((P.same _ _).mpr h.choose_spec)
  apply LargeOrderBlocks.named p block
  · intro t
    let reg := fun v => large G v ∧ block v=t
    let ids := members xs t
    have inc (i : Fin n) : reg (source G i i) ↔ P.tag i ∈ ids := by
      simp only [reg,LargeOrderBlocks.large_iff,P.fiber_size,ids,members,Finset.mem_filter,
        Finset.mem_univ,true_and,atPoint]
    have card : (vertices (source G) reg).card = weight xs ids := by
      have eq : vertices (source G) reg = Finset.univ.filter (fun i => P.tag i ∈ ids) := by
        ext i; simp only [mem_vertices,Finset.mem_filter,Finset.mem_univ,true_and,inc]
      rw [eq,←Finset.sum_card_fiberwise_eq_card_filter Finset.univ ids P.tag]
      simp_rw [P.size]; rfl
    by_cases h : ids.Nonempty
    · obtain ⟨j,hj⟩ := h
      have conditions := (Finset.mem_filter.mp hj).2
      have yes := valid.1 j conditions.1
      rw [conditions.2] at yes
      exact solve ids yes reg inc (fun _ h => h.1) card
    · exact LargeOrderBlocks.small p reg (by rw [card]; simp [weight,Finset.not_nonempty_iff_eq_empty.mp h])
  · intro i j hi hj h
    simp only [atPoint] at h
    rw [P.fiber_size] at hi hj
    rw [P.fiber_size,P.fiber_size]
    exact valid.2 _ _ hi hj h

def covered14 (xs : List Nat) := checkWith xs (fun ids => decide (weight xs ids ≤ 14))

theorem isomorphic14 {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (yes : covered14 xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  obtain ⟨e,h⟩ := named P _ yes p (fun ids ok reg _ active size => by
    have bound : weight xs ids ≤ 14 := of_decide_eq_true ok
    by_cases small : (vertices (source G) reg).card ≤ 13
    · exact LargeOrderBlocks.small p reg small
    · exact LargeOrderBlocks.fourteen p reg active (by omega))
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (h i j)⟩

def spatial (k : Nat) : Prop := k=17 ∨ k=20 ∨ k=21 ∨ k=22
instance (k : Nat) : Decidable (spatial k) := by unfold spatial; infer_instance

/-- A named map on a homogeneous nineteen-point fiber of the ambient graph. -/
def NineteenSolver (n : Nat) : Prop :=
  ∀ {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K) {reg : Nat → Prop} (f g : Fin 19 → Fin n) (D : DataFor p reg f g),
    (∀ i j, source G (f i) (f i)=source G (f j) (f j)) →
    ∃ e : Equiv.Perm (Fin 19), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j))

theorem unrestrictedNineteen (n : Nat) : NineteenSolver n := by
  intro G H K _ _ _ p reg f g D hom
  exact LargeOrderNineteen.solve p f g D hom

theorem boundedNineteen {n : Nat} (bound : n < 38) : NineteenSolver n := by
  intro G H K _ _ _ p reg f g D hom
  exact BoundedPrimeFiber.nineteen p bound f g D hom

private theorem one_region {n k : Nat} (nineteen : NineteenSolver n) {G H : Graph n} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K) {reg : Nat → Prop}
    (f g : Fin k → Fin n) (D : DataFor p reg f g) (lo : 16≤k) (hi : k≤22)
    (hom : ∀ i j, source G (f i) (f i)=source G (f j) (f j)) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, source G (f i) (f j)=targetName p (g (e i)) (g (e j)) := by
  rcases (show k=16 ∨ k=18 ∨ k=19 ∨ spatial k by unfold spatial; omega) with rfl | rfl | rfl | sp
  · exact LargeOrderSingle.solve p f g D hom
  · exact LargeOrderEighteen.solve p f g D hom
  · exact nineteen p f g D hom
  · exact LargeOrderHomogeneous.solve p sp f g D hom

set_option synthInstance.maxSize 2000 in
private def previous (limit : Nat) (xs : List Nat) (ids : Finset (Fin xs.length)) : Bool :=
  decide (weight xs ids ≤ limit ∨ (ids.card=1 ∧ 16 ≤ weight xs ids ∧ weight xs ids ≤ 22) ∨
    (weight xs ids=16 ∧ ids.card=4 ∧ ∀ i ∈ ids, xs[i.val]=4) ∨
    (weight xs ids=16 ∧ ∀ i ∈ ids, xs[i.val]=8) ∨
    (weight xs ids=16 ∧ (∃ i ∈ ids, xs[i.val]=6) ∧ ∃ i ∈ ids, xs[i.val]=10) ∨
    (weight xs ids=16 ∧ LargeOrderSixteenShapes.recognized ids=true) ∨
    (weight xs ids=18 ∧ ∀ i ∈ ids, xs[i.val]=6) ∨
    (weight xs ids=18 ∧ LargeOrderSixteenShapes.Has ids 4 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 8) ∨
    (weight xs ids=18 ∧ LargeOrderEighteenFour.accepted ids=true) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Has ids 4 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 10) ∨
    (weight xs ids=18 ∧ ∀ i ∈ ids, xs[i.val]=9) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Has ids 4 ∧ LargeOrderSixteenShapes.Has ids 16) ∨
    (weight xs ids=19 ∧ LargeOrderSixteenShapes.Has ids 4 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 9))

set_option synthInstance.maxSize 2000 in
private def additional (xs : List Nat) (ids : Finset (Fin xs.length)) : Bool :=
  decide ((weight xs ids=20 ∧ ids.card=5 ∧ ∀ i∈ids, xs[i.val]=4) ∨
    (weight xs ids=23 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 8 ∧ LargeOrderSixteenShapes.Has ids 9) ∨
    (weight xs ids=22 ∧ LargeOrderSixteenShapes.Twice ids 4 ∧ LargeOrderSixteenShapes.Has ids 14) ∨
    (weight xs ids=23 ∧ LargeOrderSixteenShapes.Twice ids 4 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 9) ∨
    (weight xs ids=21 ∧ ∀ i∈ids, xs[i.val]=7) ∨
    (weight xs ids=20 ∧ LargeOrderFourFourSixSix.accepted ids=true) ∨
    (weight xs ids=22 ∧ ∃ t∈ids, xs[t.val]=10 ∧ ∀ j∈ids, j≠t → xs[j.val]=4) ∨
    (weight xs ids=21 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 15) ∨
    (weight xs ids=22 ∧ LargeOrderSixteenShapes.Twice ids 11) ∨
    (weight xs ids=18 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 12) ∨
    (weight xs ids=20 ∧ LargeOrderFourFourFourEight.accepted ids=true) ∨
    (weight xs ids=22 ∧ LargeOrderTwentyTwoFours.accepted ids=true) ∨
    (weight xs ids=22 ∧ LargeOrderSixteenShapes.Has ids 4 ∧ LargeOrderSixteenShapes.Has ids 18) ∨
    (weight xs ids=21 ∧ LargeOrderSixteenShapes.Has ids 7 ∧ LargeOrderSixteenShapes.Has ids 14) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Twice ids 6 ∧ LargeOrderSixteenShapes.Has ids 8) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Twice ids 4 ∧ LargeOrderSixteenShapes.Has ids 12) ∨
    (weight xs ids=21 ∧ LargeOrderSixteenShapes.Has ids 9 ∧ LargeOrderSixteenShapes.Has ids 12) ∨
    (weight xs ids=21 ∧ LargeOrderSixteenShapes.Twice ids 6 ∧ LargeOrderSixteenShapes.Has ids 9) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Has ids 4 ∧ LargeOrderSixteenShapes.Twice ids 8) ∨
    (weight xs ids=22 ∧ LargeOrderSixteenShapes.Twice ids 4 ∧ LargeOrderSixteenShapes.Has ids 6 ∧ LargeOrderSixteenShapes.Has ids 8) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Has ids 8 ∧ LargeOrderSixteenShapes.Has ids 12) ∨
    (weight xs ids=20 ∧ LargeOrderSixteenShapes.Twice ids 10) ∨
    (weight xs ids=22 ∧ LargeOrderSixteenShapes.Has ids 10 ∧ LargeOrderSixteenShapes.Has ids 12) ∨
    (weight xs ids=22 ∧ LargeOrderSixteenShapes.Twice ids 6 ∧ LargeOrderSixteenShapes.Has ids 10) ∨
    (weight xs ids=22 ∧ RegionalFourSixSixSix.accepted ids=true))

def accepted (limit : Nat) (xs : List Nat) (ids : Finset (Fin xs.length)) : Bool :=
  previous limit xs ids || additional xs ids

def covered (limit : Nat) (xs : List Nat) : Bool := checkWith xs (accepted limit xs)

private theorem constant_parts {n k total : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    {ids : Finset (Fin xs.length)} {reg : Nat → Prop} (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids)
    (size : (vertices (source G) reg).card=total) (parts : ∀ i∈ids, xs[i.val]=k)
    (solve : ∀ keep : Nat → Prop, (vertices (source G) keep).card=total →
      (∀ t, keep t → (vertices (source G) (fun w => w=t)).card=k) → Realizes p keep) : Realizes p reg := by
  let keep := fun w => reg w ∧ ∃ i, source G i i=w
  have whole : vertices (source G) keep=vertices (source G) reg := by
      ext i
      simp only [mem_vertices,keep,and_iff_left_iff_imp]
      exact fun _ => ⟨i,rfl⟩
  apply RegionalFourFourEight.restrict_map p (solve keep ((congrArg Finset.card whole).trans size) ?_)
      (fun i h => ⟨h,i,rfl⟩)
  rintro t ⟨ht,i,rfl⟩
  have eq : vertices (source G) (fun w => w=source G i i)=fiber G i := by
      ext x; simp only [mem_vertices,FourTwelveFunctional.fiber_eq]
  rw [eq,P.fiber_size]
  exact parts _ ((shape _).mp ht)

private theorem solve_accepted {n limit : Nat} (nineteen : NineteenSolver n) {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    (bounded : ∀ reg : Nat → Prop, (∀ i, reg (source G i i) → large G (source G i i)) →
      (vertices (source G) reg).card ≤ limit → Realizes p reg)
    (ids : Finset (Fin xs.length)) (ok : accepted limit xs ids=true) (reg : Nat → Prop)
    (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=weight xs ids) : Realizes p reg := by
  simp only [accepted,previous,additional,Bool.or_eq_true,decide_eq_true_eq,or_assoc] at ok
  rcases ok with le | ⟨one,lo,hi⟩ | ⟨sixteen,num,parts⟩ | ⟨sixteen,eights⟩ | ⟨sixteen,six,ten⟩ |
    ⟨sixteen,more⟩ | ⟨eighteen,sixes⟩ | ⟨eighteen,four,six,eight⟩ | ⟨eighteen,fours⟩ | ⟨twenty,four,six,ten⟩ | ⟨eighteen,nines⟩ | ⟨twenty,four,sixteen⟩ | ⟨nineteen,four,six,nine⟩ |
    ⟨twenty,num,parts⟩ | ⟨twentythree,six,eight,nine⟩ | ⟨twentytwo,fours,fourteen⟩ | ⟨twentythree,fours,six,nine⟩ | ⟨twentyone,sevens⟩ | ⟨twenty,both⟩ | ⟨twentytwo,t,ht,ten,rest⟩ | ⟨twentyone,six,fifteen⟩ | ⟨twentytwo,elevens⟩ | ⟨eighteen,six,twelve⟩ | ⟨_,foureight⟩ | ⟨twentytwo,foursix⟩ | ⟨twentytwo,four,eighteen⟩ | ⟨twentyone,seven,fourteen⟩ | ⟨twenty,sixes,eight⟩ | ⟨twenty,fours,twelve⟩ | ⟨twentyone,nine,twelve⟩ | ⟨twentyone,sixes,nine⟩ | ⟨twenty,four,eights⟩ | ⟨twentytwo,fours,six,eight⟩ | ⟨twenty,eight,twelve⟩ | ⟨twenty,tens⟩ | ⟨twentytwo,ten,twelve⟩ | ⟨twentytwo,sixes,ten⟩ | ⟨twentytwo,threeSixes⟩
  · exact bounded reg active (size.trans_le le)
  · obtain ⟨tag,ht⟩ := Finset.card_eq_one.mp one
    apply LargeOrderBlocks.of_solver p reg active size
    intro f g D
    apply one_region nineteen p f g D lo hi
    intro i j
    apply (P.same _ _).mp
    have same (u) : P.tag (f u)=tag := by
      have h := (shape _).mp ((D.src _).mp ⟨u,rfl⟩)
      simpa only [ht,Finset.mem_singleton] using h
    exact (same i).trans (same j).symm
  · apply LargeOrderBlocks.of_solver p reg active (size.trans sixteen)
    intro f g D
    let tags : Fin 4 ≃ {j // j ∈ ids} := Fintype.equivOfCardEq (by simp [num])
    have hit (j : Fin 4) : ∃ i : Fin 16, P.tag (f i)=(tags j).val := by
      obtain ⟨x,hx⟩ := P.occurs (tags j).val (by rw [parts _ (tags j).property]; decide)
      obtain ⟨i,rfl⟩ := (D.src x).mpr ((shape x).mpr (hx ▸ (tags j).property))
      exact ⟨i,hx⟩
    choose u hu using hit
    have inc (i : Fin 16) : P.tag (f i) ∈ ids := (shape _).mp ((D.src _).mp ⟨i,rfl⟩)
    apply LargeOrderSixteen.four_cells p f g D (fun i => by rw [P.fiber_size,parts _ (inc i)]) u
    intro i
    obtain ⟨j,hj⟩ := tags.surjective ⟨_,inc i⟩
    exact ⟨j,(P.same _ _).mp ((congrArg Subtype.val hj).symm.trans (hu j).symm)⟩
  · exact RegionalDoubleEight.realize p reg (size.trans sixteen)
      (fun i hi => (P.fiber_size i).trans (eights _ ((shape i).mp hi)))
  · have found {k : Nat} (pos : 0<k) (h : ∃ i ∈ ids, xs[i.val]=k) :
        ∃ x, reg (source G x x) ∧ (fiber G x).card=k := by
      obtain ⟨i,hi,hk⟩ := h
      obtain ⟨x,hx⟩ := P.occurs i (hk.symm ▸ pos)
      exact ⟨x,(shape _).mpr (hx.symm ▸ hi),by rw [P.fiber_size,hx,hk]⟩
    exact RegionalSixTen.realize p reg active (size.trans sixteen) (found (by decide) six) (found (by decide) ten)
  · exact LargeOrderSixteenShapes.solve P p shape active (size.trans sixteen) more
  · exact constant_parts P p shape (size.trans eighteen) sixes (SixSixRegion.realize_of_size p)
  · exact RegionalFourSixEight.realize p reg active (size.trans eighteen)
      (LargeOrderSixteenShapes.single P shape (by decide) four)
      (LargeOrderSixteenShapes.single P shape (by decide) six)
      (LargeOrderSixteenShapes.single P shape (by decide) eight)
  · exact LargeOrderEighteenFour.solve p P fours reg shape active (size.trans eighteen)
  · exact LargeOrderTwentyMixed.realize p reg active (size.trans twenty)
      (LargeOrderSixteenShapes.single P shape (by decide) four)
      (LargeOrderSixteenShapes.single P shape (by decide) six)
      (LargeOrderSixteenShapes.single P shape (by decide) ten)
  · exact constant_parts P p shape (size.trans eighteen) nines (NineNineMain.realize_of_size p)
  · exact FourSixteenRegion.realize p reg (size.trans twenty)
      (LargeOrderSixteenShapes.single P shape (by decide) four) (LargeOrderSixteenShapes.single P shape (by decide) sixteen)
  · exact RegionalFourSixNine.realize p reg (size.trans nineteen) (LargeOrderSixteenShapes.single P shape (by decide) four)
      (LargeOrderSixteenShapes.single P shape (by decide) six) (LargeOrderSixteenShapes.single P shape (by decide) nine)
  · exact LargeOrderFiveFours.solve p P num parts reg shape active (size.trans twenty)
  · exact RegionalSixEightNine.realize p reg (size.trans twentythree) (LargeOrderSixteenShapes.single P shape (by decide) eight)
      (LargeOrderSixteenShapes.single P shape (by decide) six) (LargeOrderSixteenShapes.single P shape (by decide) nine)
  · exact RegionalFourFourFourteen.realize p reg (size.trans twentytwo)
      (LargeOrderSixteenShapes.two P shape (by decide) fours) (LargeOrderSixteenShapes.single P shape (by decide) fourteen)
  · exact RegionalFourFourSixNine.realize p reg (size.trans twentythree) (LargeOrderSixteenShapes.two P shape (by decide) fours)
      (LargeOrderSixteenShapes.single P shape (by decide) six) (LargeOrderSixteenShapes.single P shape (by decide) nine)
  · exact constant_parts P p shape (size.trans twentyone) sevens (SevenSevenRegion.realize_of_size p)
  · exact LargeOrderFourFourSixSix.solve p P both reg shape active (size.trans twenty)
  · apply OddShoreAttachment.realize p reg (size.trans twentytwo) (LargeOrderSixteenShapes.single P shape (by decide) ⟨t,ht,ten⟩)
    · intro i hi
      rw [P.fiber_size]
      by_cases eq : P.tag i=t
      · exact Or.inr (eq.symm ▸ ten)
      · exact Or.inl (rest _ ((shape i).mp hi) eq)
    · have only (i) (hi : reg (source G i i)) (k : (fiber G i).card=10) : P.tag i=t := by
        by_contra ne
        have four := rest _ ((shape i).mp hi) ne
        rw [P.fiber_size,four] at k
        contradiction
      exact fun i j hi hj ki kj => (P.same _ _).mp ((only i hi ki).trans (only j hj kj).symm)
  · exact RegionalSixFifteen.realize p reg (size.trans twentyone) (LargeOrderSixteenShapes.single P shape (by decide) six)
      (LargeOrderSixteenShapes.single P shape (by decide) fifteen)
  · exact RegionalElevenEleven.realize p reg (size.trans twentytwo) (LargeOrderSixteenShapes.two P shape (by decide) elevens)
  · exact RegionalSixTwelve.realize p reg active (size.trans eighteen) (LargeOrderSixteenShapes.single P shape (by decide) six)
      (LargeOrderSixteenShapes.single P shape (by decide) twelve)
  · exact LargeOrderFourFourFourEight.solve p P foureight reg shape active
  · exact LargeOrderTwentyTwoFours.solve p P foursix reg shape active (size.trans twentytwo)
  · exact FourEighteenRegion.realize p reg (size.trans twentytwo) (LargeOrderSixteenShapes.single P shape (by decide) four)
      (LargeOrderSixteenShapes.single P shape (by decide) eighteen)
  · obtain ⟨x,hx,sx⟩ := LargeOrderSixteenShapes.single P shape (by decide) seven
    obtain ⟨y,hy,sy⟩ := LargeOrderSixteenShapes.single P shape (by decide) fourteen
    exact SevenFourteenRegion.realize_of_size p reg (size.trans twentyone) x y hx hy sx sy
  · exact RegionalSixSixEight.realize p reg active (size.trans twenty)
      (LargeOrderSixteenShapes.single P shape (by decide) eight) (LargeOrderSixteenShapes.two P shape (by decide) sixes)
  · exact LargeOrderFourFourTwelve.realize p reg active (size.trans twenty)
      (LargeOrderSixteenShapes.two P shape (by decide) fours) (LargeOrderSixteenShapes.single P shape (by decide) twelve)
  · obtain ⟨x,hx,sx⟩ := LargeOrderSixteenShapes.single P shape (by decide) nine
    obtain ⟨y,hy,sy⟩ := LargeOrderSixteenShapes.single P shape (by decide) twelve
    exact NineTwelveRegion.realize_of_size p reg (size.trans twentyone) x y hx hy sx sy
  · exact RegionalSixSixNine.realize p reg active (size.trans twentyone)
      (LargeOrderSixteenShapes.single P shape (by decide) nine) (LargeOrderSixteenShapes.two P shape (by decide) sixes)
  · exact RegionalFourEightEight.realize p reg active (size.trans twenty)
      (LargeOrderSixteenShapes.single P shape (by decide) four) (LargeOrderSixteenShapes.two P shape (by decide) eights)
  · exact LargeOrderFourFourSixEight.realize p reg (size.trans twentytwo)
      (LargeOrderSixteenShapes.two P shape (by decide) fours) (LargeOrderSixteenShapes.single P shape (by decide) six)
      (LargeOrderSixteenShapes.single P shape (by decide) eight)

  · exact RegionalEightTwelveSigned.of_size p reg (size.trans twenty)
      (LargeOrderSixteenShapes.single P shape (by decide) eight) (LargeOrderSixteenShapes.single P shape (by decide) twelve)

  · exact RegionalTenTenComplete.of_size p reg (size.trans twenty) (LargeOrderSixteenShapes.two P shape (by decide) tens)
  · exact RegionalTenTwelve.of_size p reg (size.trans twentytwo)
      (LargeOrderSixteenShapes.single P shape (by decide) ten) (LargeOrderSixteenShapes.single P shape (by decide) twelve)
  · exact RegionalSixSixTen.realize p reg active (size.trans twentytwo)
      (LargeOrderSixteenShapes.single P shape (by decide) ten) (LargeOrderSixteenShapes.two P shape (by decide) sixes)
  · exact RegionalFourSixSixSix.solve p P threeSixes reg shape active (size.trans twentytwo)

theorem isomorphic_via_bound {n limit : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (yes : covered limit xs = true)
    (bounded : ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (p : PerfectStrategy G H K) (reg : Nat → Prop),
        (∀ i, reg (source G i i) → large G (source G i i)) →
        (vertices (source G) reg).card ≤ limit → Realizes p reg)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  obtain ⟨e,h⟩ := named P _ yes p (solve_accepted (unrestrictedNineteen n) P p (bounded p))
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (h i j)⟩

theorem isomorphic {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (yes : covered 14 xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  apply isomorphic_via_bound P yes _ q
  intro K ng ip hc p reg active bound
  by_cases h : (vertices (source G) reg).card ≤ 13
  · exact LargeOrderBlocks.small p reg h
  · exact LargeOrderBlocks.fourteen p reg active (by omega)

/-- Glue each certified gcd component, then reattach every one-, two-,
and three-point fiber in the ambient strategy. -/
theorem solveAccepted15With {n : Nat} (nineteen : NineteenSolver n) {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    (ids : Finset (Fin xs.length)) (ok : accepted 15 xs ids=true) (reg : Nat → Prop)
    (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=weight xs ids) : Realizes p reg := by
  apply solve_accepted nineteen P p _ ids ok reg shape active size
  intro reg active bound
  by_cases small : (vertices (source G) reg).card ≤ 13
  · exact LargeOrderBlocks.small p reg small
  by_cases mid : (vertices (source G) reg).card=14
  · exact LargeOrderBlocks.fourteen p reg active mid
  · exact LargeOrderBlocks.of_solver p reg active (show (vertices (source G) reg).card=15 by omega)
      (Fifteen.solve p reg)

theorem solveAccepted15 {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    (ids : Finset (Fin xs.length)) (ok : accepted 15 xs ids=true) (reg : Nat → Prop)
    (shape : ∀ i, reg (source G i i) ↔ P.tag i ∈ ids)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=weight xs ids) : Realizes p reg :=
  solveAccepted15With (unrestrictedNineteen n) P p ids ok reg shape active size

theorem isomorphic15 {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (yes : covered 15 xs = true) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  obtain ⟨e,h⟩ := named P _ yes p (solveAccepted15 P p)
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (h i j)⟩

set_option maxRecDepth 12000 in
theorem counts : (List.range 8).map (fun i => ((Routes.enumerate (16+i) 1 (16+i)).filter (covered 15)).length) =
    [231,297,382,486,616,776,973,1213] := by native_decide

end QGI.Coherent.LargeOrderProfiles
