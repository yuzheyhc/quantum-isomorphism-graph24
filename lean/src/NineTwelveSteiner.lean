import NineTwelveDesign
import SevenFourteenAnchor
import RegionalPlanar
import SingletonSwitch

noncomputable section
namespace QGI.Coherent.NineTwelveSteiner
open NineTwelveDesign

/-- The two rectangular magic sums for an incidence relation follow from
its mismatch zeros and the corresponding magic row and column sums. -/
theorem rectangular {A I J : Type} [Semiring A] [Fintype I] [Fintype J]
    (f g : I → J → Bool) (U : I → I → A) (V : J → J → A)
    (row : ∀ i, ∑ x, U i x=1) (col : ∀ j, ∑ y, V y j=1)
    (bad : ∀ i j x y, f i j≠g x y → U i x * V j y=0) (i : I) (y : J) :
    (∑ x, if g x y then U i x else 0)=∑ j, if f i j then V j y else 0 := by
  classical
  calc
    _ = ∑ x, ∑ j, if g x y then U i x*V j y else 0 := by
      apply Finset.sum_congr rfl; intro x _
      by_cases h : g x y=true <;> simp [h,←Finset.mul_sum,col]
    _ = ∑ x, ∑ j, if f i j then U i x*V j y else 0 := by
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : f i j=g x y
      · rw [h]
      · simp [bad _ _ _ _ h]
    _ = _ := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
      by_cases h : f i j=true <;> simp [h,←Finset.sum_mul,row]

/-- Localize the two incidence intertwiners at one point projection.
A line through two prescribed points is unique on both sides. -/
theorem triangle {A : Type} [Ring A] (s t : Inc) (U : P → P → A) (V : L → L → A)
    (row : ∀ x i j, i≠j → U x i*U x j=0) (col : ∀ i x y, x≠y → U x i*U y i=0)
    (bad : ∀ x i r v, s r x≠t v i → U x i*V r v=0)
    (left : ∀ r k, (∑ z ∈ line s r, U z k)=∑ v, if t v k then V r v else 0)
    (right : ∀ y v, (∑ a ∈ line t v, U y a)=∑ r, if s r y then V r v else 0)
    {r v : L} {x y z i j k : P} (xy : x≠y) (xz : x≠z) (yz : y≠z)
    (ij : i≠j) (ik : i≠k) (jk : j≠k) (src : line s r={x,y,z}) (tgt : line t v={i,j,k})
    (uniq : ∀ u, s u x=true → s u y=true → u=r) (other : ∀ u, t u i=true → t u k=true → u=v) :
    U x i*U y j=U x i*U z k := by
  classical
  have sm (w) (h : w∈line s r) := (Finset.mem_filter.mp h).2
  have tm (w) (h : w∈line t v) := (Finset.mem_filter.mp h).2
  have sx := sm x (by simp [src])
  have sy := sm y (by simp [src])
  have ti := tm i (by simp [tgt])
  have tk := tm k (by simp [tgt])
  have first : U x i*(∑ a ∈ line s r, U a k)=U x i*V r v := by
    rw [left,Finset.mul_sum,Finset.sum_eq_single v,if_pos tk]
    · intro w _ ne
      split_ifs with hit
      · have nq : t w i=false := Bool.eq_false_iff.mpr (fun wi => ne (other w wi hit))
        exact bad _ _ _ _ (by rw [sx,nq]; decide)
      · exact mul_zero _
    · simp
  have second : U x i*(∑ a ∈ line t v, U y a)=U x i*V r v := by
    rw [right,Finset.mul_sum,Finset.sum_eq_single r,if_pos sy]
    · intro w _ ne
      split_ifs with hit
      · have nq : s w x=false := Bool.eq_false_iff.mpr (fun wx => ne (uniq w wx hit))
        exact bad _ _ _ _ (by rw [ti,nq]; decide)
      · exact mul_zero _
    · simp
  have eq := first.trans second.symm
  simp only [src,tgt,Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,
    xy,xz,yz,ij,ik,jk,or_self,not_false_eq_true,Finset.sum_singleton,mul_add,row x i k ik,
    col i x y xy,zero_add] at eq
  exact add_right_cancel ((add_comm _ _).trans eq).symm

theorem third {b : Inc} {r : L} {x y : P} (rd : (line b r).card=3) (xy : x≠y)
    (hx : b r x=true) (hy : b r y=true) :
    ∃ z, x≠z ∧ y≠z ∧ line b r={x,y,z} := by
  classical
  have mx : x∈line b r := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
  have my : y∈(line b r).erase x := Finset.mem_erase.mpr ⟨(Ne.symm xy),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩⟩
  have small : (((line b r).erase x).erase y).card=1 := by rw [Finset.card_erase_of_mem my,Finset.card_erase_of_mem mx,rd]
  obtain ⟨z,eq⟩ := Finset.card_eq_one.mp small
  have mz : z∈((line b r).erase x).erase y := eq ▸ Finset.mem_singleton_self _
  have zx := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase mz)
  have zy := Finset.ne_of_mem_erase mz
  exact ⟨z,zx.symm,zy.symm,by rw [←eq,Finset.insert_erase my,Finset.insert_erase mx]⟩

open SixTenCoordinates (Shore atPoint Block)
open FourTwelveFunctional (source)
open StrategyColorLaws SmallUnion SmallFiberExtension
open private incompatible outside from RegionalPlanar

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

theorem sums {a k} (A : Shore (source G) a (Fin k)) (S : Shore (targetName p) a (Fin k)) :
    (∀ i, ∑ j, ColorTensor.P p (atPoint A i) (atPoint S j)=1) ∧
    ∀ j, ∑ i, ColorTensor.P p (atPoint A i) (atPoint S j)=1 := by
  classical
  obtain ⟨_,rr,cc⟩ := ColorTensor.quantumPermutation p
  constructor
  · intro i
    apply Eq.trans _ (rr (atPoint A i))
    apply Fintype.sum_of_injective (atPoint S) (fun _ _ eq => S.injective (Subtype.ext eq)) _ _ _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (SixSixCycle.point S (eq.symm.trans (A i).property)))
  · intro j
    apply Eq.trans _ (cc (atPoint S j))
    apply Fintype.sum_of_injective (atPoint A) (fun _ _ eq => A.injective (Subtype.ext eq))
      (fun i => ColorTensor.P p (atPoint A i) (atPoint S j)) (fun x => ColorTensor.P p x (atPoint S j)) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (SixSixCycle.point A (eq.trans (S j).property)))

/-- Two actual Steiner triple systems linked by the strategy have
commuting entries on their point shores. All auxiliary operators here
are entries of the original bounded magic matrix. -/
theorem commuting {a b} (A : Shore (source G) a P) (S : Shore (targetName p) a P)
    (Y : Shore (source G) b L) (Z : Shore (targetName p) b L) (s t : Inc) (names : Block Y Z A S s t)
    (sd : ∀ r, (line s r).card=3) (td : ∀ v, (line t v).card=3)
    (sourceLine : ∀ x y : P, x≠y → ∃! r, s r x=true ∧ s r y=true)
    (targetLine : ∀ i j : P, i≠j → ∃! v, t v i=true ∧ t v j=true) :
    ∀ x y i j, Commute (ColorTensor.P p (atPoint A x) (atPoint S i))
                        (ColorTensor.P p (atPoint A y) (atPoint S j)) := by
  classical
  let U := fun x i => ColorTensor.P p (atPoint A x) (atPoint S i)
  let V := fun r v => ColorTensor.P p (atPoint Y r) (atPoint Z v)
  obtain ⟨hp,_,_⟩ := ColorTensor.quantumPermutation p
  have ua (x i) : star (U x i)=U x i := (hp _ _).2.symm
  have iz {k d} {c : Table n} (B : Shore c d (Fin k)) : Function.Injective (atPoint B) :=
    fun _ _ h => B.injective (Subtype.ext h)
  have row (x i j) (h : i≠j) : U x i*U x j=0 :=
    incompatible p _ _ _ _ (fun eq => (iz S).ne h ((SingletonSwitch.diagonal_iff p eq).mp rfl))
  have col (i x y) (h : x≠y) : U x i*U y i=0 :=
    incompatible p _ _ _ _ (fun eq => (iz A).ne h ((SingletonSwitch.diagonal_iff p eq).mpr rfl))
  have bad (x i r v) (h : s r x≠t v i) : U x i*V r v=0 :=
    incompatible p _ _ _ _ (fun eq => h (names (common_transpose p eq)))
  have bad' (r v x i) (h : s r x≠t v i) : V r v*U x i=0 :=
    incompatible p _ _ _ _ (fun eq => h (names eq))
  have asums := sums p A S
  have ysums := sums p Y Z
  have left (r k) : (∑ z ∈ line s r, U z k)=∑ v, if t v k then V r v else 0 := by
    simpa only [line,Finset.sum_filter] using
      (rectangular s t V U ysums.1 asums.2 (fun r x v i => bad' r v x i) r k).symm
  have right (y v) : (∑ a ∈ line t v, U y a)=∑ r, if s r y then V r v else 0 := by
    simpa only [line,Finset.sum_filter] using
      rectangular (fun x r => s r x) (fun a v => t v a) U V asums.1 ysums.2 (fun x r i v => bad x i r v) y v
  have restrict {r v x y z i j k} (xy : x≠y) (xz : x≠z) (yz : y≠z) (ij : i≠j) (ik : i≠k) (jk : j≠k)
      (src : line s r={x,y,z}) (tgt : line t v={i,j,k}) : U x i*U y j=U x i*U z k := by
    have sx : x∈line s r := by simp [src]
    have sy : y∈line s r := by simp [src]
    have ti : i∈line t v := by simp [tgt]
    have tk : k∈line t v := by simp [tgt]
    apply triangle s t U V row col bad left right xy xz yz ij ik jk src tgt
    · intro u ux uy
      exact (sourceLine x y xy).unique ⟨ux,uy⟩ ⟨(Finset.mem_filter.mp sx).2,(Finset.mem_filter.mp sy).2⟩
    · intro u ui uk
      exact (targetLine i k ik).unique ⟨ui,uk⟩ ⟨(Finset.mem_filter.mp ti).2,(Finset.mem_filter.mp tk).2⟩
  intro x y i j
  change U x i*U y j=U y j*U x i
  by_cases xy : x=y
  · subst y
    by_cases ij : i=j
    · subst j; rfl
    · exact (row x i j ij).trans (row x j i (Ne.symm ij)).symm
  by_cases ij : i=j
  · subst j; exact (col i x y xy).trans (col i y x (Ne.symm xy)).symm
  obtain ⟨r,⟨rx,ry⟩,_⟩ := sourceLine x y xy
  obtain ⟨v,⟨vi,vj⟩,_⟩ := targetLine i j ij
  obtain ⟨z,xz,yz,src⟩ := third (sd r) xy rx ry
  obtain ⟨k,ik,jk,tgt⟩ := third (td v) ij vi vj
  have hP := restrict xy xz yz ij ik jk src tgt
  have hQ := restrict (Ne.symm xy) yz xz (Ne.symm ij) jk ik
    (src.trans (Finset.insert_comm _ _ _)) (tgt.trans (Finset.insert_comm _ _ _))
  have hT := restrict yz.symm xz.symm (Ne.symm xy) jk.symm ik.symm (Ne.symm ij)
    (show line s r={z,y,x} by rw [src]; ext a; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)
    (show line t v={k,j,i} by rw [tgt]; ext a; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)
  have swap (a b c d : P) : star (U a b*U c d)=U c d*U a b :=
    (ContinuousLinearMap.adjoint_comp (U a b) (U c d)).trans (congrArg₂ (·*·) (ua c d) (ua a b))
  have rev (a b c d e f) (h : U a b*U c d=U a b*U e f) : U c d*U a b=U e f*U a b := by
    calc
      _ = star (U a b*U c d) := (swap a b c d).symm
      _ = star (U a b*U e f) := congrArg star h
      _ = _ := swap a b e f
  have adjP := rev _ _ _ _ _ _ hP
  have adjQ := rev _ _ _ _ _ _ hQ
  exact adjQ.trans (hT.trans adjP.symm)


end QGI.Coherent.NineTwelveSteiner




