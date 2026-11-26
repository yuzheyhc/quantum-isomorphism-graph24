import RegionalTernaryChoice
import RegionalSignatureBound
import RegionalShorePins
import RegionalFourSixEightTetra

noncomputable section
namespace QGI.Coherent.LargeOrderFourShorePins
open LargeFourteenRegion SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates RegionalPins
open Intertwiner Synchrony RegionalCycleExtension
open FourTwelveFunctional (source)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)
local notation "c₀" => source G

def PairSize (P : Fin n → Prop) (x : Fin n) : Prop :=
  ∃ u w : Fin n, ∀ b, c₀ x x=c₀ b b → (∀ t, P t → c₀ x t=c₀ b t) → b=u ∨ b=w

theorem named {P : Fin n → Prop} {x : Fin n} (h : P x) : PairSize (G:=G) P x :=
  ⟨x,x,fun b _ hit => Or.inl (Relations.diagonal _ (hit x h).symm)⟩

theorem small {P : Fin n → Prop} {l m : Nat} (A : Shore c₀ l (Fin m)) {x : Fin n} (tag : c₀ x x=l)
    (few : ∀ i, ∃ u w, ∀ b, (∀ z, P z → c₀ (atPoint A i) z=c₀ (atPoint A b) z) → b=u ∨ b=w) :
    PairSize (G:=G) P x := by
  obtain ⟨i,hi⟩ := (range_emb A _).mpr tag
  obtain ⟨u,w,occ⟩ := few i
  refine ⟨atPoint A u,atPoint A w,fun b hd sh => ?_⟩
  obtain ⟨j,hj⟩ := (range_emb A b).mpr (hd.symm.trans tag)
  exact (occ j (fun z hh => by change c₀ (emb A i) z=c₀ (emb A j) z; rw [hi,hj]; exact sh z hh)).imp
    (fun eq => hj.symm.trans (congrArg (atPoint A) eq)) (fun eq => hj.symm.trans (congrArg (atPoint A) eq))

theorem reverse_pins (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i))
    (ξ : cyclic p.symm) (nz : ξ≠0) (few : ∀ i, reg (c₀ i i) → PairSize (G:=G) (Pinned p.symm ξ) i) : Realizes p reg := by
  classical
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g D
  obtain ⟨h,nh⟩ := RegionalPins.realize p.symm ξ nz g f D.injG D.injF
    (fun i a act => (D.src _).mpr (by
      have h := StrategyOrientation.reverse p.symm p (DoubledEdges.diag_of_nonzero p.symm act)
      change reg (Relations.color (closure G) a a); rw [h]; exact (D.tgt _).mp ⟨i,rfl⟩)) (fun i => by
      obtain ⟨a,b,only⟩ := few (f i) ((D.src _).mp ⟨i,rfl⟩)
      let coord (v : Fin n) := if ok : ∃ k, f k=v then ok.choose else i
      have val (x j) (eq : f j=x) : j=coord x := by
        have ok : ∃ k, f k=x := ⟨j,eq⟩
        apply D.injF; simpa only [coord,dif_pos ok,ok.choose_spec] using eq
      exact ⟨coord a,coord b,fun j hd hp => (only (f j) ((target_same p.symm _ _ _ _).mp hd)
        (fun t ht => (target_same p.symm _ _ _ _).mp (hp t ht))).imp (val _ _) (val _ _)⟩)
  exact ⟨h.symm,fun i j => by simpa only [Equiv.apply_symm_apply] using StrategyOrientation.reverse p.symm p (nh (h.symm i) (h.symm j))⟩

attribute [local instance 2000] Classical.propDecidable in
private theorem root_classical (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (x : Fin n)
    (short : ∀ b, reg (c₀ b b) → ∃ (l m : Nat) (A : Shore c₀ l (Fin m)), c₀ b b=l ∧
      ∀ i, (Finset.univ.filter (fun j => c₀ (atPoint A j) x=c₀ (atPoint A i) x)).card≤3) : Realizes p reg := by
  apply LargeOrderBlocks.of_solver p reg active rfl
  intro f g D
  apply RegionalTernaryChoice.root p D x
  intro v
  by_cases used : ∃ i, c₀ (f i) x=v
  · obtain ⟨i,rfl⟩ := used
    obtain ⟨l,m,A,tag,few⟩ := short (f i) ((D.src _).mp ⟨i,rfl⟩)
    obtain ⟨u,hu⟩ := (range_emb A _).mpr tag
    apply (RegionalSignatureBound.bound_set f D.injF (atPoint A) _ _ ?_).trans (few u)
    intro b hb
    simp only [Finset.mem_univ,Finset.mem_filter,true_and] at hb
    obtain ⟨z,hz⟩ := (range_emb A _).mpr ((Relations.end_colors _ hb).1.trans tag)
    exact ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change c₀ (emb A z) x=c₀ (emb A u) x; rw [hu,hz]; exact hb⟩,hz⟩
  · have emp : Finset.univ.filter (fun j => c₀ (f j) x=v)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr; intro i _ h; exact used ⟨i,h⟩
    rw [emp,Finset.card_empty]; exact Nat.zero_le _

theorem root (reg : Nat → Prop) (active : ∀ i, reg (c₀ i i) → large G (c₀ i i)) (x : Fin n)
    (short : ∀ b, reg (c₀ b b) → ∃ (l m : Nat) (A : Shore c₀ l (Fin m)), c₀ b b=l ∧
      ∀ i, (Finset.univ.filter (fun j => c₀ (atPoint A j) x=c₀ (atPoint A i) x)).card≤3) : Realizes p reg := by
  apply root_classical p reg active x
  intro u hu
  obtain ⟨l,m,A,ha,bound⟩ := short u hu
  refine ⟨l,m,A,ha,fun i => ?_⟩
  rw [Finset.filter_congr_decidable Finset.univ (fun j => c₀ (atPoint A j) x=c₀ (atPoint A i) x) (fun _ => Classical.propDecidable _)]
  exact bound i

end QGI.Coherent.LargeOrderFourShorePins
