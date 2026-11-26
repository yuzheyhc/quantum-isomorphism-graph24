import RegionalEightTwelveCatalog
import RegionalBinaryChoice
import RegionalSixTwelveDispatch

noncomputable section
open scoped InnerProductSpace
namespace QGI.Coherent.RegionalEightTwelveThin
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension
open private sums from Intertwiner
open private range from RegionalSixTwelveDispatch

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem two_candidates (reg : Nat → Prop) (ξ : cyclic p) (nz : ξ≠0)
    (bounds : ∀ x : Region (source G) reg, ∃ a b : Fin n, ∀ y, U p x.val y ξ≠0 → y=a ∨ y=b) : Realizes p reg := by
  classical
  choose a b allowed using bounds
  let f := fun (x : Region (source G) reg) (y : Fin n) => U p x.val y ξ
  let u := fun x => f x (a x)
  let v := fun x => if a x=b x then 0 else f x (b x)
  have row (x) : u x+v x=ξ := by
    have full : ∑ y∈({a x,b x} : Finset (Fin n)), f x y=ξ := by
      calc
        _ = ∑ y, f x y := Finset.sum_subset (Finset.subset_univ _) (fun y _ out => by
          by_contra h; exact out (by simpa only [Finset.mem_insert,Finset.mem_singleton] using allowed x y h))
        _ = ξ := (sums p x.val ξ).1
    by_cases h : a x=b x
    · simpa [u,v,h] using full
    · simpa [u,v,h] using full
  have orth (x) : ⟪u x,v x⟫_ℂ=0 := by
    by_cases eq : a x=b x
    · simp [v,eq]
    · simp only [u,v,if_neg eq]
      apply RegionalBinaryChoice.orthogonal
      intro hit
      have d := entries p hit (closure H).one_mem (Intertwiner.initial_diagonal p)
      simp [Matrix.one_apply,eq] at d
  obtain ⟨vec,pick,z,good⟩ := BinaryVectorChoice.exists_selection ξ nz u v row orth
  have label (x) : ∃ y, vec x=U p x.val y ξ := by
    rcases pick x with use|use
    · exact ⟨a x,use⟩
    · by_cases eq : a x=b x
      · exact (z x (by simpa [v,eq] using use)).elim
      · exact ⟨b x,by simpa only [v,if_neg eq] using use⟩
  choose g hg using label
  have named (x t) : source G x.val t.val=targetName p (g x) (g t) := by
    by_contra bad
    have h := good x t; rw [hg,hg] at h; exact h (RegionalBinaryChoice.orthogonal p ξ bad)
  obtain ⟨e,he⟩ := bundle p reg g named
  exact ⟨e,fun x t => by rw [he,he]; exact named x t⟩

private theorem linked {x y u a : Fin n} {ξ : cyclic p} (act : U p x y ξ≠0) (pin : U p u a ξ=ξ) :
    source G x u=targetName p y a := by
  apply (associated p).mpr
  apply StrategyColors.maps_support
  intro zero
  have h := congrArg (fun m : Module.End ℂ (cyclic p) => m ξ) zero
  change U p x y (U p u a ξ)=0 at h
  rw [pin] at h; exact act h

theorem realize {l r v : Nat} (F : Shore (source G) l (Fin 12)) (Y : Shore (source G) r (Fin 8))
    (T : Shore (targetName p) l (Fin 12)) (Z : Shore (targetName p) r (Fin 8)) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (a b : Fin 12 → Fin 4) (tag : Fin 8 → Fin 4) (onto : Function.Surjective a)
    (size : ∀ c, (Finset.univ.filter (fun i => tag i=c)).card=2)
    (src : ∀ j i, source G (atPoint Y j) (atPoint F i)=v ↔ a i=tag j)
    (tgt : ∀ j i, targetName p (atPoint Z j) (atPoint T i)=v ↔ b i=tag j)
    (thin : EightTwelveCatalog.Thin (fun i j => targetName p (atPoint T i) (atPoint T j))) : Realizes p reg := by
  classical
  let ψ : cyclic p := ⟨p.psi,psi_mem p⟩
  have ψnz : ψ≠0 := fun eq => psi_ne_zero p (congrArg Subtype.val eq)
  obtain ⟨z,z0⟩ := DoubledEdges.nonzero_row p ψ ψnz (atPoint F 0)
  obtain ⟨t,ht⟩ := (range T z).mpr ((DoubledEdges.diag_of_nonzero p z0).symm.trans (F _).property)
  rw [←ht] at z0
  let ξ := U p (atPoint F 0) (atPoint T t) ψ
  have base : U p (atPoint F 0) (atPoint T t) ξ=ξ := congrArg (fun e : Module.End ℂ (cyclic p) => e ψ) (restricted_projection p _ _).1
  have image (i : Fin 12) : ∃ j, U p (atPoint F i) (atPoint T j) ξ≠0 := by
    obtain ⟨y,hy⟩ := DoubledEdges.nonzero_row p ξ z0 (atPoint F i)
    obtain ⟨j,hj⟩ := (range T y).mpr ((DoubledEdges.diag_of_nonzero p hy).symm.trans (F i).property)
    exact ⟨j,by rw [hj]; exact hy⟩
  choose f active using image
  have one (i : Fin 12) (y) (act : U p (atPoint F i) y ξ≠0) : y=atPoint T (f i) := by
    obtain ⟨j,rfl⟩ := (range T y).mpr ((DoubledEdges.diag_of_nonzero p act).symm.trans (F i).property)
    have name := (common_transpose p (linked p act base)).symm.trans (common_transpose p (linked p (active i) base))
    exact congrArg (atPoint T) (thin t name)
  have fixed (i) : U p (atPoint F i) (atPoint T (f i)) ξ=ξ := by
    calc _ = ∑ y, U p (atPoint F i) y ξ := (Finset.sum_eq_single _ (fun y _ ne => by by_contra h; exact ne (one i y h)) (by simp)).symm
         _ = ξ := (sums p (atPoint F i) ξ).1
  apply two_candidates p reg ξ z0
  intro x
  rcases cover x.val ((mem_vertices _ _ _).mp x.property) with c|c
  · obtain ⟨i,hi⟩ := (range F x.val).mpr c
    exact ⟨atPoint T (f i),atPoint T (f i),fun y h => Or.inl (one i y (by rw [hi]; exact h))⟩
  obtain ⟨j,hj⟩ := (range Y x.val).mpr c
  obtain ⟨i,hi⟩ := onto (tag j)
  obtain ⟨u,w,_,pair⟩ := Finset.card_eq_two.mp (size (b (f i)))
  refine ⟨atPoint Z u,atPoint Z w,fun y act => ?_⟩
  rw [←hj] at act
  obtain ⟨t,rfl⟩ := (range Z y).mpr ((DoubledEdges.diag_of_nonzero p act).symm.trans (Y j).property)
  have eq := (tgt t (f i)).mp ((linked p act (fixed i)).symm.trans ((src j i).mpr hi))
  have incl : t∈({u,w} : Finset (Fin 8)) := by rw [←pair]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm⟩
  exact (Finset.mem_insert.mp incl).elim (fun h => Or.inl (congrArg (atPoint Z) h))
    (fun h => Or.inr (congrArg (atPoint Z) (Finset.mem_singleton.mp h)))

end QGI.Coherent.RegionalEightTwelveThin

