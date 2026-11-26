import RegionalPins
import RegionalCycleExtension
import FourSixInterfaces

noncomputable section
namespace QGI.Coherent.RegionalFourSixEightTetra
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle LargeFourteenRegion
open Intertwiner Synchrony RegionalPins
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)
variable {n k : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p₀ : PerfectStrategy G H K) {reg : Nat → Prop} {left right : Fin k → Fin n} (D : DataFor p₀ reg left right)

theorem pins {l r : Nat} (F : Shore (source G) l L) (S : Shore (source G) r (Fin 6))
    (t : Nat) (map : Equiv.Perm (Fin 6))
    (inc : ∀ i j, source G (atPoint F i) (atPoint S j)=t ↔ FourSixSix.incident i (map j)) :
    ∃ ξ : cyclic p₀.symm, ξ≠0 ∧ (∀ i, Pinned p₀.symm ξ (atPoint F i)) ∧ ∀ j, Pinned p₀.symm ξ (atPoint S j) := by
  classical
  let p := p₀.symm
  let c := source G
  let d := targetName p
  obtain ⟨m,hm⟩ := SmallUnion.diagonal_names p
  let tl := emb F
  let sl := tl.trans m.symm.toEmbedding
  have locate (i) : source H (sl i) (sl i)=d (tl i) (tl i) := by
    simpa only [sl,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using hm (sl i)
  have support (i a) (ξ : cyclic p) (ha : U p (sl i) a ξ≠0) : ∃ j, tl j=a := by
    apply (range_emb F _).mpr
    exact ((target_same p _ _ _ _).mp ((DoubledEdges.diag_of_nonzero p ha).symm.trans (locate i))).trans (F i).property
  have tetra : ∀ i j : Fin 4, i≠j → ∃ s : Fin 6, ∀ k, FourSixSix.incident k s ↔ k=i ∨ k=j := by
    unfold FourSixSix.incident; native_decide
  obtain ⟨s₀,hs⟩ := tetra 0 1 (by decide)
  let j₀ := map.symm s₀
  have active : c (tl 0) (atPoint S j₀)=t := (inc 0 _).mpr (by rw [show map j₀=s₀ from map.apply_symm_apply _,hs]; exact Or.inl rfl)
  let val := d (atPoint S j₀) (tl 0)
  have mark (i j) : d (atPoint S j) (tl i)=val ↔ FourSixSix.incident i (map j) := by
    rw [←inc,←active]
    exact (target_same p _ _ _ _).trans ⟨transpose _,transpose _⟩
  have pair (i j : Fin 4) (ne : i≠j) : ∃ y, neighbors d val y={tl i,tl j} := by
    obtain ⟨a,whereAt⟩ := tetra i j ne
    let y := map.symm a
    have ay : map y=a := map.apply_symm_apply _
    refine ⟨atPoint S y,?_⟩
    ext z
    constructor
    · intro hz
      have h := (target_same p _ _ _ _).mp (Finset.mem_filter.mp hz).2
      obtain ⟨k,rfl⟩ := (range_emb F _).mpr ((end_colors (closure G) h).2.trans (F 0).property)
      have h₁ := (mark k y).mp (Finset.mem_filter.mp hz).2
      rw [ay,whereAt] at h₁
      simpa only [Finset.mem_insert,Finset.mem_singleton] using h₁.imp (congrArg tl) (congrArg tl)
    · intro hz
      rcases Finset.mem_insert.mp hz with hz|hz
      · subst z
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mark i y).mpr (ay ▸ (whereAt i).mpr (Or.inl rfl))⟩
      · have h := Finset.mem_singleton.mp hz
        subst z
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mark j y).mpr (ay ▸ (whereAt j).mpr (Or.inr rfl))⟩
  obtain ⟨ξ,e,nz,fixed⟩ := DoubledEdges.fixed_block p sl tl support (fun i j a b =>
    DoubledEdges.pair_commute p val _ _ _ _ (fun h => pair a b (fun eq => h (congrArg tl eq))))
  have four (i) : Pinned p ξ (atPoint F i) := ⟨sl (e.symm i),by simpa only [Equiv.apply_symm_apply] using fixed (e.symm i)⟩
  have different : ∀ a b : Fin 6, (∀ i, FourSixSix.incident i a ↔ FourSixSix.incident i b) → a=b := by
    unfold FourSixSix.incident; native_decide
  have six : ∀ j, Pinned p ξ (atPoint S j) := by
    apply grow p ξ nz (emb S)
    · intro i a h
      exact (range_emb S _).mpr (((target_same p _ _ _ _).mp h).trans (S i).property)
    · intro i j h
      apply map.injective
      exact different _ _ (fun a => (mark a i).symm.trans (((congrArg (·=val) (h _ (four a))).to_iff).trans (mark a j)))
  exact ⟨ξ,nz,four,six⟩

include D in
theorem solve {l r v : Nat} (F : Shore (source G) l L) (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v Eight)
    (inside : ∀ i, source G (left i) (left i)=l ∨ source G (left i) (left i)=r ∨ source G (left i) (left i)=v)
    (t : Nat) (map : Equiv.Perm (Fin 6))
    (inc : ∀ i j, source G (atPoint F i) (atPoint S j)=t ↔ FourSixSix.incident i (map j))
    (short : ∀ j, ∃ b d, ∀ z, (∀ i, source G (atPoint F i) (atPoint Y j)=source G (atPoint F i) (atPoint Y z)) →
      (∀ i, source G (atPoint S i) (atPoint Y j)=source G (atPoint S i) (atPoint Y z)) → z=b ∨ z=d) :
    ∃ h : Equiv.Perm (Fin k), ∀ i j, source G (left i) (left j)=targetName p₀ (right (h i)) (right (h j)) := by
  classical
  let p := p₀.symm
  let c := source G
  let d := targetName p
  obtain ⟨ξ,nz,four,six⟩ := pins p₀ F S t map inc
  have only (i : Fin k) : ∃ u w : Fin n, ∀ b : Fin k, d (left i) (left i)=d (left b) (left b) →
      (∀ z, Pinned p ξ z → d (left i) z=d (left b) z) → left b=u ∨ left b=w := by
    have single (pin : Pinned p ξ (left i)) : ∀ b : Fin k, (∀ z, Pinned p ξ z → d (left i) z=d (left b) z) → left b=left i := by
      intro b h; exact diagonal _ ((target_same p _ _ _ _).mp (h _ pin)).symm
    rcases inside i with h|h|h
    · obtain ⟨j,eq⟩ := (range_emb F _).mpr h
      exact ⟨left i,left i,fun b _ hp => Or.inl (single (eq ▸ four j) b hp)⟩
    · obtain ⟨j,eq⟩ := (range_emb S _).mpr h
      exact ⟨left i,left i,fun b _ hp => Or.inl (single (eq ▸ six j) b hp)⟩
    · obtain ⟨j,eq⟩ := (range_emb Y _).mpr h
      obtain ⟨a,b,choose⟩ := short j
      refine ⟨atPoint Y a,atPoint Y b,fun x same hp => ?_⟩
      obtain ⟨k,hk⟩ := (range_emb Y _).mpr (((target_same p _ _ _ _).mp same).symm.trans h)
      have pins (t) (pin : Pinned p ξ t) : c t (atPoint Y j)=c t (atPoint Y k) := by
        have a := transpose (closure G) ((target_same p _ _ _ _).mp (hp t pin))
        change c t (emb Y j)=c t (emb Y k); rw [eq,hk]; exact a
      exact (choose k (fun i => pins _ (four i)) (fun i => pins _ (six i))).imp
        (fun h => hk.symm.trans (congrArg (emb Y) h)) (fun h => hk.symm.trans (congrArg (emb Y) h))
  obtain ⟨h,nh⟩ := RegionalPins.realize p ξ nz right left D.injG D.injF
    (fun i a act => (D.src _).mpr (by
      have h := StrategyOrientation.reverse p p₀ (DoubledEdges.diag_of_nonzero p act)
      change reg (color (closure G) a a); rw [h]; exact (D.tgt _).mp ⟨i,rfl⟩)) (fun i => by
      obtain ⟨a,b,h⟩ := only i
      let coord (v : Fin n) := if ok : ∃ k, left k=v then ok.choose else i
      have val (x j) (eq : left j=x) : j=coord x := by
        have ok : ∃ k, left k=x := ⟨j,eq⟩
        apply D.injF; simpa only [coord,dif_pos ok,ok.choose_spec] using eq
      exact ⟨coord a,coord b,fun j hd hp => (h j hd hp).imp (val _ _) (val _ _)⟩)
  exact ⟨h.symm,fun i j => by simpa only [Equiv.apply_symm_apply] using StrategyOrientation.reverse p p₀ (nh (h.symm i) (h.symm j))⟩

end QGI.Coherent.RegionalFourSixEightTetra
