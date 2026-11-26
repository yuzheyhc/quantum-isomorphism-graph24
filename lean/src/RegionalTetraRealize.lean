import RegionalTetraFixed
import RegionalTetraTriples
import RegionalBinaryChoice

noncomputable section
open scoped InnerProductSpace
namespace QGI.Coherent.RegionalTetraRealize
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates RegionalSixTwelveStats RegionalTetraLayout RegionalTetraOperators
open RegionalTetraFixed (Fixed)
open RegionalTetraTriples (table off_diagonal)
open RegionalSixTwelveGeometry (Point)
open FourTwelveFunctional (source)
open SmallUnion SmallFiberExtension
open private sums from Intertwiner
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K) {l r v w : Nat} {F : Shore (source G) l Point} {Y : Shore (source G) r Right}
  {T : Shore (targetName p) l Point} {Z : Shore (targetName p) r Right}

private theorem orth {x y a b : Fin n} (ξ : cyclic p) (z : (U p x a).comp (U p y b)=0) :
    ⟪U p x a ξ,U p y b ξ⟫_ℂ=0 := by
  change ⟪(U p x a ξ : K),(U p y b ξ : K)⟫_ℂ=0
  rw [(restricted_projection p _ _).2]
  have h := congrArg (fun f : Module.End ℂ (cyclic p) => f ξ) z
  change U p x a (U p y b ξ)=0 at h
  rw [h]; simp

theorem choose_slots (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) (V : Fixed p P Q) :
    ∃ g : Face → Equiv.Perm Slot, (∀ s i, U p (right P (s,i)) (right Q (V.face s,g s i)) V.ξ≠0) ∧
      ∀ s t i j, table P (s,i) (t,j)=table Q (V.face s,g s i) (V.face t,g t j) := by
  classical
  let X (s : Face) (i a : Slot) := U p (right P (s,i)) (right Q (V.face s,a)) V.ξ
  have inj {c : Fin n → Fin n → Nat} {F' : Shore c l Point} {Y' : Shore c r Right} (A : Layout F' Y' v w) (s : Face) :
      Function.Injective (fun i : Slot => right A (s,i)) := fun _ _ h => (Prod.mk.inj (right_inj A h)).2
  have row (s i) : ∑ a, X s i a=V.ξ := by
    have h := restrict_sum _ (inj Q (V.face s)) (fun a => U p (right P (s,i)) a V.ξ)
      (fun a out => by by_contra nz; exact out (V.right_domain (s,i) a nz))
    exact h.symm.trans (sums p (right P (s,i)) V.ξ).1
  have col (s a) : ∑ i, X s i a=V.ξ := by
    let z := right Q (V.face s,a)
    have h := restrict_sum _ (inj P s) (fun i => U p i z V.ξ) (by
      intro x out
      by_contra nz
      have ty := (DoubledEdges.diag_of_nonzero p nz).trans (Z _).property
      obtain ⟨⟨t,k⟩,rfl⟩ := (right_range P x).mpr ty
      obtain ⟨b,hb⟩ := V.right_domain (t,k) z nz
      have eq : t=s := V.face.injective (Prod.mk.inj (right_inj Q hb)).1
      exact out ⟨k,by rw [eq]⟩)
    exact h.symm.trans (sums p z V.ξ).2
  have ro (s i a b) (ne : a≠b) : ⟪X s i a,X s i b⟫_ℂ=0 :=
    orth p V.ξ (magic_orthogonal p _ _ _ ((inj Q _).ne ne)).1
  have co (s a i j) (ne : i≠j) : ⟪X s i a,X s j a⟫_ℂ=0 :=
    orth p V.ξ (magic_orthogonal p _ _ _ ((inj P _).ne ne)).2
  have bad (s t i j a b) (ne : table P (s,i) (t,j)≠table Q (V.face s,a) (V.face t,b)) :
      ⟪X s i a,X t j b⟫_ℂ=0 := RegionalBinaryChoice.orthogonal p V.ξ ne
  have nz {s i a} (h : ⟪X s i a,X s i a⟫_ℂ≠0) : X s i a≠0 := fun z => h (by rw [z,inner_zero_left])
  rcases off_diagonal (sourceLaws _) (targetLaws p) (commonLaws p) vw P Q with ⟨c,source,target⟩|⟨c,source,target⟩
  · choose g good using fun s => TernaryVectorChoice.local_choice V.ξ V.nz (X s) (row s) (col s) (ro s) (co s)
    refine ⟨g,fun s i => nz (good s i i),fun s t i j => ?_⟩
    by_cases st : s=t
    · subst t
      exact of_not_not (fun h => good s i j (bad s s i j _ _ h))
    · exact (source s t st i j).trans (target _ _ (V.face.injective.ne st) _ _).symm
  · have transport (t : Face) : ∃ f g : Equiv.Perm Slot, ∀ i a, X 0 i a=X t (f i) (g a) := by
      by_cases h : 0=t
      · subst t; exact ⟨Equiv.refl _,Equiv.refl _,fun _ _ => rfl⟩
      obtain ⟨f,hf⟩ := source 0 t h
      obtain ⟨g,hg⟩ := target _ _ (V.face.injective.ne h)
      refine ⟨f,g,fun i a => TernaryVectorChoice.match_entry V.ξ (X 0 i) (X t (f i)) (row 0 i) (row t (f i)) a (g a)
        (fun k ne => ro 0 i a k (Ne.symm ne)) (fun k ne => ro t (f i) (g a) k (Ne.symm ne)) ?_ ?_⟩
      · intro k ne; apply bad; intro eq
        exact ne ((hg a k).mp (eq.symm.trans ((hf i (f i)).mpr rfl))).symm
      · intro k ne; apply inner_eq_zero_symm.mp; apply bad; intro eq
        exact ne (g.injective ((hg k (g a)).mp (eq.symm.trans ((hf i (f i)).mpr rfl))))
    obtain ⟨g,good⟩ := TernaryVectorChoice.synchronize (0 : Face) V.ξ V.nz X (row 0) (col 0) (ro 0) (co 0) transport
    exact ⟨g,fun s i => nz (good s s i i),fun s t i j => of_not_not (fun h => good s t i j (bad s t i j _ _ h))⟩

theorem realize (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) : Realizes p reg := by
  obtain ⟨V⟩ := RegionalTetraFixed.choose p vw P Q
  obtain ⟨g,nz,rr⟩ := choose_slots p vw P Q V
  have named {x y u a : Fin n} (act : U p x y V.ξ≠0) (pin : U p u a V.ξ=V.ξ) :
      source G x u=targetName p y a := by
    apply (associated p).mpr
    apply StrategyColors.maps_support
    intro zero
    have z := congrArg (fun f : Module.End ℂ (cyclic p) => f V.ξ) zero
    change U p x y (U p u a V.ξ)=0 at z
    rw [pin] at z
    exact act z
  let s : Point ⊕ Vertex → Fin n := Sum.elim (left P) (right P)
  let t : Point ⊕ Vertex → Fin n := Sum.elim (fun i => left Q (V.point i)) (fun x => right Q (V.face x.1,g x.1 x.2))
  have cross (j : Vertex) (i : Point) : source G (right P j) (left P i)=targetName p (t (.inr j)) (t (.inl i)) :=
    named (nz j.1 j.2) (V.left_fixed i)
  have all (i j) : source G (s i) (s j)=targetName p (t i) (t j) := by
    cases i with
    | inl i => cases j with
      | inl j => exact named (fun z => V.nz ((V.left_fixed i).symm.trans z)) (V.left_fixed j)
      | inr j => exact common_transpose p (cross j i)
    | inr i => cases j with
      | inl j => exact cross i j
      | inr j => exact rr i.1 j.1 i.2 j.2
  have pick (x : Region (source G) reg) : ∃ i, s i=x.val := by
    rcases cover _ ((mem_vertices _ _ _).mp x.property) with left|right
    · obtain ⟨i,hi⟩ := (left_range P _).mpr left; exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := (right_range P _).mpr right; exact ⟨.inr i,hi⟩
  choose k hk using pick
  have names (i j) : source G i.val j.val=targetName p (t (k i)) (t (k j)) := by rw [←hk i,←hk j]; exact all _ _
  obtain ⟨e,he⟩ := bundle p reg (fun i => t (k i)) names
  exact ⟨e,fun i j => by rw [he,he]; exact names i j⟩

end QGI.Coherent.RegionalTetraRealize

