import SmallVectorOrbits
import SmallTableMatching

noncomputable section
namespace QGI.SmallVectorCells
open scoped InnerProductSpace
open Classical
variable {E X Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype X] [Fintype Y]
variable {ξ : E} {u : X → Y → E} {c : X → X → Nat} {d : Y → Y → Nat} (D : Data ξ u c d)

abbrev Src (u : X → Y → E) (s : Component u) := {i // left u i=s}
abbrev Tgt (u : X → Y → E) (s : Component u) := {a // right u a=s}
abbrev entry (u : X → Y → E) (s : Component u) (i : Src u s) (a : Tgt u s) := u i.val a.val

include D

theorem size_eq (s : Component u) : Fintype.card (Src u s)=Fintype.card (Tgt u s) := by
  simpa only [Src,Tgt,Fintype.card_subtype] using same_size D s

theorem part_row (s : Component u) (i : Src u s) : ∑ a, entry u s i a=ξ := by
  rw [←D.row i.val]
  apply Fintype.sum_of_injective (fun a : Tgt u s => a.val) Subtype.val_injective (entry u s i) (u i.val) _ (fun _ => rfl)
  intro a no
  by_contra nz
  exact no ⟨⟨a,(edge nz).symm.trans i.property⟩,rfl⟩

theorem part_col (s : Component u) (a : Tgt u s) : ∑ i, entry u s i a=ξ := by
  rw [←D.col a.val]
  apply Fintype.sum_of_injective (fun i : Src u s => i.val) Subtype.val_injective (fun i => entry u s i a) (fun i => u i a.val) _ (fun _ => rfl)
  intro i no
  by_contra nz
  exact no ⟨⟨i,(edge nz).trans a.property⟩,rfl⟩

omit D in
private theorem inside_count {Z W : Type*} [Fintype Z] (tag : Z → W) (s : W) (P : Z → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i : {j // tag j=s} => P i.val)).card=(Finset.univ.filter (fun i => tag i=s ∧ P i)).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ eq
    exact Subtype.ext eq
  · intro j hj
    obtain ⟨h,k⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j,h⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k⟩,rfl⟩

private theorem counts (s t : Component u) (P : Nat → Prop) [DecidablePred P] :
    ∃ h k : Nat,
      (∀ i : Src u s, (Finset.univ.filter (fun j : Src u t => P (c i.val j.val))).card=h) ∧
      (∀ a : Tgt u s, (Finset.univ.filter (fun b : Tgt u t => P (d a.val b.val))).card=h) ∧
      (∀ j : Src u t, (Finset.univ.filter (fun i : Src u s => P (c i.val j.val))).card=k) ∧
       ∀ b : Tgt u t, (Finset.univ.filter (fun a : Tgt u s => P (d a.val b.val))).card=k := by
  let φ (v : Nat) : Nat := if P v then 1 else 0
  have test (v) : φ v=1 ↔ P v := by by_cases hv : P v <;> simp [φ,hv]
  have alt : Data ξ u (fun i j => φ (c i j)) (fun a b => φ (d a b)) :=
    { D with bad := fun i j a b ne => D.bad i j a b (fun h => ne (congrArg φ h)) }
  obtain ⟨h,hl,hr⟩ := degrees alt t 1
  obtain ⟨k,kl,kr⟩ := indegrees alt s 1
  simp only [test] at hl hr kl kr
  refine ⟨h s,k t,?_,?_,?_,?_⟩
  · intro i
    exact (inside_count _ _ _).trans ((hl i.val).symm.trans (congrArg h i.property))
  · intro a
    exact (inside_count _ _ _).trans ((hr a.val).symm.trans (congrArg h a.property))
  · intro j
    exact (inside_count _ _ _).trans ((kl j.val).symm.trans (congrArg k j.property))
  · intro b
    exact (inside_count _ _ _).trans ((kr b.val).symm.trans (congrArg k b.property))

omit D in
private theorem from_sum {J : Type*} [Fintype J] {ξ : E} (w : J → E) (x : E) (j : J) (total : ∑ b,w b=ξ)
      (only : ∀ b, b≠j → ⟪x,w b⟫_ℂ=0) : ⟪x,ξ⟫_ℂ=⟪x,w j⟫_ℂ := by
  rw [←total,inner_sum]
  exact Finset.sum_eq_single j (fun b _ h => only b h) (by simp)

/-- A relation determined by the names whose matrix on each side is a
bijection transports individual entries between the two vector tables. -/
private theorem transport (s t : Component u) (P : Nat → Prop)
    (f : Src u s ≃ Src u t) (g : Tgt u s ≃ Tgt u t)
    (sf : ∀ i j, P (c i.val j.val) ↔ f i=j) (tg : ∀ a b, P (d a.val b.val) ↔ g a=b) :
    SmallVectorOrbits.Related (entry u) s t := by
  refine ⟨f,g,fun i a => ?_⟩
  let l := entry u s i
  let r := entry u t (f i)
  have a₁ : ∀ z : Tgt u s, z≠a → ⟪l a,l z⟫_ℂ=0 := fun z ne => D.ro _ _ _ (fun h => ne (Subtype.ext h.symm))
  have b₁ : ∀ z : Tgt u t, z≠g a → ⟪r (g a),r z⟫_ℂ=0 := fun z ne => D.ro _ _ _ (fun h => ne (Subtype.ext h.symm))
  have a₂ (z : Tgt u t) (ne : z≠g a) : ⟪l a,r z⟫_ℂ=0 := by
    apply D.bad
    intro eq
    exact ne ((tg a z).mp (eq ▸ (sf i (f i)).mpr rfl)).symm
  have b₂ (z : Tgt u s) (ne : z≠a) : ⟪r (g a),l z⟫_ℂ=0 := by
    apply inner_eq_zero_symm.mp
    apply D.bad
    intro eq
    exact ne (g.injective ((tg z (g a)).mp (eq ▸ (sf i (f i)).mpr rfl)))
  have ll := (from_sum l (l a) a (part_row D s i) a₁).symm.trans (from_sum r _ _ (part_row D t (f i)) a₂)
  have rr := (from_sum r (r (g a)) _ (part_row D t (f i)) b₁).symm.trans (from_sum l _ _ (part_row D s i) b₂)
  have zero : ⟪l a-r (g a),l a-r (g a)⟫_ℂ=0 := by simp only [inner_sub_left,inner_sub_right,ll,rr,sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

theorem rectangular (small : ∀ s, Fintype.card (Src u s)≤3) (s t : Component u) :
    (∀ (i : Src u s) (j : Src u t) (a : Tgt u s) (b : Tgt u t), c i.val j.val=d a.val b.val) ∨
    SmallVectorOrbits.Related (entry u) s t := by
  by_cases good : ∀ (i : Src u s) (j : Src u t) (a : Tgt u s) (b : Tgt u t), c i.val j.val=d a.val b.val
  · exact Or.inl good
  apply Or.inr
  push_neg at good
  obtain ⟨i₀,j₀,a₀,b₀,diff⟩ := good
  let v := c i₀.val j₀.val
  let mask (x : Nat) := decide (x=v)
  let p (i : Src u s) (j : Src u t) := mask (c i.val j.val)
  let q (a : Tgt u s) (b : Tgt u t) := mask (d a.val b.val)
  obtain ⟨h,k,sr,tr,sc,_⟩ := counts D s t (fun x => mask x=true)
  have reg : SmallTableMatching.regular p := ⟨fun i j => (sr i).trans (sr j).symm,fun a b => (sc a).trans (sc b).symm⟩
  rcases SmallTableMatching.masks (small s) (small t) p reg with ⟨val,un⟩|⟨val,one⟩
  · have hit : p i₀ j₀=true := by simp [p,mask,v]
    have eq := (un i₀ j₀).symm.trans hit
    subst val
    have full : (Finset.univ.filter (fun j => p i₀ j=true))=Finset.univ := by ext j; simp [un]
    have size : h=Fintype.card (Tgt u t) := by
      rw [←sr i₀,←size_eq D t]
      exact congrArg Finset.card full
    have cover := Finset.eq_univ_of_card _ ((tr a₀).trans size)
    have mem : b₀ ∈ Finset.univ.filter (fun b : Tgt u t => mask (d a₀.val b.val)=true) := cover.symm ▸ Finset.mem_univ b₀
    have yes : q a₀ b₀=true := (Finset.mem_filter.mp mem).2
    exact (diff ((of_decide_eq_true yes).symm)).elim
  · obtain ⟨h₁,k₁,r₁,r₂,c₁,c₂⟩ := counts D s t (fun x => mask x=val)
    have eqh : h₁=1 := (r₁ i₀).symm.trans ((Fintype.existsUnique_iff_card_one _).mp (one.1 i₀))
    have eqk : k₁=1 := (c₁ j₀).symm.trans ((Fintype.existsUnique_iff_card_one _).mp (one.2 j₀))
    have two : SmallTableMatching.one q val := ⟨fun a => (Fintype.existsUnique_iff_card_one _).mpr ((r₂ a).trans eqh),
      fun b => (Fintype.existsUnique_iff_card_one _).mpr ((c₂ b).trans eqk)⟩
    exact transport D s t (fun x => mask x=val) (SmallTableMatching.equivOfOne p val one)
      (SmallTableMatching.equivOfOne q val two) (SmallTableMatching.marks one) (SmallTableMatching.marks two)

end QGI.SmallVectorCells
