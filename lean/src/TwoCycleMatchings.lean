import FourEightGeometry
import TwoMatchingAnchors

noncomputable section
namespace QGI.Coherent.TwoCycleMatchings
open Relations SixTenCoordinates FourEightGeometry FourTwelveCycle
open scoped BigOperators

abbrev E := Fin 8
abbrev F := Fin 4

private structure Mate (f : E → F) where
  p : E → E
  free : ∀ i, p i≠i
  inv : Function.Involutive p
  hit : ∀ i, f (p i)=f i
  only : ∀ i j, f j=f i → j≠i → j=p i

private theorem makeMate (f : E → F) (two : ∀ t, (Finset.univ.filter fun i => f i=t).card=2) : Nonempty (Mate f) := by
  classical
  let s (i : E) := (Finset.univ.filter (fun j => f j=f i)).erase i
  have one (i) : (s i).card=1 := by
    rw [show s i=(Finset.univ.filter (fun j => f j=f i)).erase i from rfl,
      Finset.card_erase_of_mem (by simp),two]
  choose p spec using fun i => Finset.card_eq_one.mp (one i)
  have atP (i) : p i ∈ s i := by simp [spec]
  have ne (i) := (Finset.mem_erase.mp (atP i)).1
  have hit (i) := (Finset.mem_filter.mp (Finset.mem_erase.mp (atP i)).2).2
  have only (i j) (h : f j=f i) (g : j≠i) : j=p i := by
    have hs : j∈s i := Finset.mem_erase.mpr ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    simpa only [spec,Finset.mem_singleton] using hs
  exact ⟨⟨p,ne,fun i => (only (p i) i (hit i).symm (Ne.symm (ne i))).symm,hit,only⟩⟩

private theorem same_code {b : E→Edge} (B : RepeatedCycle b) (i j : E) :
    B.label i=B.label j ↔ overlap (b i) (b j)=2 := by
  rw [FourTwelveTypes.edge_overlap]
  have inj : Function.Injective (fun k : F => edge (cycle k)) := by native_decide
  constructor
  · intro h
    apply FourTwelveTypes.edge_inj
    rw [B.edges,B.edges,h]
  · intro h
    exact inj (Finset.map_injective _ ((B.edges _).symm.trans ((congrArg edge h).trans (B.edges _))))

private def countCuts (h : F→F) (i j : F) :=
  (Finset.univ.filter (fun k : F => i∈edge (cycle k) ∧ j∈edge (cycle (h k)))).card

private theorem no_uniform : ∀ h : Equiv.Perm F, ¬∀ i j, countCuts h i j=countCuts h 0 0 := by native_decide

theorem two_base {n} {c : Fin n → Fin n → Nat} (law : Laws c c) {l r v : Nat}
    (A : Shore c l F) (C : Shore c r F) (Y : Shore c v E)
    (uniform : ∀ i j, c (atPoint A i) (atPoint C j)=c (atPoint A 0) (atPoint C 0))
    (u w : Nat) (b d : E → Edge)
    (fb : ∀ i j, c (atPoint A i) (atPoint Y j)=u ↔ i∈edge (b j))
    (sd : ∀ i j, c (atPoint C i) (atPoint Y j)=w ↔ i∈edge (d j))
    (B : RepeatedCycle b) (D : RepeatedCycle d) :
    ∃ i j, ∀ σ : Equiv.Perm E, σ i=i → σ j=j →
      (∀ x y, c (atPoint Y x) (atPoint Y y)=c (atPoint Y (σ x)) (atPoint Y (σ y))) → ∀ x, σ x=x := by
  classical
  obtain ⟨P⟩ := makeMate B.label B.twice
  obtain ⟨Q⟩ := makeMate D.label D.twice
  have detect {u} {A : Shore c u F} {v b} (B : RepeatedCycle b)
      (fb : ∀ i j, c (atPoint A i) (atPoint Y j)=v ↔ i∈edge (b j)) {i j x y}
      (h : c (atPoint Y i) (atPoint Y j)=c (atPoint Y x) (atPoint Y y)) :
      B.label i=B.label j ↔ B.label x=B.label y := by
    have eq : overlap (b i) (b j)=overlap (b x) (b y) := gram_color law A Y v b fb h
    rw [same_code,same_code,eq]
  let union (i j : E) := if B.label j=B.label i ∧ D.label j=D.label i then 1 else 0
  have joint : Block Y Y Y Y union union := by
    intro i j x y h
    have rev := law.rev h
    simp only [union,detect B fb rev,detect D sd rev]
  let set (i : E) := Finset.univ.filter (fun j => B.label j=B.label i ∧ D.label j=D.label i)
  have const (i j) : (set i).card=(set j).card := by
    simpa [set,Block.hist,union] using Block.hist_eq law joint i j 1
  have seteq (i) : set i = if P.p i=Q.p i then {i,P.p i} else {i} := by
    ext j
    have matchP : B.label j=B.label i ↔ j=i ∨ j=P.p i :=
      ⟨fun h => or_iff_not_imp_left.mpr (P.only i j h), fun h => h.elim (fun eq => eq ▸ rfl) (fun eq => eq ▸ P.hit i)⟩
    have matchQ : D.label j=D.label i ↔ j=i ∨ j=Q.p i :=
      ⟨fun h => or_iff_not_imp_left.mpr (Q.only i j h), fun h => h.elim (fun eq => eq ▸ rfl) (fun eq => eq ▸ Q.hit i)⟩
    by_cases h : P.p i=Q.p i
    · simp [set,matchP,matchQ,h]
    · simp only [set,Finset.mem_filter,Finset.mem_univ,true_and,matchP,matchQ,if_neg h,Finset.mem_singleton]
      exact ⟨fun p => p.1.elim id (fun hp => p.2.elim id (fun hq => (h (hp.symm.trans hq)).elim)),fun p => ⟨Or.inl p,Or.inl p⟩⟩
  have sameIf {i} (hit : P.p i=Q.p i) : ∀ j, P.p j=Q.p j := by
    intro j
    by_contra bad
    have eq := const i j
    rw [seteq,seteq,if_pos hit,if_neg bad,Finset.card_pair (Ne.symm (P.free i)),Finset.card_singleton] at eq
    contradiction
  have sur {f : E → F} (two : ∀ t, (Finset.univ.filter fun i => f i=t).card=2) : Function.Surjective f := by
    intro t
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter fun i => f i=t).card by rw [two]; decide)
    exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  have apart (i : E) : P.p i≠Q.p i := by
    intro bad
    have identical := sameIf bad
    have eqTag (i j) (h : B.label j=B.label i) : D.label j=D.label i := by
      by_cases hji : j=i
      · rw [hji]
      · rw [P.only i j h hji,identical,Q.hit]
    choose rep hrep using sur B.twice
    let h := fun t => D.label (rep t)
    have code (z) : D.label z=h (B.label z) := eqTag _ _ (hrep _).symm
    have onto : Function.Surjective h := by
      intro t
      obtain ⟨z,hz⟩ := sur D.twice t
      exact ⟨B.label z,(code z).symm.trans hz⟩
    let perm := Equiv.ofBijective h (Finite.surjective_iff_bijective.mp onto)
    let ab (i : F) (j : E) := decide (c (atPoint A i) (atPoint Y j)=u)
    let cd (i : F) (j : E) := decide (c (atPoint C i) (atPoint Y j)=w)
    have left : Block A A Y Y ab ab := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=u)) eq
    have right : Block C C Y Y cd cd := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=w)) eq
    let paths (i j : F) := ∑ z, if ab i z=true ∧ cd j z=true then 1 else 0
    have prod : Block A A C C paths paths := Block.fold law left (Block.flip law right)
      (fun a b => if a=true ∧ b=true then 1 else 0)
    have bits (i j) : ab (B.points i) j=true ↔ i∈edge (cycle (B.label j)) := by
      simp only [ab,decide_eq_true_eq,fb,B.edges,Finset.mem_map_equiv,Equiv.symm_apply_apply]
    have bits' (i j) : cd (D.points i) j=true ↔ i∈edge (cycle (h (B.label j))) := by
      simp only [cd,decide_eq_true_eq,sd,D.edges,Finset.mem_map_equiv,Equiv.symm_apply_apply,code]
    have expand (i j) : paths (B.points i) (D.points j)=countCuts h i j * 2 := by
      have sumCount := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
        (Finset.univ.filter (fun k : F => i∈edge (cycle k) ∧ j∈edge (cycle (h k)))) B.label
      simpa [paths,bits,bits',B.twice,countCuts] using sumCount.symm
    apply no_uniform perm
    intro x y
    have value := prod (i:=B.points x) (j:=D.points y) (x:=B.points 0) (y:=D.points 0)
      ((uniform _ _).trans (uniform _ _).symm)
    rw [expand,expand] at value
    exact Nat.mul_right_cancel (by decide : 0<2) value
  obtain ⟨a,b',rigid⟩ := TwoMatchingAnchors.determine P.p Q.p P.inv Q.inv P.free Q.free apart
  refine ⟨a,b',fun σ ha hb colors => rigid _ ha hb ?_ ?_⟩
  · intro i fixed
    have hit := (detect B fb (colors (P.p i) i)).mp (P.hit i)
    rw [fixed] at hit
    exact P.only _ _ hit (fun eq => P.free i (σ.injective (eq.trans fixed.symm)))
  · intro i fixed
    have hit := (detect D sd (colors (Q.p i) i)).mp (Q.hit i)
    rw [fixed] at hit
    exact Q.only _ _ hit (fun eq => Q.free i (σ.injective (eq.trans fixed.symm)))

end QGI.Coherent.TwoCycleMatchings
