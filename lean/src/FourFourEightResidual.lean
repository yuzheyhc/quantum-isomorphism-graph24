import FourFourEightReduction
import FourEightMixed
import FourEightPhases

noncomputable section
namespace QGI.Coherent.FourFourEight
open Relations SixTenCoordinates FourEightGeometry FourTwelveCycle

/-- The two four-point fibers form a uniform rectangle. Both four-by-eight
interfaces are doubled four-cycles, with the same Gram-defined division
of the eight-point fiber into two sets of four. -/
def EqualPhase (G : Graph 16) : Prop :=
  let c := color (closure G)
  ∃ l r v, l≠r ∧ l≠v ∧ r≠v ∧
    ∃ (F : Shore c l (Fin 4)) (S : Shore c r (Fin 4)) (Y : Shore c v (Fin 8)),
      (∀ x, c x x=l ∨ c x x=r ∨ c x x=v) ∧
      (∀ i j, c (atPoint F i) (atPoint S j)=c (atPoint F 0) (atPoint S 0)) ∧
      ∃ a e, ∃ b d : Fin 8 → Edge,
        (∀ i j, c (atPoint F i) (atPoint Y j)=a ↔ i∈edge (b j)) ∧
        (∀ i j, c (atPoint S i) (atPoint Y j)=e ↔ i∈edge (d j)) ∧
        Nonempty (RepeatedCycle b) ∧ Nonempty (RepeatedCycle d) ∧
        ∀ i j, overlap (b i) (b j)≠1 ↔ overlap (d i) (d j)≠1

private theorem center {G H : Graph 16} {k m t l r v : Nat} [NeZero k] [NeZero m] [NeZero t]
    (C : Shore (color (closure G)) l (Fin k)) (S : Shore (color (closure G)) r (Fin m))
    (Y : Shore (color (closure G)) v (Fin t)) (lr : l≠r) (lv : l≠v) (lo : 3≤k) (hi : k≤13)
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v)
    (first : ThreeFiberTwins.twinBlock (color (closure G)) l r)
    (second : ThreeFiberTwins.twinBlock (color (closure G)) l v) (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,gr,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gr
  letI : InnerProductSpace ℂ K := ip
  let c := color (closure G)
  let x : ThreeFiberTwins.Outside c l := ⟨atPoint S 0,fun eq => lr (eq.symm.trans (S 0).property)⟩
  let y : ThreeFiberTwins.Outside c l := ⟨atPoint Y 0,fun eq => lv (eq.symm.trans (Y 0).property)⟩
  have hx : c x.val x.val=r := (S 0).property
  have hy : c y.val y.val=v := (Y 0).property
  have card : (SmallUnion.vertices c (fun z => z=l)).card=k := by
    let e := Equiv.subtypeEquivRight (p := fun x => x∈SmallUnion.vertices c (fun z => z=l))
      (q := fun x => c x x=l) (fun x => SmallUnion.mem_vertices _ _ x)
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_congr (e.trans C.symm)
  have compl : SmallUnion.vertices c (fun z => z≠l) = (SmallUnion.vertices c (fun z => z=l))ᶜ := by
    ext w; simp only [Finset.mem_compl,SmallUnion.mem_vertices]
  have rest : (SmallUnion.vertices c (fun z => z≠l)).card ≤13 := by
    rw [compl,Finset.card_compl,card,Fintype.card_fin]; omega
  apply ThreeFiberTwins.isomorphic p C 0 hi x y rest ?_ (by
    rw [show color (closure G) x.val x.val=r from hx]; exact first) (by
    rw [show color (closure G) y.val y.val=v from hy]; exact second)
  intro j
  rcases cover j.val with h|h|h
  · exact (j.property h).elim
  · exact Or.inl (h.trans hx.symm)
  · exact Or.inr (h.trans hy.symm)

private theorem twins {G : Graph 16} {l r : Nat} {n m : Nat}
    (F : Shore (color (closure G)) l (Fin n)) (Y : Shore (color (closure G)) r (Fin m))
    (h : SplitRectangle.Twins (fun i j => color (closure G) (atPoint F i) (atPoint Y j))) :
    ThreeFiberTwins.twinBlock (color (closure G)) l r := by
  constructor
  · intro i x j he y
    have transported := h.1 (F.symm i) (F.symm x) (Y.symm j)
      (by simpa only [atPoint,Equiv.apply_symm_apply] using he) (Y.symm y)
    simpa only [atPoint,Equiv.apply_symm_apply] using transported
  · intro i j y he x
    have transported := h.2 (F.symm i) (Y.symm j) (Y.symm y)
      (by simpa only [atPoint,Equiv.apply_symm_apply] using he) (F.symm x)
    simpa only [atPoint,Equiv.apply_symm_apply] using transported

theorem isomorphic_or_equal_phase {G H : Graph 16} (a b y : Fin 16)
    (ha : (fiber G a).card=4) (hb : (fiber G b).card=4) (hy : (fiber G y).card=8)
    (apart : a ∉ fiber G b) (q : QuantumIso G H) : Isomorphic G H ∨ EqualPhase G := by
  classical
  obtain ⟨l,r,v,lr,lv,rv,⟨F⟩,⟨S⟩,⟨Y⟩,cover⟩ :=
    ThreeFiberCoordinates.frames G a b y ha hb hy (by decide) apart
      (ThreeFiberCoordinates.disjoint_of_sizes (by omega)) (ThreeFiberCoordinates.disjoint_of_sizes (by omega))
  let c := color (closure G)
  let M := fun i j => c (atPoint F i) (atPoint S j)
  have coverS (x) : c x x=r ∨ c x x=l ∨ c x x=v := by rcases cover x with h|h|h <;> tauto
  have coverY (x) : c x x=v ∨ c x x=l ∨ c x x=r := by rcases cover x with h|h|h <;> tauto
  by_cases mixed : ∃ i j, M i j≠M 0 0
  · have mixedS : ∃ j i, c (atPoint S j) (atPoint F i)≠c (atPoint S 0) (atPoint F 0) := by
      obtain ⟨i,j,h⟩ := mixed
      exact ⟨j,i,fun eq => h (Relations.transpose _ eq)⟩
    rcases dispatch lv F Y q with iso|ft|⟨u,_,_,b,fb,⟨B⟩⟩
    · exact Or.inl iso
    · rcases dispatch rv S Y q with iso|st|⟨w,_,_,d,sd,⟨D⟩⟩
      · exact Or.inl iso
      · exact Or.inl (center Y F S (Ne.symm lv) (Ne.symm rv) (by decide) (by decide) coverY
          (reverse_twins F Y ft) (reverse_twins S Y st) q)
      · exact Or.inl (FourEightMixed.isomorphic S F Y coverS mixedS w d sd D q)
    · exact Or.inl (FourEightMixed.isomorphic F S Y cover mixed u b fb B q)
  · push_neg at mixed
    have uniform : SplitRectangle.Twins M :=
      ⟨fun i x _ _ y => (mixed i y).trans (mixed x y).symm,fun _ j y _ x => (mixed x j).trans (mixed x y).symm⟩
    rcases dispatch lv F Y q with iso|ft|⟨u,_,_,b,fb,⟨B⟩⟩
    · exact Or.inl iso
    · exact Or.inl (center F S Y lr lv (by decide) (by decide) cover (twins F S uniform) (twins F Y ft) q)
    · rcases dispatch rv S Y q with iso|st|⟨w,_,_,d,sd,⟨D⟩⟩
      · exact Or.inl iso
      · exact Or.inl (center S F Y (Ne.symm lr) rv (by decide) (by decide) coverS (reverse_twins F S uniform) (twins S Y st) q)
      · rcases FourEightPhases.isomorphic_or_equal F S Y cover u w b d fb sd B D q with iso|remain
        · exact Or.inl iso
        · exact Or.inr ⟨l,r,v,lr,lv,rv,F,S,Y,cover,mixed,u,w,b,d,fb,sd,⟨B⟩,⟨D⟩,remain⟩

end QGI.Coherent.FourFourEight
