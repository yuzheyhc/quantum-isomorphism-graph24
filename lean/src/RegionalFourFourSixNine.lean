import RegionalSixEightNine
import TwoShoreAttachment

noncomputable section
namespace QGI.Coherent.RegionalFourFourSixNine
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
open private shore twins reverse from RegionalFourFourEight
open private uniform_merge bundle from SmallFiberExtension

theorem card_insert {n t} (c : Table n) (reg : Nat → Prop) (apart : ¬reg t) :
    (vertices c (fun v => reg v ∨ v=t)).card=(vertices c reg).card+(vertices c (·=t)).card := by
  have eq : vertices c (fun v => reg v ∨ v=t)=vertices c reg∪vertices c (·=t) := by ext x; simp only [mem_vertices,Finset.mem_union]
  rw [eq,Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun x h k => apart (((congrArg reg ((mem_vertices c (·=t) x).mp k)).mp ((mem_vertices _ _ _).mp h))))

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

theorem solve {l h r v : Nat} (lh : l≠h) (rl : r≠l) (rh : r≠h) (rv : r≠v)
    (F : Shore (source G) l (Fin 4)) (W : Shore (source G) h (Fin 4))
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) v (Fin 9)) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → ((source G i i=l ∨ source G i i=h) ∨ source G i i=r) ∨ source G i i=v) :
    Realizes p reg := by
  classical
  let c := source G
  let ext := fun t => t=l ∨ t=h
  let keep := fun t => ext t ∨ t=r
  let other := fun t => t=r ∨ t=v
  have sz {t k : Nat} (A : Shore c t (Fin k)) (i : Fin n) (eq : c i i=t) : (fiber G i).card=k := by
    have same : fiber G i=vertices c (·=t) := by ext u; rw [fiber_eq,mem_vertices]; change (c u u=c i i ↔ c u u=t); rw [eq]
    rw [same]; exact RegionalTwoAnchor.card A
  have fourSize (i : Fin n) (a : ext (c i i)) : (fiber G i).card=4 := a.elim (sz F i) (sz W i)
  have uniform (i j a b : Fin n) (hi : ext (c i i)) (jv : c j j=v)
      (ai : c a a=c i i) (bj : c b b=c j j) : c i j=c a b :=
    (CoprimeFibers.monochromatic G i j (by rw [fourSize i hi,sz Y j jv]; decide)
      ((fiber_eq _ _).mpr ai) ((fiber_eq _ _).mpr bj)).symm
  have size14 : (vertices c keep).card=14 := by
    rw [card_insert c ext (fun t => t.elim rl rh),RegionalFourSixEight.pair_card lh F W,RegionalTwoAnchor.card S]
  have old := LargeOrderBlocks.fourteen p keep (fun i hi => by
    apply (LargeOrderBlocks.large_iff _).mpr
    rcases hi with hi|hi
    · rw [fourSize i hi]
    · rw [sz S i hi]; decide) size14
  have pair := LargeOrderBlocks.of_solver p other (fun i hi => by
    apply (LargeOrderBlocks.large_iff _).mpr
    rcases hi with hi|hi
    · rw [sz S i hi]; decide
    · rw [sz Y i hi]; decide)
    (RegionalFourSixEight.pair_card rv S Y) (Fifteen.solve p _)
  by_cases dup : ∃ i j, i≠j ∧ ∀ t, c (atPoint S i) (atPoint Y t)=c (atPoint S j) (atPoint Y t)
  · rcases SixNineTriples.classify rv S Y dup with uni|⟨v₀,A,B,oa,ob,rect,wt⟩
    · obtain ⟨f,hf⟩ := old
      obtain ⟨g,hg⟩ := LargeOrderBlocks.small p (·=v) ((RegionalTwoAnchor.card Y).le.trans (by decide))
      have full (a b : Fin n) (ha : c a a=r) (hb : c b b=v) :
          c a b=c (atPoint S 0) (atPoint Y 0) := by
        simpa only [atPoint,Equiv.apply_symm_apply] using uni (S.symm ⟨a,ha⟩) (Y.symm ⟨b,hb⟩)
      obtain ⟨d,hd,_⟩ := uniform_merge p keep v f hf g hg (fun a b i j ha hb ai jv => by
        rcases ha with ha|ha
        · exact uniform _ _ _ _ ha hb ai (jv.trans hb.symm)
        · exact (full _ _ ha hb).trans (full _ _ (ai.trans ha) jv).symm)
      obtain ⟨u,hu⟩ := bundle p (fun t => keep t ∨ t=v) d hd
      exact RegionalFourFourEight.restrict_map p ⟨u,fun i j => by rw [hu,hu]; exact hd i j⟩ cover
    · exact SixNineAttachments.attach_keep p S Y reg keep (Or.inr rfl) cover
        (fun i j a b k no hv ha hb => uniform i j a b (k.resolve_right no) hv ha hb) old v₀ A B oa ob rect wt
  obtain ⟨side,sur,coh⟩ := SixNineCuts.cut rv S Y dup
  have rectangle {s} (A : Shore c s (Fin 4)) : FiberPairExtension.twins c s r :=
    reverse (twins S A (SixNineCuts.even_rectangle (k:=2) S A side sur coh (fun u t hu hd => by omega)))
  let anchor : Region c other := ⟨atPoint S 0,(mem_vertices _ _ _).mpr (Or.inl (S 0).property)⟩
  have result := TwoShoreAttachment.attach p (atPoint F 0) (atPoint W 0) (F 0).property (W 0).property
    ((RegionalTwoAnchor.pair_bound F W).trans (by decide)) other pair anchor (S 0).property (rectangle F) (rectangle W)
    (fun i j a b hi hj no ha hb => uniform _ _ _ _ hi (hj.resolve_left no) ha hb)
  apply RegionalFourFourEight.restrict_map p result
  intro i hi
  rcases cover i hi with (h|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem realize (reg : Nat → Prop) (total : (vertices (source G) reg).card=23)
    (fours : ∃ x z, reg (source G x x) ∧ reg (source G z z) ∧ (fiber G x).card=4 ∧ (fiber G z).card=4 ∧ source G x x≠source G z z)
    (six : ∃ b, reg (source G b b) ∧ (fiber G b).card=6)
    (nine : ∃ y, reg (source G y y) ∧ (fiber G y).card=9) : Realizes p reg := by
  classical
  obtain ⟨x,z,hx,hz,sx,sz,xz⟩ := fours
  obtain ⟨b,hb,sb⟩ := six; obtain ⟨y,hy,sy⟩ := nine
  obtain ⟨F⟩ := shore x sx; obtain ⟨W⟩ := shore z sz; obtain ⟨S⟩ := shore b sb; obtain ⟨Y⟩ := shore y sy
  let c := source G
  have ne (i j : Fin n) (diff : (fiber G i).card≠(fiber G j).card) : c i i≠c j j := by
    intro eq
    exact diff (congrArg Finset.card (show fiber G i=fiber G j by ext u; rw [fiber_eq,fiber_eq]; change (c u u=c i i ↔ c u u=c j j); rw [eq]))
  have bx := ne b x (by rw [sb,sx]; decide)
  have bz := ne b z (by rw [sb,sz]; decide)
  have yx := ne y x (by rw [sy,sx]; decide)
  have yz := ne y z (by rw [sy,sz]; decide)
  have yb := ne y b (by rw [sy,sb]; decide)
  let first := fun t => t=c x x ∨ t=c z z
  let middle := fun t => first t ∨ t=c b b
  let whole := fun t => middle t ∨ t=c y y
  have s : (vertices c whole).card=23 := by
    rw [card_insert c middle (fun a => a.elim (fun h => h.elim yx yz) yb),card_insert c first (fun a => a.elim bx bz),
      RegionalFourSixEight.pair_card xz F W,RegionalTwoAnchor.card S,RegionalTwoAnchor.card Y]
  have eq : vertices c whole=vertices c reg := by
    apply Finset.eq_of_subset_of_card_le _ (total.trans s.symm).le
    intro i hi
    apply (mem_vertices _ _ _).mpr
    rcases (mem_vertices _ _ _).mp hi with ((h|h)|h)|h
    · exact (congrArg reg h).mpr hx
    · exact (congrArg reg h).mpr hz
    · exact (congrArg reg h).mpr hb
    · exact (congrArg reg h).mpr hy
  apply solve p xz bx bz (Ne.symm yb) F W S Y reg
  intro i hi
  apply (mem_vertices c whole _).mp
  rw [eq]; exact (mem_vertices _ _ _).mpr hi

end QGI.Coherent.RegionalFourFourSixNine
