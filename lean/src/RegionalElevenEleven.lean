import ElevenDesign
import NineNineRectangles
import SixSixRegion
import RegionalFourSixEight

noncomputable section
namespace QGI.Coherent.RegionalElevenEleven
open ElevenDesign SmallUnion SmallFiberExtension StrategyColorLaws
open SixTenCoordinates (Shore atPoint Block sourceLaws commonLaws)
open FourTwelveFunctional (source fiber_eq)
open private shore twins reverse from RegionalFourFourEight

private def coords {n k d} {c : Table n} (F : Shore c d (Fin k)) : Fin k ≃ Region c (·=d) :=
  F.trans (Equiv.subtypeEquivRight (fun i => (mem_vertices c (·=d) i).symm))

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K)

private theorem frame {l} (A : Shore (source G) l V) :
    ∃ T : Shore (targetName p) l V, ∀ i j, source G (atPoint A i) (atPoint A j)=targetName p (atPoint T i) (atPoint T j) := by
  obtain ⟨e,he⟩ := LargeOrderBlocks.small p (·=l) ((RegionalTwoAnchor.card A).le.trans (by decide))
  let T := ((coords A).trans e).trans (Equiv.subtypeEquivRight (fun i => mem_vertices (targetName p) (·=l) i))
  exact ⟨T,fun i j => he (coords A i) (coords A j)⟩

private theorem choose_color (M : ElevenDesign.M) (x y : Nat) (pal : ∀ i j, M i j=x ∨ M i j=y)
    (mix : ¬uniform M) (no : ¬thin M)
    (rd : ∀ v i, FiberRectangles.degree (fun j => decide (M i j=v))=FiberRectangles.degree (fun j => decide (M 0 j=v))) :
    ∃ v w, v≠w ∧ (∀ i j, M i j=v ∨ M i j=w) ∧
      2≤FiberRectangles.degree (fun j => decide (M 0 j=v)) ∧ FiberRectangles.degree (fun j => decide (M 0 j=v))≤5 := by
  classical
  have diff : x≠y := by
    rintro rfl
    exact mix (fun i j => (or_self_iff.mp (pal i j)).trans (or_self_iff.mp (pal 0 0)).symm)
  let R (v : Nat) (i : V) := Finset.univ.filter fun j => M i j=v
  have same (v i) : (R v i).card=(R v 0).card := by simpa only [R,FiberRectangles.degree,decide_eq_true_eq] using rd v i
  have lower (v w) (all : ∀ i j, M i j=v ∨ M i j=w) : 2≤(R v 0).card := by
    by_contra! h
    rcases (show (R v 0).card=0 ∨ (R v 0).card=1 by omega) with h0|h1
    · have name (i j) : M i j=w := (all i j).resolve_left (fun hv => by
        have pos := Finset.card_pos.mpr (show (R v i).Nonempty from ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩)
        rw [same,h0] at pos; omega)
      exact mix (fun i j => (name i j).trans (name 0 0).symm)
    · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h1
      have mark : M 0 a=v := (Finset.mem_filter.mp (ha.symm ▸ Finset.mem_singleton_self a : a∈R v 0)).2
      exact no ⟨0,a,fun z eq => Finset.mem_singleton.mp (ha ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.trans mark⟩ : z∈R v 0))⟩
  have total : (R x 0).card+(R y 0).card=11 := by
    have both : R x 0∪R y 0=Finset.univ := Finset.eq_univ_of_forall (fun j => by simpa [R] using pal 0 j)
    have dis : Disjoint (R x 0) (R y 0) := Finset.disjoint_left.mpr (fun _ h k => diff ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp k).2))
    simpa only [Finset.card_union_of_disjoint dis,Finset.card_univ,Fintype.card_fin] using congrArg Finset.card both
  have reverse := fun i j => (pal i j).symm
  by_cases small : (R x 0).card≤5
  · exact ⟨x,y,diff,pal,by simpa only [R,FiberRectangles.degree,decide_eq_true_eq] using lower x y pal,
      by simpa only [R,FiberRectangles.degree,decide_eq_true_eq] using small⟩
  · have s : (R y 0).card≤5 := by omega
    exact ⟨y,x,diff.symm,reverse,by simpa only [R,FiberRectangles.degree,decide_eq_true_eq] using lower y x reverse,
      by simpa only [R,FiberRectangles.degree,decide_eq_true_eq] using s⟩

theorem solve {l r : Nat} (apart : l≠r) (A : Shore (source G) l V) (Y : Shore (source G) r V) :
    Realizes p (fun s => s=l ∨ s=r) := by
  classical
  let c := source G
  let d := targetName p
  let M := fun i j => c (atPoint A i) (atPoint Y j)
  have old := LargeOrderBlocks.small p (·=l) ((RegionalTwoAnchor.card A).le.trans (by decide))
  by_cases h : uniform M
  · have sh := twins A Y (show SplitRectangle.Twins M from ⟨fun i x _ _ j => (h i j).trans (h x j).symm,
        fun _ j z _ i => (h i j).trans (h i z).symm⟩)
    let a := coords A 0
    have al : source G a.val a.val=l := (A 0).property
    have sh' := reverse (G:=G) sh
    apply FiberPairExtension.attach p Y 0 (by decide) (·=l) old a a
    · exact fun j => Or.inl (((mem_vertices _ _ _).mp j.property).trans al.symm)
    · rwa [al]
    · rwa [al]
  by_cases th : thin M
  · exact SixSixRegion.thin_extend p (·=l) rfl A Y th old
  have cc : Configuration c := ⟨fun _ _ _ h => Relations.diagonal _ h,fun _ _ _ _ h => Relations.transpose _ h,Relations.products _⟩
  obtain ⟨left,right,x,y,pal⟩ := Literature.sharafdini_hirasaka_eleven_ranks cc A Y apart h th
  obtain ⟨T,ht⟩ := frame p A; obtain ⟨Z,hz⟩ := frame p Y
  let N := fun i j => d (atPoint T i) (atPoint Z j)
  let bs (t : Nat) := fun i j => decide (M i j=t)
  let bt (t : Nat) := fun i j => decide (N i j=t)
  have block (v) : Block A A Y Y (bs v) (bs v) := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=v)) eq
  have share (v) : Block A T Y Z (bs v) (bt v) := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=v)) eq
  have rd (v i) := Block.degree_eq (sourceLaws _) (block v) i 0
  obtain ⟨v,w,vw,pal,lower,upper⟩ := choose_color M x y pal h th rd
  let B := bs v
  let D := bt v
  let k := FiberRectangles.degree (B 0)
  have cd0 (j) := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) (block v)) j 0
  have bal := FiberRectangles.balance B (rd v) cd0
  have eq : FiberRectangles.degree (fun i => B i 0)=k := by
    change 11*k=11*FiberRectangles.degree (fun i => B i 0) at bal
    omega
  have cd (j) := (cd0 j).trans eq
  have des := ElevenDesign.parameters B lower upper (rd v) cd (fun i j ne => Block.gram (sourceLaws _) (block v)
    (left i j 0 1 ⟨fun h => (ne h).elim,fun h => ((by decide : (0:V)≠1) h).elim⟩))
  have bot : bip D := by
    refine ⟨fun i => (Block.degree_eq (commonLaws p) (share v) i i).symm.trans (des.1 i),
      fun j => (Block.degree_eq (commonLaws p) (Block.flip (commonLaws p) (share v)) j j).symm.trans (des.2.1 j),?_⟩
    exact fun i j ne => (Block.gram (commonLaws p) (share v) (ht i j)).symm.trans (des.2.2 i j ne)
  obtain ⟨e,f,bits⟩ := Literature.unique_eleven_biplane B D des bot
  have pal' (i j) : N i j=v ∨ N i j=w := by
    obtain ⟨a,b,hit⟩ := StrategyColors.exists_source p (atPoint T i) (atPoint Z j)
    have nm := (associated p).mpr (StrategyColors.maps_support p hit)
    obtain ⟨da,db⟩ := SmallShore.endpoints p nm
    obtain ⟨a,ea⟩ := SixSixCycle.point A (da.trans (T i).property)
    obtain ⟨b,eb⟩ := SixSixCycle.point Y (db.trans (Z j).property)
    exact (pal a b).imp (fun hv => nm.symm.trans (ea ▸ eb ▸ hv)) (fun hw => nm.symm.trans (ea ▸ eb ▸ hw))
  have cross (i j) : M i j=N (e i) (f j) := by
    have bit := bits i j
    change decide (M i j=v)=decide (N (e i) (f j)=v) at bit
    rcases pal i j with h|h <;> rcases pal' (e i) (f j) with a|a
    · exact h.trans a.symm
    · simp [h,a,Ne.symm vw] at bit
    · simp [h,a,Ne.symm vw] at bit
    · exact h.trans a.symm
  let m := (coords A).symm.trans (e.trans (coords T))
  let g := (coords Y).symm.trans (f.trans (coords Z))
  have ma (i) : m (coords A i)=coords T (e i) := by simp [m]
  have gy (j) : g (coords Y j)=coords Z (f j) := by simp [g]
  apply ThreeRectangleExtension.merge_maps p (·=l) r m g
  · intro i j; obtain ⟨i,rfl⟩ := (coords A).surjective i; obtain ⟨j,rfl⟩ := (coords A).surjective j
    rw [ma,ma]; exact (left i j (e i) (e j) e.injective.eq_iff.symm).trans (ht _ _)
  · intro i j; obtain ⟨i,rfl⟩ := (coords Y).surjective i; obtain ⟨j,rfl⟩ := (coords Y).surjective j
    rw [gy,gy]; exact (right i j (f i) (f j) f.injective.eq_iff.symm).trans (hz _ _)
  · intro i j; obtain ⟨i,rfl⟩ := (coords A).surjective i; obtain ⟨j,rfl⟩ := (coords Y).surjective j
    rw [ma,gy]; exact cross i j

theorem realize (reg : Nat → Prop) (total : (vertices (source G) reg).card=22)
    (pair : ∃ x y, reg (source G x x) ∧ reg (source G y y) ∧ (fiber G x).card=11 ∧ (fiber G y).card=11 ∧ source G x x≠source G y y) :
    Realizes p reg := by
  obtain ⟨x,y,hx,hy,sx,sy,ne⟩ := pair
  obtain ⟨A⟩ := shore x sx; obtain ⟨Y⟩ := shore y sy
  let keep := fun t => t=source G x x ∨ t=source G y y
  have eq : vertices (source G) keep=vertices (source G) reg := by
    apply Finset.eq_of_subset_of_card_le _ (total.trans (RegionalFourSixEight.pair_card ne A Y).symm).le
    intro i hi
    exact (mem_vertices _ _ _).mpr (((mem_vertices (source G) keep i).mp hi).elim
      (fun h => (congrArg reg h).mpr hx) (fun h => (congrArg reg h).mpr hy))
  apply RegionalFourFourEight.restrict_map p (solve p ne A Y)
  intro i hi
  apply (mem_vertices (source G) keep i).mp
  exact eq.symm ▸ (mem_vertices _ _ _).mpr hi

end QGI.Coherent.RegionalElevenEleven
