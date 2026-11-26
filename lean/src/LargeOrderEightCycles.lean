import LargeOrderSquareInterface
import RegionalCycleExtension

noncomputable section
namespace QGI.Coherent.LargeOrderEightCycles
open SixTenCoordinates FiberPairExtension LargeOrderSquareInterface LargeOrderStrongPaths
open FourEightGeometry (Eight RepeatedCycle)
open FourTwelveCycle (Edge edge)
open FourTwelveFunctional (source)

structure CycleData {n l v : Nat} {G : Graph n} (F : Shore (source G) l I) (Y : Shore (source G) v Eight) where
  mark : Nat
  other : Nat
  palette : ∀ i j, source G (atPoint F i) (atPoint Y j)=mark ∨ source G (atPoint F i) (atPoint Y j)=other
  code : Eight → Edge
  cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=mark ↔ i∈edge (code j)
  cycle : RepeatedCycle code

def sharp {n l v : Nat} {G : Graph n} (F : Shore (source G) l I) (Y : Shore (source G) v Eight) (a b : Eight) :=
  ∀ i j, source G (atPoint F i) (atPoint Y a)=source G (atPoint F j) (atPoint Y a) →
    source G (atPoint F i) (atPoint Y b)=source G (atPoint F j) (atPoint Y b) → i=j

theorem direction {n l v : Nat} {G : Graph n} {F : Shore (source G) l I} {Y : Shore (source G) v Eight}
    (D : CycleData F Y) : ∃ bit : Eight → Bool, (∀ t, (Finset.univ.filter (fun z => bit z=t)).card=4) ∧
      ∀ a b, bit a≠bit b → sharp F Y a b := by
  obtain ⟨bit,iff,size⟩ := D.cycle.halves
  have sep : ∀ a b : Edge, FourTwelveCycle.overlap a b=1 → ∀ i j : I,
      (i∈edge a ↔ j∈edge a) → (i∈edge b ↔ j∈edge b) → i=j := by native_decide
  refine ⟨bit,size,fun a b ne i j la lb => sep _ _ (not_not.mp (fun h => ne ((iff a b).mpr h))) i j ?_ ?_⟩
  · rw [←D.cells,←D.cells,la]
  · rw [←D.cells,←D.cells,lb]

theorem two_cuts : ∀ f g : Eight → Bool,
    (∀ t, (Finset.univ.filter (fun z => f z=t)).card=4) → (∀ t, (Finset.univ.filter (fun z => g z=t)).card=4) →
    ∃ a b, f a≠f b ∧ g a≠g b := by native_decide

private def adjacent (i k : I) : Bool := decide (i∈edge (FourTwelveCycle.cycle k))

private def walk (h : Equiv.Perm I) : I → I → Nat :=
  meet (fun k i => adjacent i k) (fun j i => LargeOrderStrongPaths.cycle j (h i))

private theorem isolate : ∀ h : Equiv.Perm I, regular (walk h) 0 →
    ∃ j, ∀ z, walk h 0 z=walk h 0 j → z=j := by native_decide

/-- An eight-cycle and a doubled eight-cycle sharing a four-point shore
force a color that singles out a point on the other four-point shore. -/
theorem conflict {n l r v : Nat} {G : Graph n} {F : Shore (source G) l I} {Y : Shore (source G) v Eight}
    (D : CycleData F Y) (cycle' : CycleAt (source G) r l) : MapsOne (source G) v r := by
  let c := source G
  let law := sourceLaws (closure G)
  obtain ⟨S,M,sq⟩ := cycle'
  let P := D.cycle.points.trans F
  let h := P.trans M.symm
  have shift (i) : atPoint M (h i)=atPoint P i := by simp only [h,atPoint,Equiv.trans_apply,Equiv.apply_symm_apply]
  have second : Block S S P P (fun j i => LargeOrderStrongPaths.cycle j (h i)) (fun j i => LargeOrderStrongPaths.cycle j (h i)) :=
    fun ⦃i j x y⦄ eq => sq (by simpa only [shift] using eq)
  have flag (i j) : c (atPoint P i) (atPoint Y j)=D.mark ↔ adjacent i (D.cycle.label j)=true := by
    change c (atPoint F (D.cycle.points i)) (atPoint Y j)=D.mark ↔ _
    rw [D.cells,D.cycle.edges]
    simp [adjacent,Finset.mem_map_equiv]
  have first : Block P P Y Y (fun i j => adjacent i (D.cycle.label j)) (fun i j => adjacent i (D.cycle.label j)) := by
    intro i j x y eq
    apply Bool.eq_iff_iff.mpr
    rw [←flag,←flag]
    exact Iff.of_eq (congrArg (fun s => s=D.mark) eq)
  have names : Block Y Y S S (fun z j => walk h (D.cycle.label z) j) (fun z j => walk h (D.cycle.label z) j) :=
    Block.fold law (Block.flip law first) (Block.flip law second) (fun a b => if a=true ∧ b=true then 1 else 0)
  have full (i : I) : ∃ z, D.cycle.label z=i := by
    obtain ⟨z,mem⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun z => D.cycle.label z=i)).card by rw [D.cycle.twice]; decide)
    exact ⟨z,(Finset.mem_filter.mp mem).2⟩
  choose z hz using full
  have reg : regular (walk h) 0 := by
    intro i k
    have bit := Block.map names (fun x => decide (x=k.val))
    simpa only [row,hz,decide_eq_true_eq] using Block.degree_eq law bit (z i) (z 0)
  obtain ⟨j,one⟩ := isolate h reg
  refine ⟨atPoint Y (z 0),atPoint S j,(Y _).property,(S _).property,fun t eq => ?_⟩
  let k := S.symm ⟨t,(law.last eq).trans (S j).property⟩
  have hk : atPoint S k=t := congrArg Subtype.val (S.apply_symm_apply _)
  have same := names (i:=z 0) (j:=k) (x:=z 0) (y:=j) (by rw [hk]; exact eq)
  exact hk.symm.trans (congrArg (atPoint S) (one k (by simpa only [hz] using same)))

end QGI.Coherent.LargeOrderEightCycles
