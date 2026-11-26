import FourHalfChart

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog (Four Eight pos hit)
open SixTenCoordinates SmallUnion SmallFiberExtension FourTwelveCycle StrategyColorLaws
open RegionalCycleExtension (emb range_emb)
open FourTwelveFunctional (source)

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
   (p : PerfectStrategy G H K)

/-- Coordinates on the two four-point fibers after aligning all columns on the cycle side. -/
structure Aligned (X : Shore (source G) r Eight) (TX : Shore (targetName p) r Eight)
    (l : Nat) (q : Eight → Four) where
  F : Shore (source G) l Four
  T : Shore (targetName p) l Four
  active : Nat
  rest : Nat
  distinct : active≠rest
  sourceRow : ∀ j i, source G (atPoint X j) (atPoint F i)=if hit i (q j) then active else rest
  targetRow : ∀ j i, targetName p (atPoint TX j) (atPoint T i)=if hit i (q j) then active else rest
  four : ∀ i j x y, pos i j=pos x y → source G (atPoint F i) (atPoint F j)=targetName p (atPoint T x) (atPoint T y)

theorem align (F : Shore (source G) l Four) (X : Shore (source G) r Eight)
    (TX : Shore (targetName p) r Eight)
    (same : ∀ i j, source G (atPoint X i) (atPoint X j)=targetName p (atPoint TX i) (atPoint TX j))
    (pattern : FourDoubleEightCycle.circular F X) :
    ∃ q : Eight → Four, (∀ i, (Finset.univ.filter (fun j => q j=i)).card=2) ∧ Nonempty (Aligned p X TX l q) := by
  classical
  obtain ⟨a,z,palette,b,cells,⟨C⟩⟩ := pattern
  obtain ⟨a,z,az,rows,names⟩ := RegionalCycleExtension.edges F X a z palette b cells C
  let S := C.points.trans F
  let sl := emb S
  obtain ⟨m,hm⟩ := diagonal_names p
  let T : Shore (targetName p) l Four := F.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
  have full (k : Four) : ∃ j, C.label j=k := by
    have card := C.twice k
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun j => C.label j=k)).card by omega)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  obtain ⟨e,inside,across⟩ := RegionalFourTwelve.cycle_named p az sl (emb T) (emb X) (emb TX)
    (range_emb S) (range_emb T) same C.label full rows names
  choose rep hr using full
  have frame : FourPointCycleGlue.Frame (source G) sl (fun k => atPoint X (rep k)) a z :=
    ⟨fun k => by simpa only [hr] using rows (rep k),fun k i => by simpa only [hr] using names (rep k) i⟩
  have mark : ∀ i k : Four, (i∈edge (cycle k)) ↔ hit i k=true := by decide
  have name (j i) : source G (atPoint X j) (atPoint S i)=if hit i (C.label j) then a else z := by
    simpa only [mark] using names j i
  refine ⟨C.label,C.twice,⟨⟨S,e.trans T,a,z,az,name,fun j i => (across j i).symm.trans (name j i),?_⟩⟩⟩
  intro i j x y h
  exact (FourPointCycleGlue.internal_names frame frame (Relations.products (closure G)) (Relations.products (closure G))
    (fun i j => (S i).property.trans (S j).property.symm) (i:=i) (j:=j) (x:=x) (y:=y) h).trans (inside x y)

end QGI.Coherent.FourHalfModel
