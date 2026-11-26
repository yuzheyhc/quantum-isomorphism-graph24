import NineNinePappus
import NineNinePartition
import NineNineRectangles
import NineNineChecks
import SixSixRegion

noncomputable section
namespace QGI.Coherent.NineNineGeometry
open QGI.NineNine QGI.NineNine.Checks
open BareLex (V rows transpose)
open SixTenCoordinates (Shore atPoint Block Laws)
open SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private small_map bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

abbrev cell {c : Table n} {a b} (A : Shore c a V) (Y : Shore c b V) : N := fun i j => c (atPoint A i) (atPoint Y j)
abbrev mark {c : Table n} {a b} (A : Shore c a V) (Y : Shore c b V) (v : Nat) : B := fun i j => decide (cell A Y i j=v)

theorem coordinates {c : Table n} {a b} (A : Shore c a V) (Y : Shore c b V) (diff : a≠b) :
    ∃ F : (V ⊕ V) ≃ Region c (fun t => t=a ∨ t=b),
      (∀ i, (F (.inl i)).val=atPoint A i) ∧ ∀ i, (F (.inr i)).val=atPoint Y i := by
  let f : (V ⊕ V) → Region c (fun t => t=a ∨ t=b) := Sum.elim
    (fun i => ⟨atPoint A i,(mem_vertices _ _ _).mpr (Or.inl (A i).property)⟩)
    (fun i => ⟨atPoint Y i,(mem_vertices _ _ _).mpr (Or.inr (Y i).property)⟩)
  have apart (i j : V) : atPoint A i≠atPoint Y j := by
    intro h; exact diff ((A i).property.symm.trans ((congrArg (fun x => c x x) h).trans (Y j).property))
  have inj : Function.Injective f := by
    intro x y eq
    have e := congrArg Subtype.val eq
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (A.injective (Subtype.ext e))
      | inr j => exact (apart i j e).elim
    | inr i =>
      cases y with
      | inl j => exact (apart j i e.symm).elim
      | inr j => exact congrArg Sum.inr (Y.injective (Subtype.ext e))
  have surj : Function.Surjective f := by
    intro z
    rcases (mem_vertices _ _ _).mp z.property with h|h
    · obtain ⟨i,hi⟩ := SixSixCycle.point A h; exact ⟨.inl i,Subtype.ext hi⟩
    · obtain ⟨i,hi⟩ := SixSixCycle.point Y h; exact ⟨.inr i,Subtype.ext hi⟩
  exact ⟨Equiv.ofBijective f ⟨inj,surj⟩,fun _ => rfl,fun _ => rfl⟩

private def edge : (V ⊕ V) → (V ⊕ V) → Bool
  | .inl _, .inl _ | .inr _, .inr _ => false
  | .inl i, .inr j | .inr j, .inl i => matrix pappusRows i j

private theorem lcf : ∃ e : (V ⊕ V) ≃ Fin 18, ∀ i j, edge i j=Pappus.edge (e i) (e j) := by
  obtain ⟨q,h⟩ := Pappus.numbering
  have same : ∀ i j : V ⊕ V, edge i j=Pappus.pairEdge (finSumFinEquiv i) (finSumFinEquiv j) := by native_decide
  exact ⟨finSumFinEquiv.trans q,fun i j => (same i j).trans (h _ _)⟩

theorem pappus {a b v : Nat} (diff : a≠b) (A : Shore (source G) a V) (Y : Shore (source G) b V)
    (S : Shore (targetName p) a V) (T : Shore (targetName p) b V)
    (src : rows (mark A Y v)=pappusRows) (tgt : rows (mark S T v)=pappusRows) :
    Realizes p (fun t => t=a ∨ t=b) := by
  obtain ⟨F,FL,FR⟩ := coordinates A Y diff
  obtain ⟨Q,QL,QR⟩ := coordinates S T diff
  have point {c : Table n} {u w} (L : Shore c u V) (R : Shore c w V)
      (h : rows (mark L R v)=pappusRows) (i j) : mark L R v i j=matrix pappusRows i j :=
    congrFun (congrFun ((matrix_rows _).symm.trans (congrArg matrix h)) i) j
  have cross (i j x y) (eq : cell A Y i j=cell S T x y) : matrix pappusRows i j=matrix pappusRows x y :=
    ((point A Y src _ _).symm.trans (Bool.decide_congr (by rw [eq]))).trans (point S T tgt _ _)
  let label : V ⊕ V → Nat := Sum.elim (fun _ => a) (fun _ => b)
  have srcDiag (i) : source G (F i).val (F i).val=label i := by
    cases i with
    | inl i => rw [FL]; exact (A i).property
    | inr i => rw [FR]; exact (Y i).property
  have tgtDiag (i) : targetName p (Q i).val (Q i).val=label i := by
    cases i with
    | inl i => rw [QL]; exact (S i).property
    | inr i => rw [QR]; exact (T i).property
  obtain ⟨e,he⟩ := lcf
  apply NamedQuantumGraph.realize p (fun t => t=a ∨ t=b) (Sum.inl 0) F Q edge _ (Literature.schmidt_pappus edge e he)
  intro i j x y h
  obtain ⟨hh,tt⟩ := SmallShore.endpoints p h
  have hi := (srcDiag i).symm.trans (hh.trans (tgtDiag x))
  have hj := (srcDiag j).symm.trans (tt.trans (tgtDiag y))
  cases i <;> cases j <;> cases x <;> cases y <;> simp only [label,Sum.elim_inl,Sum.elim_inr] at hi hj
  all_goals first | exact (diff hi).elim | exact (diff hj).elim | exact (diff hi.symm).elim | exact (diff hj.symm).elim | rfl | skip
  · simp only [FL,FR,QL,QR] at h; exact cross _ _ _ _ h
  · simp only [FL,FR,QL,QR] at h; exact cross _ _ _ _ (common_transpose p h)

theorem marked_degree {c d : Table n} {a b} (law : Laws c d)
    (A : Shore c a V) (Y : Shore c b V) (S : Shore d a V) (T : Shore d b V) (v : Nat) (i x : V) :
    FiberRectangles.degree (mark A Y v i)=FiberRectangles.degree (mark S T v x) :=
  Block.degree_eq law (Block.map Block.names (fun t => decide (t=v))) i x

theorem regular {c : Table n} {a b} (law : Laws c c) (A : Shore c a V) (Y : Shore c b V) (v : Nat) :
    let d := FiberRectangles.degree (mark A Y v 0)
    (∀ i, FiberRectangles.degree (mark A Y v i)=d) ∧
      ∀ j, FiberRectangles.degree (transpose (mark A Y v) j)=d := by
  let z := mark A Y v
  have f := Block.map (Block.names (L:=A) (L':=A) (R:=Y) (R':=Y)) (fun t => decide (t=v))
  have rr (i : V) : FiberRectangles.degree (z i)=FiberRectangles.degree (z 0) := Block.degree_eq law f i 0
  have cc (j : V) : FiberRectangles.degree (transpose z j)=FiberRectangles.degree (transpose z 0) :=
    Block.degree_eq law (Block.flip law f) j 0
  have balance := FiberRectangles.balance z rr cc
  change 9 * FiberRectangles.degree (z 0)=9 * FiberRectangles.degree (transpose z 0) at balance
  have same : FiberRectangles.degree (transpose z 0)=FiberRectangles.degree (z 0) := by omega
  exact ⟨rr,fun j => (cc j).trans same⟩

theorem thin_of_degree {C : N} {v : Nat} {i : V} (one : FiberRectangles.degree (fun j => decide (C i j=v))=1) :
    Thin C := by
  classical
  obtain ⟨j,only⟩ := Finset.card_eq_one.mp one
  have hit := (Finset.ext_iff.mp only j).mpr (by simp)
  have eq : C i j=v := of_decide_eq_true (Finset.mem_filter.mp hit).2
  refine ⟨i,j,fun k hk => Finset.mem_singleton.mp ((Finset.ext_iff.mp only k).mp ?_)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true (hk.trans eq)⟩

theorem pull_thin {c d : Table n} {a b} (law : Laws c d) (A : Shore c a V) (Y : Shore c b V)
    (S : Shore d a V) (T : Shore d b V) (thin : Thin (cell S T)) : Thin (cell A Y) := by
  obtain ⟨i,j,one⟩ := thin
  let v := cell S T i j
  have single : FiberRectangles.degree (mark S T v i)=1 := by
    apply Finset.card_eq_one.mpr
    refine ⟨j,?_⟩
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mark,decide_eq_true_eq,Finset.mem_singleton]
    exact ⟨fun h => one _ h,fun h => h ▸ rfl⟩
  exact thin_of_degree ((marked_degree law A Y S T v 0 i).trans single)

theorem different {c d : Table n} {a b} (law : Laws c d) (A : Shore c a V) (Y : Shore c b V)
    (S : Shore d a V) (T : Shore d b V) (v : Nat)
    (src : rows (mark A Y v)=pappusRows) (tgt : rows (mark S T v)=rectangleRows) : False := by
  have first : mark A Y v=matrix pappusRows := (matrix_rows _).symm.trans (congrArg matrix src)
  have next : mark S T v=matrix rectangleRows := (matrix_rows _).symm.trans (congrArg matrix tgt)
  have hb : Block A S Y T (mark A Y v) (mark S T v) := Block.map Block.names (fun t => decide (t=v))
  have eq := Block.hist_eq law (Block.gram law hb) 0 0 3
  rw [first,next] at eq
  exact (by native_decide : Block.hist (Block.overlap (matrix pappusRows)) 0 3 ≠
    Block.hist (Block.overlap (matrix rectangleRows)) 0 3) eq

end QGI.Coherent.NineNineGeometry



