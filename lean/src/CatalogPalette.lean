import StrategyColorLaws

noncomputable section
open scoped BigOperators
namespace QGI.Coherent.CatalogPalette
open StrategyColors StrategyColorLaws

variable {n : Nat}

/-- A point labeling and the induced bijection between the table's used
colors and the graph's coherent relations. The points go from table to graph. -/
structure Model (G : Graph n) {r : Nat} (c : Fin n → Fin n → Fin r) where
  points : Equiv.Perm (Fin n)
  palette : Fin r ≃ Palette G
  atCell : ∀ i j, palette (c i j) = label G (points i) (points j)

def of_partition {r : Nat} (G : Graph n) (c : Fin n → Fin n → Fin r) (u : Equiv.Perm (Fin n))
    (used : ∀ k, ∃ i j, c i j = k)
    (same : ∀ i j x y, c i j = c x y ↔
      Relations.color (closure G) (u i) (u j) = Relations.color (closure G) (u x) (u y)) : Model G c := by
  classical
  choose x y hy using used
  let f (k : Fin r) := label G (u (x k)) (u (y k))
  have names (i j) : f (c i j) = label G (u i) (u j) :=
    Subtype.ext ((same _ _ _ _).mp (hy _))
  have inj : Function.Injective f := by
    intro k l eq
    have h := (same (x k) (y k) (x l) (y l)).mpr (congrArg Subtype.val eq)
    simpa only [hy] using h
  have sur : Function.Surjective f := by
    rintro ⟨_,i,j,rfl⟩
    exact ⟨c (u.symm i) (u.symm j),by simpa [label] using names (u.symm i) (u.symm j)⟩
  exact ⟨u,Equiv.ofBijective f ⟨inj,sur⟩,names⟩

variable {G H : Graph n} {r s : Nat} {c : Fin n → Fin n → Fin r} {d : Fin n → Fin n → Fin s}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K) (S : Model G c) (T : Model H d)

def mapping : Fin r ≃ Fin s := S.palette.trans ((equiv p).trans T.palette.symm)

theorem mapped (i j x y) : mapping p S T (c i j) = d x y ↔
    Relations.color (closure G) (S.points i) (S.points j) = targetName p (T.points x) (T.points y) := by
  rw [associated p]
  change T.palette.symm (equiv p (S.palette (c i j))) = d x y ↔ _
  rw [Equiv.symm_apply_eq, S.atCell, T.atCell]

private theorem source_color (k : Fin r) (i j) :
    Relations.color (closure G) (S.points i) (S.points j) = (S.palette k).val ↔ c i j = k := by
  change (label G _ _).val = _ ↔ _
  rw [← S.atCell,Subtype.val_inj,S.palette.injective.eq_iff]

private theorem target_color (k : Fin r) (x y) :
    targetName p (T.points x) (T.points y) = (S.palette k).val ↔ d x y = mapping p S T k := by
  change ((equiv p).symm (label H _ _)).val = _ ↔ _
  rw [Subtype.val_inj,← T.atCell,Equiv.symm_apply_eq]
  exact ⟨fun h => T.palette.injective (by simpa [mapping] using h),fun h => by rw [h]; simp [mapping]⟩

theorem transpose_preserved {i j x y} (eq : mapping p S T (c i j) = d x y) :
    mapping p S T (c j i) = d y x :=
  (mapped p S T _ _ _ _).mpr (common_transpose p ((mapped p S T _ _ _ _).mp eq))

theorem product_preserved {i j x y} (eq : mapping p S T (c i j) = d x y) (a b : Fin r) :
    (∑ z, if c i z = a ∧ c z j = b then 1 else 0 : Nat) =
    ∑ z, if d x z = mapping p S T a ∧ d z y = mapping p S T b then 1 else 0 := by
  have h := common_products p (S.palette a).val (S.palette b).val ((mapped p S T _ _ _ _).mp eq)
  rw [← count_relabel _ S.points,← count_relabel _ T.points] at h
  simpa only [count,source_color S,target_color p S T] using h

def graphMatrix {r : Nat} (labeling : Fin n → Fin n → Fin r) (v : Fin r)
    (u : Equiv.Perm (Fin n)) : Intertwiner.Mat n :=
  fun i j => if labeling (u.symm i) (u.symm j) = v then 1 else 0

theorem named_intertwines (k : Fin r) :
    Intertwiner.Intertwines p (graphMatrix c k S.points) (graphMatrix d (mapping p S T k) T.points) := by
  have hs (i j) := source_color S k (S.points.symm i) (S.points.symm j)
  have ht (i j) := target_color p S T k (T.points.symm i) (T.points.symm j)
  simp only [Equiv.apply_symm_apply] at hs ht
  have left : mark (Relations.color (closure G)) (S.palette k).val = graphMatrix c k S.points := by
    ext i j; simp only [mark,graphMatrix,hs]
  have right : mark (targetName p) (S.palette k).val = graphMatrix d (mapping p S T k) T.points := by
    ext i j; simp only [mark,graphMatrix,ht]
  rw [← left, ← right]
  exact mark_intertwines p (S.palette k).val

theorem graph_iso (e : Equiv.Perm (Fin n)) (point : ∀ i j, mapping p S T (c i j) = d (e i) (e j)) :
    QGI.Isomorphic G H := by
  let f := S.points.symm.trans (e.trans T.points)
  refine ⟨⟨f,f.symm,f.symm_apply_apply,f.apply_symm_apply,?_⟩⟩
  rintro x y
  obtain ⟨i,rfl⟩ := S.points.surjective x
  obtain ⟨j,rfl⟩ := S.points.surjective y
  simpa [f] using common_edge p ((mapped p S T _ _ _ _).mp (point i j))

end QGI.Coherent.CatalogPalette