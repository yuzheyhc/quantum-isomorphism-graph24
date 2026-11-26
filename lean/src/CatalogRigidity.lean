import ThetaBridge

open scoped BigOperators
namespace QGI.CatalogRigidity
open ThetaBridge Intertwiner

def diagSum {n : Nat} (a : NMat n) := ∑ i : Fin n, entry a i i

theorem reads_trace {n : Nat} {e : Fin n ≃ Fin n} {a : NMat n} {A : Mat n}
    (h : Reads e a A) : (diagSum a : ℂ) = Matrix.trace A := by
  unfold Reads at h
  unfold diagSum
  simp only [Nat.cast_sum, h]
  exact Equiv.sum_comp e (fun i => A i i)

def step {n : Nat} (a : NMat n) : NMat n :=
  let a2 := prod a a
  prod (tab fun i j => entry a i j * entry a2 i j) a

def key {n : Nat} (a : NMat n) : Nat × Nat × Nat :=
  let a2 := prod a a
  let a3 := prod a2 a
  let a9 := prod (prod a3 a3) a3
  (diagSum (prod a2 a9), thetaNat a, diagSum (prod (step a) (step a)))

theorem key_sound {n : Nat} {G H : QGI.Graph n} {a b : NMat n}
    {e f : Fin n ≃ Fin n} (ha : Reads e a (adjacency G))
    (hb : Reads f b (adjacency H)) (q : QuantumIso G H) : key a = key b := by
  have spec {J : QGI.Graph n} {u : NMat n} {s : Fin n ≃ Fin n}
      (h : Reads s u (adjacency J)) :
      ((key u).1 : ℂ) = cycle11Count J ∧
      ((key u).2.1 : ℂ) = theta139Count J ∧
      ((key u).2.2 : ℂ) = oppositeTrianglesCount J := by
    have h2 := reads_prod h h
    have h3 := reads_prod h2 h
    have h9 := reads_prod (reads_prod h3 h3) h3
    have ht : Reads s (tab fun i j => entry u i j * entry (prod u u) i j)
        (fun i j => adjacency J i j * walk2 J i j) := by
      intro i j
      unfold Reads at h h2
      simp only [entry_tab, Nat.cast_mul, h, h2, walk2]
    have hl := reads_prod ht h
    exact ⟨reads_trace (reads_prod h2 h9), thetaNat_spec h, reads_trace (reads_prod hl hl)⟩
  obtain ⟨x,y,z⟩ := spec ha
  obtain ⟨x',y',z'⟩ := spec hb
  obtain ⟨r,s,t⟩ := three_counts_qc q
  apply Prod.ext
  · exact_mod_cast x.trans (r.trans x'.symm)
  · apply Prod.ext
    · exact_mod_cast y.trans (s.trans y'.symm)
    · exact_mod_cast z.trans (t.trans z'.symm)

def records (n : Nat) : List (NMat n) :=
  match Homogeneous.catalog n with
  | none => []
  | some (_, src) => (Homogeneous.lines src).filterMap fun line =>
    match Homogeneous.decode n line with
    | .error _ => none
    | .ok g => some (tab fun i j => ((g.rows[i.val]?.getD #[])[j.val]?.getD 0))

def Valid (n count : Nat) : Prop :=
  (records n).length = count ∧ ((records n).map key).Nodup

instance (n count : Nat) : Decidable (Valid n count) := by unfold Valid; infer_instance

private theorem same_of_key {α β : Type} (k : α → β) {a b : α} (l : List α)
    (nd : (l.map k).Nodup) (ha : a ∈ l) (hb : b ∈ l)
    (eq : k a = k b) : a = b := by
  revert nd ha hb
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro nd ha hb
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · exact ha.trans hb.symm
    · subst a
      exact (nd.1 (List.mem_map.mpr ⟨b,hb,eq.symm⟩)).elim
    · subst b
      exact (nd.1 (List.mem_map.mpr ⟨a,ha,eq⟩)).elim
    · exact ih nd.2 ha hb

/-- The input includes actual labelings onto catalog records. -/
def Represented {n : Nat} (G : QGI.Graph n) : Prop :=
  ∃ a ∈ records n, ∃ e : Fin n ≃ Fin n, Reads e a (adjacency G)

theorem catalog_iso_of_key {n : Nat} {β : Type} (k : NMat n → β)
    (nd : ((records n).map k).Nodup)
    (sound : ∀ {G H : QGI.Graph n} {a b : NMat n} {e f : Fin n ≃ Fin n},
      Reads e a (adjacency G) → Reads f b (adjacency H) → QuantumIso G H → k a = k b)
    {G H : QGI.Graph n}
    (g : Represented G) (h : Represented H) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨a,ha,e,he⟩ := g
  obtain ⟨b,hb,f,hf⟩ := h
  have eq := same_of_key k _ nd ha hb (sound he hf q)
  subst b
  let u := e.symm.trans f
  refine ⟨⟨u, u.symm, u.symm_apply_apply, u.apply_symm_apply, ?_⟩⟩
  intro x y
  have v := (he (e.symm x) (e.symm y)).symm.trans (hf (e.symm x) (e.symm y))
  have w : adjacency G x y = adjacency H (u x) (u y) := by simpa [u] using v
  change G.edge x y = H.edge (u x) (u y)
  cases hG : G.edge x y <;> cases hH : H.edge (u x) (u y) <;>
    first | rfl | simp [adjacency, hG, hH] at w

theorem catalog_iso {n c : Nat} (ok : Valid n c) {G H : QGI.Graph n}
    (g : Represented G) (h : Represented H) (q : QuantumIso G H) : Isomorphic G H :=
  catalog_iso_of_key key ok.2 (fun ha hb hq => key_sound ha hb hq) g h q

end QGI.CatalogRigidity
