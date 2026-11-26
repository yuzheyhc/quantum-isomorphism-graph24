import StrategyColorLaws

noncomputable section
namespace QGI.Coherent.StrategyAlgebra
open StrategyColors StrategyColorLaws Intertwiner

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

private def image (M : Mat n) : Mat n := by
  classical
  exact if h : M ∈ (closure G).space then (exists_mem_intertwining_target p h).choose else 0

private theorem image_spec {M : Mat n} (h : M ∈ (closure G).space) :
    image p M ∈ (closure H).space ∧ Intertwines p M (image p M) := by
  simp only [image,dif_pos h]
  exact (exists_mem_intertwining_target p h).choose_spec

theorem unique_target {M N Q : Mat n} (h : Intertwines p M N) (k : Intertwines p M Q) : N = Q := by
  ext x y
  obtain ⟨i,j,hit⟩ := exists_source p x y
  exact (entry_eq p h hit).symm.trans (entry_eq p k hit)

theorem unique_source {M N Q : Mat n} (h : Intertwines p M Q) (k : Intertwines p N Q) : M = N := by
  ext i j
  obtain ⟨x,y,hit⟩ := exists_target p i j
  exact (entry_eq p h hit).trans (entry_eq p k hit).symm

private theorem image_eq {M N : Mat n} (m : M ∈ (closure G).space) (h : Intertwines p M N) : image p M = N :=
  unique_target p (image_spec p m).2 h

/-- The algebra isomorphism belongs to the specified strategy and therefore acts
on every basis relation with the color name obtained from that same strategy. -/
def equivalence : AlgebraIso (closure G) (closure H) where
  map := image p
  mapsTo := fun _ h => (image_spec p h).1
  injectiveOn := fun _ hm _ hn eq => unique_source p (eq ▸ (image_spec p hm).2) (image_spec p hn).2
  surjectiveOn := by
    intro N hn
    obtain ⟨M,hm,h⟩ := exists_mem_intertwines_of_mem_closure p hn
    exact ⟨M,hm,image_eq p hm h⟩
  map_one := image_eq p (closure G).one_mem (initial_diagonal p)
  map_ones := image_eq p (closure G).ones_mem (initial_full p 1)
  map_add := fun _ hm _ hn => image_eq p ((closure G).space.add_mem hm hn)
    (entrywise₂ p (· + ·) (image_spec p hm).2 (image_spec p hn).2)
  map_smul := fun c _ hm => image_eq p ((closure G).space.smul_mem c hm)
    (entrywise₂ p (fun x _ => c • x) (image_spec p hm).2 (image_spec p hm).2)
  map_mul := fun _ hm _ hn => image_eq p ((closure G).mul_mem hm hn)
    (matrix_mul p (image_spec p hm).2 (image_spec p hn).2)
  map_schur := fun _ hm _ hn => image_eq p ((closure G).schur_mem hm hn)
    (hadamard p (image_spec p hm).2 (image_spec p hn).2)
  map_adjoint := fun _ hm => image_eq p ((closure G).adjoint_mem hm)
    (conjugate_transpose p (image_spec p hm).2)

theorem maps_adjacency : (equivalence p).map (adjacency G) = adjacency H :=
  image_eq p (adjacency_mem G) (initial_adjacency p)

/-- Graph-level form of coherent algebra transport, obtained entirely from
the strategy intertwiners. -/
theorem coherentIso_of_qc (q : QuantumIso G H) :
    ∃ e : AlgebraIso (closure G) (closure H), e.map (adjacency G) = adjacency H := by
  obtain ⟨K,g,ip,_,⟨s⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  exact ⟨equivalence s,maps_adjacency s⟩

theorem maps_basic (v : Nat) :
    (equivalence p).map (mark (Relations.color (closure G)) v) = mark (targetName p) v :=
  image_eq p (Relations.indicator_mem _ _) (mark_intertwines p v)

theorem names_of_realized (hr : (equivalence p).Realized) :
    ∃ e : Equiv.Perm (Fin n), ∀ i j, Relations.color (closure G) i j = targetName p (e i) (e j) := by
  obtain ⟨e,he⟩ := hr
  refine ⟨e,fun i j => ?_⟩
  let v := Relations.color (closure G) i j
  have eq := he (mark (Relations.color (closure G)) v) (Relations.indicator_mem _ _) i j
  rw [maps_basic] at eq
  by_contra ne
  simp [mark,v,Ne.symm ne] at eq

end QGI.Coherent.StrategyAlgebra
