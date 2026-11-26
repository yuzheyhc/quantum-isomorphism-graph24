import Orders.Base15
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Sum

noncomputable section
namespace QGI.Components

variable {n : Nat}

def simple (G : Graph n) : SimpleGraph (Fin n) where
  Adj i j := G.edge i j = true
  symm i j h := (G.symm j i).trans h
  loopless i := by simp [G.loopless]

abbrev Component (G : Graph n) := (simple G).ConnectedComponent
abbrev Points (G : Graph n) (c : Component G) := {i : Fin n // (simple G).connectedComponentMk i = c}

def induced {k : Nat} (G : Graph n) {c : Component G} (u : Fin k ≃ Points G c) : Graph k where
  edge i j := G.edge (u i).val (u j).val
  symm _ _ := G.symm _ _
  loopless _ := G.loopless _

/-- Meunier, Quantum properties of F-cographs, Theorem 3.7 (arXiv:2312.01516).
Its unital C*-algebra notion of graph quantum isomorphism agrees with the
commuting game by Lupini–Mančinska–Roberson, Theorem 4.4. Matching components
have equally many vertices, so their local games can use the same Fin k.
https://arxiv.org/html/2312.01516v2#S3
https://arxiv.org/abs/1712.01820 -/
axiom meunier_match_components {G H : Graph n} (q : QuantumIso G H) :
  ∃ f : Component G ≃ Component H, ∀ c : Component G,
    ∃ (k : Nat) (u : Fin k ≃ Points G c) (v : Fin k ≃ Points H (f c)),
      QuantumIso (induced G u) (induced H v)

private theorem across {G : Graph n} {a b : Component G} (ne : a ≠ b)
    (i : Points G a) (j : Points G b) : G.edge i.val j.val = false := by
  cases h : G.edge i.val j.val with
  | false => rfl
  | true =>
    have edge : (simple G).Adj i.val j.val := h
    exact (ne (i.property.symm.trans ((SimpleGraph.ConnectedComponent.sound edge.reachable).trans j.property))).elim

private theorem glue {G H : Graph n} (f : Component G ≃ Component H)
    (localIso : ∀ c, ∃ e : Points G c ≃ Points H (f c),
      ∀ i j, G.edge i.val j.val = H.edge (e i).val (e j).val) : Isomorphic G H := by
  choose e he using localIso
  let ug := Equiv.sigmaFiberEquiv (simple G).connectedComponentMk
  let uh := Equiv.sigmaFiberEquiv (simple H).connectedComponentMk
  let m := ug.symm.trans ((Equiv.sigmaCongr f e).trans uh)
  refine ⟨⟨m,m.symm,m.symm_apply_apply,m.apply_symm_apply,?_⟩⟩
  intro x y
  obtain ⟨⟨a,i⟩,rfl⟩ := ug.surjective x
  obtain ⟨⟨b,j⟩,rfl⟩ := ug.surjective y
  have ev (a) (i : Points G a) : m (ug ⟨a,i⟩) = (e a i).val := by
    simp only [m,Equiv.trans_apply,Equiv.symm_apply_apply]; rfl
  rw [ev,ev]
  change G.edge i.val j.val = _
  by_cases eq : a = b
  · subst b; exact he a i j
  · rw [across eq,across (f.injective.ne eq)]

/-- A bound applies separately to each source component. The two full
graphs may have many more vertices than the bound. -/
theorem of_component_bound {G H : Graph n} {k : Nat} (through : Through k)
    (small : ∀ c : Component G, Nat.card (Points G c) ≤ k) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨f,quantum⟩ := meunier_match_components q
  apply glue f
  intro c
  obtain ⟨s,u,v,qs⟩ := quantum c
  have bound := small c
  rw [← Nat.card_congr u,Nat.card_eq_fintype_card,Fintype.card_fin] at bound
  obtain ⟨h⟩ := through s bound _ _ qs
  let e : Fin s ≃ Fin s := ⟨h.toFun,h.invFun,h.leftInv,h.rightInv⟩
  refine ⟨u.symm.trans (e.trans v),?_⟩
  rintro i j
  obtain ⟨i,rfl⟩ := u.surjective i
  obtain ⟨j,rfl⟩ := u.surjective j
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h.edge_eq i j

private theorem smaller_component (G : Graph n) (h : ¬(simple G).Preconnected) (c : Component G) :
    Nat.card (Points G c) < n := by
  classical
  letI : Fintype (Points G c) := Fintype.ofFinite _
  have miss : ¬Function.Surjective (Subtype.val : Points G c → Fin n) := by
    intro onto
    apply h
    intro i j
    obtain ⟨x,rfl⟩ := onto i
    obtain ⟨y,rfl⟩ := onto j
    exact SimpleGraph.ConnectedComponent.exact (x.property.trans y.property.symm)
  simpa [Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_not_surjective _ Subtype.val_injective miss

theorem disconnected_sixteen {G H : Graph 16} (h : ¬(simple G).Preconnected)
    (q : QuantumIso G H) : Isomorphic G H :=
  of_component_bound through15 (fun c => by have := smaller_component G h c; omega) q

def complement (G : Graph n) : Graph n where
  edge i j := decide (i ≠ j) && !G.edge i j
  symm i j := by simp [ne_comm,G.symm i j]
  loopless i := by simp

private theorem rel_complement (G : Graph n) (i j : Fin n) :
    rel (complement G) i j = ((rel G i j).1, !(rel G i j).1 && !(rel G i j).2) := by
  simp [rel,complement]

theorem complement_qc {G H : Graph n} (q : QuantumIso G H) :
    QuantumIso (complement G) (complement H) := by
  obtain ⟨K,g,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  refine ⟨K,g,ip,hc,⟨{ p with perfect := ?_ }⟩⟩
  intro u v a b loss
  apply p.perfect u v a b
  intro same
  apply loss
  simp only [rel_complement,same]

private theorem iso_of_complement {G H : Graph n} (h : Isomorphic (complement G) (complement H)) :
    Isomorphic G H := by
  obtain ⟨e⟩ := h
  refine ⟨{ e with edge_eq := ?_ }⟩
  intro i j
  by_cases eq : i = j
  · subst j; rw [G.loopless,H.loopless]
  · have neq : e.toFun i ≠ e.toFun j := fun bad => eq ((e.leftInv i).symm.trans ((congrArg e.invFun bad).trans (e.leftInv j)))
    have edges := e.edge_eq i j
    cases h1 : G.edge i j <;> cases h2 : H.edge (e.toFun i) (e.toFun j) <;>
      first | rfl | simp [complement,eq,neq,h1,h2] at edges

theorem disconnected_complement_sixteen {G H : Graph 16} (h : ¬(simple (complement G)).Preconnected)
    (q : QuantumIso G H) : Isomorphic G H := iso_of_complement (disconnected_sixteen h (complement_qc q))

private theorem cut_disconnected (G : Graph n) (side : Fin n → Bool)
    (both : Function.Surjective side) (closed : ∀ i j, G.edge i j = true → side i = side j) :
    ¬(simple G).Preconnected := by
  obtain ⟨a,ha⟩ := both false
  obtain ⟨b,hb⟩ := both true
  intro connected
  have reach := ((simple G).reachable_iff_reflTransGen a b).mp (connected a b)
  have eq : side a = side b := by
    clear hb
    induction reach with
    | refl => rfl
    | tail walk edge ih => exact ih.trans (closed _ _ edge)
  simp [ha,hb] at eq

/-- An arbitrary nontrivial cut with constant edge value suffices. This
includes two coherent fibers whose whole cross rectangle has one color. -/
theorem uniform_cut_sixteen {G H : Graph 16} (side : Fin 16 → Bool) (both : Function.Surjective side)
    (value : Bool) (uniform : ∀ i j, side i ≠ side j → G.edge i j = value)
    (q : QuantumIso G H) : Isomorphic G H := by
  cases value with
  | false =>
    apply disconnected_sixteen (cut_disconnected G side both ?_) q
    intro i j adj
    by_contra ne
    simp [uniform i j ne] at adj
  | true =>
    apply disconnected_complement_sixteen (cut_disconnected (complement G) side both ?_) q
    intro i j adj
    by_contra ne
    simp [complement,uniform i j ne] at adj

end QGI.Components
