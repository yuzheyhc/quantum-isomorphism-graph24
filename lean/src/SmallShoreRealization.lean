import StrategyColorLaws
import SmallConfigurationInput
import SmallShoreLocal

noncomputable section
namespace QGI.Literature
open Coherent.SmallShore

/-- Ziv-Av, *Enumeration of coherent configurations of order at most 15*
(2018), §2.2 and Tables 2–3: below order 14 there are no proper algebraic
automorphisms, and the first algebraically isomorphic nonisomorphic types
occur at order 16. Applied to homogeneous configurations with their used
relations in common names, any particular multiplication-table isomorphism
is induced by a point map. https://actamath.savbb.sk/pdf/aumb2605.pdf -/
theorem zivAv_named_small_scheme {k : Nat} (positive : 0 < k) (small : k ≤ 13) {c b : Table k}
    {d : Nat} (hc : Local c d) (hb : Local b d)
    (used : ∀ s, (∃ i j, c i j = s) ↔ ∃ x y, b x y = s)
    (products : ∀ s t i j x y, c i j = b x y →
      Coherent.StrategyColorLaws.count c s t i j = Coherent.StrategyColorLaws.count b s t x y) :
    ∃ e : Equiv.Perm (Fin k), ∀ i j, c i j = b (e i) (e j) :=
  zivAv_named_small_configuration positive small hc.configuration hb.configuration used products

/-- Ziv-Av (2018), Table 1, lists total and Schurian coherent configurations
in orders 1–15. In orders 1–13 the columns coincide. A homogeneous
Schurian configuration is the orbital partition of a transitive group. -/
theorem zivAv_transitive_small_scheme {k : Nat} (positive : 0 < k) (small : k ≤ 13)
    {c : Table k} {d : Nat} (hc : Local c d) (i j : Fin k) :
    ∃ e : Equiv.Perm (Fin k), e i = j ∧ ∀ x y, c x y = c (e x) (e y) := by
  have diag := ((hc.diag i i).mpr rfl).trans ((hc.diag j j).mpr rfl).symm
  obtain ⟨e, point, _, colors⟩ := zivAv_small_relation_transitive positive small hc.configuration i i j j diag
  exact ⟨e, point, colors⟩

end QGI.Literature

namespace QGI.Coherent.SmallShore
open StrategyColorLaws

def restrict {n k : Nat} (c : Table n) (f : Fin k → Fin n) : Table k :=
  fun i j => c (f i) (f j)

private theorem count_restrict {k n : Nat} {c : Table n} {f : Fin k → Fin n}
    (hf : Function.Injective f) {d : Nat} (sh : ∀ z, (∃ i, f i = z) ↔ c z z = d)
    (ends : ∀ i j x y, c i j = c x y → c j j = c y y) {s : Nat}
    (used : ∃ i j, restrict c f i j = s) (t : Nat) (i j : Fin k) :
    count (restrict c f) s t i j = count c s t (f i) (f j) := by
  classical
  obtain ⟨a,b,rfl⟩ := used
  let value := fun z => if c (f i) z = restrict c f a b ∧ c z (f j) = t then 1 else 0
  change (∑ z, value (f z)) = ∑ z, value z
  apply Fintype.sum_of_injective f hf (fun z => value (f z)) value _ (fun _ => rfl)
  intro z outside
  have no : c (f i) z ≠ restrict c f a b := fun eq =>
    outside ((sh z).mpr ((ends _ _ _ _ eq).trans ((sh (f b)).mp ⟨b,rfl⟩)))
  simp [value,no]

private theorem local_of_restriction {k n : Nat} (c : Table n) (f : Fin k → Fin n)
    (hf : Function.Injective f) {d : Nat} (sh : ∀ z, (∃ i, f i = z) ↔ c z z = d)
    (diag : ∀ i j x, c i j = c x x → i = j)
    (rev : ∀ i j x y, c i j = c x y → c j i = c y x)
    (ends : ∀ i j x y, c i j = c x y → c j j = c y y)
    (prod : DoubleEight.FixedInterface.HasIntersectionNumbers c) : Local (restrict c f) d := by
  refine ⟨fun i j => ?_, fun _ _ _ _ eq => rev _ _ _ _ eq,?_⟩
  · have atI := (sh (f i)).mp ⟨i,rfl⟩
    exact ⟨fun h => hf (diag _ _ _ (h.trans atI.symm)),fun e => e ▸ (sh (f j)).mp ⟨j,rfl⟩⟩
  intro s t i j x y same
  change count (restrict c f) s t i j = count (restrict c f) s t x y
  by_cases used : ∃ i j, restrict c f i j = s
  · rw [count_restrict hf sh ends used, count_restrict hf sh ends used]
    exact prod s t _ _ _ _ same
  · push_neg at used
    simp [count,used]

variable {n : Nat} {G H : Graph n} {K : Type}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

private theorem ends_left {i j x y : Fin n} (eq : Relations.color (closure G) i j = targetName p x y) :
    Relations.color (closure G) i i = targetName p x x := by
  let c := Relations.color (closure G)
  let b := targetName p
  have balance := common_products p (c i i) (c i j) eq
  have hp : 0 < (Finset.univ.filter (fun z => c i z = c i i ∧ c z j = c i j)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩⟩
  have same : (Finset.univ.filter (fun z => c i z = c i i ∧ c z j = c i j)).card =
      (Finset.univ.filter (fun z => b x z = c i i ∧ b z y = c i j)).card := by
    simpa only [count,Finset.sum_boole] using balance
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (hp.trans_eq same)
  have h := (Finset.mem_filter.mp hz).2.1.symm
  have id := entries p h (closure H).one_mem (Intertwiner.initial_diagonal p)
  have xz : x = z := by by_contra ne; simp [Matrix.one_apply,ne] at id
  exact xz ▸ h

/-- Corresponding endpoint colors determine the diagonal names at both ends. -/
theorem endpoints {i j x y : Fin n} (eq : Relations.color (closure G) i j = targetName p x y) :
    Relations.color (closure G) i i = targetName p x x ∧
    Relations.color (closure G) j j = targetName p y y :=
  ⟨ends_left p eq,ends_left p (common_transpose p eq)⟩

/-- The two restrictions to matched fibers have the same used color names
and the same restricted intersection counts. This statement is independent of order. -/
theorem correspondence {k : Nat} (f g : Fin k → Fin n) (d : Nat) (hf : Function.Injective f) (hg : Function.Injective g)
    (sf : ∀ z, (∃ i, f i = z) ↔ Relations.color (closure G) z z = d)
    (sg : ∀ z, (∃ i, g i = z) ↔ targetName p z z = d) :
    Local (restrict (Relations.color (closure G)) f) d ∧ Local (restrict (targetName p) g) d ∧
    (∀ a, (∃ i j, Relations.color (closure G) (f i) (f j)=a) ↔ ∃ x y, targetName p (g x) (g y)=a) ∧
    (∀ a b i j x y, Relations.color (closure G) (f i) (f j)=targetName p (g x) (g y) →
      count (restrict (Relations.color (closure G)) f) a b i j = count (restrict (targetName p) g) a b x y) := by
  classical
  let c := Relations.color (closure G)
  let b := targetName p
  have ce (i j x y : Fin n) (h : c i j = c x y) := (Relations.end_colors (closure G) h).2
  have be (i j x y : Fin n) (h : b i j = b x y) : b j j = b y y :=
    (target_same p _ _ _ _).mpr (Relations.end_colors (closure H) ((target_same p _ _ _ _).mp h)).2
  have lc : Local (restrict c f) d := local_of_restriction c f hf sf
    (fun _ _ _ eq => Relations.diagonal _ eq) (fun _ _ _ _ eq => Relations.transpose _ eq) ce (Relations.products _)
  have lb : Local (restrict b g) d := local_of_restriction b g hg sg
    (fun _ _ _ eq => Relations.diagonal _ ((target_same p _ _ _ _).mp eq))
    (fun _ _ _ _ eq => (target_same p _ _ _ _).mpr (Relations.transpose _ ((target_same p _ _ _ _).mp eq))) be
    (DoubleEight.FixedInterface.rename_products (fun i j x y => (target_same p i j x y).symm) (Relations.products _))
  have used (a : Nat) : (∃ i j, restrict c f i j = a) ↔ ∃ x y, restrict b g x y = a := by
    constructor
    · rintro ⟨i,j,rfl⟩
      obtain ⟨x,y,hit⟩ := StrategyColors.exists_target p (f i) (f j)
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨l,r⟩ := endpoints p eq
      obtain ⟨i',rfl⟩ := (sg x).mpr (l.symm.trans ((sf _).mp ⟨i,rfl⟩))
      obtain ⟨j',rfl⟩ := (sg y).mpr (r.symm.trans ((sf _).mp ⟨j,rfl⟩))
      exact ⟨i',j',eq.symm⟩
    · rintro ⟨x,y,rfl⟩
      obtain ⟨i,j,hit⟩ := StrategyColors.exists_source p (g x) (g y)
      have eq := (associated p).mpr (StrategyColors.maps_support p hit)
      obtain ⟨l,r⟩ := endpoints p eq
      obtain ⟨i',rfl⟩ := (sf i).mpr (l.trans ((sg _).mp ⟨x,rfl⟩))
      obtain ⟨j',rfl⟩ := (sf j).mpr (r.trans ((sg _).mp ⟨y,rfl⟩))
      exact ⟨i',j',eq⟩
  refine ⟨lc,lb,used,?_⟩
  intro a t i j x y same
  change count (restrict c f) a t i j = count (restrict b g) a t x y
  by_cases hit : ∃ i j, restrict c f i j = a
  · rw [count_restrict hf sf ce hit, count_restrict hg sg be ((used _).mp hit)]
    exact common_products p _ _ same
  · have miss := mt (used _).mpr hit
    push_neg at hit miss
    simp [count,hit,miss]

/-- Point coordinates can be any injections onto the matched fibers. The
realization induces the prescribed names and also sends one specified
point to one specified image. -/
theorem realize_at {k : Nat} (positive : 0 < k) (small : k ≤ 13)
    (f g : Fin k → Fin n) (d : Nat) (hf : Function.Injective f) (hg : Function.Injective g)
    (sf : ∀ z, (∃ i, f i = z) ↔ Relations.color (closure G) z z = d)
    (sg : ∀ z, (∃ i, g i = z) ↔ targetName p z z = d) (u v : Fin k) :
    ∃ e : Equiv.Perm (Fin k), e u = v ∧
      ∀ i j, Relations.color (closure G) (f i) (f j) = targetName p (g (e i)) (g (e j)) := by
  obtain ⟨lc,lb,used,products⟩ := correspondence p f g d hf hg sf sg
  obtain ⟨e,he⟩ := Literature.zivAv_named_small_scheme positive small lc lb used products
  obtain ⟨fix,atPoint,colors⟩ := Literature.zivAv_transitive_small_scheme positive small lb (e u) v
  exact ⟨e.trans fix,atPoint,fun i j => (he i j).trans (colors _ _)⟩

end QGI.Coherent.SmallShore