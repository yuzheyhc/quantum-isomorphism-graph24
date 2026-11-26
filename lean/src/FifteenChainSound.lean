import FifteenChain
import Mathlib.Data.List.Count

namespace QGI.Fifteen.System
open private get_ofFn perm_of_equiv sorted_eq from DoubleEightPrepared
variable {n r : Nat} {s : System r n}
local instance {n : Nat} : BEq (Fin n × Fin n) := instBEqOfDecidableEq
abbrev Implements (s : System r n) (e : Equiv.Perm (Fin r)) (h : Equiv.Perm (Fin n)) :=
  ∀ i j, e (s.name i j) = s.name (h i) (h j)

structure Laws (s : System r n) (e : Equiv.Perm (Fin r)) : Prop where
  diagonal : ∀ i j u v, e (s.name i j) = s.name u v → (i=j ↔ u=v)
  reverse : ∀ i j u v, e (s.name i j) = s.name u v → e (s.name j i) = s.name v u
  middle : ∀ i j u v, e (s.name i j) = s.name u v →
    ∃ h : Equiv.Perm (Fin n), ∀ z,
      e (s.name i z) = s.name u (h z) ∧ e (s.name z j) = s.name (h z) v

private theorem unsend (e a : Equiv.Perm (Fin r)) (p : Equiv.Perm (Fin n))
    (laws : s.Laws e) (rep : s.Implements a p) : s.Laws (e.trans a.symm) := by
  have match' {i j u v} (eq : (e.trans a.symm) (s.name i j) = s.name u v) :
      e (s.name i j) = s.name (p u) (p v) := (a.symm_apply_eq.mp eq).trans (rep u v)
  refine ⟨fun i j u v eq => (laws.diagonal _ _ _ _ (match' eq)).trans p.injective.eq_iff,?_,?_⟩
  · intro i j u v eq
    exact a.symm_apply_eq.mpr ((laws.reverse _ _ _ _ (match' eq)).trans (rep v u).symm)
  · intro i j u v eq
    obtain ⟨m,hm⟩ := laws.middle _ _ _ _ (match' eq)
    refine ⟨m.trans p.symm,fun z => ⟨a.symm_apply_eq.mpr ?_,a.symm_apply_eq.mpr ?_⟩⟩
    · simpa using ((hm z).1.trans (by simpa using (rep u (p.symm (m z))).symm))
    · simpa using ((hm z).2.trans (by simpa using (rep (p.symm (m z)) v).symm))

private theorem list_of_vector {α : Type} {n} (v : Vector α n) :
    List.ofFn v.get = v.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Vector.get]

private theorem idx_map (e : Equiv.Perm (Fin r)) (base : List (Fin r)) (k : Fin r) :
    (base.map e).idxOf (e k) = base.idxOf k := by
  induction base with
  | nil => rfl
  | cons x xs ih => simp [List.idxOf_cons,cond_eq_if,e.injective.eq_iff,ih]

private theorem step_eq (e : Equiv.Perm (Fin r)) (laws : s.Laws e)
    (spots : ∀ k, s.name (s.spot k).1 (s.spot k).2 = k)
    (v w : Vector Nat r) (old : ∀ i, v.get i = w.get (e i)) (k : Fin r) :
    (s.step s.features v).get k = (s.step s.features w).get (e k) := by
  have atEq := (congrArg e (spots k)).trans (spots (e k)).symm
  have tr := laws.reverse _ _ _ _ atEq
  obtain ⟨p,hp⟩ := laws.middle _ _ _ _ atEq
  let A := fun z : (Fin n) => (s.name (s.spot k).1 z,s.name z (s.spot k).2)
  let B := fun z : (Fin n) => (s.name (s.spot (e k)).1 z,s.name z (s.spot (e k)).2)
  let f := e.prodCongr e
  have same (z) : f (A z) = B (p z) := Prod.ext (hp z).1 (hp z).2
  have perms : ((List.ofFn A).map f).Perm (List.ofFn B) := by
    rw [List.map_ofFn]
    exact perm_of_equiv p _ _ same
  have counts (z) : (List.ofFn A).count (A z) = (List.ofFn B).count (B (p z)) := by
    rw [←same]
    exact (List.count_map_of_injective (List.ofFn A) f f.injective (A z)).symm.trans
      (perms.count_eq (f (A z)))
  let term := fun (v : Vector Nat r) (F : (Fin n) → Fin r × Fin r) (z : (Fin n)) =>
    hash [v.get (F z).1,v.get (F z).2,(List.ofFn F).count (F z)]
  have sub := perm_of_equiv p (term v A) (term w B) (fun z => by
    simp only [term,old,counts,hp,A,B])
  have ordered : sorted (List.ofFn (term v A)) = sorted (List.ofFn (term w B)) := sorted_eq sub
  have expr (k' : Fin r) (v' : Vector Nat r) :
      (s.step s.features v').get k' = hash (v'.get k' :: v'.get (s.rev k') ::
        sorted (List.ofFn (term v' (fun z => (s.name (s.spot k').1 z,s.name z (s.spot k').2))))) := by
    simp only [step,get_ofFn,features,paths,Vector.toList_map,Vector.toList_ofFn,
      List.map_map,List.map_ofFn,term,Function.comp_apply]
    rfl
  rw [expr,expr,old,old,show e (s.rev k) = s.rev (e k) from tr,ordered]

private theorem keys_eq (e : Equiv.Perm (Fin r)) (laws : s.Laws e)
    (spots : ∀ k, s.name (s.spot k).1 (s.spot k).2 = k) (base : List (Fin r)) :
    ∀ k, (s.keys s.features base).get k = (s.keys s.features (base.map e)).get (e k) := by
  have start : ∀ k, (s.initial base).get k = (s.initial (base.map e)).get (e k) := by
    intro k
    have eq := (congrArg e (spots k)).trans (spots (e k)).symm
    have tr : e (s.rev k) = s.rev (e k) := laws.reverse _ _ _ _ eq
    have fixed : (s.rev k=k) ↔ s.rev (e k)=e k := by rw [←tr,e.injective.eq_iff]
    have diag := laws.diagonal _ _ _ _ eq
    simp only [initial,get_ofFn,List.mem_map, e.injective.eq_iff,exists_eq_right,idx_map,
      decide_eq_decide.mpr diag,decide_eq_decide.mpr fixed]
  exact step_eq e laws spots _ _ (step_eq e laws spots _ _ (step_eq e laws spots _ _ start))

private theorem mark_eq (e : Equiv.Perm (Fin r)) (laws : s.Laws e)
    (spots : ∀ k, s.name (s.spot k).1 (s.spot k).2 = k) (base : List (Fin r)) (k : Fin r) :
    s.mark s.features base k = s.mark s.features (base.map e) (e k) := by
  have h := keys_eq e laws spots (base ++ [k])
  simp only [List.map_append,List.map_cons,List.map_nil] at h
  have perm := perm_of_equiv e _ _ h
  simp only [list_of_vector] at perm
  exact congrArg hash (sorted_eq perm)

theorem check_sound (spots : ∀ k, s.name (s.spot k).1 (s.spot k).2 = k)
    (chain : Chain r) (base : List (Fin r)) (ok : s.check s.features base chain=true)
    (e : Equiv.Perm (Fin r)) (laws : s.Laws e) (fixed : ∀ k ∈ base, e k = k) :
    ∃ h : Equiv.Perm (Fin n), s.Implements e h := by
  induction chain generalizing base e with
  | nil =>
    have map_eq : base.map e = base := List.map_congr_left fixed |>.trans (List.map_id base)
    have invariant := keys_eq e laws spots base
    rw [map_eq] at invariant
    have unique := of_decide_eq_true ok
    exact ⟨Equiv.refl _,fun i j => (unique _ _ (invariant (s.name i j))).symm⟩
  | cons head rest ih =>
    obtain ⟨x,ws⟩ := head
    obtain ⟨pass,next⟩ := Bool.and_eq_true_iff.mp ok
    by_cases equal : e x=x
    · apply ih _ next e laws
      intro k hk
      rcases List.mem_append.mp hk with h|h
      · exact fixed k h
      · obtain rfl := List.mem_singleton.mp h
        exact equal
    · have map_eq : base.map e = base := List.map_congr_left fixed |>.trans (List.map_id base)
      have invariant := keys_eq e laws spots base
      rw [map_eq] at invariant
      have m := mark_eq e laws spots base x
      rw [map_eq] at m
      have h := List.all_eq_true.mp pass (e x) (List.mem_finRange _)
      simp only [beq_iff_eq,Bool.or_eq_true,bne_iff_ne,List.any_eq_true,decide_eq_true_eq,
        eq_comm (a:=x) (b:=e x),equal,false_or,invariant x,m,ne_eq,not_true_eq_false] at h
      obtain ⟨w,_,good⟩ := h
      obtain ⟨image,stab,ip,ia,point_ok⟩ := good
      let a := Equiv.ofBijective (s.action w) (Finite.injective_iff_bijective.mp ia)
      let p := Equiv.ofBijective (point w) (Finite.injective_iff_bijective.mp ip)
      have impl : s.Implements a p := point_ok
      have newer : ∀ k ∈ base ++ [x], (e.trans a.symm) k=k := by
        intro k hk
        apply a.symm_apply_eq.mpr
        rcases List.mem_append.mp hk with h|h
        · exact (fixed k h).trans (stab k h).symm
        · obtain rfl := List.mem_singleton.mp h
          exact image.symm
      obtain ⟨h,ih'⟩ := ih _ next _ (unsend e a p laws impl) newer
      refine ⟨h.trans p,fun i j => ?_⟩
      exact (a.symm_apply_eq.mp (ih' i j)).trans (impl _ _)

end QGI.Fifteen.System
