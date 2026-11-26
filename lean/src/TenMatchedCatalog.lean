import TenMatchedTransport

namespace QGI.TenPointCross.MatchedCatalog
abbrev Q := Fin 5
def together (a : Key) (z i j : V) := i=j ∨ cell a i j=cell a 0 z
instance (a : Key) (z i j : V) : Decidable (together a z i j) := by unfold together; infer_instance

def sees (a : Key) (z u t : V) := ∃ y : V, ∀ x k : V, cell a x y=cell a k y →
    ((together a z x u ∨ together a z x t) ↔ (together a z k u ∨ together a z k t))
def Rich (a : Key) (z : V) := ∀ u t : V, ¬together a z u t → sees a z u t
instance (a : Key) (z : V) : Decidable (Rich a z) := by unfold Rich sees; infer_instance

attribute [local irreducible] matrices
theorem valid : ∀ (a : Key) (z : V), z≠0 →
    (∀ i, (Finset.univ.filter (fun j => together a z i j)).card=2) →
    (∀ i j, together a z i j → together a z j i) →
    Rich a z ∨ ((a=1 ∨ a=5) ∧ z=1) := by native_decide
theorem occurs : ∀ (a : Key) (i z : V), ∃ j, cell a i j=cell a 0 z := by native_decide
theorem diagonal : ∀ (a : Key) (i j x : V), cell a i j=cell a x x ↔ i=j := by native_decide

def site (a : Key) (q : Q) (b : Bool) : V :=
  if a=1 then Fin.ofNat' 10 (2*q.val+b.toNat)
  else if q=0 then Fin.ofNat' 10 b.toNat
  else Fin.ofNat' 10 (q.val+if b then 5 else 1)
def flatName (a : Key) (i j : Q) (s t : Bool) :=
  if i=j then (if s=t then 0 else 1) else if a=1 ∨ s=t then 2 else 3

theorem flat : ∀ (a : Key), a=1 ∨ a=5 →
    Function.Bijective (fun x : Q × Bool => site a x.1 x.2) ∧
    (∀ i j s t, cell a (site a i s) (site a j t)=flatName a i j s t) ∧
    (∀ i j s t, together a 1 (site a i s) (site a j t) ↔ i=j) := by
  unfold Function.Bijective Function.Injective Function.Surjective
  native_decide

end QGI.TenPointCross.MatchedCatalog

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross TenPointCross.MatchedCatalog TenPointCrossLaws
open SixTenCoordinates (Shore atPoint Laws)
def Detects {n l : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l V) (q : V → Q) :=
  ∀ a b : Q, a≠b → ∃ y : V, ∀ i k : V, c (atPoint F i) (atPoint F y)=c (atPoint F k) (atPoint F y) →
    ((q i=a ∨ q i=b) ↔ (q k=a ∨ q k=b))

theorem local_cases {n l r v : Nat} {c : Fin n → Fin n → Nat} {F : Shore c l V} {Y : Shore c r V}
    (S : Pairs F Y v) (law : Laws c c) {a : Key} (ch : ∀ i j x y, c (atPoint F i) (atPoint F j)=c (atPoint F x) (atPoint F y)
      ↔ cell a i j=cell a x y) :
    Detects F S.left ∨ ((a=1 ∨ a=5) ∧ ∀ i j, S.left i=S.left j ↔ together a 1 i j) := by
  have two := S.left_two (S.left 0)
  have extra : ∃ z : V, z≠0 ∧ S.left z=S.left 0 := by
    by_contra! h
    have incl : Finset.univ.filter (fun i => S.left i=S.left 0) ⊆ {0} := fun i hi =>
      Finset.mem_singleton.mpr (by by_contra ne; exact h i ne (Finset.mem_filter.mp hi).2)
    have le := Finset.card_le_card incl
    rw [two,Finset.card_singleton] at le
    omega
  obtain ⟨z,ne,eq⟩ := extra
  have inside {i j : V} (h : cell a i j=cell a 0 z) : S.left i=S.left j :=
    (internal S S law ((ch i j 0 z).mpr h)).mpr eq.symm
  have both (i j : V) : S.left i=S.left j ↔ together a z i j := by
    refine ⟨?_,fun h => h.elim (fun e => congrArg S.left e) inside⟩
    intro h
    obtain ⟨k,hk⟩ := occurs a i z
    have different : i≠k := by rintro rfl; exact ne ((diagonal a 0 z i).mp hk.symm).symm
    let set := Finset.univ.filter (fun x => S.left x=S.left i)
    have pair : ({i,k} : Finset V)=set := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; rcases Finset.mem_insert.mp hx with h|h
        · subst x; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
        · have ex := Finset.mem_singleton.mp h; subst x
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(inside hk).symm⟩
      · change set.card≤_; rw [show set.card=2 from S.left_two _,Finset.card_pair different]
    have mem : j∈set := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.symm⟩
    rw [←pair] at mem
    rcases Finset.mem_insert.mp mem with h|h
    · exact Or.inl h.symm
    · exact Or.inr (Finset.mem_singleton.mp h ▸ hk)
  have sizes (i) : (Finset.univ.filter (fun j => together a z i j)).card=2 := by
    simpa only [←both,eq_comm (a:=S.left i)] using S.left_two (S.left i)
  rcases valid a z ne sizes (fun i j h => (both j i).mp ((both i j).mpr h).symm) with rich|⟨keys,rfl⟩
  · left
    intro s t st
    obtain ⟨i,rfl⟩ := label_onto S.left_two s
    obtain ⟨j,rfl⟩ := label_onto S.left_two t
    obtain ⟨y,hy⟩ := rich i j (fun h => st ((both i j).mpr h))
    exact ⟨y,fun x k h => by simpa only [←both] using hy x k ((ch x y k y).mp h)⟩
  · exact Or.inr ⟨keys,both⟩

end QGI.Coherent.TenPointMatched
