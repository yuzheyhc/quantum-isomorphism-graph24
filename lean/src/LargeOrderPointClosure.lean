import LargeOrderFiveAnchors
import SmallFiberExtension

noncomputable section
namespace QGI.Coherent.LargeOrderPointClosure
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G
local notation "d₀" => targetName p

def MapOn (X : Finset (Fin n)) := ∃ f : Fin n → Fin n,
  ∀ i∈X, ∀ j∈X, c₀ i j=d₀ (f i) (f j)

structure Closed (c : Fin n → Fin n → Nat) (X : Finset (Fin n)) : Prop where
  one : ∀ x∈X, ∀ a, ∀ P : Nat → Prop, (∀ z, P (c x z) ↔ z=a) → a∈X
  two : ∀ x∈X, ∀ r∈X, ∀ a, a≠r → ∀ P : Nat → Prop, (∀ z, P (c x z) ↔ z=r ∨ z=a) → a∈X

private theorem insert_point {X : Finset (Fin n)} {a b : Fin n} (f : Fin n → Fin n)
    (h : ∀ i∈X, ∀ j∈X, c₀ i j=d₀ (f i) (f j)) (x : Fin n) (hx : x∈X)
    (links : ∀ j∈X, c₀ a j=d₀ b (f j)) : MapOn p (insert a X) := by
  classical
  by_cases mem : a∈X
  · rw [Finset.insert_eq_of_mem mem]; exact ⟨f,h⟩
  let g := fun i => if i=a then b else f i
  have old (i : Fin n) (hi : i∈X) : g i=f i := by
    apply if_neg
    rintro rfl
    exact mem hi
  have added : g a=b := if_pos rfl
  refine ⟨g,fun i hi j hj => ?_⟩
  rcases Finset.mem_insert.mp hi with ei|oi <;> rcases Finset.mem_insert.mp hj with ej|oj
  · rw [ei,ej,added]; exact (SmallShore.endpoints p (links x hx)).1
  · rw [ei,added,old _ oj]; exact links _ oj
  · rw [ej,old _ oi,added]; exact common_transpose p (links _ oi)
  · rw [old _ oi,old _ oj]; exact h i oi j oj

private theorem add_one {X : Finset (Fin n)} (real : MapOn p X) (x : Fin n) (hx : x∈X) (a : Fin n)
    (P : Nat → Prop) (one : ∀ z, P (c₀ x z) ↔ z=a) : MapOn p (insert a X) := by
  obtain ⟨f,h⟩ := real
  obtain ⟨e,he⟩ := (commonLaws p).middle (h x hx x hx)
  have only (z) : P (d₀ (f x) z) ↔ z=e a := by
    obtain ⟨k,rfl⟩ := e.surjective z
    rw [←(he k).1,one,e.injective.eq_iff]
  apply insert_point p f h x hx
  intro j hj
  obtain ⟨t,ht⟩ := (commonLaws p).middle (h x hx j hj)
  have fixed : t a=e a := (only _).mp ((ht a).1 ▸ (one a).mpr rfl)
  exact (ht a).2.trans (congrArg (fun z => d₀ z (f j)) fixed)

private theorem add_two {X : Finset (Fin n)} (real : MapOn p X) (x : Fin n) (hx : x∈X)
    (r : Fin n) (hr : r∈X) (a : Fin n) (ne : a≠r) (P : Nat → Prop)
    (two : ∀ z, P (c₀ x z) ↔ z=r ∨ z=a) : MapOn p (insert a X) := by
  classical
  obtain ⟨f,h⟩ := real
  obtain ⟨e,he⟩ := (commonLaws p).middle (h x hx x hx)
  have only (z) : P (d₀ (f x) z) ↔ z=e r ∨ z=e a := by
    obtain ⟨k,rfl⟩ := e.surjective z
    rw [←(he k).1,two,e.injective.eq_iff,e.injective.eq_iff]
  have choice : ∃ b, b≠f r ∧ ∀ z, P (d₀ (f x) z) ↔ z=f r ∨ z=b := by
    rcases (only _).mp ((h x hx r hr) ▸ (two r).mpr (Or.inl rfl)) with eq|eq
    · exact ⟨e a,by rw [eq]; exact fun q => ne (e.injective q),fun z => by rw [eq]; exact only z⟩
    · exact ⟨e r,by rw [eq]; exact fun q => ne (e.injective q.symm),fun z => by rw [eq]; exact (only z).trans or_comm⟩
  obtain ⟨b,bne,targets⟩ := choice
  apply insert_point p (b:=b) f h x hx
  intro j hj
  obtain ⟨t,ht⟩ := (commonLaws p).middle (h x hx j hj)
  have aa := (targets (t a)).mp (by rw [←(ht a).1]; exact (two a).mpr (Or.inr rfl))
  have rr := (targets (t r)).mp (by rw [←(ht r).1]; exact (two r).mpr (Or.inl rfl))
  rcases aa with ar|ab
  · have rb := rr.resolve_left (fun q => ne (t.injective (ar.trans q.symm)))
    calc c₀ a j = d₀ (t a) (f j) := (ht a).2
         _ = d₀ (f r) (f j) := congrArg (fun z => d₀ z (f j)) ar
         _ = c₀ r j := (h r hr j hj).symm
         _ = d₀ (t r) (f j) := (ht r).2
         _ = d₀ b (f j) := congrArg (fun z => d₀ z (f j)) rb
  · exact (ht a).2.trans (congrArg (fun z => d₀ z (f j)) ab)

theorem anchors {k : Nat} (u v : Fin k → Fin n)
    (names : ∀ i j, c₀ (u i) (u j)=d₀ (v i) (v j)) : MapOn p (Finset.univ.image u) := by
  classical
  let f (x : Fin n) := if h : ∃ i, u i=x then v h.choose else x
  have point (x) (hx : x∈Finset.univ.image u) : ∃ i, u i=x ∧ v i=f x := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    have ex : ∃ j, u j=x := ⟨i,hi⟩
    exact ⟨ex.choose,ex.choose_spec,by simp only [f,dif_pos ex]⟩
  refine ⟨f,fun i hi j hj => ?_⟩
  obtain ⟨a,ha,ka⟩ := point i hi
  obtain ⟨b,hb,kb⟩ := point j hj
  simpa only [ha,hb,ka,kb] using names a b

theorem solve (reg : Nat → Prop) (seeds : Finset (Fin n)) (initial : MapOn p seeds)
    (generate : ∀ X, seeds ⊆ X → Closed c₀ X → vertices c₀ reg ⊆ X) : Realizes p reg := by
  classical
  let sets := Finset.univ.filter (fun X => seeds ⊆ X ∧ MapOn p X)
  have member (X) : X∈sets ↔ seeds ⊆ X ∧ MapOn p X := by simp [sets]
  obtain ⟨X,hX,maximum⟩ := Finset.exists_max_image sets Finset.card ⟨seeds,(member _).mpr ⟨Finset.Subset.rfl,initial⟩⟩
  obtain ⟨sub,real⟩ := (member _).mp hX
  have stop (a) (add : MapOn p (insert a X)) : a∈X := by
    by_contra no
    have bound := maximum (insert a X) ((member _).mpr ⟨sub.trans (Finset.subset_insert _ _),add⟩)
    rw [Finset.card_insert_of_not_mem no] at bound
    omega
  have all := generate X sub ⟨fun x hx a P h => stop a (add_one p real x hx a P h),
    fun x hx r hr a ne P h => stop a (add_two p real x hx r hr a ne P h)⟩
  obtain ⟨f,h⟩ := real
  obtain ⟨e,he⟩ := bundle p reg (fun x => f x.val) (fun i j => h i.val (all i.property) j.val (all j.property))
  exact ⟨e,fun i j => by rw [he,he]; exact h i.val (all i.property) j.val (all j.property)⟩

end QGI.Coherent.LargeOrderPointClosure
