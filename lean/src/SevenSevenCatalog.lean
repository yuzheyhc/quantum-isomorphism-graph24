import ZivAvCoreCheck

namespace QGI.Coherent.SevenSevenCatalog
open QGI.ZivAv
abbrev V := Fin 7
abbrev M := V → V → Nat
def Uniform (m : M) := ∀ i j, m i j=m 0 0
def Thin (m : M) := ∃ i j, ∀ z, m i z=m i j → z=j
def Fano (m : M) (v w : Nat) :=
  (∀ i j, m i j=v ∨ m i j=w) ∧
  (∀ i, (∑ j, if m i j=v then (1:Nat) else 0)=3) ∧
  (∀ j, (∑ i, if m i j=v then (1:Nat) else 0)=3) ∧
  (∀ j k, (∀ i, m i j=v ↔ m i k=v) → j=k)
def Strong (m : M) := ∃ i j x y, Fano m (m i j) (m x y)
def Shape (m : M) := Uniform m ∨ Thin m ∨ Strong m

def side (swap : Bool) (i : V) : Vertex := ⟨(if swap then 7 else 0)+i.val,by cases swap <;> simp <;> omega⟩
theorem side_inj (swap : Bool) : Function.Injective (side swap) := by
  intro i j e
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))
def diagSize (a : Index) (i : Vertex) :=
  (Finset.univ.filter (fun j => color a j j=color a i i)).card
def cross (a : Index) (swap : Bool) : M := fun i j => color a (side swap i) (side (!swap) j)

theorem halves : ∀ a : Index, (∀ i, diagSize a i=7) →
    (∀ (swap : Bool) i, color a (side swap i) (side swap i)=color a (side swap 0) (side swap 0)) ∧
    color a (side false 0) (side false 0)≠color a (side true 0) (side true 0) := by native_decide

private theorem enumeration : ∀ a : Index, (∀ i, diagSize a i=7) → ∀ swap : Bool,
    (∀ i j, cross a swap i j=cross a swap 0 0) ∨
    (∃ i j, ∀ z, cross a swap i z=cross a swap i j → z=j) ∨
    ∃ j k, Fano (cross a swap) (cross a swap 0 j) (cross a swap 0 k) := by
  unfold Fano
  native_decide

theorem alternatives (a : Index) (sz : ∀ i, diagSize a i=7) (swap) : Shape (cross a swap) := by
  rcases enumeration a sz swap with h|h|⟨j,k,h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨0,j,0,k,h⟩)

theorem transport {m t : M} (u w : Equiv.Perm V)
    (cell : ∀ i j x y, t (u i) (w j)=t (u x) (w y) ↔ m i j=m x y) (shape : Shape m) : Shape t := by
  rcases shape with h|⟨i,j,h⟩|⟨i,j,x,y,pal,row,col,sep⟩
  · left
    have all (i j) : t i j=t (u 0) (w 0) := by
      obtain ⟨i,rfl⟩ := u.surjective i
      obtain ⟨j,rfl⟩ := w.surjective j
      exact (cell ..).mpr (h i j)
    exact fun i j => (all i j).trans (all 0 0).symm
  · right; left; refine ⟨u i,w j,?_⟩
    intro z hz
    obtain ⟨z,rfl⟩ := w.surjective z
    exact congrArg w (h z ((cell ..).mp hz))
  · right; right
    refine ⟨u i,w j,u x,w y,?_,?_,?_,?_⟩
    · intro l r
      obtain ⟨l,rfl⟩ := u.surjective l
      obtain ⟨r,rfl⟩ := w.surjective r
      exact (pal l r).imp (cell ..).mpr (cell ..).mpr
    · intro l
      obtain ⟨l,rfl⟩ := u.surjective l
      rw [← Equiv.sum_comp w (fun k => if t (u l) k=t (u i) (w j) then (1:Nat) else 0)]
      simpa only [cell] using row l
    · intro r
      obtain ⟨r,rfl⟩ := w.surjective r
      rw [← Equiv.sum_comp u (fun k => if t k (w r)=t (u i) (w j) then (1:Nat) else 0)]
      simpa only [cell] using col r
    · intro l r iff
      obtain ⟨l,rfl⟩ := w.surjective l
      obtain ⟨r,rfl⟩ := w.surjective r
      exact congrArg w (sep l r (fun h => (cell ..).symm.trans ((iff (u h)).trans (cell ..))))

end QGI.Coherent.SevenSevenCatalog


