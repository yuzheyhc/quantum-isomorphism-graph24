import EightTwelveSignCliques
import data.EightFourteenFamilies

namespace QGI.EightFourteenWords
abbrev Word := Fin 128
abbrev Axis := Fin 7
abbrev I := Fin 8
abbrev J := Fin 14
abbrev Shape := Fin 30
def word (s : Shape) (i : I) : Word := Fin.ofNat' 128 (((EightFourteenInput.families[s.val]?).getD 0) >>> (7*i.val))
def family (s : Shape) : Finset Word := Finset.univ.image (word s)
def bit (w : Word) (j : Axis) := w.val.testBit j.val
def dist (u v : Word) := (Finset.univ.filter (fun j => bit u j≠bit v j)).card
def truncWord (u : Word) : EightTwelveSigns.Cliques.Word := Fin.ofNat' 64 u.val
def liftWord (u : EightTwelveSigns.Cliques.Word) : Word := Fin.ofNat' 128 (u.val+64*(EightTwelveSigns.Cliques.distance 0 u%2))
def axis (j : J) : Axis := ⟨j.val/2,by omega⟩
def side (j : J) := j.val.testBit 0
def incident (u : Word) (j : J) := decide (bit u (axis j)=side j)
def shift (u t : Word) : Word := Fin.ofNat' 128 (u.val^^^t.val)

theorem encode : ∀ f : Axis → Bool, ∃ w : Word, ∀ j, bit w j=f j := by native_decide
theorem injective_word : ∀ s : Shape, Function.Injective (word s) := by unfold Function.Injective; native_decide
theorem distance_from_common : ∀ u v : Word, (Finset.univ.filter fun j => incident u j=true ∧ incident v j=true).card+dist u v=7 := by native_decide
theorem shift_bit : ∀ u t j, bit (shift u t) j=(bit u j ^^ bit t j) := by native_decide
theorem shift_self : ∀ w : Word, shift w w=0 := by native_decide
theorem shift_dist (u v t : Word) : dist (shift u t) (shift v t)=dist u v := by
  apply congrArg Finset.card; ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,shift_bit]
  cases bit u j <;> cases bit v j <;> cases bit t j <;> decide

private theorem project : ∀ u v : Word, dist u v=4 → truncWord u≠truncWord v ∧ EightTwelveSigns.Cliques.Adj (truncWord u) (truncWord v) := by native_decide
private theorem recover : ∀ u : Word, u=0 ∨ dist 0 u=4 → liftWord (truncWord u)=u := by native_decide
attribute [local irreducible] EightFourteenInput.families EightTwelveSigns.Input.words
private theorem normalized : ∀ s : EightTwelveSigns.Cliques.Shape, 0∈EightTwelveSigns.Cliques.family s → ∃ t : Shape, (EightTwelveSigns.Cliques.family s).image liftWord=family t := by native_decide

theorem classify (w : I → Word) (zero : w 0=0) (sep : ∀ i j, i≠j → dist (w i) (w j)=4) :
    ∃ t : Shape, ∃ e : Equiv.Perm I, ∀ i, w (e i)=word t i := by
  let q := fun i => truncWord (w i)
  have qi : Function.Injective q := fun i j h => Classical.byContradiction (fun ne => (project _ _ (sep i j ne)).1 h)
  let f := Finset.univ.image q
  obtain ⟨s,hs⟩ := EightTwelveSigns.Cliques.exhaustive (f:=f) (by dsimp only [f]; rw [Finset.card_image_of_injective _ qi]; decide) (by
    intro x hx y hy diff
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact (project _ _ (sep i j (fun e => diff (congrArg q e)))).2)
  have z : (0 : EightTwelveSigns.Cliques.Word)∈EightTwelveSigns.Cliques.family s := by
    rw [hs]; exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,congrArg truncWord zero⟩
  obtain ⟨t,ht⟩ := normalized s z
  have back (i) : liftWord (q i)=w i := by
    apply recover; by_cases h : i=0
    · exact Or.inl (h ▸ zero)
    · exact Or.inr (zero ▸ sep 0 i (Ne.symm h))
  have covers (i) : ∃ j, w j=word t i := by
    have mem : word t i∈family t := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [←ht,hs] at mem
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp mem
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨j,(back j).symm.trans eq⟩
  choose e he using covers
  exact ⟨t,Equiv.ofBijective e (Finite.injective_iff_bijective.mp (fun i j eq =>
    injective_word t ((he i).symm.trans ((congrArg w eq).trans (he j))))),he⟩
end QGI.EightFourteenWords
