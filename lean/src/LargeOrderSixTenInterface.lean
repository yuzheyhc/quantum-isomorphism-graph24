import LargeOrderSquareInterface
import RegionalSixTen
import FourByEven

noncomputable section
namespace QGI.Coherent.LargeOrderSixTenInterface
open SixTenCoordinates FourSixSix.Interfaces LargeOrderSquareInterface LargeOrderStrongPaths
open QGI.SixTen.Cross (design rowGram colGram splitModel)
open private twins from RegionalFourFourEight
private def ind (M : A → B → Nat) (v : Nat) (i : A) (j : B) := decide (M i j=v)

private theorem uniform_or_two (M : A → B → Nat) (reg : FiberRectangles.BiregularColors M) :
    (∃ v, ∀ i j, M i j = v) ∨
    (∃ v w, v ≠ w ∧ (∀ i j, M i j = v ∨ M i j = w) ∧
      (∀ i, FiberRectangles.degree (ind M v i) = 5) ∧
      (∀ j, FiberRectangles.degree (fun i => ind M v i j) = 3)) := by
  classical
  let v := M 0 0
  by_cases all : ∀ i j, M i j = v
  · exact Or.inl ⟨v,all⟩
  push_neg at all
  obtain ⟨a,b,hab⟩ := all
  let w := M a b
  let S (k : Nat) (i : A) := Finset.univ.filter (fun j : B => M i j = k)
  have deg (k : Nat) (i : A) : FiberRectangles.degree (ind M k i) = (S k i).card := by
    simp [FiberRectangles.degree,ind,S]
  obtain ⟨r₁,s₁,hr₁,hs₁⟩ := reg v
  obtain ⟨r₂,s₂,hr₂,hs₂⟩ := reg w
  have bal₁ := FiberRectangles.balance (ind M v) hr₁ hs₁
  have bal₂ := FiberRectangles.balance (ind M w) hr₂ hs₂
  have card₁ (i : A) : (S v i).card = r₁ := (deg v i).symm.trans (hr₁ i)
  have card₂ (i : A) : (S w i).card = r₂ := (deg w i).symm.trans (hr₂ i)
  have pos₁ : 0 < r₁ := (card₁ 0) ▸ Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have pos₂ : 0 < r₂ := (card₂ a) ▸ Finset.card_pos.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have disj (i : A) : Disjoint (S v i) (S w i) := by
    refine Finset.disjoint_left.mpr fun j hv hw => ?_
    exact hab ((Finset.mem_filter.mp hw).2.symm.trans (Finset.mem_filter.mp hv).2)
  have size (i : A) : (S v i ∪ S w i).card = r₁+r₂ := by
    rw [Finset.card_union_of_disjoint (disj i),card₁,card₂]
  have bound := Finset.card_le_univ (S v 0 ∪ S w 0)
  rw [size] at bound
  change r₁+r₂ ≤ 10 at bound
  change 6*r₁ = 10*s₁ at bal₁
  change 6*r₂ = 10*s₂ at bal₂
  have num : r₁=5 ∧ s₁=3 ∧ r₂=5 := by omega
  refine Or.inr ⟨v,w,Ne.symm hab,?_,fun i => (hr₁ i).trans num.1,fun j => (hs₁ j).trans num.2.1⟩
  intro i j
  have full : S v i ∪ S w i = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [size,num.1,num.2.2]; decide)
  have mem : j ∈ S v i ∪ S w i := full ▸ Finset.mem_univ _
  simpa only [Finset.mem_union,S,Finset.mem_filter,Finset.mem_univ,true_and] using mem


def DesignAt {n} (c : Fin n → Fin n → Nat) (l v : Nat) :=
  ∃ (S : Shore c l A) (Y : Shore c v B), Block S S Y Y design design

theorem classify {n l r} {c : Fin n → Fin n → Nat} (law : Laws c c) (S : Shore c l A) (Y : Shore c r B) :
    FiberPairExtension.twins c l r ∨ DesignAt c l r := by
  let M := fun i j => c (atPoint S i) (atPoint Y j)
  have mark (s : Nat) : Block S S Y Y (ind M s) (ind M s) := fun ⦃_ _ _ _⦄ h => congrArg (fun u => decide (u=s)) h
  have reg : FiberRectangles.BiregularColors M := fun v =>
    ⟨_,_,fun i => Block.degree_eq law (mark v) i 0,fun j => Block.degree_eq law (Block.flip law (mark v)) j 0⟩
  rcases uniform_or_two M reg with ⟨s,all⟩ | ⟨s,t,st,palette,rows,cols⟩
  · exact Or.inl (twins S Y ⟨fun i x _ _ y => (all i y).trans (all x y).symm,
      fun _ j y _ x => (all x j).trans (all x y).symm⟩)
  obtain ⟨a,b,shape⟩ := QGI.SixTen.Cross.normal (ind M s) rows cols
    (fun i j k => Block.hist_eq law (Block.gram law (mark s)) i j k)
    (fun i j k => Block.hist_eq law (Block.gram law (Block.flip law (mark s))) i j k)
  rcases shape with split | dsg
  · have eq : M=fun i j => if decide ((a i).val<3)=decide ((b j).val<5) then s else t := by
      funext i j
      have bits : M i j=s ↔ decide ((a i).val<3)=decide ((b j).val<5) := by
        calc
          _ ↔ ind M s i j=true := by simp [ind]
          _ ↔ splitModel (a i) (b j)=true := by rw [split]
          _ ↔ _ := by simp [splitModel]
      by_cases h : M i j=s
      · rw [if_pos (bits.mp h),h]
      · rw [if_neg (mt bits.mpr h)]; exact (palette i j).resolve_left h
    apply Or.inl (twins S Y ?_)
    change SplitRectangle.Twins M
    rw [eq]; exact SplitRectangle.twins_of_halves _ _ _ _
  · refine Or.inr ⟨a.symm.trans S,b.symm.trans Y,fun ⦃i j x y⦄ h => ?_⟩
    have ok := (dsg (a.symm i) (b.symm j)).symm.trans
      (((mark s) (i:=a.symm i) (j:=b.symm j) (x:=a.symm x) (y:=b.symm y) h).trans (dsg (a.symm x) (b.symm y)))
    simpa only [Equiv.apply_symm_apply] using ok

private theorem no_design : ∀ h : Equiv.Perm (Fin 6),
    ¬regular (meet (fun j k => design k j) (fun j k => flag j (h k))) 0 := by native_decide

theorem incompatible {n l r u} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (tetra : TetraAt c l u) (design' : DesignAt c u r) : False := by
  obtain ⟨F,L,left⟩ := tetra
  obtain ⟨R,B,right⟩ := design'
  obtain ⟨h,_,reg⟩ := path law B F R L (fun j k => design k j) flag (Block.flip law right) left 0
  exact no_design h reg

end QGI.Coherent.LargeOrderSixTenInterface
