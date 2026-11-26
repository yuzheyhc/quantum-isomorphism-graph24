import FourHalfOrientation
import FourHalfChart
import FourPointGeneral

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog (Four Eight Col dot comp)
open SixTenCoordinates StrategyColorLaws SmallUnion SmallFiberExtension FourTwelveCycle
open FourTwelveFunctional (source)

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
   (p : PerfectStrategy G H K)

abbrev markColumn {c : Fin n → Fin n → Nat} (F : Shore c l Four) (Y : Shore c r Eight) (a : Nat) : Eight → Col :=
  fun j i => decide (c (atPoint F i) (atPoint Y j)=a)

/-- Equal entries in a twin rectangle with two names force identical columns.
When no entries agree, the two membership vectors are complementary. -/
theorem col_parts (F : Shore (source G) l Four) (Y : Shore (source G) r Eight)
    (a z : Nat) (two : ∀ i j, source G (atPoint F i) (atPoint Y j)=a ∨ source G (atPoint F i) (atPoint Y j)=z)
    (tw : FiberPairExtension.twins (source G) l r) (j : Eight) :
    markColumn F Y a j=markColumn F Y a 0 ∨ markColumn F Y a j=comp (markColumn F Y a 0) := by
  classical
  let t (i : Four) (k : Eight) := source G (atPoint F i) (atPoint Y k)
  by_cases h : ∃ i, t i j=t i 0
  · obtain ⟨i,e⟩ := h
    exact Or.inl (funext (fun k => congrArg (fun u => decide (u=a)) (tw.2 (F i) (Y j) (Y 0) e (F k))))
  · right
    funext i
    have ne : t i j≠t i 0 := fun e => h ⟨i,e⟩
    change decide (t i j=a)= !decide (t i 0=a)
    have diff {u v : Nat} (hu : u=a ∨ u=z) (hv : v=a ∨ v=z) (neq : u≠v) :
        decide (u=a)= !decide (v=a) := by
      have back := Ne.symm neq
      rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> simp_all
    exact diff (two i j) (two i 0) ne

theorem palette_target (F : Shore (source G) l Four) (Y : Shore (source G) r Eight)
    (T : Shore (targetName p) l Four) (Z : Shore (targetName p) r Eight)
    (a b : Nat) (h : ∀ i j, source G (atPoint F i) (atPoint Y j)=a ∨ source G (atPoint F i) (atPoint Y j)=b)
    (i : Four) (j : Eight) : targetName p (atPoint T i) (atPoint Z j)=a ∨ targetName p (atPoint T i) (atPoint Z j)=b := by
  obtain ⟨u,v,hit⟩ := StrategyColors.exists_source p (atPoint T i) (atPoint Z j)
  have eq := (associated p).mpr (StrategyColors.maps_support p hit)
  obtain ⟨du,dv⟩ := SmallShore.endpoints p eq
  have hu := du.trans (T i).property
  have hv := dv.trans (Z j).property
  have left := h (F.symm ⟨u,hu⟩) (Y.symm ⟨v,hv⟩)
  simpa only [atPoint,Equiv.apply_symm_apply,eq] using left

theorem col_names (F : Shore (source G) l Four) (Y : Shore (source G) r Eight)
    (T : Shore (targetName p) l Four) (Z : Shore (targetName p) r Eight)
    (a b : Nat) (h : ∀ i j, source G (atPoint F i) (atPoint Y j)=a ∨ source G (atPoint F i) (atPoint Y j)=b)
    (i j x y) : source G (atPoint Y i) (atPoint F j)=targetName p (atPoint Z x) (atPoint T y) ↔
       markColumn F Y a i j=markColumn T Z a x y := by
  constructor
  · exact fun e => congrArg (fun u => decide (u=a)) (common_transpose p e)
  · intro e
    apply common_transpose p
    have iff := decide_eq_decide.mp e
    rcases h j i with h₁|h₁ <;> rcases palette_target p F Y T Z a b h y x with h₂|h₂ <;> simp_all

theorem col_two (F : Shore (source G) l Four) (Y : Shore (source G) r Eight) (a : Nat) (b : Eight → Edge)
    (mark : ∀ i j, source G (atPoint F i) (atPoint Y j)=a ↔ i∈edge (b j)) :
    dot (markColumn F Y a 0) (markColumn F Y a 0)=2 := by
  have eq : Finset.univ.filter (fun i => markColumn F Y a 0 i=true ∧ markColumn F Y a 0 i=true)=edge (b 0) := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,and_self,markColumn,decide_eq_true_eq,mark]
  exact (congrArg Finset.card eq).trans ((show ∀ e : Edge, (edge e).card=2 by decide) _)

theorem mixed {s : Nat} (X : Shore (source G) s Eight) (TX : Shore (targetName p) s Eight)
    (Y : Shore (source G) r Eight) (TY : Shore (targetName p) r Eight)
    (F : Shore (source G) l Four) (T : Shore (targetName p) l Four)
    (O : Eight → Col) (M N : Eight → Col) (ho : Block X TX F T O O) (hm : Block Y TY F T M N)
    (old : ∀ i j, source G (atPoint X i) (atPoint Y j)=targetName p (atPoint TX i) (atPoint TY j)) (i j) :
    dot (O i) (M j)=dot (O i) (N j) := by
  simpa only [dot,Finset.sum_boole] using Block.fold (commonLaws p) ho (Block.flip (commonLaws p) hm)
    (fun a b => if a=true ∧ b=true then 1 else 0) (old i j)

end QGI.Coherent.FourHalfModel
