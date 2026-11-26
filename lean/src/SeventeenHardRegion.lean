import SeventeenHardGlue

noncomputable section
namespace QGI.Coherent.SeventeenHardRegion
open FourTwelveFunctional (source)
open StrategyColorLaws SixTenCoordinates
open private root_unique pair_middle from SingletonSwitch
open private induce from SmallUnionRealization

/-- Coordinates for the complement of a named one-point fiber. -/
structure Core (G : Graph 17) where
  root : Fin 17
  one : (fiber G root).card=1

namespace Core
variable {G : Graph 17} (R : Core G)
abbrev f := R.root.succAbove
abbrev rootName := source G R.root R.root
abbrev c := SmallShore.restrict (source G) R.f
abbrev pointAt {l X} (S : Shore R.c l X) (i : X) := R.f (atPoint S i)

theorem range (x : Fin 17) : (∃ i, R.f i=x) ↔ source G x x ≠ R.rootName := by
  rw [show (∃ i, R.f i=x) ↔ x ≠ R.root from Fin.exists_succAbove_eq_iff]
  exact ⟨fun h eq => h (root_unique _ R.one _ eq),fun h eq => h (eq ▸ rfl)⟩

theorem laws : Laws R.c R.c := by
  have sc : SmallUnion.Configuration (source G) :=
    ⟨fun _ _ _ h => Relations.diagonal _ h,fun _ _ _ _ h => Relations.transpose _ h,Relations.products _⟩
  have cc := induce (keep := fun t => t ≠ R.rootName) sc (fun h => (Relations.end_colors (closure G) h).2) R.f
    Fin.succAbove_right_injective (R.range)
  exact ⟨fun h => Relations.transpose (closure G) h,fun h => (Relations.end_colors (closure G) h).2,
    fun a b _ _ _ _ h => cc.products a b _ _ _ _ h⟩

def points {l : Nat} (apart : l ≠ R.rootName) : {i : Fin 16 // R.c i i=l} ≃ {i : Fin 17 // source G i i=l} :=
  Equiv.ofBijective (fun i => ⟨R.f i.val,i.property⟩) (by
    refine ⟨fun i j h => Subtype.ext (Fin.succAbove_right_injective (congrArg Subtype.val h)),?_⟩
    intro j
    obtain ⟨i,hi⟩ := (R.range j.val).mpr (fun eq => apart (j.property.symm.trans eq))
    refine ⟨⟨i,show source G (R.f i) (R.f i)=l by rw [hi]; exact j.property⟩,Subtype.ext hi⟩)

theorem point {l X} (apart : l ≠ R.rootName) (S : Shore R.c l X) {z : Fin 17}
    (h : source G z z=l) : ∃ i, R.pointAt S i=z := by
  obtain ⟨i,hi⟩ := (S.trans (R.points apart)).surjective ⟨z,h⟩
  exact ⟨i,congrArg Subtype.val hi⟩

theorem frame {a : Fin 17} {l k : Nat} (apart : l ≠ R.rootName) (name : source G a a=l)
    (size : (fiber G a).card=k) : Nonempty (Shore R.c l (Fin k)) := by
  let first := Fintype.equivOfCardEq (show Fintype.card (Fin k)=Fintype.card {z // z∈fiber G a} by simp [size])
  let second := Equiv.subtypeEquivRight (fun z => (FourTwelveFunctional.fiber_eq a z).trans (by rw [name]))
  exact ⟨(first.trans second).trans (R.points apart).symm⟩

theorem outside_card {l : Nat} {i : Fin 17} (name : source G i i=l) :
    (SmallUnion.vertices (source G) (fun t => t≠l)).card = 17-(fiber G i).card := by
  have setEq : SmallUnion.vertices (source G) (fun t => t≠l) = (fiber G i)ᶜ := by
    ext z; simp only [SmallUnion.mem_vertices,Finset.mem_compl,FourTwelveFunctional.fiber_eq,name]
  rw [setEq,Finset.card_compl]; rfl

theorem root_pair {a b : Fin 17} (eq : source G a a=source G b b) :
    source G a R.root = source G b R.root := by
  obtain ⟨m,hm⟩ := pair_middle (fun s t => Relations.products (closure G) s t _ _ _ _ eq)
  have h := (hm R.root).1
  have fixed := root_unique R.root R.one (m R.root) ((Relations.end_colors (closure G) h).2.symm)
  rwa [fixed] at h

theorem same_edge {i j x y : Fin 17} (eq : source G i j=source G x y) : G.edge i j=G.edge x y := by
  have h := (Relations.same _ _ _ _ _).mp eq _ (adjacency_mem G)
  cases a : G.edge i j <;> cases b : G.edge x y <;> first | rfl | simp [Intertwiner.adjacency,a,b] at h

end Core
end QGI.Coherent.SeventeenHardRegion
