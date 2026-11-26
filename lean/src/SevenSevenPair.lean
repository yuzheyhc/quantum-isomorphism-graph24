import SevenSevenCatalog
import LargeOrderFourteen
import SixSixCycle

noncomputable section
namespace QGI.Coherent.SevenSevenPair
open Relations StrategyColorLaws SmallUnion SmallFiberExtension SevenSevenCatalog
open SixTenCoordinates (Shore atPoint)
open FourTwelveFunctional (source fiber_eq)
open private induce from SmallUnionRealization

abbrev cells {n} {c : Table n} {r s} (L : Shore c r V) (R : Shore c s V) : M :=
  fun i j => c (atPoint L i) (atPoint R j)

theorem pair_card {n l r a b} {G : Graph n} (lr : l≠r)
    (A : Shore (source G) l (Fin a)) (Y : Shore (source G) r (Fin b)) :
    (vertices (source G) (fun t => t=l ∨ t=r)).card=a+b := by
  have eq : vertices (source G) (fun z => z=l ∨ z=r)=vertices (source G) (·=l) ∪ vertices (source G) (·=r) := by
    ext z; simp only [mem_vertices,Finset.mem_union]
  have dj : Disjoint (vertices (source G) (·=l)) (vertices (source G) (·=r)) :=
    Finset.disjoint_left.mpr (fun z hl hr => lr (((mem_vertices _ _ _).mp hl).symm.trans ((mem_vertices _ _ _).mp hr)))
  rw [eq,Finset.card_union_of_disjoint dj,SixSixCycle.size A,SixSixCycle.size Y]

theorem classify {n} {G : Graph n} {r s} (apart : r≠s)
    (S : Shore (source G) r V) (Y : Shore (source G) s V) : Shape (cells S Y) := by
  classical
  let c := source G
  let reg := fun t => t=r ∨ t=s
  let X := Region c reg
  have sz : (vertices c reg).card=14 := pair_card apart S Y
  let E : Fin 14 ≃ X := Fintype.equivOfCardEq (by simpa only [X,Region,Fintype.card_fin,Fintype.card_coe] using sz.symm)
  let f := fun i => (E i).val
  have inj : Function.Injective f := fun _ _ e => E.injective (Subtype.ext e)
  have range (z) : (∃ i, f i=z) ↔ reg (c z z) := by
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_vertices _ _ _).mp (E i).property
    · intro h
      let v : X := ⟨z,(mem_vertices _ _ _).mpr h⟩
      exact ⟨E.symm v,congrArg Subtype.val (E.apply_symm_apply v)⟩
  have allConfig : Configuration c := ⟨fun _ _ _ h => diagonal _ h,fun _ _ _ _ h => transpose _ h,Relations.products _⟩
  have cc := induce allConfig (fun {_ _ _ _} h => (end_colors (closure G) h).2) f inj range
  have cardFiber {a k : Nat} (A : Shore c a (Fin k)) (i : Fin n) (h : c i i=a) : (fiber G i).card=k := by
    have eq : fiber G i=vertices c (·=a) := by ext z; rw [fiber_eq,mem_vertices]; change (c z z=c i i ↔ c z z=a); rw [h]
    rw [eq]; exact SixSixCycle.size A
  have sizes (i) : 4 ≤ (Finset.univ.filter (fun j => source G (f j) (f j)=source G (f i) (f i))).card := by
    rw [LargeOrderBlocks.fiber_card f inj range]
    rcases (range _).mp ⟨i,rfl⟩ with h|h
    · rw [cardFiber S _ h]; decide
    · rw [cardFiber Y _ h]; decide
  obtain ⟨a,⟨P⟩,_⟩ := Literature.zivAv_fourteen_common_catalog cc cc sizes (fun _ => Iff.rfl) cc.products
  let g := f ∘ P.coordinates
  have gi : Function.Injective g := inj.comp P.coordinates.injective
  have gr (z) : (∃ i, g i=z) ↔ reg (c z z) := Iff.trans
    ⟨fun ⟨i,h⟩ => ⟨P.coordinates i,h⟩,fun ⟨i,h⟩ => ⟨P.coordinates.symm i,by simpa [g] using h⟩⟩ (range z)
  have cell (i j) : c (g i) (g j)=P.labels (ZivAv.name a i j) := P.cell i j
  have same (i j x y) : c (g i) (g j)=c (g x) (g y) ↔ ZivAv.color a i j=ZivAv.color a x y := by
    rw [cell,cell,P.labels.injective.eq_iff,← Fin.val_inj]
    rfl
  have card (i) : diagSize a i=7 := by
    have h := LargeOrderBlocks.fiber_card g gi gr i
    change (Finset.univ.filter (fun j => c (g j) (g j)=c (g i) (g i))).card=_ at h
    simp only [same] at h
    rcases (gr _).mp ⟨i,rfl⟩ with tag|tag
    · exact h.trans (cardFiber S _ tag)
    · exact h.trans (cardFiber Y _ tag)
  obtain ⟨const,apartRaw⟩ := halves a card
  let d := fun swap => c (g (side swap 0)) (g (side swap 0))
  have tags (swap i) : c (g (side swap i)) (g (side swap i))=d swap := (same ..).mpr (const swap i)
  have ne : d false≠d true := fun h => apartRaw ((same ..).mp h)
  have belongs (swap) : d swap=r ∨ d swap=s := (gr _).mp ⟨side swap 0,rfl⟩
  obtain ⟨swap,left,right⟩ : ∃ swap : Bool, d swap=r ∧ d (!swap)=s := by
    rcases belongs false with h|h <;> rcases belongs true with k|k
    · exact (ne (h.trans k.symm)).elim
    · exact ⟨false,h,k⟩
    · exact ⟨true,k,h⟩
    · exact (ne (h.trans k.symm)).elim
  let L (i : V) := S.symm ⟨g (side swap i),(tags swap i).trans left⟩
  let R (i : V) := Y.symm ⟨g (side (!swap) i),(tags (!swap) i).trans right⟩
  have ll (i) : atPoint S (L i)=g (side swap i) := congrArg Subtype.val (S.apply_symm_apply _)
  have rr (i) : atPoint Y (R i)=g (side (!swap) i) := congrArg Subtype.val (Y.apply_symm_apply _)
  have li : Function.Injective L := fun i j h => side_inj _ (gi ((ll i).symm.trans ((congrArg (atPoint S) h).trans (ll j))))
  have ri : Function.Injective R := fun i j h => side_inj _ (gi ((rr i).symm.trans ((congrArg (atPoint Y) h).trans (rr j))))
  let u := Equiv.ofBijective L (Finite.injective_iff_bijective.mp li)
  let w := Equiv.ofBijective R (Finite.injective_iff_bijective.mp ri)
  apply SevenSevenCatalog.transport u w _ (alternatives a card swap)
  intro i j x y
  change c (atPoint S (L i)) (atPoint Y (R j))=c (atPoint S (L x)) (atPoint Y (R y)) ↔ _
  rw [ll,rr,ll,rr]; exact same ..

end QGI.Coherent.SevenSevenPair



