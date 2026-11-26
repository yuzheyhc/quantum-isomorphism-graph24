import SixNineCatalog
import RegionalFourSixEight
import NineNineRectangles

noncomputable section
namespace QGI.Coherent.SixNineModel
open Relations StrategyColorLaws SixTenCoordinates SmallUnion SmallFiberExtension
open FourTwelveFunctional (source fiber_eq)
open RegionalCycleExtension (emb range_emb)
open private induce from SmallUnionRealization

/-- Named rectangle shapes needed on a six- and a nine-point
shore. The local input is obtained by inducing the original configuration. -/
theorem represent {n : Nat} {G : Graph n} {r s : Nat} (apart : r≠s)
    (S : Shore (source G) r (Fin 6)) (Y : Shore (source G) s (Fin 9))
    : ∃ (a : QGI.Fifteen.Index) (u : Equiv.Perm (Fin 6)) (w : Equiv.Perm (Fin 9)) (name : QGI.Fifteen.Color a ↪ Nat),
       SixNineCatalog.diagSize a (SixNineCatalog.left 0)=6 ∧ SixNineCatalog.diagSize a (SixNineCatalog.right 0)=9 ∧
       (∀ i j, source G (atPoint S (u i)) (atPoint Y (w j))=name (SixNineCatalog.M a i j)) ∧
       ∀ i j, source G (atPoint S (u i)) (atPoint S (u j))=name (SixNineCatalog.value a (SixNineCatalog.left i) (SixNineCatalog.left j)) := by
  classical
  let c := source G
  let reg := fun t => t=r ∨ t=s
  let X := Region c reg
  have sz : (vertices c reg).card=15 := RegionalFourSixEight.pair_card apart S Y
  let E : Fin 15 ≃ X := Fintype.equivOfCardEq (by simpa only [X,Region,Fintype.card_fin,Fintype.card_coe] using sz.symm)
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
    rw [eq]; exact RegionalTwoAnchor.card A
  have sizes (i) : 4 ≤ (Finset.univ.filter (fun j => source G (f j) (f j)=source G (f i) (f i))).card := by
    rw [LargeOrderBlocks.fiber_card f inj range]
    rcases (range _).mp ⟨i,rfl⟩ with h|h
    · rw [cardFiber S _ h]; decide
    · rw [cardFiber Y _ h]; decide
  obtain ⟨a,⟨P⟩,_⟩ := Literature.zivAv_fifteen_common_catalog cc cc sizes (fun _ => Iff.rfl) cc.products
  let g := f ∘ P.coordinates
  have gi : Function.Injective g := inj.comp P.coordinates.injective
  have gr (z) : (∃ i, g i=z) ↔ reg (c z z) := Iff.trans
    ⟨fun ⟨i,h⟩ => ⟨P.coordinates i,h⟩,fun ⟨i,h⟩ => ⟨P.coordinates.symm i,by simpa [g] using h⟩⟩ (range z)
  have cell (i j) : c (g i) (g j)=P.labels (SixNineCatalog.value a i j) := (P.cell i j).trans (congrArg P.labels (SixNineCatalog.read_cell a i j))
  have card (i) : SixNineCatalog.diagSize a i=(fiber G (g i)).card := by
    have h := LargeOrderBlocks.fiber_card g gi gr i
    change (Finset.univ.filter (fun j => c (g j) (g j)=c (g i) (g i))).card=_ at h
    simpa only [cell,P.labels.injective.eq_iff,SixNineCatalog.diagSize] using h
  have existsNum {k h : Nat} (A : Shore c h (Fin k)) (i : Fin k) (ok : reg h) : ∃ j, SixNineCatalog.diagSize a j=k := by
    obtain ⟨j,hj⟩ := (gr (atPoint A i)).mpr ((congrArg reg (A i).property).mpr ok)
    exact ⟨j,(card j).trans (cardFiber A _ (hj.symm ▸ (A i).property))⟩
  obtain ⟨ls,rs⟩ := SixNineCatalog.coordinates a (existsNum S 0 (Or.inl rfl)) (existsNum Y 0 (Or.inr rfl))
  have leftTag (i) : c (g (SixNineCatalog.left i)) (g (SixNineCatalog.left i))=r := by
    rcases (gr _).mp ⟨SixNineCatalog.left i,rfl⟩ with h|h
    · exact h
    · have ne := (ls i).symm.trans ((card _).trans (cardFiber Y _ h)); contradiction
  have rightTag (i) : c (g (SixNineCatalog.right i)) (g (SixNineCatalog.right i))=s := by
    rcases (gr _).mp ⟨SixNineCatalog.right i,rfl⟩ with h|h
    · have ne := (rs i).symm.trans ((card _).trans (cardFiber S _ h)); contradiction
    · exact h
  let L (i : Fin 6) := S.symm ⟨g (SixNineCatalog.left i),leftTag i⟩
  let R (i : Fin 9) := Y.symm ⟨g (SixNineCatalog.right i),rightTag i⟩
  have ll (i) : atPoint S (L i)=g (SixNineCatalog.left i) := congrArg Subtype.val (S.apply_symm_apply _)
  have rr (i) : atPoint Y (R i)=g (SixNineCatalog.right i) := congrArg Subtype.val (Y.apply_symm_apply _)
  have li : Function.Injective L := fun i j h => Fin.ext (congrArg (Fin.val : Fin 15 → Nat) (gi ((ll i).symm.trans ((congrArg (atPoint S) h).trans (ll j)))))
  have ri : Function.Injective R := by
    intro i j h
    have eq := congrArg Fin.val (gi ((rr i).symm.trans ((congrArg (atPoint Y) h).trans (rr j))))
    change 6+i.val=6+j.val at eq; exact Fin.ext (Nat.add_left_cancel eq)
  let u := Equiv.ofBijective L (Finite.injective_iff_bijective.mp li)
  let w := Equiv.ofBijective R (Finite.injective_iff_bijective.mp ri)
  let N := fun i j => c (atPoint S i) (atPoint Y j)
  have cells (i j) : N (u i) (w j)=P.labels (SixNineCatalog.M a i j) := by
    change c (atPoint S (L i)) (atPoint Y (R j))=_
    rw [ll,rr]; exact cell _ _
  refine ⟨a,u,w,P.labels,ls 0,rs 0,cells,?_⟩
  intro i j
  change c (atPoint S (L i)) (atPoint S (L j))=_
  rw [ll,ll]; exact cell _ _

end QGI.Coherent.SixNineModel
