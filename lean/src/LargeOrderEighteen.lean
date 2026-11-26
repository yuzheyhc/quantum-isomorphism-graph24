import EighteenPlacement
import LargeOrderBlocks
import RegionalPlanar
import HomogeneousUnions
import Mathlib.Data.List.Permutation

namespace QGI.LargeOrderEighteen
open Coherent.SmallUnion Coherent.StrategyColorLaws Homogeneous.Unions Certificate
abbrev V := Fin 18
abbrev C := Fin 8

def matrix : ColorMatrix :=
  let t := (rawTables 18)[59]?.getD #[]
  ⟨18,8,Array.ofFn fun i : Fin 324 => colorAt t (i.val/18) (i.val%18)⟩
def name (i j : V) : C := Fin.ofNat' 8 (matrix.get i.val j.val)
private def spot (k : C) : V :=
  ((List.finRange 18).find? fun y => name 0 y=k).getD 0
private def tensor : Vector Nat 512 := Vector.ofFn fun w =>
  let k : C := Fin.ofNat' 8 (w.val/64)
  count (fun i j => (name i j).val) ((w.val/8)%8) (w.val%8) 0 (spot k)
def coeff (k i j : C) := tensor.get ⟨64*k.val+8*i.val+j.val,by omega⟩
private theorem facts : (∀ k, name 0 (spot k)=k) ∧ (∀ x y, matrix.get x.val y.val=(name x y).val) ∧
    ∀ x y i j, count (fun u v => (name u v).val) i.val j.val x y=coeff (name x y) i j := by native_decide

structure Presentation (c : Coherent.SmallUnion.Table 18) where
  points : Equiv.Perm V
  labels : C ↪ Nat
  cell : ∀ i j, c (points i) (points j)=labels (name i j)

def maps : List (List Nat × Option (List Nat)) := [
  ([0,1,2,3,4,5,6,7],some [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]),
  ([0,1,2,3,4,5,7,6],some [0,1,2,3,5,4,6,8,7,9,11,10,15,16,17,12,13,14]),
  ([0,1,2,4,5,3,6,7],some [0,1,2,6,7,8,9,10,11,3,4,5,12,13,14,15,16,17]),
  ([0,1,2,4,5,3,7,6],some [0,1,2,6,8,7,9,11,10,3,5,4,15,16,17,12,13,14]),
  ([0,1,2,5,3,4,6,7],some [0,1,2,9,10,11,3,4,5,6,7,8,12,13,14,15,16,17]),
  ([0,1,2,5,3,4,7,6],some [0,1,2,9,11,10,3,5,4,6,8,7,15,16,17,12,13,14]),
  ([0,2,1,3,5,4,6,7],none),
  ([0,2,1,3,5,4,7,6],none),
  ([0,2,1,4,3,5,6,7],none),
  ([0,2,1,4,3,5,7,6],none),
  ([0,2,1,5,4,3,6,7],none),
  ([0,2,1,5,4,3,7,6],none)]

def image (pi : List Nat) (k : C) : C := Fin.ofNat' 8 (pi.getD k.val 8)
def place (f : List Nat) (x : V) : V := Fin.ofNat' 18 (f.getD x.val 18)
def arcs : List Nat := [3,3,6,6,3,4]

def preserves (pi : List Nat) : Prop := ∀ k i j, coeff k i j=coeff (image pi k) (image pi i) (image pi j)
instance (pi : List Nat) : Decidable (preserves pi) := by unfold preserves; infer_instance

private theorem complete : (List.ofFn (fun k : C => k.val)).permutations.all
    (fun pi => !decide (preserves pi) || (maps.map Prod.fst).contains pi) = true := by native_decide

private def correct (pi : List Nat) : Option (List Nat) → Prop
  | some f => Function.Injective (place f) ∧ ∀ x y, image pi (name x y)=name (place f x) (place f y)
  | none => homCount matrix .tetra arcs=54 ∧ homCount matrix .tetra (arcs.map (fun k => pi.getD k 8))=0
private instance (pi : List Nat) (w : Option (List Nat)) : Decidable (correct pi w) := by
  cases w <;> simp only [correct,Function.Injective] <;> infer_instance
private theorem checked : maps.all (fun m => decide (correct m.1 m.2))=true := by native_decide

theorem classify (e : Equiv.Perm C) (h : ∀ k i j, coeff k i j=coeff (e k) (e i) (e j)) :
    (∃ f : Equiv.Perm V, ∀ i j, e (name i j)=name (f i) (f j)) ∨
      (homCount matrix .tetra arcs=54 ∧ homCount matrix .tetra (arcs.map (fun k => (e (Fin.ofNat' 8 k)).val))=0) := by
  let pi := List.ofFn (fun k => (e k).val)
  have im (k : C) : pi.getD k.val 8=(e k).val := by
    simp only [pi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos k.isLt,Option.getD_some]
  have img (k : C) : image pi k=e k := by
    apply Fin.ext
    change pi.getD k.val 8 % 8=(e k).val
    rw [im,Nat.mod_eq_of_lt (e k).isLt]
  have mem : pi ∈ (List.ofFn (fun k : C => k.val)).permutations :=
    List.mem_permutations.mpr (Equiv.Perm.ofFn_comp_perm e Fin.val)
  have perm : preserves pi := by intro k i j; simp only [img]; exact h _ _ _
  have t := List.all_eq_true.mp complete pi mem
  have hit : pi ∈ maps.map Prod.fst := by simpa [perm] using t
  obtain ⟨⟨l,w⟩,mw,eq⟩ := List.mem_map.mp hit
  change l=pi at eq
  subst l
  have ok : correct pi w := of_decide_eq_true (List.all_eq_true.mp checked _ mw)
  cases w with
  | some f =>
    obtain ⟨inj,point⟩ := ok
    exact Or.inl ⟨Equiv.ofBijective (place f) (Finite.injective_iff_bijective.mp inj),fun i j => (img _).symm.trans (point i j)⟩
  | none =>
    obtain ⟨left,right⟩ := ok
    refine Or.inr ⟨left,?_⟩
    have map_eq : arcs.map (fun k => (e (Fin.ofNat' 8 k)).val)=arcs.map (fun k => pi.getD k 8) := by
      apply List.map_congr_left
      intro k hk
      have small : k<8 := (show ∀ i ∈ arcs, i<8 by decide) _ hk
      let u : C := ⟨k,small⟩
      have e0 : (Fin.ofNat' 8 k)=u := by apply Fin.ext; simp [u,Nat.mod_eq_of_lt small]
      change (e (Fin.ofNat' 8 k)).val=pi.getD k 8
      rw [e0]; exact (im u).symm
    rw [map_eq]; exact right
end QGI.LargeOrderEighteen

namespace QGI.Literature
open Coherent.SmallUnion Coherent.StrategyColorLaws LargeOrderEighteen
/-- An independently checked intersection tensor search isolates row 60.
The residual Hanaki–Miyamoto census supplies the nonthin input tables. -/
theorem zivAv_eighteen_catalog_position {c d : Table 18} (src : Configuration c) (tgt : Configuration d)
    (hom : ∀ i j, c i i=c j j) (hom' : ∀ i j, d i i=d j j)
    (used : ∀ a, (∃ i j, c i j=a) ↔ ∃ x y, d x y=a)
    (numbers : ∀ a b i j x y, c i j=d x y → count c a b i j=count d a b x y) :
    (∃ h : Equiv.Perm V, ∀ i j, c i j=d (h i) (h j)) ∨ Nonempty (Presentation c) ∧ Nonempty (Presentation d) := by
  have align : ∀ i j : V, Fin.ofNat' 8 (Homogeneous.Unions.colorAt (EighteenPalette.row 59) i.val j.val)=name i j := by native_decide
  have convert {u : Table 18} (S : EighteenPalette.Exceptional u) : Nonempty (Presentation u) :=
    ⟨⟨S.points,S.labels,fun i j => (S.cell i j).trans (congrArg S.labels (align i j))⟩⟩
  rcases EighteenPalette.position src tgt hom hom' used numbers with done_|⟨⟨A⟩,⟨B⟩⟩
  · exact Or.inl done_
  · exact Or.inr ⟨convert A,convert B⟩
end QGI.Literature

noncomputable section
namespace QGI.LargeOrderEighteen
open Coherent Coherent.SmallUnion Coherent.StrategyColorLaws Coherent.LargeFourteenRegion Certificate
open Coherent.FourTwelveFunctional (source)

private theorem reindex {n} (f : V → Fin n) (e : Equiv.Perm V) (x : Fin n) :
    (∃ i, (f ∘ e) i=x) ↔ ∃ i, f i=x :=
  ⟨fun ⟨i,h⟩ => ⟨e i,h⟩,fun ⟨i,h⟩ => ⟨e.symm i,by simpa using h⟩⟩
private theorem local_count {c : Table 18} (S : Presentation c) (i j : C) (x y : V) :
    count c (S.labels i) (S.labels j) (S.points x) (S.points y)=coeff (name x y) i j := by
  rw [←(facts.2.2 x y i j),←count_relabel c S.points]
  simp only [count,S.cell,S.labels.injective.eq_iff,Fin.val_inj]

theorem solve {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) {reg : Nat → Prop} (f g : V → Fin n)
    (D : DataFor p reg f g) (single : ∀ i j, source G (f i) (f i)=source G (f j) (f j)) :
    ∃ h : Equiv.Perm V, ∀ i j, source G (f i) (f j)=targetName p (g (h i)) (g (h j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  have other (i j) : d i i=d j j := (D.sameDiag i).symm.trans ((single i j).trans (D.sameDiag j))
  rcases Literature.zivAv_eighteen_catalog_position D.srcConfig D.tgtConfig single other D.used D.products with
    yes | ⟨⟨A⟩,⟨B⟩⟩
  · exact yes
  have hits (i : C) : ∃ j, A.labels i=B.labels j := by
    obtain ⟨u,v,hv⟩ := (D.used _).mp ⟨A.points 0,A.points (spot i),(A.cell 0 _).trans (congrArg A.labels (facts.1 i))⟩
    obtain ⟨u,rfl⟩ := B.points.surjective u
    obtain ⟨v,rfl⟩ := B.points.surjective v
    exact ⟨_,hv.symm.trans (B.cell u v)⟩
  choose e he using hits
  have inj : Function.Injective e := fun i j h =>
    A.labels.injective ((he i).trans ((congrArg B.labels h).trans (he j).symm))
  let E := Equiv.ofBijective e (Finite.injective_iff_bijective.mp inj)
  have labels (i) : A.labels i=B.labels (E i) := he i
  have same (i j x y : V) : E (name i j)=name x y ↔ c (A.points i) (A.points j)=d (B.points x) (B.points y) := by
    change _ ↔ restricted (source G) f _ _=restricted (targetName p) g _ _
    rw [A.cell,B.cell,labels,B.labels.injective.eq_iff]
  have coeffs (k i j : C) : coeff k i j=coeff (E k) (E i) (E j) := by
    have matchColor := (same 0 (spot k) 0 (spot (E k))).mp (by rw [facts.1,facts.1])
    have h := D.products (A.labels i) (A.labels j) _ _ _ _ matchColor
    rw [local_count A,labels i,labels j,local_count B,facts.1,facts.1] at h
    exact h
  rcases classify E coeffs with ⟨h,point⟩ | ⟨left,right⟩
  · refine ⟨A.points.symm.trans (h.trans B.points),fun i j => ?_⟩
    obtain ⟨i,rfl⟩ := A.points.surjective i
    obtain ⟨j,rfl⟩ := A.points.surjective j
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (point i j)
  · have tr := RegionalPlanar.homCount_region p (by decide : 0<18) reg (f ∘ A.points) (g ∘ B.points)
      (D.injF.comp A.points.injective) (D.injG.comp B.points.injective)
      (fun z => (reindex f A.points z).trans (D.src z)) (fun z => (reindex g B.points z).trans (D.tgt z))
      matrix matrix rfl rfl .tetra (drawing_of_tetraPrism (by decide)) arcs rfl (fun k => (E (Fin.ofNat' 8 k)).val)
      (fun i j x y hc k hk => by
        have small : k<8 := (show ∀ k ∈ arcs, k<8 by decide) _ hk
        let u : C := ⟨k,small⟩
        have eu : Fin.ofNat' 8 k=u := by apply Fin.ext; simp [u,Nat.mod_eq_of_lt small]
        change matrix.get i.val j.val=k ↔ matrix.get x.val y.val=(E (Fin.ofNat' 8 k)).val
        rw [facts.2.1,facts.2.1,←(same i j x y).mpr hc,eu]
        exact (Fin.val_inj (a:=name i j) (b:=u)).trans (E.injective.eq_iff.symm.trans Fin.val_inj.symm))
    exact False.elim ((by decide : (54:Nat)≠0) (left.symm.trans (tr.trans right)))
end QGI.LargeOrderEighteen
