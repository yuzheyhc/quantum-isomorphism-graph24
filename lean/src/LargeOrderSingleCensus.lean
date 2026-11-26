import LargeOrderSingleData
import Single16Attach
import SixteenCensusSound
import RegionalPlanar

namespace QGI.LargeOrderSingle
open SixteenMapSearch Single16 Certificate
open Coherent Coherent.StrategyColorLaws
open Homogeneous.Unions (colorAt rawTables)
open private at2 from HomogeneousUnions

open DoubleEight.Prepared hiding coefficient_at
open private Table Table.trans tab stage_congr sorted_eq perm_of_equiv from DoubleEightPrepared
open private intrinsic decode key_ok facts coefficient_at from LargeOrderSingleData

attribute [local irreducible] scheme row name

theorem eligible (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (tr : ∀ x y u v, e (name a x y)=name b u v → e (name a y x)=name b v u)
    (numbers : ∀ x y u v, e (name a x y)=name b u v → ∀ i j : Fin (scheme a).rank,
      (∑ z : V, if name a x z=i ∧ name a z y=j then 1 else 0 : Nat) =
      ∑ z : V, if name b u z=e i ∧ name b z v=e j then 1 else 0) :
    (scheme a).rank=(scheme b).rank ∧ (scheme a).profile=(scheme b).profile ∧
      List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (scheme a) (scheme b) := by
  have rev (i : Fin (scheme a).rank) :
      e (Table.trans (tab (scheme a)) i)=Table.trans (tab (scheme b)) (e i) := by
    obtain ⟨x,y,h⟩ := onto a i
    obtain ⟨u,v,t⟩ := onto b (e i)
    have left : Table.trans (tab (scheme a)) i=name a y x := by
      apply Fin.ext; simp only [tab,dif_pos ((facts a).1 i),←h,(facts a).2.2.2,dif_pos (name a y x).isLt]
    have right : Table.trans (tab (scheme b)) (e i)=name b v u := by
      apply Fin.ext; simp only [tab,dif_pos ((facts b).1 (e i)),←t,(facts b).2.2.2,dif_pos (name b v u).isLt]
    rw [left,right]; exact tr _ _ _ _ ((congrArg e h).trans t.symm)
  have mul (k i j : Fin (scheme a).rank) : coefficient (scheme a) k.val i.val j.val =
      coefficient (scheme b) (e k).val (e i).val (e j).val := by
    obtain ⟨x,y,h⟩ := onto a k
    obtain ⟨u,v,t⟩ := onto b (e k)
    rw [←h,coefficient_at,h,←t,coefficient_at]
    exact numbers _ _ _ _ ((congrArg e h).trans t.symm) _ _
  have keys (i : Fin (scheme a).rank) : refinedKey (scheme a) i.val=refinedKey (scheme b) (e i).val :=
    (key_ok a i).symm.trans ((congrArg decode (stage_congr (tab (scheme a)) (tab (scheme b)) e rev mul 3 i)).trans (key_ok b (e i)))
  refine ⟨by simpa using Fintype.card_congr e,(facts a).2.1.trans
    ((sorted_eq (perm_of_equiv _ _ _ keys)).trans (facts b).2.1.symm),mem_of_palette_equiv _ _ e keys ?_ mul⟩
  intro i j
  have trEq : Table.trans (tab (scheme a)) i=j ↔ Table.trans (tab (scheme b)) (e i)=e j := by
    rw [←rev,e.injective.eq_iff]
  simpa only [←Fin.val_inj,tab,dif_pos ((facts a).1 i),dif_pos ((facts b).1 (e i))] using trEq

def table (a : Index) : Homogeneous.Unions.Table :=
  Array.ofFn fun i : V => Array.ofFn fun j : V => (name a i j).val

private theorem archive : rawTables 16 = (List.finRange 208).map table := by native_decide
theorem in_archive {t} (h : t ∈ rawTables 16) : ∃ a : Index, table a=t := by
  rw [archive] at h
  obtain ⟨a,_,eq⟩ := List.mem_map.mp h
  exact ⟨a,eq⟩
theorem table_color (a : Index) (i j : V) : colorAt (table a) i.val j.val=(name a i j).val := by
  simp [table,colorAt,at2,i.isLt,j.isLt]

private theorem enumerated : (List.range Input.matrices.length).zip Input.matrices=
    (List.finRange 208).map (fun a : Index => (a.val,row a)) := by native_decide
private theorem prepared : preparedSchemes [16] Input.matrices=some ((List.finRange 208).map scheme) := by
  unfold preparedSchemes
  rw [enumerated]
  have compute (xs : List Index) :
      (xs.map fun a => (a.val,row a)).mapM (fun im => prepare [16] (im.1+1) im.2)=some (xs.map scheme) := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons,List.mapM_cons,prepare_row,ih]; rfl
  exact compute _

private theorem metadata : ∀ a : Index, (scheme a).id=a.val+1 ∧ Input.matrices[a.val]?=some (row a) ∧
    ∀ x y : V, (row a)[x.val*16+y.val]?=some (name a x y).val := by native_decide

private theorem counted : ∃ C : Counts, census=some C ∧ onMatrices [16] Input.matrices=some C := by
  have h := catalogueCheck
  unfold checked at h
  cases eq : census with
  | none => simp [eq] at h
  | some C =>
    refine ⟨C,rfl,?_⟩
    unfold census at eq
    split at eq
    · exact eq
    · exact nomatch eq

private theorem witnessFacts : Attachment.rows.all (fun r =>
    tetraPrism r.pattern && r.colors.length == r.pattern.edges.length &&
      r.colors.all (fun k => decide (k<r.perm.length)))=true := by native_decide

private theorem name_val (a : Index) (i j : V) : (name a i j).val=pointColor (scheme a) i j := by
  unfold name <;> rfl

theorem dichotomy (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (ranks : (scheme a).rank=(scheme b).rank) (profile : (scheme a).profile=(scheme b).profile)
    (eligible : List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (scheme a) (scheme b)) :
    (∃ h : Equiv.Perm V, ∀ i j, e (name a i j)=name b (h i) (h j)) ∨
    ∃ r ∈ Attachment.rows, r.key=(a.val+1,b.val+1,List.ofFn fun i => (e i).val) ∧ Attachment.OnCatalog r ∧
      homCount r.src r.pattern r.colors ≠ homCount r.dst r.pattern (renamed r.src r.perm r.colors) := by
  let pi := List.ofFn fun i => (e i).val
  cases test : pointTest (scheme a) (scheme b) pi with
  | true =>
    obtain ⟨h,hh⟩ := pointTest_sound test
    refine Or.inl ⟨h,fun i j => Fin.ext ?_⟩
    have point := hh i j
    rw [←name_val,←name_val] at point
    simpa only [pi,List.getElem?_ofFn,dif_pos (name a i j).isLt,Option.getD_some] using point
  | false =>
    obtain ⟨C,hC,run⟩ := counted
    have mem (i : Index) : scheme i ∈ (List.finRange 208).map scheme :=
      List.mem_map_of_mem (List.mem_finRange i)
    have key := key_mem_exceptions prepared run (mem a) (mem b) ranks profile eligible test
    rw [(metadata a).1,(metadata b).1] at key
    exact Or.inr (Attachment.actual_key_has_checked_witness C hC _ key)

private theorem read {m : ColorMatrix} {a : Index} (ord : m.order=16)
    (entries : Input.matrices[a.val]?=some m.entries) (x y : V) : m.get x.val y.val=(name a x y).val := by
  have eq := Option.some.inj (entries.symm.trans (metadata a).2.1)
  simp only [ColorMatrix.get,ord,eq,(metadata a).2.2 x y,Option.getD_some]

theorem exclude {n} {G H : QGI.Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (reg : Nat → Prop) (f g : V → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (sf : ∀ z, (∃ i, f i=z) ↔ reg (Relations.color (closure G) z z))
    (sg : ∀ z, (∃ i, g i=z) ↔ reg (targetName p z z))
    (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (same : ∀ i j x y, Relations.color (closure G) (f i) (f j)=targetName p (g x) (g y) →
      e (name a i j)=name b x y)
    (r : Attachment.Row) (member : r ∈ Attachment.rows)
    (key : r.key=(a.val+1,b.val+1,List.ofFn fun i => (e i).val)) (valid : Attachment.OnCatalog r)
    (diff : homCount r.src r.pattern r.colors ≠ homCount r.dst r.pattern (renamed r.src r.perm r.colors)) : False := by
  obtain ⟨sid,tid,perm⟩ := (show r.srcId=a.val+1 ∧ r.dstId=b.val+1 ∧
    r.perm=List.ofFn (fun i => (e i).val) by simpa only [Attachment.Row.key,Prod.mk.injEq] using key)
  obtain ⟨_,_,so,to_,left,right⟩ := valid
  rw [sid,Nat.add_sub_cancel] at left
  rw [tid,Nat.add_sub_cancel] at right
  have facts := List.all_eq_true.mp witnessFacts r member
  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq] at facts
  apply diff (RegionalPlanar.homCount_region p (by decide : 0<16) reg f g hf hg sf sg r.src r.dst so to_
    r.pattern (drawing_of_tetraPrism facts.1.1) r.colors facts.1.2 (fun k => r.perm[k]?.getD r.src.rank) ?_)
  intro i j x y hit k hk
  have small : k<(scheme a).rank := by simpa only [perm,List.length_ofFn] using facts.2 k hk
  let u : Fin (scheme a).rank := ⟨k,small⟩
  have hu : (r.perm[k]?).getD r.src.rank=(e u).val := by simp only [perm,List.getElem?_ofFn,dif_pos small,Option.getD_some,u]
  rw [read so left,read to_ right]
  change _ ↔ (name b x y).val=r.perm[k]?.getD r.src.rank
  rw [hu,←same i j x y hit]
  exact (Fin.val_inj (a:=name a i j) (b:=u)).trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm)

end QGI.LargeOrderSingle
