import RegionalDoubleEightTables
import RegionalPlanar
import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.RegionalDoubleEight
open DoubleEight DoubleEight.Prepared SmallUnion StrategyColorLaws LargeFourteenRegion Certificate
open FourTwelveFunctional (source)
open private row_size key_fields lookup_entries witness_bound from DoubleEightQuantum
open private pattern_checks from ColoredPlanarWitness
set_option maxRecDepth 12000
attribute [local irreducible] scheme row

private def Used (c : Table 16) := {z // ∃ i j, c i j=z}

private def palette {a : Index} {c : Table 16} (P : Presentation a c) : Fin (scheme a).rank ≃ Used c := by
  classical
  choose x y xy using name_surjective a
  let f := fun k => (⟨c (P.coordinates (x k)) (P.coordinates (y k)),_,_,rfl⟩ : Used c)
  have atCell (i j) : (f (name a i j)).val=c (P.coordinates i) (P.coordinates j) :=
    (P.same _ _ _ _).mp (xy _)
  apply Equiv.ofBijective f
  constructor
  · intro k l eq
    have t := (P.same _ _ _ _).mpr (congrArg Subtype.val eq)
    simpa only [xy] using t
  · rintro ⟨z,i,j,rfl⟩
    exact ⟨name a (P.coordinates.symm i) (P.coordinates.symm j),Subtype.ext
      (by simpa using atCell (P.coordinates.symm i) (P.coordinates.symm j))⟩

private theorem atCell {a : Index} {c : Table 16} (P : Presentation a c) (i j) :
    (palette P (name a i j)).val=c (P.coordinates i) (P.coordinates j) := by
  apply (P.same _ _ _ _).mp
  exact Classical.choose_spec (Classical.choose_spec (name_surjective a (name a i j)))

private theorem range_comp {n} (f : Fin 16 → Fin n) (e : Equiv.Perm (Fin 16)) (x : Fin n) :
    (∃ i, (f ∘ e) i = x) ↔ ∃ i, f i=x :=
  ⟨fun ⟨i,h⟩ => ⟨e i,h⟩,fun ⟨i,h⟩ => ⟨e.symm i,by simpa using h⟩⟩

private theorem literal {a : Index} {m : ColorMatrix} (order : m.order=16)
    (same : m.entries=row a) (i j : Fin 16) : m.get i.val j.val=(name a i j).val := by
  have small : 16*i.val+j.val < (row a).size := by rw [row_size]; omega
  simp only [ColorMatrix.get,order,same,Nat.mul_comm i.val 16,name_val,Placements.color,
    Array.getD_eq_getD_getElem?,getElem?_pos (row a) (16*i.val+j.val) small,Option.getD_some]

/-- Source and target are independently identified with rows of the 636-row
catalog. The map under test is the association of names of the original strategy. -/
private theorem of_models {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (reg : Nat → Prop) (f g : Fin 16 → Fin n)
    (D : DataFor p reg f g) {a b : Index} (A : Presentation a (restricted (source G) f))
    (B : Presentation b (restricted (targetName p) g)) :
    ∃ h : Equiv.Perm (Fin 16), ∀ i j, source G (f i) (f j)=targetName p (g (h i)) (g (h j)) := by
  classical
  let c := restricted (source G) f
  let d := restricted (targetName p) g
  let u : Used c ≃ Used d := Equiv.subtypeEquiv (Equiv.refl Nat) D.used
  let e := (palette A).trans (u.trans (palette B).symm)
  have named (k) : (palette A k).val=(palette B (e k)).val := by
    change (palette A k).val=(palette B ((palette B).symm (u (palette A k)))).val
    rw [Equiv.apply_symm_apply]
    rfl
  have same (i j x y) : e (name a i j)=name b x y ↔ c (A.coordinates i) (A.coordinates j)=
      d (B.coordinates x) (B.coordinates y) := by
    dsimp only [c,d]
    rw [←atCell A i j,←atCell B x y,named,Subtype.val_inj,(palette B).injective.eq_iff]
  let pi := List.ofFn fun k => (e k).val
  have get (k : Fin (scheme a).rank) (fallback : Nat) : (pi[k.val]?).getD fallback=(e k).val := by
    simp only [pi,List.getElem?_ofFn,dif_pos k.isLt,Option.getD_some]
  have countAs {t : Index} {T : Table 16} (M : Presentation t T) (k l : Fin (scheme t).rank) (i j) :
      count T (palette M k).val (palette M l).val (M.coordinates i) (M.coordinates j) =
      ∑ z : Fin 16, if name t i z=k ∧ name t z j=l then 1 else 0 := by
    rw [←count_relabel T M.coordinates]
    simp only [count,←atCell,Subtype.val_inj,(palette M).injective.eq_iff]
  obtain ⟨rankEq,profile,listed⟩ := eligible_of_cells a b e
    (fun i j x y h => (same _ _ _ _).mpr (common_transpose p ((same _ _ _ _).mp h)))
    (fun i j x y eq k l => by
      have num := D.products (palette A k).val (palette A l).val _ _ _ _ ((same _ _ _ _).mp eq)
      rw [countAs A,named,named l,countAs B] at num
      exact num)
  rcases CensusMaps.dichotomy a b pi rankEq profile listed with ⟨h,point⟩ | ⟨C,hC,key⟩
  · have ok (i j) : e (name a i j)=name b (h i) (h j) := by
      apply Fin.ext
      rw [←get (name a i j) 0,name_val,name_val]
      exact point i j
    refine ⟨A.coordinates.symm.trans (h.trans B.coordinates),?_⟩
    intro i j
    obtain ⟨i,rfl⟩ := A.coordinates.surjective i
    obtain ⟨j,rfl⟩ := A.coordinates.surjective j
    simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (same _ _ _ _).mp (ok i j)
  · obtain ⟨r,hr,hkey,bound,diff⟩ := Attachment.actual_key_has_checked_witness C hC _ key
    obtain ⟨_,_,os,ot,src,dst⟩ := bound
    obtain ⟨sid,tid,perm⟩ := key_fields r (a.val+1) (b.val+1) pi hkey
    have hs : r.src.entries = row a := lookup_entries (by simpa only [sid,Nat.add_sub_cancel] using src)
    have ht : r.dst.entries = row b := lookup_entries (by simpa only [tid,Nat.add_sub_cancel] using dst)
    have meta := List.all_eq_true.mp pattern_checks r hr
    simp only [Bool.and_eq_true,beq_iff_eq] at meta
    exfalso
    apply diff
    apply RegionalPlanar.homCount_region p (by decide) reg (f ∘ A.coordinates) (g ∘ B.coordinates)
      (D.injF.comp A.coordinates.injective) (D.injG.comp B.coordinates.injective)
      (fun z => (range_comp _ _ z).trans (D.src z)) (fun z => (range_comp _ _ z).trans (D.tgt z))
      r.src r.dst os ot r.pattern (drawing_of_tetraPrism meta.1) r.colors meta.2
      (fun v => r.perm[v]?.getD r.src.rank)
    intro i j x y eq s hs'
    have len := List.all_eq_true.mp (List.all_eq_true.mp witness_bound r hr) s hs'
    have lt : s < (scheme a).rank := by simpa only [decide_eq_true_eq,perm,pi,List.length_ofFn] using len
    let k : Fin (scheme a).rank := ⟨s,lt⟩
    have rename : (r.perm[s]?).getD r.src.rank=(e k).val := by rw [perm]; exact get k _
    rw [literal os hs,literal ot ht,rename,←(same i j x y).mpr eq]
    exact (Fin.val_inj (a:=name a i j) (b:=k)).trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm)

/-- Both eight-point fibers of any matched regional restriction admit
one point bijection realizing the strategy on every ordered pair. -/
theorem solve {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (reg : Nat → Prop) (f g : Fin 16 → Fin n)
    (D : DataFor p reg f g) (sizes : Sizes (restricted (source G) f)) :
    ∃ h : Equiv.Perm (Fin 16), ∀ i j, source G (f i) (f j)=targetName p (g (h i)) (g (h j)) := by
  have de : Ends (restricted (targetName p) g) := by
    intro i j x y eq
    have ends := Relations.end_colors (closure H) ((target_same p _ _ _ _).mp eq)
    exact ⟨(target_same p _ _ _ _).mpr ends.1,(target_same p _ _ _ _).mpr ends.2⟩
  rcases alternatives D.srcConfig D.tgtConfig sizes D.sameDiag
    (fun _ _ _ _ eq => Relations.end_colors (closure G) eq) de
    (fun _ _ _ _ eq => common_transpose p eq) D.products D.used with h | ⟨a,b,⟨A⟩,⟨B⟩⟩
  · exact h
  · exact of_models p reg f g D A B

theorem realize {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K) (reg : Nat → Prop)
    (size : (vertices (source G) reg).card=16)
    (sizes : ∀ i, reg (source G i i) → (fiber G i).card=8) : SmallFiberExtension.Realizes p reg := by
  apply LargeOrderBlocks.of_solver p reg (fun i hi => (LargeOrderBlocks.large_iff _).mpr (by rw [sizes i hi]; decide)) size
  intro f g D
  exact solve p reg f g D (fun i => (LargeOrderBlocks.fiber_card f D.injF D.src i).trans
    (sizes (f i) ((D.src _).mp ⟨i,rfl⟩)))

end QGI.Coherent.RegionalDoubleEight
