import SixCrossMasks

namespace QGI.SixCross
open SixShoreAtlas (Key cell)
open ZivAvSix (S M Shape Thin Constant)
open Coherent SixTenCoordinates

abbrev rect {n l r} {c : Fin n → Fin n → Nat} (X : Shore c l S) (Y : Shore c r S) : M :=
  fun i j => c (atPoint X i) (atPoint Y j)
abbrev Reads {n l r} {c : Fin n → Fin n → Nat} (X : Shore c l S) (Y : Shore c r S) (T : M) :=
  ∀ i j x y, rect X Y i j=rect X Y x y ↔ T i j=T x y
def col (T : M) (j : S) (v : Nat) := Finset.univ.filter fun i => T i j=v
abbrev flip (T : M) : M := fun i j => T j i

private theorem balanced {n l r} {c : Fin n → Fin n → Nat} {X : Shore c l S} {Y : Shore c r S}
    {T : M} (law : Laws c c) (chart : Reads X Y T) (v : Nat) (i j : S) :
    (col T j v).card=(col (flip T) i v).card := by
  let bits := fun x y => decide (T x y=v)
  have blk : Block X X Y Y bits bits := fun ⦃u w z t⦄ hit => congrArg (fun a => decide (a=v)) ((chart _ _ _ _).mp hit)
  have rows := Block.degree_eq law blk
  have cols := Block.degree_eq law (Block.flip law blk)
  have bal := FiberRectangles.balance bits (fun x => rows x i) (fun y => cols y j)
  change 6*_=6*_ at bal
  have equal := Nat.eq_of_mul_eq_mul_left (by decide : 0<6) bal
  simpa [col,bits] using equal.symm

private theorem basic_of_color {n l r} {c : Fin n → Fin n → Nat}
    {X : Shore c l S} {Y : Shore c r S} {a : Key} {T : M}
    (law : Laws c c) (inside : Reads X X (cell a)) (chart : Reads X Y T) (v : Nat) (j : S)
    (two : 2≤(col T j v).card) : Basic a (col T j v) := by
  let N := cell a
  let bit := fun i y => decide (T i y=v)
  have bits : Block X X Y Y bit bit := fun ⦃i y z t⦄ h => congrArg (fun z => decide (z=v)) ((chart _ _ _ _).mp h)
  have names : Block X X X X N N := fun ⦃i j x y⦄ h => (inside _ _ _ _).mp h
  have inCol (i y) : i∈col T y v ↔ T i y=v := by simp [col]
  have mid (i y x z : S) (hi : T i y=v) (hx : T x z=v) (t : Nat) :
      countIn N (col T y v) i t=countIn N (col T z v) x t := by
    have h := Block.fold law names bits (fun nm b => if nm=t ∧ b=true then 1 else 0)
      ((chart _ _ _ _).mpr (hi.trans hx.symm))
    have fmt (i y) : (Finset.univ.filter (fun z => N i z=t ∧ bit z y=true)).card=countIn N (col T y v) i t := by
      congr 1; ext; simp [bit,col,countIn,and_comm]
    simpa only [Finset.sum_boole,fmt] using h
  refine ⟨two,fun i hi x t => ⟨fun hx => mid i j x j ((inCol _ _).mp hi) ((inCol _ _).mp hx) _,?_⟩⟩
  let u := N 0 t
  let neigh := Finset.univ.filter fun z => N i z=u
  have size : neigh.card=countIn N Finset.univ 0 u := by
    have tag := Block.map names (fun nm => decide (nm=u))
    simpa [neigh,countIn] using Block.degree_eq law tag i 0
  obtain ⟨z,hz⟩ : neigh.Nonempty := by
    apply Finset.card_pos.mp
    rw [size]
    exact Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have uniform (y) (hy : y∈neigh) : Block.overlap bit i y=Block.overlap bit i z :=
    Block.gram law bits ((inside _ _ _ _).mpr (((Finset.mem_filter.mp hy).2).trans ((Finset.mem_filter.mp hz).2).symm))
  have total : ∑ y∈neigh, Block.overlap bit i y=countIn N Finset.univ 0 u*Block.overlap bit i z := by
    rw [Finset.sum_congr rfl uniform,Finset.sum_const,nsmul_eq_mul,size]
    rfl
  have expand (y) : Block.overlap bit i y=∑ q, if bit i q=true ∧ bit y q=true then 1 else 0 := by simp [Block.overlap]
  simp_rw [expand] at total
  rw [Finset.sum_comm] at total
  have summand (q) : (∑ y∈neigh, if bit i q=true ∧ bit y q=true then 1 else 0)=
      (if T i q=v then 1 else 0)*countIn N (col T j v) i u := by
    by_cases yes : T i q=v
    · rw [if_pos yes,one_mul,←mid i q i j yes ((inCol _ _).mp hi) u]
      simp only [bit,decide_eq_true_eq,yes,true_and,Finset.sum_boole]
      apply congrArg Finset.card
      ext; simp [neigh,col,countIn,and_comm]
    · simp [bit,yes]
  simp_rw [summand] at total
  rw [←Finset.sum_mul,Finset.sum_boole] at total
  have card := balanced law chart v i j
  change (col (flip T) i v).card*_= _ at total
  rw [←expand z] at total
  exact ⟨Block.overlap bit i z,by simpa only [←card] using total⟩

private theorem mask {n l r} {c : Fin n → Fin n → Nat}
    {X : Shore c l S} {Y : Shore c r S} {a : Key} {T : M}
    (law : Laws c c) (inside : Reads X X (cell a)) (chart : Reads X Y T)
    (two : ∀ x y, 2≤(col T y (T x y)).card) (x y : S) :
    col T y (T x y)∈possible.get a := by
  apply admit a (basic_of_color law inside chart _ _ (two x y))
  intro z away
  refine ⟨col T y (T z y),basic_of_color law inside chart _ _ (two z y),by simp [col],?_⟩
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact away (Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hi).2).symm.trans (Finset.mem_filter.mp hj).2⟩)

private theorem transpose_reads {n l r} {c : Fin n → Fin n → Nat} {X : Shore c l S} {Y : Shore c r S}
    {T : M} (law : Laws c c) (h : Reads X Y T) : Reads Y X (flip T) :=
  fun _ _ _ _ => ⟨fun eq => (h _ _ _ _).mp (law.rev eq),fun eq => law.rev ((h _ _ _ _).mpr eq)⟩

theorem normalized_shape {n l r} {c : Fin n → Fin n → Nat}
    {X : Shore c l S} {Y : Shore c r S} {a b : Key} {T : M}
    (law : Laws c c) (left : Reads X X (cell a)) (right : Reads Y Y (cell b))
    (chart : Reads X Y T) : Shape (cell a) (cell b) T := by
  classical
  by_cases thin : Thin T
  · exact Or.inl thin
  by_cases cyc : hasCycle b
  · exact Or.inr (Or.inl (cycle_of cyc))
  right; right
  have wide (i j : S) : 2≤(col (flip T) i (T i j)).card := by
    by_contra! small
    have mem : j∈col (flip T) i (T i j) := by simp [col]
    have pos := Finset.card_pos.mpr ⟨j,mem⟩
    obtain ⟨u,eu⟩ := Finset.card_eq_one.mp (show (col (flip T) i (T i j)).card=1 by omega)
    apply thin
    refine ⟨i,j,fun v h => ?_⟩
    have hv : v∈col (flip T) i (T i j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    rw [eu,Finset.mem_singleton] at hv mem
    exact hv.trans mem.symm
  have rowMask (i j) := mask law right (transpose_reads law chart) (fun j i => wide i j) j i
  have colMask (i j) := mask law left chart (fun x y => (balanced law chart _ x y).symm ▸ wide x y) i j
  refine ⟨fun x z i part => ?_,?_⟩
  · have hz : z∈col (flip T) i (T i z) := by simp [col]
    exact ((Finset.mem_filter.mp (columns b cyc _ (rowMask i z) z x part hz)).2).symm
  by_cases both : ∀ j, T 0 j=T 0 0
  · left
    have full : col (flip T) 0 (T 0 0)=Finset.univ := by ext; simp [col,both]
    have global (i) : col (flip T) i (T 0 0)=Finset.univ := by
      apply Finset.eq_univ_of_card
      have eq := (balanced law chart (T 0 0) i 0).symm.trans (balanced law chart _ 0 0)
      simpa [full] using eq
    have every (i j : S) : T i j=T 0 0 := by
      have mem : j∈col (flip T) i (T 0 0) := (global i).symm ▸ Finset.mem_univ j
      exact (Finset.mem_filter.mp mem).2
    exact fun i j x y => (every i j).trans (every x y).symm
  right
  obtain ⟨t,split⟩ := not_forall.mp both
  have apart : Disjoint (col (flip T) 0 (T 0 t)) (col (flip T) 0 (T 0 0)) :=
    Finset.disjoint_left.mpr (fun z f s => split (((Finset.mem_filter.mp f).2).symm.trans (Finset.mem_filter.mp s).2))
  have selected : ∃ j : S, (col (flip T) 0 (T 0 j)).card=width b ∧ col (flip T) 0 (T 0 j)≠Finset.univ := by
    have next := alternatives b cyc _ (rowMask 0 t) _ (rowMask 0 0) apart
    rcases next with h|h
    · refine ⟨t,h,fun full => split ?_⟩
      have mem : (0:S)∈col (flip T) 0 (T 0 t) := full.symm ▸ Finset.mem_univ 0
      exact ((Finset.mem_filter.mp mem).2).symm
    · refine ⟨0,h,fun full => split ?_⟩
      have mem : t∈col (flip T) 0 (T 0 0) := full.symm ▸ Finset.mem_univ t
      exact (Finset.mem_filter.mp mem).2
  obtain ⟨t,sz,proper⟩ := selected
  let v := T 0 t
  have k := sizes b cyc _ (rowMask 0 t) sz proper
  have colSize (y) : (col T y v).card=width b := (balanced law chart v 0 y).trans sz
  have rowSize (i) : (col (flip T) i v).card=width b := (balanced law chart v i 0).symm.trans (colSize 0)
  obtain ⟨u,w,cert⟩ := anchors a (width b) k
  refine ⟨0,t,u,w,?_,?_⟩
  · intro i j y one two hit
    have cert' := colMask i y
    rw [show T i y=v from hit] at cert'
    have mem : i∈col T y v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    exact hit.trans ((Finset.mem_filter.mp (cert _ cert' (colSize y) i j one two mem)).2).symm
  · intro x
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(col T x v).card by rw [colSize]; omega)
    have hit := (Finset.mem_filter.mp hi).2
    refine ⟨i,hit,fun z eq => ?_⟩
    have m := rowMask i x
    change col (flip T) i (T i x)∈possible.get b at m
    rw [show T i x=v from hit] at m
    exact singlePart b cyc _ m (rowSize i) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.trans hit⟩)
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩)

open private local_of_restriction from SmallShoreRealization in
private theorem model {n : Nat} {c : Fin n → Fin n → Nat} (cc : SmallUnion.Configuration c)
    (law : Laws c c) {v : Nat} (X : Shore c v S) :
    ∃ a : Key, ∃ e : Equiv.Perm S, Reads (e.trans X) (e.trans X) (cell a) := by
  have range (z : Fin n) : (∃ i, atPoint X i=z) ↔ c z z=v := by
    refine ⟨fun ⟨i,hi⟩ => hi ▸ (X i).property,fun eq => ?_⟩
    exact ⟨X.symm ⟨z,eq⟩,congrArg Subtype.val (X.apply_symm_apply _)⟩
  have core := local_of_restriction _ (atPoint X) (Subtype.val_injective.comp X.injective) range
    cc.diagonal cc.reverse (fun _ _ _ _ h => law.last h) cc.products
  exact Literature.zivAv_six_homogeneous_catalog _ core

/-- From any two six-point fibers of any coherent configuration, recover
the interface shape used for gluing. The ambient order is unrestricted. -/
theorem shape_of_configuration {n l r} {c : Fin n → Fin n → Nat} (cc : SmallUnion.Configuration c)
    (X : Shore c l S) (Y : Shore c r S) : Shape (rect X X) (rect Y Y) (rect X Y) := by
  have law : Laws c c := by
    refine ⟨fun h => cc.reverse _ _ _ _ h,?_,fun a b _ _ _ _ h => cc.products a b _ _ _ _ h⟩
    intro i j x y eq
    have positive : 0<Coherent.StrategyColorLaws.count c (c i j) (c j j) i j := by
      simp only [Coherent.StrategyColorLaws.count,Finset.sum_boole,Nat.cast_id,Finset.card_pos]
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩⟩
    have same := cc.products (c i j) (c j j) i j x y eq
    change Coherent.StrategyColorLaws.count c _ _ i j=Coherent.StrategyColorLaws.count c _ _ x y at same
    rw [same] at positive
    simp only [Coherent.StrategyColorLaws.count,Finset.sum_boole,Nat.cast_id,Finset.card_pos] at positive
    obtain ⟨z,hz⟩ := positive
    have diag := (Finset.mem_filter.mp hz).2.2
    exact (cc.diagonal z y j diag) ▸ diag.symm
  obtain ⟨a,e,ae⟩ := model cc law X
  obtain ⟨b,f,bf⟩ := model cc law Y
  let T := rect (e.trans X) (f.trans Y)
  have proof := normalized_shape (T:=T) law ae bf (fun _ _ _ _ => Iff.rfl)
  exact ZivAvSix.transport (e:=e) (f:=f) ⟨ae,bf,fun _ _ _ _ => Iff.rfl⟩ proof

theorem shape_of_shores {n l r} (C : CoherentAlgebra n) (X : Shore (Relations.color C) l S)
    (Y : Shore (Relations.color C) r S) : Shape (rect X X) (rect Y Y) (rect X Y) :=
  shape_of_configuration ⟨fun _ _ _ h => Relations.diagonal C h,fun _ _ _ _ h => Relations.transpose C h,
    Relations.products C⟩ X Y

end QGI.SixCross
