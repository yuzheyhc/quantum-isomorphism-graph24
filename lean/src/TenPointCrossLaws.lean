import TenPointCrossCatalog
import RegionalTenTen

namespace QGI.Coherent.TenPointCrossLaws
open TenPointCross
open SixTenCoordinates hiding V
open FourTwelveFunctional (source)

variable {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l V) (Y : Shore c r V)
def entry (i j : V) := c (atPoint F i) (atPoint Y j)
def col (v : Nat) (j : V) := Finset.univ.filter fun i => entry F Y i j=v
def row (v : Nat) (i : V) := Finset.univ.filter fun j => entry F Y i j=v

theorem col_size (law : Laws c c) (v : Nat) (i j : V) : (col F Y v j).card=(row F Y v i).card := by
  let B (x y : V) := decide (entry F Y x y=v)
  have named : Block F F Y Y B B := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=v)) eq
  have e := FiberRectangles.balance B (fun x => Block.degree_eq law named x i) (fun y => Block.degree_eq law (Block.flip law named) y j)
  have sizes : 10*(row F Y v i).card=10*(col F Y v j).card := by
    simpa only [row,col,FiberRectangles.degree,B,decide_eq_true_eq] using e
  omega

variable {a : Key} (law : Laws c c)
    (names : ∀ i j x y : V, c (atPoint F i) (atPoint F j)=c (atPoint F x) (atPoint F y) ↔ cell a i j=cell a x y)

include law names in
theorem count_block (v : Nat) {i k x y : V} (e : entry F Y i k=entry F Y x y) (u : Nat) :
    count a (col F Y v k) i u=count a (col F Y v y) x u := by
  let B (x y : V) := decide (entry F Y x y=v)
  let C := col F Y v
  have cross : Block F F Y Y B B := fun ⦃_ _ _ _⦄ e => congrArg (fun t => decide (t=v)) e
  have localNames : Block F F F F (cell a) (cell a) := fun ⦃i k x y⦄ eq => (names i k x y).mp eq

  have E := Block.fold law localNames cross (fun t b => if (t=u ∧ b=true) then 1 else 0) e
  have shrink (i j) : (Finset.univ.filter (fun z => cell a i z=u ∧ entry F Y z j=v)).card=count a (C j) i u := by
    apply congrArg Finset.card; ext z; simp [C,col,count,and_comm]
  simpa only [B,decide_eq_true_eq,Finset.sum_boole,shrink] using E

include law names in
theorem constraints (v d : Nat) (j : V) (size : ∀ i, (row F Y v i).card=d)
    (smallest : ∀ i k, d≤(col F Y (entry F Y i k) k).card) : Admits a d (col F Y v j) ∧
    ∀ i∈col F Y v j, ∀ k z : V, cell a i k=cell a 0 z →
    d*sig a (col F Y v j) i z=valency a (cell a 0 z)*(row F Y v i∩row F Y v k).card := by
  classical
  let B (x y : V) := decide (entry F Y x y=v)
  let C := col F Y v
  let H (i k : V) := (Finset.univ.filter fun h => i∈C h ∧ k∈C h).card
  have bits (i k) : i∈C k ↔ entry F Y i k=v := by simp [C,col]
  have cross : Block F F Y Y B B := fun ⦃_ _ _ _⦄ e => congrArg (fun t => decide (t=v)) e
  have localNames : Block F F F F (cell a) (cell a) := fun ⦃i k x y⦄ eq => (names i k x y).mp eq
  have gram : Block F F F F H H := by
    intro i k x y eq; simpa only [H,Block.overlap,bits,B,decide_eq_true_eq] using Block.gram law cross eq
  have countEq {i k x y : V} (e : entry F Y i k=entry F Y x y) (u : Nat) := count_block F Y law names v e u
  have inside (i k x y : V) (hi : i∈C k) (hx : x∈C y) (u : Nat) : count a (C k) i u=count a (C y) x u :=
    countEq (((bits _ _).mp hi).trans ((bits _ _).mp hx).symm) u
  have coeff (i : V) (hi : i∈C j) (k z : V) (hk' : cell a i k=cell a 0 z) :
      d*sig a (C j) i z=valency a (cell a 0 z)*H i k := by
    let u := cell a 0 z
    let N := Finset.univ.filter fun k => cell a i k=u
    have regular := Block.degree_eq law (Block.map localNames (fun t => decide (t=u))) i 0
    have card : N.card=valency a u := by simpa only [N,count,valency,decide_eq_true_eq] using regular
    have hk : k∈N := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk'⟩
    change d*count a (C j) i u=valency a u*H i k
    have outer (x) (hx : x∈N) : H i x=H i k := gram ((names _ _ _ _).mpr ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hk).2.symm))
    have total : (∑ x∈N,H i x)=valency a u*H i k := by
      rw [Finset.sum_congr rfl outer,Finset.sum_const,smul_eq_mul,card]
    have expand (x) : H i x=∑ h : V, if i∈C h ∧ x∈C h then 1 else 0 := by simp [H]
    have contrib (h : V) : (∑ x∈N,if i∈C h ∧ x∈C h then 1 else 0 : Nat)=(if i∈C h then 1 else 0)*count a (C j) i u := by
      by_cases hit : i∈C h
      · simp only [hit,true_and,if_true,one_mul,Finset.sum_boole]
        rw [←inside i h i j hit hi]
        apply congrArg Finset.card; ext x; simp [N,count,and_comm]
      · simp [hit]
    rw [←total]; simp_rw [expand]; rw [Finset.sum_comm]
    simp_rw [contrib]
    rw [←Finset.sum_mul,Finset.sum_boole]
    simp only [bits]
    exact congrArg (·*count a (C j) i u) (size i).symm
  constructor
  · refine ⟨(col_size F Y law v 0 j).trans (size 0),fun i hi k hk => funext (fun z => inside _ _ _ _ hi hk _),?_,?_⟩
    · intro i hi z
      let u := cell a 0 z
      have h := Block.degree_eq law (Block.map localNames (fun t => decide (t=u))) i 0
      have hz : 0<(Finset.univ.filter (fun t : V => cell a 0 t=u)).card := Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
      simp only [decide_eq_true_eq] at h
      obtain ⟨k,hk⟩ := Finset.card_pos.mp (hz.trans_eq h.symm)
      exact ⟨H i k,coeff i hi k z (Finset.mem_filter.mp hk).2⟩
    · intro i hi
      refine (smallest i j).trans (Finset.card_le_card ?_)
      intro k hk
      have eq := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun mem => hi ((bits _ _).mpr (eq.symm.trans ((bits _ _).mp mem))),
        funext (fun z => countEq eq _)⟩
  · intro i hi k z hz
    have same : H i k=(row F Y v i∩row F Y v k).card := by
      apply congrArg Finset.card; ext t; simp [H,C,col,row]
    exact (coeff i hi k z hz).trans (congrArg (_*·) same)

/-- The two directions of a whole named rectangle have the same color partition. -/
theorem swap (law : Laws c c) (i k j t : V) :
    entry F Y i j=entry F Y k t ↔ entry Y F j i=entry Y F t k := ⟨law.rev,law.rev⟩

def Chart {n l : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l V) (a : Key) :=
  ∀ i j x y : V, c (atPoint F i) (atPoint F j)=c (atPoint F x) (atPoint F y) ↔ cell a i j=cell a x y

variable {G H : Graph n} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (p : PerfectStrategy G H E)

private theorem range' {b : Fin n → Fin n → Nat} {l} (A : Shore b l V) (x : Fin n) :
    (∃ i, atPoint A i=x) ↔ b x x=l :=
  ⟨fun ⟨i,h⟩ => h ▸ (A i).property,fun h => ⟨A.symm ⟨x,h⟩,congrArg Subtype.val (A.apply_symm_apply _)⟩⟩

include p in
theorem chart (X : Shore (source G) l V) : ∃ (a : Key) (e : Equiv.Perm V), Chart (e.trans X) a := by
  obtain ⟨m,diag⟩ := SmallUnion.diagonal_names p
  let T : Shore (StrategyColorLaws.targetName p) l V := X.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  exact Literature.zivAv_ten_homogeneous_catalog _ (SmallShore.correspondence p (atPoint X) (atPoint T) l
    (Subtype.val_injective.comp X.injective) (Subtype.val_injective.comp T.injective) (range' X) (range' T)).1

end QGI.Coherent.TenPointCrossLaws
