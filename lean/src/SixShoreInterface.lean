import SixShoreAtlas
import RegionalTenTwelve

noncomputable section
namespace QGI.Coherent.SixShoreInterface
open SixTenCoordinates BinaryShore SixShoreAtlas
open private simple_twins from RegionalTenTwelve
abbrev F6 := Fin 6
def name {n l r m : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l F6) (Y : Shore c r (Fin m)) (i : F6) (j : Fin m) := c (atPoint F i) (atPoint Y j)
def flag {n l r m : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l F6) (Y : Shore c r (Fin m)) (v : Nat) (i : F6) (j : Fin m) := decide (name F Y i j=v)
def Reads {n l : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l F6) (a : Key) := ∀ i j x y,
    c (atPoint F i) (atPoint F j)=c (atPoint F x) (atPoint F y) ↔ cell a i j=cell a x y
variable {n l r h v w : Nat} {c d : Fin n → Fin n → Nat} [NeZero (2*h)]
    (F : Shore c l F6) (Y : Shore c r (Fin (2*h))) (T : Shore d l F6) (Z : Shore d r (Fin (2*h)))

theorem cross (v : Nat) : Block F T Y Z (flag F Y v) (flag T Z v) :=
  fun ⦃_ _ _ _⦄ e => congrArg (fun t => decide (t=v)) e

theorem palette (law : Laws c c) (allowed : h=4 ∨ h=8) : (∃ v, ∀ i j, name F Y i j=v) ∨
    ∃ v w, (∀ i j, name F Y i j=v ∨ name F Y i j=w) ∧ ∀ i, degree (flag F Y v) i=h := by
  rcases OddHalfPartition.palette (p:=h) law F Y (fun x y pos eq => by rcases allowed with rfl|rfl <;> omega) with u|⟨v,w,_,two,rows⟩
  · exact Or.inl u
  · exact Or.inr ⟨v,w,two,fun i => by simpa only [degree,flag,name,decide_eq_true_eq] using rows i⟩

theorem description (law : Laws c c) (half : h=4 ∨ h=8) {a : Key} (atlas : Reads F a)
    (two : ∀ i j, name F Y i j=v ∨ name F Y i j=w) (rows : ∀ i, degree (flag F Y v) i=h) :
    (¬hard a → SplitRectangle.Twins (name F Y)) ∧ (hard a → ∀ j, ∃ u : Fin 9, ∀ i, flag F Y v i j=mask u i) := by
  let B := flag F Y v
  have block := cross F Y F Y v
  have eqrows := Block.degree_eq law (Block.flip law block)
  have bal := FiberRectangles.balance B rows (fun j => eqrows j 0)
  have cols (j) : (support B j).card=3 := (eqrows j 0).trans (by rcases half with rfl|rfl <;> omega)
  have C : Chart (b:=h) (d:=3) F Y B (cell a) := ⟨law,block,fun i j x y eq =>
    (RegionalEightTwelveHalfModels.both_colors (two i j) (two x y)).mpr (by simpa only [B,flag,decide_eq_decide] using eq),
    fun i j x y => (atlas i j x y).symm,rows,cols⟩
  obtain ⟨ok,profiles⟩ := necessary C (by decide) (by decide)
  constructor
  · intro soft
    apply simple_twins (name F Y) two (support B 0)
    intro j
    apply (cases_of a half (cols 0) (ok 0)).1 soft
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,cols j⟩,ok j,profiles j 0⟩
  · intro hardKey j
    obtain ⟨u,hu⟩ := (cases_of a half (cols j) (ok j)).2 hardKey
    refine ⟨u,fun i => Bool.eq_iff_iff.mpr ?_⟩
    have eq : i∈support B j ↔ i∈subsets u := by rw [hu]
    simpa only [support,subsets,Finset.mem_filter,Finset.mem_univ,true_and] using eq

theorem two_target (law : Laws c d) (two : ∀ i j, name F Y i j=v ∨ name F Y i j=w) (i j) :
    name T Z i j=v ∨ name T Z i j=w := by
  let u := name T Z i j
  have eq := Block.degree_eq law (cross F Y T Z u) i i
  have mem : j∈Finset.univ.filter (fun y => flag T Z u i y=true) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [flag,u]⟩
  obtain ⟨k,hk⟩ := Finset.card_pos.mp ((Finset.card_pos.mpr ⟨j,mem⟩).trans_eq eq.symm)
  have e : name F Y i k=u := of_decide_eq_true (Finset.mem_filter.mp hk).2
  change u=v ∨ u=w
  rw [←e]; exact two i k

structure Columns (a : Key) where
  mark : Nat
  leftWord : Fin (2*h) → Fin 9
  rightWord : Fin (2*h) → Fin 9
  sourceBits : ∀ i j, flag F Y mark i j=mask (leftWord j) i
  targetBits : ∀ i j, flag T Z mark i j=mask (rightWord j) i
  reflect : ∀ i j x y, flag F Y mark i j=flag T Z mark x y → name F Y i j=name T Z x y

theorem choose (law : Laws c d) (src : Laws c c) (tgt : Laws d d) (half : h=4 ∨ h=8) {a : Key}
    (sf : Reads F a) (tf : Reads T a) (ha : hard a) : Nonempty (Columns F Y T Z a) := by
  classical
  rcases palette F Y src half with ⟨v,full⟩|⟨v,w,pal,rows⟩
  · have tar (i j) : name T Z i j=v := ((two_target F Y T Z law (v:=v) (w:=v) (fun i j => Or.inl (full i j)) i j)).elim id id
    exact ⟨⟨v,fun _ => 8,fun _ => 8,fun i j => by simp [flag,full,mask],fun i j => by simp [flag,tar,mask],
      fun i j x y _ => (full i j).trans (tar x y).symm⟩⟩
  · have pal' := two_target F Y T Z law pal
    have rows' (i) : degree (flag T Z v) i=h := (Block.degree_eq law (cross F Y T Z v) i i).symm.trans (rows i)
    choose a0 ha0 using (description F Y src half sf pal rows).2 ha
    choose b0 hb0 using (description T Z tgt half tf pal' rows').2 ha
    refine ⟨⟨v,a0,b0,(fun i j => ha0 j i),(fun i j => hb0 j i),fun i j x y eq => ?_⟩⟩
    exact (RegionalEightTwelveHalfModels.both_colors (pal i j) (pal' x y)).mpr (by simpa only [flag,decide_eq_decide] using eq)
end QGI.Coherent.SixShoreInterface
