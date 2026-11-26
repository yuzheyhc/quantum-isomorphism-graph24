import HalfRectangle
import FourSixInterfaces

noncomputable section
namespace QGI.Coherent.OddHalfPartition
open SixTenCoordinates
open private uniform_fiber_dvd from HalfRectangle
variable {n : Nat} {c : Fin n → Fin n → Nat}

theorem palette {a p l r : Nat} [NeZero a] [NeZero (2*p)]
    (law : Laws c c) (F : Shore c l (Fin a)) (Y : Shore c r (Fin (2*p)))
    (half : ∀ x y : Nat, 0<x → a*x=(2*p)*y → p≤x) :
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    (∃ v, ∀ i j, M i j=v) ∨ ∃ v w, v≠w ∧ (∀ i j, M i j=v ∨ M i j=w) ∧
      ∀ i, (Finset.univ.filter (fun j => M i j=v)).card=p := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  let v := M 0 0
  by_cases all : ∀ i j, M i j=v
  · exact Or.inl ⟨v,all⟩
  push_neg at all
  obtain ⟨u,k,h⟩ := all
  let w := M u k
  have vw : v≠w := Ne.symm h
  let B (t : Nat) := fun i j => decide (M i j=t)
  have named (t) : Block F F Y Y (B t) (B t) := fun ⦃_ _ _ _⦄ eq => congrArg (fun x => decide (x=t)) eq
  let row (t : Nat) (i : Fin a) := Finset.univ.filter (fun j => M i j=t)
  have rd (t i) : (row t i).card=(row t 0).card := by simpa [row,B] using Block.degree_eq law (named t) i 0
  have min (i j) : p ≤ (row (M i j) 0).card := by
    let t := M i j
    have balance := FiberRectangles.balance (B t) (fun x => Block.degree_eq law (named t) x 0)
      (fun y => Block.degree_eq law (Block.flip law (named t)) y 0)
    have pos : 0 < (row t 0).card := (Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ :
      0 < (row t i).card).trans_eq (rd t i)
    apply half _ _ pos
    simpa only [row,B,decide_eq_true_eq] using balance
  have disj (i) : Disjoint (row v i) (row w i) := Finset.disjoint_left.mpr
    fun _ h₁ h₂ => vw ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
  have cap := Finset.card_le_univ (row v 0 ∪ row w 0)
  rw [Finset.card_union_of_disjoint (disj _),Fintype.card_fin] at cap
  have vp : p≤(row v 0).card := min 0 0
  have wp : p≤(row w 0).card := min u k
  have vr (i) : (row v i).card=p := (rd v i).trans (by omega)
  have wr (i) : (row w i).card=p := (rd w i).trans (by omega)
  have palette (i j) : M i j=v ∨ M i j=w := by
    have all := Finset.eq_univ_of_card (row v i ∪ row w i) (by rw [Finset.card_union_of_disjoint (disj _),vr,wr,Fintype.card_fin]; omega)
    have hit : j∈row v i ∪ row w i := all ▸ Finset.mem_univ _
    simpa [row] using hit
  exact Or.inr ⟨v,w,vw,palette,vr⟩

def sideCount {k : Nat} (side col : Fin k → Bool) (i : Fin k) :=
  ∑ z, if side i=side z then (if col z=true then 1 else 0 : Nat) else 0

private theorem odd {k a b : Nat} (s u : Fin k → Bool)
    (both : Function.Surjective s) (size : (Finset.univ.filter (fun z => u z=true)).card=2*a+1)
    (common : ∀ i, sideCount s u i=b) : False := by
  classical
  obtain ⟨i,hi⟩ := both true
  obtain ⟨j,hj⟩ := both false
  have split (z : Fin k) :
      (if s i=s z then (if u z=true then 1 else 0 : Nat) else 0) +
      (if s j=s z then (if u z=true then 1 else 0 : Nat) else 0) = (if u z=true then 1 else 0 : Nat) := by
    rw [hi,hj]; cases s z <;> simp
  have eq : sideCount s u i+sideCount s u j=(Finset.univ.filter (fun z => u z=true)).card := by
    rw [sideCount,sideCount,←Finset.sum_add_distrib]
    simp [split,Finset.sum_boole]
  rw [common,common,size] at eq
  omega

/-- A coherent partition into two halves of odd size forces a binary
half-valent rectangle to be constant on each half. -/
theorem rigid_with_rows {k m l r a : Nat} [NeZero k] [NeZero m] (law : Laws c c)
    (F : Shore c l (Fin k)) (Y : Shore c r (Fin m)) (side : Fin k → Bool) (sur : Function.Surjective side)
    (coherent : Block F F F F (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j)))
    (v w : Nat) (vw : v≠w)
    (palette : ∀ i j, c (atPoint F i) (atPoint Y j)=v ∨ c (atPoint F i) (atPoint Y j)=w)
    (cols : ∀ j, (Finset.univ.filter (fun i => c (atPoint F i) (atPoint Y j)=v)).card=2*a+1) :
    SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint Y j)) ∧
      ∀ i x, side i=side x → ∀ j, c (atPoint F i) (atPoint Y j)=c (atPoint F x) (atPoint Y j) := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  let B := fun i j => decide (M i j=v)
  let paths := fun i j => sideCount side (fun x => B x j) i
  have named : Block F F Y Y B B := fun ⦃_ _ _ _⦄ eq => congrArg (fun x => decide (x=v)) eq
  have prod : Block F F Y Y paths paths := by
    simpa only [paths,sideCount,decide_eq_true_eq] using Block.fold law coherent named
      (fun s b => if s=true then (if b=true then 1 else 0 : Nat) else 0)
  have same (i x : Fin k) (sideEq : side i=side x) (j : Fin m) : M i j=M x j := by
    by_contra ne
    have tied : paths i j=paths x j := by simp only [paths,sideCount,sideEq]
    have all (z : Fin k) : paths z j=paths i j := by
      have one : M z j=M i j ∨ M z j=M x j := by
        rcases palette z j with h|h <;> rcases palette i j with g|g <;> rcases palette x j with f|f
        all_goals first | exact Or.inl (h.trans g.symm) | exact Or.inr (h.trans f.symm) | exact (ne (g.trans f.symm)).elim
      exact one.elim (fun eq => prod eq) (fun eq => (prod eq).trans tied.symm)
    exact odd side (fun z => B z j) sur (by simpa only [B,M,decide_eq_true_eq] using cols j) all
  have separates (j : Fin m) (i x : Fin k) (eq : M i j=M x j) : side i=side x := by
    by_contra ne
    have constant (z : Fin k) : M z j=M i j := by
      by_cases h : side z=side i
      · exact same z i h j
      · have hx : side z=side x := by
          cases si : side i <;> cases sx : side x <;> cases sz : side z <;> simp_all
        exact (same z x hx j).trans eq.symm
    have both (z : Fin k) : paths z j=paths i j := prod (constant z)
    exact odd side (fun z => B z j) sur (by simpa only [B,M,decide_eq_true_eq] using cols j) both
  refine ⟨?_,same⟩
  exact ⟨fun i x j eq t => same i x (separates j i x eq) t,fun i j t eq x => by
    by_cases tag : side i=side x
    · exact (same i x tag j).symm.trans (eq.trans (same i x tag t))
    have left : M x j≠M i j := fun h => tag (separates j x i h).symm
    have right : M x t≠M i t := fun h => tag (separates t x i h).symm
    rcases palette x j with h|h <;> rcases palette x t with g|g <;> rcases palette i j with f|f
    all_goals first | exact h.trans g.symm | exact (left (h.trans f.symm)).elim | exact (right (g.trans (eq.symm.trans f).symm)).elim⟩

theorem rigid {k m l r a : Nat} [NeZero k] [NeZero m] (law : Laws c c)
    (F : Shore c l (Fin k)) (Y : Shore c r (Fin m)) (side : Fin k → Bool) (sur : Function.Surjective side)
    (coherent : Block F F F F (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j)))
    (v w : Nat) (vw : v≠w)
    (palette : ∀ i j, c (atPoint F i) (atPoint Y j)=v ∨ c (atPoint F i) (atPoint Y j)=w)
    (cols : ∀ j, (Finset.univ.filter (fun i => c (atPoint F i) (atPoint Y j)=v)).card=2*a+1) :
    SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint Y j)) :=
  (rigid_with_rows law F Y side sur coherent v w vw palette cols).1

theorem full_inter {k : Nat} (u v : Fin k → Bool) {d : Nat}
    (hs : FiberRectangles.degree u=d) (ht : FiberRectangles.degree v=d) :
    (Finset.univ.filter (fun i => u i=true ∧ v i=true)).card=d ↔ u=v := by
  let S := Finset.univ.filter (fun i => u i=true)
  let T := Finset.univ.filter (fun i => v i=true)
  have eq : Finset.univ.filter (fun i => u i=true ∧ v i=true)=S∩T := by ext i; simp [S,T]
  rw [eq]
  constructor
  · intro h
    have a : S∩T=S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by change S.card≤_; rw [show S.card=d from hs,h])
    have b : S∩T=T := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by change T.card≤_; rw [show T.card=d from ht,h])
    funext i; apply Bool.eq_iff_iff.mpr
    simpa only [S,T,Finset.mem_filter,Finset.mem_univ,true_and] using Finset.ext_iff.mp (a.symm.trans b) i
  · rintro rfl; simpa [S,T] using hs

/-- Equal columns of a binary biregular relation are recognizable on the
column shore as the maximal intersection size. -/
theorem column_block {k m l r v b : Nat} (law : Laws c c) (F : Shore c l (Fin k)) (Y : Shore c r (Fin m))
    (B : Fin m → Fin k → Bool) (cells : ∀ j i, B j i=true ↔ c (atPoint F i) (atPoint Y j)=v)
    (deg : ∀ j, FiberRectangles.degree (B j)=b) :
    Block Y Y Y Y (fun j z => decide (B j=B z)) (fun j z => decide (B j=B z)) := by
  have named : Block F F Y Y (fun i j => B j i) (fun i j => B j i) := by
    intro i j x y h; apply Bool.eq_iff_iff.mpr; rw [cells,cells,h]
  have eq (j z) : Block.overlap B j z=b ↔ B j=B z := full_inter _ _ (deg j) (deg z)
  have gram := Block.gram law (Block.flip law named)
  intro i j x y h
  apply decide_eq_decide.mpr
  exact (eq i j).symm.trans ((congrArg (·=b) (gram h)).to_iff.trans (eq x y))

/-- On a six-by-eight rectangle, a non-twin interface leaves at most
two possible columns for a prescribed full vector of six colors. -/
theorem short_or_twins {l r : Nat} (law : Laws c c) (F : Shore c l (Fin 6)) (Y : Shore c r (Fin 8)) :
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    SplitRectangle.Twins M ∨ ∀ j, ∃ a b, ∀ k, (∀ i, M i j=M i k) → k=a ∨ k=b := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  rcases palette (p:=4) law F Y (fun x y hx h => by omega) with ⟨v,all⟩|⟨v,w,vw,pal,rows⟩
  · left; exact ⟨fun i x _ _ j => (all i j).trans (all x j).symm,fun _ j z _ i => (all i j).trans (all i z).symm⟩
  let B (j : Fin 8) (i : Fin 6) := decide (M i j=v)
  have named : Block F F Y Y (fun i j => B j i) (fun i j => B j i) := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have row (i j) : FiberRectangles.degree (fun t => B t i)=FiberRectangles.degree (fun t => B t j) := Block.degree_eq law named i j
  have col (i j) : FiberRectangles.degree (B i)=FiberRectangles.degree (B j) := Block.degree_eq law (Block.flip law named) i j
  have cap (i) : FiberRectangles.degree (fun t => B t i)=4 := by simpa only [B,M,FiberRectangles.degree,decide_eq_true_eq] using rows i
  have balance := FiberRectangles.balance (fun i j => B j i) (fun i => row i 0) (fun j => col j 0)
  rw [cap] at balance
  have deg (j) : FiberRectangles.degree (B j)=3 := (col j 0).trans (by omega)
  have cb := column_block (v:=v) law F Y B (fun _ _ => by simp [B,M]) deg
  let C (j) := Finset.univ.filter (fun k => B k=B j)
  let d := (C 0).card
  have unit (j) : (C j).card=d := by
    have flip (i x : Fin 8) : decide (B i=B x)=true ↔ B x=B i := by rw [decide_eq_true_eq]; exact eq_comm
    simpa only [C,d,flip] using Block.degree_eq law cb j 0
  by_cases small : d≤2
  · right; intro j
    obtain ⟨a,b,ab⟩ := DegreeClassRigidity.two_labels (C j) 0 ((unit j).trans_le small)
    exact ⟨a,b,fun k h => ab k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,funext (fun i => congrArg (fun t => decide (t=v)) (h i).symm)⟩)⟩
  have dvd : d∣8 := uniform_fiber_dvd B d unit
  have lim : 4≤d := by
    by_cases eq : d=3
    · rw [eq] at dvd; exact ((by decide : ¬(3∣8)) dvd).elim
    · omega
  have sameName (i x : Fin 6) (j z : Fin 8) : B j i=B z x ↔ M i j=M x z := by
    rcases pal i j with h|h <;> rcases pal x z with g|g <;> simp [B,M,h,g,vw,Ne.symm vw]
  let rowSet (i : Fin 6) (j : Fin 8) := Finset.univ.filter (fun k => B k i=B j i)
  have rowSize (i j) : (rowSet i j).card=4 := by
    by_cases h : B j i=true
    · simpa only [rowSet,h,FiberRectangles.degree] using cap i
    · have eq : rowSet i j=(Finset.univ.filter (fun k => B k i=true))ᶜ := by
        ext k; simp only [rowSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
        cases a : B k i <;> cases b : B j i <;> simp_all
      rw [eq,Finset.card_compl,Fintype.card_fin,show (Finset.univ.filter (fun k => B k i=true)).card=4 from cap i]
  have coincides (i j) : C j=rowSet i j := Finset.eq_of_subset_of_card_le
    (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrFun (Finset.mem_filter.mp hk).2 i⟩)
    (by rw [rowSize,unit]; exact lim)
  have colsEq (i j z) (h : B j i=B z i) : B j=B z := (Finset.mem_filter.mp
    ((coincides i z).symm ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ j,h⟩ : j∈rowSet i z) : j∈C z)).2
  left
  constructor
  · intro i x j h y; apply (sameName _ _ _ _).mp
    have hij := (sameName _ _ _ _).mpr h
    by_cases hit : B y i=B j i
    · have eq := colsEq i y j hit; simpa only [eq] using hij
    · have hx : B y x≠B j x := fun hh => hit (congrFun (colsEq x y j hh) i)
      cases h₁ : B y i <;> cases h₂ : B y x <;> cases h₃ : B j i <;> cases h₄ : B j x <;> simp_all
  · intro i j z h x
    exact (sameName _ _ _ _).mp (congrFun (colsEq i j z ((sameName _ _ _ _).mpr h)) x)

/-- A nonuniform twin rectangle on the four- and six-point fibers
forces the six-by-eight rectangle to be twin as well. -/
theorem force {l r s : Nat} (law : Laws c c) (A : Shore c l (Fin 4)) (F : Shore c r (Fin 6)) (Y : Shore c s (Fin 8))
    (twin : FiberPairExtension.twins c l r)
    (nonuniform : ¬∀ i j, c (atPoint A i) (atPoint F j)=c (atPoint A 0) (atPoint F 0)) :
    SplitRectangle.Twins (fun i j => c (atPoint F i) (atPoint Y j)) := by
  classical
  rcases palette (p:=3) law A F (fun x y hx h => by omega) with ⟨u,all⟩|⟨u,w,uw,pal,rows⟩
  · exact (nonuniform (fun i j => (all i j).trans (all 0 0).symm)).elim
  let B := fun j i => decide (c (atPoint A i) (atPoint F j)=u)
  have named : Block A A F F (fun i j => B j i) (fun i j => B j i) := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=u)) h
  have row (i j) : FiberRectangles.degree (fun t => B t i)=FiberRectangles.degree (fun t => B t j) := Block.degree_eq law named i j
  have col (i j) : FiberRectangles.degree (B i)=FiberRectangles.degree (B j) := Block.degree_eq law (Block.flip law named) i j
  have cap (i) : FiberRectangles.degree (fun t => B t i)=3 := by simpa only [B,FiberRectangles.degree,decide_eq_true_eq] using rows i
  have balance := FiberRectangles.balance (fun i j => B j i) (fun i => row i 0) (fun j => col j 0)
  rw [cap] at balance
  have deg (j) : FiberRectangles.degree (B j)=2 := (col j 0).trans (by omega)
  have cb := column_block (v:=u) law A F B (fun _ _ => by simp [B]) deg
  let side := fun j => B j 0
  have bit (i j x y) : B j i=B y x ↔ c (atPoint A i) (atPoint F j)=c (atPoint A x) (atPoint F y) := by
    rcases pal i j with h|h <;> rcases pal x y with g|g <;> simp [B,h,g,uw,Ne.symm uw]
  have key (i j) : B i=B j ↔ side i=side j := by
    refine ⟨fun h => congrFun h 0,fun h => funext (fun k => (bit k i k j).mpr ?_)⟩
    exact twin.2 (A 0) (F i) (F j) ((bit 0 i 0 j).mp h) (A k)
  have co : Block F F F F (fun i j => decide (side i=side j)) (fun i j => decide (side i=side j)) := by
    intro i j x y h
    simpa only [←key] using cb h
  have sur : Function.Surjective side := by
    have sz : (Finset.univ.filter (fun i => side i=true)).card=3 := cap 0
    intro b
    by_contra! no
    have all (i) : side i=(!b) := by cases hs : side i <;> cases b <;> simp_all
    cases b <;> simp [all] at sz
  rcases palette (p:=4) law F Y (fun x y hx h => by omega) with ⟨v,all⟩|⟨v,z,vz,pal',r⟩
  · exact ⟨fun i x _ _ j => (all i j).trans (all x j).symm,fun _ j x _ i => (all i j).trans (all i x).symm⟩
  let N := fun i j => decide (c (atPoint F i) (atPoint Y j)=v)
  have nb : Block F F Y Y N N := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have nr (i) : FiberRectangles.degree (N i)=4 := by simpa only [N,FiberRectangles.degree,decide_eq_true_eq] using r i
  have nc (j x) : FiberRectangles.degree (fun i => N i j)=FiberRectangles.degree (fun i => N i x) := Block.degree_eq law (Block.flip law nb) j x
  have bal := FiberRectangles.balance N (fun i => (nr i).trans (nr 0).symm) (fun j => nc j 0)
  rw [nr] at bal
  apply rigid (a:=1) law F Y side sur co v z vz pal'
  intro j
  have h : FiberRectangles.degree (fun i => N i j)=3 := (nc j 0).trans (by omega)
  simpa only [FiberRectangles.degree,N,decide_eq_true_eq] using h

end QGI.Coherent.OddHalfPartition
