import FourByEven

noncomputable section
namespace QGI.Coherent.HalfRectangle
open SixTenCoordinates

private theorem uniform_fiber_dvd {a : Nat} {α : Type} [DecidableEq α]
    (f : Fin a → α) (d : Nat) (size : ∀ i, (Finset.univ.filter (fun j => f j=f i)).card=d) :
    d ∣ a := by
  let values := Finset.univ.image f
  have all : Finset.univ.filter (fun i => f i∈values)=Finset.univ := Finset.eq_univ_of_forall
    (fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  have eq := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin a)) values f
  have eval : (∑ u ∈ values, (Finset.univ.filter (fun j => f j=u)).card) = ∑ _u ∈ values, d := Finset.sum_congr (rfl : values=values) (fun u hu => by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    exact size i)
  rw [eval,all,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at eq
  exact ⟨values.card,eq.symm.trans (Nat.mul_comm _ _)⟩

/-- Products of the relation that counts row intersections with the active
cross color are constant on that color. Thus the number of rows meeting a
fixed row in t points, multiplied by t, is divisible by its row size. -/
theorem overlap_dvd {n a b l r : Nat} [NeZero a] [NeZero b] {c : Fin n → Fin n → Nat}
    (law : Laws c c) (F : Shore c l (Fin a)) (Y : Shore c r (Fin b))
    (v p : Nat) (base : c (atPoint F 0) (atPoint Y 0)=v)
    (B : Fin a → Fin b → Bool) (bits : ∀ i j, B i j=true ↔ c (atPoint F i) (atPoint Y j)=v)
    (rows : ∀ i, FiberRectangles.degree (B i)=p) (i : Fin a) (t : Nat) :
    p ∣ Block.hist (Block.overlap B) i t * t := by
  classical
  let H := Block.overlap B
  let R := Finset.univ.filter (fun k => H i k=t)
  let U (k) := Finset.univ.filter (fun j => B k j=true)
  have named : Block F F Y Y B B := by
    intro i j x y h
    apply Bool.eq_iff_iff.mpr
    rw [bits,bits,h]
  have gram := Block.gram law named
  let paths (k : Fin a) (y : Fin b) := ∑ z, if H k z=t then (if B z y=true then 1 else 0 : Nat) else 0
  have prod : Block F F Y Y paths paths :=
    Block.fold law gram named (fun h bit => if h=t then (if bit=true then 1 else 0) else 0)
  have count (k) : (U i ∩ U k).card=H i k := by
    apply congrArg Finset.card
    ext j; simp [U,H,Block.overlap]
  have total (y) : paths i y = ∑ k ∈ R, if B k y=true then 1 else 0 := by
    simp only [paths,R,Finset.sum_filter]
  have number : (∑ y ∈ U i, paths i y)=p*paths 0 0 := by
    calc
      _ = ∑ _y ∈ U i, paths 0 0 := Finset.sum_congr rfl (fun y hy =>
        prod ((bits i y).mp (Finset.mem_filter.mp hy).2 |>.trans base.symm))
      _ = _ := by rw [Finset.sum_const,smul_eq_mul,show (U i).card=p from rows i]
  refine ⟨paths 0 0,?_⟩
  calc
    Block.hist (Block.overlap B) i t * t = ∑ _k ∈ R, t := by simp [Block.hist,R,H]
    _ = ∑ k ∈ R, ∑ j ∈ U i, (if B k j=true then 1 else 0 : Nat) := Finset.sum_congr rfl (fun k hk => by
      have eq : (U i).filter (fun j => B k j=true)=U i ∩ U k := by ext j; simp [U,and_assoc]
      rw [Finset.sum_boole,eq,count,(Finset.mem_filter.mp hk).2]; simp)
    _ = ∑ j ∈ U i, paths i j := by rw [Finset.sum_comm]; simp only [total]
    _ = _ := number

/-- The parallel rows are the rows equal to a fixed row or to its
complement. Their common class size divides the total number of rows.
For prime row size, every other intersection class has size divisible
by that prime. -/
theorem parallel {n a p l r : Nat} [NeZero a] [NeZero (2*p)] {c : Fin n → Fin n → Nat}
    (law : Laws c c) (F : Shore c l (Fin a)) (Y : Shore c r (Fin (2*p)))
    (prime : Nat.Prime p)
    (only : ∀ d, 0<d → d≤a → d∣a → p∣(a-d) → d=a)
    (v : Nat) (base : c (atPoint F 0) (atPoint Y 0)=v)
    (B : Fin a → Fin (2*p) → Bool) (bits : ∀ i j, B i j=true ↔ c (atPoint F i) (atPoint Y j)=v)
    (rows : ∀ i, FiberRectangles.degree (B i)=p) :
    ∀ i, (∀ j, B i j=B 0 j) ∨ (∀ j, B i j=!(B 0 j)) := by
  classical
  let U (i) := Finset.univ.filter (fun j => B i j=true)
  let H := Block.overlap B
  have size (i) : (U i).card=p := rows i
  have complement (i) : (U i)ᶜ.card=p := by rw [Finset.card_compl,size,Fintype.card_fin]; omega
  have meet (i j) : (U i ∩ U j).card=H i j := by
    apply congrArg Finset.card
    ext z; simp [H,Block.overlap,U]
  have bound (i j) : H i j≤p := by
    calc H i j = _ := (meet i j).symm
         _ ≤ (U i).card := Finset.card_le_card Finset.inter_subset_left
         _ = p := size i
  let key (i : Fin a) : Finset (Finset (Fin (2*p))) := {U i,(U i)ᶜ}
  have compare (i j) : key i=key j ↔ H i j=0 ∨ H i j=p := by
    constructor
    · intro h
      have mem : U i ∈ key j := h ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp mem with eq|eq
      · right; rw [←meet,eq,Finset.inter_self,size]
      · have hit := Finset.mem_singleton.mp eq
        left; rw [←meet,hit,Finset.inter_comm]; simp
    · intro h
      rcases h with h|h
      · have disj : Disjoint (U i) (U j) := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ((meet i j).trans h))
        have eq : U i=(U j)ᶜ := Finset.eq_of_subset_of_card_le
          (fun z hz => Finset.mem_compl.mpr (fun hz' => Finset.disjoint_left.mp disj hz hz'))
          (by rw [size,complement])
        simp [key,eq,Finset.pair_comm]
      · have left := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left : U i ∩ U j ⊆ U i) (by rw [size,meet,h])
        have right := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : U i ∩ U j ⊆ U j) (by rw [size,meet,h])
        simp [key,left.symm.trans right]
  have named : Block F F Y Y B B := by
    intro i j x y h; apply Bool.eq_iff_iff.mpr; rw [bits,bits,h]
  have gram := Block.gram law named
  have symmetric (i j) : key j=key i ↔ H i j=0 ∨ H i j=p := eq_comm.trans (compare i j)
  let tied (i j) := decide (H i j=0 ∨ H i j=p)
  have bT : Block F F F F tied tied := Block.map gram (fun x => decide (x=0 ∨ x=p))
  let d := (Finset.univ.filter (fun j => key j=key 0)).card
  have cls (i) : (Finset.univ.filter (fun j => key j=key i)).card=d := by
    have eq := Block.degree_eq law bT i 0
    simpa only [tied,decide_eq_true_eq,←symmetric,d] using eq
  have dv := uniform_fiber_dvd key d cls
  have pos : 0<d := Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have le : d≤a := by simpa only [d,Fintype.card_fin] using Finset.card_le_univ (Finset.univ.filter (fun j => key j=key 0))
  let middle := (Finset.range p).erase 0
  have parts := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin a)) middle (H 0)
  have each (t) (ht : t∈middle) : p ∣ Block.hist H 0 t := by
    have zt := Finset.mem_erase.mp ht
    have ct := overlap_dvd law F Y v p base B bits rows 0 t
    exact (prime.dvd_mul.mp ct).resolve_right (fun h =>
      (not_le_of_gt (Finset.mem_range.mp zt.2)) (Nat.le_of_dvd (Nat.pos_of_ne_zero zt.1) h))
  have divis : p ∣ (Finset.univ.filter (fun j => H 0 j∈middle)).card := by
    rw [←parts]
    exact Finset.dvd_sum each
  have split : Finset.univ.filter (fun j => H 0 j∈middle)=(Finset.univ.filter (fun j => key j=key 0))ᶜ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,middle,
      Finset.mem_erase,Finset.mem_range,symmetric]
    have := bound 0 j
    omega
  rw [split,Finset.card_compl,Fintype.card_fin] at divis
  have full : Finset.univ.filter (fun j => key j=key 0)=Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa only [Fintype.card_fin] using only d pos le dv divis)
  intro i
  have eq := (Finset.mem_filter.mp (full ▸ Finset.mem_univ i)).2
  have mem : U i∈key 0 := eq ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp mem with h|h
  · left; intro j; apply Bool.eq_iff_iff.mpr
    simpa [U] using (Finset.ext_iff.mp h j)
  · have hc := Finset.mem_singleton.mp h
    right; intro j; apply Bool.eq_iff_iff.mpr
    have hmem : (j∈U i ↔ j∉U 0) := hc ▸ Finset.mem_compl
    simpa [U] using hmem

end QGI.Coherent.HalfRectangle


namespace QGI.Coherent.HalfRectangle
open SixTenCoordinates FourTwelveFunctional

/-- The arithmetic hypotheses test only the two fiber sizes. The prime
divisors apply to sizes of intersection classes on the first fiber. -/
theorem rectangle {n a p l r : Nat} [NeZero a] [NeZero (2*p)] {c : Fin n → Fin n → Nat}
    (law : Laws c c) (F : Shore c l (Fin a)) (Y : Shore c r (Fin (2*p))) (prime : Nat.Prime p)
    (half : ∀ x y : Nat, 0<x → a*x=(2*p)*y → p≤x)
    (only : ∀ d, 0<d → d≤a → d∣a → p∣(a-d) → d=a) :
    FiberPairExtension.twins c l r := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  let v := M 0 0
  suffices twin : SplitRectangle.Twins M by
    constructor
    · intro i x j eq y
      simpa only [M,atPoint,Equiv.apply_symm_apply] using twin.1 (F.symm i) (F.symm x) (Y.symm j)
        (by simpa only [M,atPoint,Equiv.apply_symm_apply] using eq) (Y.symm y)
    · intro i j y eq x
      simpa only [M,atPoint,Equiv.apply_symm_apply] using twin.2 (F.symm i) (Y.symm j) (Y.symm y)
        (by simpa only [M,atPoint,Equiv.apply_symm_apply] using eq) (F.symm x)
  by_cases all : ∀ i j, M i j=v
  · exact ⟨fun i x _ _ y => (all i y).trans (all x y).symm,fun _ j y _ x => (all x j).trans (all x y).symm⟩
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
  have para := parallel law F Y prime only v rfl (B v) (fun i j => by simp [B,M])
    (fun i => by simpa [B,row,FiberRectangles.degree] using vr i)
  let ls (i : Fin a) := B v i 0
  let rs (j : Fin (2*p)) := B v 0 j
  have active (i j) : M i j=v ↔ ls i=rs j := by
    have first : B v 0 0=true := by simp [B,v]
    have hit : M i j=v ↔ B v i j=true := by simp [B]
    rw [hit]
    rcases para i with same|opp
    · change B v i j=true ↔ B v i 0=B v 0 j
      rw [same j,same 0,first]; exact eq_comm
    · change B v i j=true ↔ B v i 0=B v 0 j
      rw [opp j,opp 0,first]; cases B v 0 j <;> decide
  have eq : M=fun i j => if ls i=rs j then v else w := by
    funext i j
    by_cases h : M i j=v
    · rw [if_pos ((active _ _).mp h),h]
    · rw [if_neg (mt (active _ _).mpr h)]; exact (palette _ _).resolve_left h
  rw [eq]
  exact SplitRectangle.twins_of_halves ls rs v w

end QGI.Coherent.HalfRectangle
