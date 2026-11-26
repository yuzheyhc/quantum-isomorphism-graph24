import SixTenCoordinates

set_option maxHeartbeats 800000
namespace QGI.Coherent.NineTwelveDesign
open SixTenCoordinates

abbrev P := Fin 9
abbrev L := Fin 12
abbrev Inc := L → P → Bool

def line (b : Inc) (i : L) := Finset.univ.filter (fun x => b i x)
def concurrence (b : Inc) (x y : P) := ∑ i, if b i x && b i y then 1 else 0
def score (b : Inc) (i : L) (x : P) := ∑ y, if b i y then concurrence b y x else 0

theorem score_block {n} {c d : Fin n → Fin n → Nat} {a t} {A : Shore c a P} {S : Shore d a P}
    {Y : Shore c t L} {Z : Shore d t L} {b e : Inc} (law : Laws c d) (h : Block Y Z A S b e) :
    Block Y Z A S (score b) (score e) :=
  Block.fold law h (Block.fold law (Block.flip law h) h (fun u v => if u && v then 1 else 0))
    (fun u k => if u then k else 0)

theorem symmetry (b : Inc) (x y) : concurrence b x y=concurrence b y x := by
  simp only [concurrence,Bool.and_comm]

theorem diag (b : Inc) (cd : ∀ x, FiberRectangles.degree (fun i => b i x)=4) (x) :
    concurrence b x x=4 := by
  simpa only [concurrence,Bool.and_self,FiberRectangles.degree,Finset.card_filter] using cd x

theorem sum_concurrence (b : Inc) (rd : ∀ i, (line b i).card=3)
    (cd : ∀ x, FiberRectangles.degree (fun i => b i x)=4) (x) : ∑ y, concurrence b x y=12 := by
  have each (i : L) : (∑ y : P, if b i x && b i y then 1 else 0 : Nat)=if b i x then 3 else 0 := by
    cases h : b i x with
    | false => simp [h]
    | true => simpa only [h,Bool.true_and,if_true,line,Finset.card_filter] using rd i
  have cnt := cd x
  simp only [FiberRectangles.degree,Finset.card_filter] at cnt
  unfold concurrence
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun i _ => each i)]
  have times (i : L) : (if b i x then 3 else 0 : Nat)=3*(if b i x then 1 else 0) := by
    cases b i x <;> rfl
  simp_rw [times]
  rw [← Finset.mul_sum,cnt]; decide

/-- A single basic triple relation has one common concurrence on every
distinct pair occurring in a line. At any flag the length-three walk
count is the diagonal value plus the two pair concurrences. -/
theorem pair_weight (b : Inc) (rd : ∀ i, (line b i).card=3)
    (cd : ∀ x, FiberRectangles.degree (fun i => b i x)=4)
    (flat : ∀ i x j y, b i x=true → b j y=true → score b i x=score b j y) :
    ∃ k, (k=1 ∨ k=2 ∨ k=4) ∧ ∀ i x y, b i x=true → b i y=true → x≠y → concurrence b x y=k := by
  classical
  obtain ⟨o,ho⟩ := Finset.card_pos.mp ((rd 0).symm ▸ (by decide : 0 < 3))
  let C := score b 0 o
  have val (i x) (hit : x∈line b i) : score b i x=C :=
    flat i x 0 o (Finset.mem_filter.mp hit).2 (Finset.mem_filter.mp ho).2
  let k := (C-4)/2
  have same (i x y) (hx : b i x=true) (hy : b i y=true) (ne : x≠y) :
      concurrence b x y=k := by
    obtain ⟨a,s,t,as',at',st,triple⟩ := Finset.card_eq_three.mp (rd i)
    have ha : a∈line b i := by simp [triple]
    have hs : s∈line b i := by simp [triple]
    have ht : t∈line b i := by simp [triple]
    have eq (z) : score b i z=concurrence b a z+concurrence b s z+concurrence b t z := by
      change (∑ y, if b i y then concurrence b y z else 0)=_
      rw [← Finset.sum_filter]
      change (∑ y ∈ line b i, concurrence b y z)=_
      simp [triple,as',at',st,Nat.add_assoc]
    have va := (eq a).symm.trans (val i a ha)
    have vs := (eq s).symm.trans (val i s hs)
    have vt := (eq t).symm.trans (val i t ht)
    rw [diag b cd a,symmetry b s a,symmetry b t a] at va
    rw [diag b cd s,symmetry b t s] at vs
    rw [diag b cd t] at vt
    have ku : concurrence b a s=k := by dsimp [k]; omega
    have kv : concurrence b a t=k := by dsimp [k]; omega
    have kw : concurrence b s t=k := by dsimp [k]; omega
    have cx : x=a ∨ x=s ∨ x=t := by
      have h : x∈line b i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
      simpa [triple] using h
    have cy : y=a ∨ y=s ∨ y=t := by
      have h : y∈line b i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩
      simpa [triple] using h
    have uk := (symmetry b s a).trans ku
    have vk := (symmetry b t a).trans kv
    have wk := (symmetry b t s).trans kw
    rcases cx with e|e|e <;> rcases cy with h|h|h
    · exact (ne (e.trans h.symm)).elim
    · exact (congrArg₂ (concurrence b) e h).trans ku
    · exact (congrArg₂ (concurrence b) e h).trans kv
    · exact (congrArg₂ (concurrence b) e h).trans uk
    · exact (ne (e.trans h.symm)).elim
    · exact (congrArg₂ (concurrence b) e h).trans kw
    · exact (congrArg₂ (concurrence b) e h).trans vk
    · exact (congrArg₂ (concurrence b) e h).trans wk
    · exact (ne (e.trans h.symm)).elim
  have off (x y) (h : x≠y) : concurrence b x y=0 ∨ concurrence b x y=k := by
    by_cases both : ∃ i, b i x=true ∧ b i y=true
    · obtain ⟨i,hx,hy⟩ := both; exact Or.inr (same i x y hx hy h)
    · left; apply Finset.sum_eq_zero; intro i _
      by_cases hx : b i x=true
      · have hy : b i y=false := Bool.eq_false_iff.mpr (fun h => both ⟨i,hx,h⟩)
        simp [hy]
      · simp [hx]
  have total := sum_concurrence b rd cd 0
  rw [← Finset.add_sum_erase _ (fun y => concurrence b 0 y) (Finset.mem_univ 0),diag b cd 0] at total
  have hdiv : k ∣ ∑ y ∈ Finset.univ.erase (0:P), concurrence b 0 y := by
    apply Finset.dvd_sum
    intro j hj
    rcases off 0 j (Finset.ne_of_mem_erase hj).symm with h|h <;> simp [h]
  have eight : (∑ y ∈ Finset.univ.erase (0:P), concurrence b 0 y)=8 := by omega
  rw [eight] at hdiv
  obtain ⟨a,s,t,as',_,_,triple⟩ := Finset.card_eq_three.mp (rd 0)
  have inc (w) (h : w∈line b 0) := (Finset.mem_filter.mp h).2
  have ab := same 0 a s (inc _ (by simp [triple])) (inc _ (by simp [triple])) as'
  have bound : concurrence b a s ≤ concurrence b a a := by
    apply Finset.sum_le_sum; intro i _
    cases b i a <;> cases b i s <;> decide
  rw [ab,diag b cd] at bound
  refine ⟨k,?_,same⟩
  exact (by decide : ∀ z : Fin 5, z.val ∣ 8 → z.val=1 ∨ z.val=2 ∨ z.val=4) ⟨k,by omega⟩ hdiv

def touching (b : Inc) (x : P) := (Finset.univ.erase x).filter (fun y => 0<concurrence b x y)

theorem hit_iff (b : Inc) (x y) : 0<concurrence b x y ↔ ∃ i, b i x=true ∧ b i y=true := by
  simp only [concurrence,←Finset.card_filter,Finset.card_pos,Finset.Nonempty,Finset.mem_filter,Finset.mem_univ,true_and,
    Bool.and_eq_true]

theorem neighbor_count {b : Inc} {k : Nat} (rd : ∀ i, (line b i).card=3)
    (cd : ∀ x, FiberRectangles.degree (fun i => b i x)=4)
    (pair : ∀ i x y, b i x=true → b i y=true → x≠y → concurrence b x y=k) (x : P) :
    k*(touching b x).card=8 := by
  have total := sum_concurrence b rd cd x
  rw [←Finset.add_sum_erase _ (fun y => concurrence b x y) (Finset.mem_univ x),diag b cd] at total
  have each (y) (hy : y∈Finset.univ.erase x) : concurrence b x y=if 0<concurrence b x y then k else 0 := by
    split_ifs with pos
    · obtain ⟨i,hi,hh⟩ := (hit_iff b x y).mp pos
      exact pair i x y hi hh (Finset.ne_of_mem_erase hy).symm
    · omega
  have e := Finset.sum_congr rfl each
  rw [←Finset.sum_filter] at e
  change (∑ y ∈ Finset.univ.erase x, concurrence b x y)=∑ _ ∈ touching b x, k at e
  rw [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm] at e
  omega

theorem max_copies {b : Inc} {k : Nat} (rd : ∀ i, (line b i).card=3)
    (pair : ∀ i x y, b i x=true → b i y=true → x≠y → concurrence b x y=k) (i : L) :
    (Finset.univ.filter (fun j => b j=b i)).card≤k := by
  obtain ⟨x,y,z,xy,_,_,shape⟩ := Finset.card_eq_three.mp (rd i)
  have marked (v) (hv : v∈line b i) := (Finset.mem_filter.mp hv).2
  have hx := marked x (by simp [shape])
  have hy := marked y (by simp [shape])
  rw [←pair i x y hx hy xy]
  simp only [concurrence,←Finset.card_filter]
  apply Finset.card_le_card
  intro j hj
  have eq := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [eq,hx,hy,Bool.and_self]⟩

theorem steiner {b : Inc} (rd : ∀ i, (line b i).card=3)
    (cd : ∀ x, FiberRectangles.degree (fun i => b i x)=4)
    (pair : ∀ i x y, b i x=true → b i y=true → x≠y → concurrence b x y=1)
    {x y : P} (ne : x≠y) : ∃! i, b i x=true ∧ b i y=true := by
  have cnt : (touching b x).card=8 := by simpa only [one_mul] using neighbor_count rd cd pair x
  have all : touching b x=Finset.univ.erase x := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simp [cnt])
  have member : y∈touching b x := by rw [all]; simp [ne.symm]
  obtain ⟨i,hx,hy⟩ := (hit_iff b x y).mp (Finset.mem_filter.mp member).2
  have c := pair i x y hx hy ne
  simp only [concurrence,←Finset.card_filter] at c
  obtain ⟨a,only⟩ := Finset.card_eq_one.mp c
  have atA (j) (h : b j x=true ∧ b j y=true) : j=a := by
    have hit : j∈Finset.univ.filter (fun a => b a x && b a y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [h.1,h.2]; decide⟩
    exact Finset.mem_singleton.mp ((Finset.ext_iff.mp only j).mp hit)
  exact ⟨i,⟨hx,hy⟩,fun j hj => (atA j hj).trans (atA i ⟨hx,hy⟩).symm⟩


end QGI.Coherent.NineTwelveDesign





