import RegionalEightTwelveHalfCatalog
import RegionalEightTwelveStats

namespace QGI.Coherent.RegionalEightTwelveHalfLaws
open SixTenCoordinates RegionalEightTwelveStats EightTwelveHalf
open EightTwelveCatalog (Row cell)
abbrev J := Fin 12

def supports (a : J → C) : Family := Finset.univ.image a

private theorem weighted (a : J → C) (m : Nat) (uniform : ∀ j, copies a j=m) (φ : C → Nat) :
    ∑ j, φ (a j)=m*∑ t∈supports a, φ t := by
  have inside : ∀ j∈(Finset.univ : Finset J), a j∈supports a := fun j _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [←Finset.sum_fiberwise_of_maps_to inside (fun j => φ (a j)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  calc
    _ = ∑ _k∈(Finset.univ.filter fun k => a k=a j), φ (a j) := Finset.sum_congr rfl
      (fun k hk => congrArg φ (Finset.mem_filter.mp hk).2)
    _ = m*φ (a j) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      exact congrArg (·*φ (a j)) (uniform j)

private theorem scaled (a : J → C) (m : Nat) (u : ∀ j, copies a j=m) (q : C → Prop) [DecidablePred q] :
    (Finset.univ.filter (fun j => q (a j))).card=m*((supports a).filter q).card := by
  simpa only [Finset.sum_boole] using weighted a m u (fun t => if q t then 1 else 0)

private theorem out_not (s : C) (bal : s.card=4) : outer s∉s := by
  have ex : ∃ i : P, i∉s := by
    by_contra! all
    have eq := Finset.eq_univ_of_forall all
    rw [eq,Finset.card_univ,Fintype.card_fin] at bal
    omega
  obtain ⟨i,hi⟩ := ex
  have n : ((List.finRange 8).find? (fun j => decide (j∉s))).isSome := by
    rw [List.find?_isSome]; exact ⟨i,List.mem_finRange _,decide_eq_true hi⟩
  obtain ⟨j,hj⟩ := Option.isSome_iff_exists.mp n
  have p := List.find?_some hj
  simpa only [outer,hj,Option.getD_some] using of_decide_eq_true p

variable {n l d v w : Nat} {c : Fin n → Fin n → Nat}

structure Chart (M : Row) (F : Shore c l P) (Y : Shore c d J) (v w : Nat) : Prop where
  names : ∀ i j x y, cell M i j=cell M x y ↔ c (atPoint F i) (atPoint F j)=c (atPoint F x) (atPoint F y)
  two : ∀ j i, color F Y j i=v ∨ color F Y j i=w
  balance : ∀ j, (family F Y v j).card=4

private theorem membership {M} {F : Shore c l P} {Y : Shore c d J} (h : Chart M F Y v w) {i j x y}
    (eq : i∈family F Y v j ↔ x∈family F Y v y) : c (atPoint Y j) (atPoint F i)=c (atPoint Y y) (atPoint F x) := by
  by_cases hj : i∈family F Y v j
  · exact (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp (eq.mp hj)).2.symm
  have hx := mt eq.mpr hj
  have left := (h.two j i).resolve_left fun same => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,same⟩)
  have right := (h.two y x).resolve_left fun same => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,same⟩)
  exact left.trans right.symm

private theorem profile {M} {F : Shore c l P} {Y : Shore c d J} (h : Chart M F Y v w)
    (law : Laws c c) {i j x y} (eq : i∈family F Y v j ↔ x∈family F Y v y) (u : Nat) :
    count M (family F Y v j) i u=count M (family F Y v y) x u := by
  let a := family F Y v
  have localBlock : Block F F F F (fun i k => cell M i k) (fun i k => cell M i k) :=
    fun ⦃i k x z⦄ e => (h.names i k x z).mpr e
  have folded := Block.fold law localBlock (Block.flip law (incidence F Y F Y v))
    (fun k b => if k=u ∧ b=true then 1 else 0) (law.rev (membership h eq))
  have calcCount (s : C) (p : P) :
      (Finset.univ.filter (fun z => cell M p z=u ∧ z∈s)).card=count M s p u := by
    congr 1
    ext z
    simp [and_comm,count]
  simpa only [decide_eq_true_eq,Finset.sum_boole,calcCount] using folded

private theorem rowCount {M} {F : Shore c l P} {Y : Shore c d J} (h : Chart M F Y v w)
    (law : Laws c c) (i : P) : (Finset.univ.filter (fun j => i∈family F Y v j)).card=6 := by
  have deg := degrees law F Y v
  have total := deg.2.2
  rw [h.balance 0] at total
  have eq := deg.2.1 i
  change (Finset.univ.filter (fun j => i∈family F Y v j)).card=_
  change (Finset.univ.filter (fun j => i∈family F Y v j)).card=_ at eq
  omega

private theorem gram_count {M} {F : Shore c l P} {Y : Shore c d J} (h : Chart M F Y v w) (law : Laws c c)
    (seed : J) (inside : (0:P)∈family F Y v seed) (i j : P) :
    valency M (cell M i j)*(Finset.univ.filter (fun k => i∈family F Y v k ∧ j∈family F Y v k)).card
    =6*count M (family F Y v seed) 0 (cell M i j) := by
  let a := family F Y v
  let u := cell M i j
  let neigh := Finset.univ.filter (fun z => cell M i z=u)
  have deg (b : P) : count M Finset.univ b u=valency M u := by
    have rel : Block F F F F (fun p q => decide (cell M p q=u)) (fun p q => decide (cell M p q=u)) :=
      fun ⦃p q x y⦄ e => congrArg (fun z => decide (z=u)) ((h.names p q x y).mpr e)
    simpa only [count,valency,decide_eq_true_eq] using Block.degree_eq law rel b 0
  let μ := fun z : P => (Finset.univ.filter (fun k => i∈a k ∧ z∈a k)).card
  have constant (z) (hz : z∈neigh) : μ z=μ j := by
    have e := (h.names i z i j).mp (Finset.mem_filter.mp hz).2
    simpa only [μ,Block.overlap,decide_eq_true_eq] using Block.gram law (Block.flip law (incidence F Y F Y v)) e
  have eqsum : (∑ z∈neigh, μ z)=valency M u*μ j := by
    calc
      _ = ∑ _z∈neigh, μ j := Finset.sum_congr rfl (fun z hz => constant z hz)
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; exact congrArg (·*μ j) (deg i)
  have expand (z) : μ z=∑ k : J, if i∈a k ∧ z∈a k then 1 else 0 := by simp [μ]
  rw [←eqsum]
  simp_rw [expand]
  rw [Finset.sum_comm]
  have one (k : J) : (∑ z∈neigh, if i∈a k ∧ z∈a k then 1 else 0)=
      (if i∈a k then 1 else 0)*count M (a seed) 0 u := by
    split_ifs with hh
    · rw [one_mul,←profile h law (show i∈a k ↔ (0:P)∈a seed from iff_of_true hh inside) u]
      simp only [hh,true_and,Finset.sum_boole]
      unfold count
      apply congrArg Finset.card
      ext z
      simp [neigh,and_comm,a]
    · simp [hh]
  simp_rw [one]
  rw [←Finset.sum_mul,Finset.sum_boole,rowCount h law]
  rfl

private theorem uniform_hist {M} {F : Shore c l P} {Y : Shore c d J}
    (h : Chart M F Y v w) (law : Laws c c) : Uniform (supports (family F Y v)) := by
  let a := family F Y v
  let m := copies a 0
  have mass : 0 < m := Finset.card_pos.mpr ⟨(0:J),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have u : ∀ j, copies a j=m := uniform_copies law F Y v
  intro s hs t ht i j eq k
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp ht
  have gram : Block Y Y Y Y (fun x y => (a x∩a y).card) (fun x y => (a x∩a y).card) :=
    fun ⦃x y z p⦄ h => mixed_counts law F Y F Y v v h
  have folded := Block.fold law gram (incidence F Y F Y v) (fun v hit => if v=k.val ∧ hit=true then 1 else 0) (membership h eq)
  simp only [decide_eq_true_eq,Finset.sum_boole] at folded
  apply Nat.eq_of_mul_eq_mul_left mass
  exact (scaled a m u (fun x => (a b∩x).card=k.val ∧ i∈x)).symm.trans
    (folded.trans (scaled a m u (fun x => (a g∩x).card=k.val ∧ j∈x)))

attribute [local irreducible] EightTwelveCatalog.row EightTwelveCatalog.rows8 EightTwelveCatalog.rows12

private theorem colors_occur : ∀ a : Fin 21, ∀ i j : P, ∃ t : P,
    cell (EightTwelveCatalog.row 8 a.val) i j=cell (EightTwelveCatalog.row 8 a.val) 0 t := by native_decide

set_option maxHeartbeats 2000000 in
theorem model_chart (idx : Fin 21) {F : Shore c l P} {Y : Shore c d J}
    (h : Chart (EightTwelveCatalog.row 8 idx.val) F Y v w) (law : Laws c c) :
    Separates (EightTwelveCatalog.row 8 idx.val) (supports (family F Y v)) ∧
    ∃ k : Fin 5, ∃ e : Equiv.Perm P, (supports (family F Y v)).image (fun t => t.image e)=model k := by
  let M := EightTwelveCatalog.row 8 idx.val
  let a := family F Y v
  let m := copies a 0
  have u : ∀ j, copies a j=m := uniform_copies law F Y v
  have pos : 0 < m := Finset.card_pos.mpr ⟨(0:J),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have total : 12=m*(supports a).card := by simpa using weighted a m u (fun _ => 1)
  have six : 6=m*((supports a).filter (fun t => (0:P)∈t)).card := (rowCount h law 0).symm.trans (scaled a m u (fun t => (0:P)∈t))
  have dv : m∣6 := ⟨_,six⟩
  have small := Nat.le_of_dvd (by decide : 0 < 6) dv
  have opts : ∀ q : Fin 7, 0<q.val → q.val∣6 → q.val∈([1,2,3,6] : List Nat) := by native_decide
  have mass := opts ⟨m,by omega⟩ pos dv
  have nonempty := Finset.card_pos.mp ((by decide : 0 < 6).trans_eq (rowCount h law 0).symm)
  obtain ⟨seed,mem⟩ := nonempty
  have inside : (0:P)∈a seed := (Finset.mem_filter.mp mem).2
  have outside := out_not (a seed) (h.balance seed)
  have allowed (b : J) : allow M (a seed) (a b)=true := by
    apply decide_eq_true
    intro i j
    split_ifs with hit
    · exact profile h law (iff_of_true hit inside) _
    · exact profile h law (iff_of_false hit outside) _
  have equation (i j : P) : valency M (cell M i j)*m*
      ((supports a).filter (fun t => i∈t ∧ j∈t)).card=6*count M (a seed) 0 (cell M i j) := by
    rw [Nat.mul_assoc,←scaled a m u]; exact gram_count h law seed inside i j
  apply model_of_constraints idx M rfl (a seed) _ m mass (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h.balance seed⟩) inside (allowed seed)
  · apply decide_eq_true
    intro i j
    exact ⟨_,by simpa only [Nat.mul_one,Nat.mul_assoc] using (equation i j).symm⟩
  · intro t _ equal
    have vals := of_decide_eq_true equal
    have transfer (i j : P) : count M (a seed) 0 (cell M i j)=count M t 0 (cell M i j) := by
      obtain ⟨z,hit⟩ := colors_occur idx i j
      change cell M i j=cell M 0 z at hit
      rw [hit]; exact (vals z).1
    have fit (i j : P) : valency M (cell M i j)*m*((supports a).filter (fun t => i∈t ∧ j∈t)).card=6*count M t 0 (cell M i j) :=
      (equation i j).trans (congrArg (6*·) (transfer i j))
    refine ⟨decide_eq_true (fun i j => ⟨_,(fit i j).symm⟩),?_,?_⟩
    · intro b hb
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h.balance j⟩,decide_eq_true ?_⟩
      intro i z
      have he := of_decide_eq_true (allowed j) i z
      split_ifs at he ⊢ <;> first | exact he.trans (vals z).1 | exact he.trans (vals z).2
    · intro z
      unfold rule
      split_ifs with eq
      · change ((supports a).filter (fun _ => true=true)).card=12/m
        rw [Finset.filter_true_of_mem (fun _ _ => rfl),total,Nat.mul_div_cancel_left _ pos]
      · let i : P := Fin.ofNat' 8 ((z.val-1)/8)
        let j : P := Fin.ofNat' 8 ((z.val-1)%8)
        have p : 0 < valency M (cell M i j) := by
          obtain ⟨b,hb⟩ := colors_occur idx i j
          exact Finset.card_pos.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb.symm⟩⟩
        simpa only [RegionalHalfSearch.cut,decide_eq_true_eq] using
          (show ((supports a).filter (fun t => i∈t ∧ j∈t)).card=6*count M t 0 (cell M i j)/(valency M (cell M i j)*m) by
            rw [←fit i j,Nat.mul_div_cancel_left _ (Nat.mul_pos p pos)])
  · exact uniform_hist h law


def rowCells (a : J → C) (i : P) := Finset.univ.filter (fun j => i∈a j)
def crossGram (a : J → C) (i j : P) := (Finset.univ.filter (fun k => i∈a k ∧ j∈a k)).card

def NamedGram {l : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l P) (a : J → C) :=
  Function.Injective (rowCells a) → ∀ i j x y, crossGram a i j=crossGram a x y →
  c (atPoint F i) (atPoint F j)=c (atPoint F x) (atPoint F y)

private theorem named_gram {idx : Fin 21} {F : Shore c l P} {Y : Shore c d J}
    (h : Chart (EightTwelveCatalog.row 8 idx.val) F Y v w) (law : Laws c c)
    (sep : Separates (EightTwelveCatalog.row 8 idx.val) (supports (family F Y v))) :
    NamedGram F (family F Y v) := by
  let a := family F Y v
  let m := copies a 0
  have u := uniform_copies law F Y v
  have pos : 0 < m := Finset.card_pos.mpr ⟨(0:J),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  intro inj i j x y eq
  apply (h.names i j x y).mp
  apply sep
  · intro s t he
    apply inj
    ext k
    have inc : a k∈supports a := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have test := Finset.ext_iff.mp he (a k)
    change a k∈(supports a).filter (fun u => s∈u) ↔ a k∈(supports a).filter (fun u => t∈u) at test
    simpa only [rowCells,Finset.mem_filter,Finset.mem_univ,inc,true_and] using test
  · apply Nat.eq_of_mul_eq_mul_left pos
    exact (scaled a m u (fun b => i∈b ∧ j∈b)).symm.trans (eq.trans (scaled a m u (fun b => x∈b ∧ y∈b)))

/-- Classify the twelve supports in the caller's original eight-point coordinates. -/
theorem classification (F : Shore c l P) (Y : Shore c d J)
    (localData : SmallShore.Local (fun i j => c (atPoint F i) (atPoint F j)) l) (law : Laws c c)
    (two : ∀ j i, color F Y j i=v ∨ color F Y j i=w) (balance : ∀ j, (family F Y v j).card=4) :
    NamedGram F (family F Y v) ∧ ∃ k : Fin 5, ∃ e : Equiv.Perm P, (supports (family F Y v)).image (fun t => t.image e)=model k := by
  obtain ⟨idx,z,names⟩ := Literature.eight_homogeneous_catalog _ localData
  let F' := z.trans F
  have reindex (j) : family F' Y v j=(family F Y v j).map z.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_map_equiv,Equiv.symm_symm,family,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  have chart : Chart (EightTwelveCatalog.row 8 idx.val) F' Y v w :=
    ⟨fun i j x y => (names i j x y).symm,fun j i => two j (z i),fun j => by rw [reindex,Finset.card_map,balance]⟩
  obtain ⟨sep,k,e,rep⟩ := model_chart idx chart law
  have identify (i j) : i∈family F' Y v j ↔ z i∈family F Y v j := by simp [family,F',atPoint]
  have rows (i : P) : rowCells (family F' Y v) i=rowCells (family F Y v) (z i) := by ext j; simp only [rowCells,Finset.mem_filter,Finset.mem_univ,true_and,identify]
  have counts (i j : P) : crossGram (family F' Y v) i j=crossGram (family F Y v) (z i) (z j) := by simp only [crossGram,identify]
  constructor
  · intro inj i j x y heq
    obtain ⟨i,rfl⟩ := z.surjective i; obtain ⟨j,rfl⟩ := z.surjective j
    obtain ⟨x,rfl⟩ := z.surjective x; obtain ⟨y,rfl⟩ := z.surjective y
    apply named_gram chart law sep (fun s t eq => z.injective (inj ((rows s).symm.trans (eq.trans (rows t))))) i j x y
    exact (counts i j).trans (heq.trans (counts x y).symm)
  · exact ⟨k,z.symm.trans e,by
      rw [←rep]
      unfold supports
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro j _
      simp only [Function.comp_apply]
      rw [reindex,Finset.map_eq_image,Finset.image_image]
      rfl⟩

end QGI.Coherent.RegionalEightTwelveHalfLaws

