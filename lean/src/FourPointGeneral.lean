import RegionalCycleExtension

noncomputable section
namespace QGI.Coherent.FourPointGeneral
open SixTenCoordinates FourTwelveCycle FourTwelveTypes Relations
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)

abbrev L := Fin 4

structure Cycle {m : Nat} (b : Fin m → Edge) where
  points : Equiv.Perm L
  label : Fin m → Fin 4
  edges : ∀ j, edge (b j) = (edge (cycle (label j))).map points.toEmbedding
  full : Function.Surjective label

def Full {m : Nat} (b : Fin m → Edge) := Function.Surjective b ∧ ∀ e, 6*mult b e=m

theorem classify_all {n m} [NeZero m] {c : Fin n → Fin n → Nat} (law : Laws c c) {l r : Nat}
    (F : Shore c l L) (Y : Shore c r (Fin m)) (v : Nat)
    (two : ∀ j, (Finset.univ.filter fun i => c (atPoint F i) (atPoint Y j)=v).card=2) :
    ∃ b : (Fin m) → Edge, (∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) ∧
      ((∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ (Nonempty (Cycle b) ∨ Full b)) := by
  classical
  let B := fun i j => decide (c (atPoint F i) (atPoint Y j)=v)
  have named : Block F F Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun t => decide (t=v)) h
  have repr : ∀ s : Finset L, s.card=2 → ∃ e, edge e=s := by native_decide
  choose b hb using fun j => repr _ (two j)
  have cells (i j) : (c (atPoint F i) (atPoint Y j)=v) ↔ i∈edge (b j) := by simp [hb]
  have bits (i j) : B i j = true ↔ i∈edge (b j) := by simp [B,cells]
  have rows (i : L) : degree b i=degree b 0 := by
    simpa only [degree,bits] using Block.degree_eq law named i 0
  have same (j k : (Fin m)) : Block.overlap (fun j i => B i j) j k = 2 ↔ b j=b k := by
    have sets : Finset.univ.filter (fun i => B i j=true ∧ B i k=true) = edge (b j) ∩ edge (b k) := by
      ext i; simp [bits]
    simpa only [Block.overlap,sets,overlap] using edge_overlap (b j) (b k)
  have uniform (j x : (Fin m)) : mult b (b j)=mult b (b x) := by
    have h := Block.hist_eq law (Block.gram law (Block.flip law named)) j x 2
    simpa only [Block.hist,same,mult,eq_comm] using h
  refine ⟨b,cells,?_⟩
  rcases shapes b rows with matched|⟨q,uses,full⟩|onto
  · exact Or.inl matched
  · choose label hl using uses
    have inj : Function.Injective (fun i => edge (cycle i)) := by native_decide
    exact Or.inr (Or.inl ⟨⟨q,label,hl,fun i => by
      obtain ⟨j,hj⟩ := full i
      exact ⟨j,inj (Finset.map_injective _ ((hl j).symm.trans hj))⟩⟩⟩)
  · have eq (e : Edge) : mult b e=mult b (b 0) := by
      obtain ⟨j,rfl⟩ := onto e; exact uniform j 0
    have total : (∑ e, mult b e)=m := by
      simpa [mult] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m)) (Finset.univ : Finset Edge) b
    have bad : m=6*mult b (b 0) := by
      simpa only [Finset.sum_congr rfl (fun e _ => eq e), Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using total.symm
    exact Or.inr (Or.inr ⟨onto,fun e => (congrArg (6*·) (eq e)).trans bad.symm⟩)

theorem classify {n m} [NeZero m] (nodiv : ¬6 ∣ m) {c : Fin n → Fin n → Nat} (law : Laws c c) {l r : Nat}
    (F : Shore c l L) (Y : Shore c r (Fin m)) (v : Nat)
    (two : ∀ j, (Finset.univ.filter fun i => c (atPoint F i) (atPoint Y j)=v).card=2) :
    ∃ b : (Fin m) → Edge, (∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) ∧
      ((∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ Nonempty (Cycle b)) := by
  obtain ⟨b,cells,sh⟩ := classify_all law F Y v two
  exact ⟨b,cells,sh.imp_right (fun h => h.elim id (fun f => (nodiv ⟨_,(f.2 0).symm⟩).elim))⟩

theorem interface_detailed {n m} [NeZero m] {G : Graph n} {l r : Nat}
    (F : Shore (Relations.color (closure G)) l L) (Y : Shore (Relations.color (closure G)) r (Fin m)) :
    let c := Relations.color (closure G)
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    (∃ i j, ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) ∨ (∀ i j, M i j=M 0 0) ∨
      ∃ v w, v≠w ∧ (∀ i j, M i j=v ∨ M i j=w) ∧ ∃ b : (Fin m) → Edge,
        (∀ i j, M i j=v ↔ i∈edge (b j)) ∧ ((∃ e, ∀ j, b j=e ∨ b j=opposite e) ∨ Nonempty (Cycle b) ∨ Full b) := by
  classical
  let c := Relations.color (closure G)
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  let S (t : Nat) (j : (Fin m)) := Finset.univ.filter (fun i => M i j=t)
  let v := M 0 0
  by_cases all : ∀ i j, M i j=v
  · exact Or.inr (Or.inl all)
  push_neg at all
  obtain ⟨i₁,j₁,diff⟩ := all
  let w := M i₁ j₁
  have vw : v ≠ w := Ne.symm diff
  have constant (t : Nat) (j : (Fin m)) : (S t j).card = (S t 0).card := by
    let B := fun i j => decide (M i j=t)
    have name : Block F F Y Y B B := fun ⦃_ _ _ _⦄ h => congrArg (fun u => decide (u=t)) h
    simpa only [S,B,decide_eq_true_eq] using Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) name) j 0
  have present (i : L) (j : (Fin m)) : 0 < (S (M i j) 0).card :=
    (Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ :
      0 < (S (M i j) j).card).trans_eq (constant _ _)
  have singleton (i : L) (j : (Fin m)) (one : (S (M i j) 0).card=1) :
      ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i := by
    intro z hz
    have endz := (Relations.end_colors (closure G) hz).2.trans (F i).property
    let k := F.symm ⟨z,endz⟩
    have loc : atPoint F k=z := congrArg Subtype.val (F.apply_symm_apply _)
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp ((constant _ j).trans one)
    have kMem : k∈S (M i j) j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      change c (atPoint F k) (atPoint Y j)=_; rw [loc]; exact Relations.transpose _ hz⟩
    have iMem : i∈S (M i j) j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    rw [ht,Finset.mem_singleton] at kMem iMem
    exact loc.symm.trans (congrArg (atPoint F) (kMem.trans iMem.symm))
  by_cases oneV : (S v 0).card=1
  · exact Or.inl ⟨0,0,singleton 0 0 oneV⟩
  by_cases oneW : (S w 0).card=1
  · exact Or.inl ⟨i₁,j₁,singleton i₁ j₁ oneW⟩
  have disj (j) : Disjoint (S v j) (S w j) := Finset.disjoint_left.mpr
    fun _ av aw => vw (((Finset.mem_filter.mp av).2).symm.trans (Finset.mem_filter.mp aw).2)
  have cap := Finset.card_le_univ (S v 0 ∪ S w 0)
  rw [Finset.card_union_of_disjoint (disj _)] at cap
  change _ ≤ 4 at cap
  have pv : 0 < (S v 0).card := present 0 0
  have pw : 0 < (S w 0).card := present i₁ j₁
  have nv : (S v 0).card=2 := by omega
  have nw : (S w 0).card=2 := by omega
  have palette (i j) : M i j=v ∨ M i j=w := by
    have eq : S v j ∪ S w j=Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (disj _),constant,constant w,nv,nw]; decide)
    have h : i ∈ S v j ∪ S w j := eq ▸ Finset.mem_univ _
    simpa only [Finset.mem_union,S,Finset.mem_filter,Finset.mem_univ,true_and] using h
  obtain ⟨b,cells,shape⟩  := classify_all (sourceLaws _) F Y v (fun j => (constant v j).trans nv)
  exact Or.inr (Or.inr ⟨v,w,vw,palette,b,cells,shape⟩)

theorem interface_all {n m} [NeZero m] {G : Graph n} {l r : Nat}
    (F : Shore (Relations.color (closure G)) l L) (Y : Shore (Relations.color (closure G)) r (Fin m)) :
    let c := Relations.color (closure G)
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    (∃ i j, ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) ∨ SplitRectangle.Twins M ∨
      ∃ v w, (∀ i j, M i j=v ∨ M i j=w) ∧ ∃ b : (Fin m) → Edge,
        (∀ i j, M i j=v ↔ i∈edge (b j)) ∧ (Nonempty (Cycle b) ∨ Full b) := by
  classical
  let c := Relations.color (closure G)
  let M := fun i j => c (atPoint F i) (atPoint Y j)
  rcases interface_detailed F Y with thin|all|⟨v,w,vw,palette,b,cells,shape⟩
  · exact Or.inl thin
  · exact Or.inr (Or.inl ⟨fun i x _ _ y => (all i y).trans (all x y).symm,
      fun _ _ _ _ x => (all x _).trans (all x _).symm⟩)
  rcases shape with ⟨e,matching⟩ | cycle'
  · right; left
    let ls (i : L) := decide (i∈edge e)
    let rs (j : (Fin m)) := decide (b j=e)
    have opposite_ne : ∀ t : Edge, opposite t ≠ t := by native_decide
    have mark (i j) : M i j=v ↔ ls i=rs j := by
      rw [cells i j]
      rcases matching j with a|a
      · simp [ls,rs,a]
      · simp [ls,rs,a,opposite_edge,opposite_ne]
    have eq : M = fun i j => if ls i=rs j then v else w := by
      funext i j
      by_cases hv : M i j=v
      · rw [if_pos ((mark i j).mp hv),hv]
      · rw [if_neg (mt (mark i j).mpr hv)]; exact (palette i j).resolve_left hv
    change SplitRectangle.Twins M
    rw [eq]
    exact SplitRectangle.twins_of_halves ls rs v w
  · exact Or.inr (Or.inr ⟨v,w,palette,b,cells,cycle'⟩)

theorem interface {n m} [NeZero m] (nodiv : ¬6 ∣ m) {G : Graph n} {l r : Nat}
    (F : Shore (Relations.color (closure G)) l L) (Y : Shore (Relations.color (closure G)) r (Fin m)) :
    let c := Relations.color (closure G)
    let M := fun i j => c (atPoint F i) (atPoint Y j)
    (∃ i j, ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) ∨ SplitRectangle.Twins M ∨
      ∃ v w, (∀ i j, M i j=v ∨ M i j=w) ∧ ∃ b : (Fin m) → Edge,
        (∀ i j, M i j=v ↔ i∈edge (b j)) ∧ Nonempty (Cycle b) := by
  rcases interface_all F Y with thin|twin|⟨v,w,pal,b,cells,h⟩
  · exact Or.inl thin
  · exact Or.inr (Or.inl twin)
  · exact Or.inr (Or.inr ⟨v,w,pal,b,cells,h.elim id (fun f => (nodiv ⟨_,(f.2 0).symm⟩).elim)⟩)

theorem edges {n m l v : Nat} [NeZero m] {G : Graph n} (F : Shore (source G) l L) (Y : Shore (source G) v (Fin m))
    (t w : Nat) (palette : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ∨ source G (atPoint F i) (atPoint Y j)=w)
    (b : (Fin m) → Edge) (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=t ↔ i∈edge (b j))
    (C : Cycle b) :
    let sl := C.points.toEmbedding.trans (emb F)
    ∃ a z, a≠z ∧ (∀ j, neighbors (source G) a (atPoint Y j)=(edge (cycle (C.label j))).map sl) ∧
       ∀ j i, source G (atPoint Y j) (sl i)=if i∈edge (cycle (C.label j)) then a else z := by
  classical
  let c := source G
  let sl := C.points.toEmbedding.trans (emb F)
  have mark (i j) : c (sl i) (atPoint Y j)=t ↔ i∈edge (cycle (C.label j)) := by
    change source G (atPoint F (C.points i)) (atPoint Y j)=t ↔ _
    rw [cells,C.edges]
    exact Finset.mem_map' C.points.toEmbedding
  have slots : ∀ k : Fin 4, ∃ i x : Fin 4, i∈edge (cycle k) ∧ x∉edge (cycle k) := by decide
  obtain ⟨i₀,x₀,yes,no⟩ := slots (C.label 0)
  have active := (mark i₀ 0).mpr yes
  have neg := mt (mark x₀ 0).mp no
  have other := (palette (C.points x₀) 0).resolve_left neg
  let a := c (atPoint Y 0) (sl i₀)
  let z := c (atPoint Y 0) (sl x₀)
  have az : a≠z := fun h => neg ((transpose (closure G) h).symm.trans active)
  have names (j i) : c (atPoint Y j) (sl i)=if i∈edge (cycle (C.label j)) then a else z := by
    by_cases h : i∈edge (cycle (C.label j))
    · rw [if_pos h]; exact transpose (closure G) (((mark i j).mpr h).trans active.symm)
    · rw [if_neg h]; exact transpose (closure G) (((palette (C.points i) j).resolve_left (mt (mark i j).mp h)).trans other.symm)
  refine ⟨a,z,az,fun j => ?_,names⟩
  ext x
  constructor
  · intro hx
    have hit := (Finset.mem_filter.mp hx).2
    have tag := (end_colors (closure G) hit).2.trans (F (C.points i₀)).property
    obtain ⟨i,hi⟩ := (range_emb F x).mpr tag
    obtain ⟨i,rfl⟩ := C.points.surjective i
    have loc : sl i=x := hi
    have body : c (atPoint Y j) (sl i)=a := loc ▸ hit
    rw [names] at body
    by_cases h : i∈edge (cycle (C.label j))
    · exact Finset.mem_map.mpr ⟨i,h,loc⟩
    · exact (az (by simpa [h] using body.symm)).elim
  · rintro hx; obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(names j i).trans (if_pos hi)⟩


end QGI.Coherent.FourPointGeneral
