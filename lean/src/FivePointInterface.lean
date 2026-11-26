import FivePointFrame
import RegionalCycleExtension
import OddHalfPartition

noncomputable section
namespace QGI.Coherent.FivePointInterface
open SixTenCoordinates hiding V
open FivePointFrame
open FourTwelveFunctional (source)
open FourTwelveCycle (neighbors)
open RegionalCycleExtension (emb range_emb)

theorem cycle_support {m : Nat} [NeZero m] (b : Fin m → Edge)
    (rows : ∀ i : V, (Finset.univ.filter (fun j => i∈edge (b j))).card=(Finset.univ.filter (fun j => 0∈edge (b j))).card)
    (mult : ∀ i j, (Finset.univ.filter (fun k => b k=b i)).card=(Finset.univ.filter (fun k => b k=b j)).card) :
    ∃ q : Equiv.Perm V, ∀ i, ∃ j, edge (b j)=(cycle i).map q.toEmbedding := by
  classical
  let s := Finset.univ.image b
  let μ := (Finset.univ.filter (fun k => b k=b 0)).card
  have pos : 0<μ := Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have equals (i : V) : (s.filter (fun k => i∈edge k)).card*μ=(Finset.univ.filter (fun j => i∈edge (b j))).card := by
    let I := s.filter (fun k => i∈edge k)
    have count := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m)) I b
    have term (e) (he : e∈I) : (Finset.univ.filter (fun k => b k=e)).card=μ := by
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
      exact mult j 0
    have used (j) : b j∈s := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    simpa only [Finset.sum_congr rfl term,Finset.sum_const,smul_eq_mul,I,Finset.mem_filter,used,true_and] using count
  obtain ⟨q,cycle'⟩ := contains_cycle s ⟨b 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
    (fun i => Nat.eq_of_mul_eq_mul_right pos ((equals i).trans ((rows i).trans (equals 0).symm)))
  refine ⟨q,fun i => ?_⟩
  obtain ⟨e,he,h⟩ := cycle' i
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
  exact ⟨j,h⟩

theorem classify {n m l r : Nat} [NeZero m] {G : Graph n} (F : Shore (source G) l V) (Y : Shore (source G) r (Fin m)) :
    let c := source G
    (∀ i j, c (atPoint Y j) (atPoint F i)=c (atPoint Y 0) (atPoint F 0)) ∨
    (∃ i j, ∀ z, c (atPoint Y j) z=c (atPoint Y j) (atPoint F i) → z=atPoint F i) ∨
    ∃ (q : Equiv.Perm V) (rep : V → Fin m) (a w : Nat),
      Frame c (q.toEmbedding.trans (emb F)) (fun i => atPoint Y (rep i)) a w := by
  classical
  let c := source G
  let M := fun j i => c (atPoint Y j) (atPoint F i)
  let sel := fun j t => Finset.univ.filter (fun i => M j i=t)
  by_cases all : ∀ i j, M j i=M 0 0
  · exact Or.inl all
  right
  by_cases thin : ∃ j i, (sel j (M j i)).card=1
  · left; obtain ⟨j,i,one⟩ := thin
    refine ⟨i,j,fun z h => ?_⟩
    obtain ⟨k,hk⟩ := (range_emb F _).mpr (((Relations.end_colors (closure G) h).2).trans (F i).property)
    have inn : k∈sel j (M j i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(congrArg (c (atPoint Y j)) hk).trans h⟩
    have ini : i∈sel j (M j i) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    obtain ⟨z₀,single⟩ := Finset.card_eq_one.mp one
    rw [single,Finset.mem_singleton] at inn ini
    exact hk.symm.trans (congrArg (emb F) (inn.trans ini.symm))
  right
  let B t j i := decide (M j i=t)
  have block (t : Nat) : Block Y Y F F (B t) (B t) := fun ⦃_ _ _ _⦄ h => congrArg (fun x => decide (x=t)) h
  have rd (t j k) : (sel j t).card=(sel k t).card := by
    simpa only [sel,B,decide_eq_true_eq] using Block.degree_eq (sourceLaws (closure G)) (block t) j k
  have minimum (j i) : 2≤(sel 0 (M j i)).card := by
    have pos : 0<(sel j (M j i)).card := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
    have ne : (sel j (M j i)).card≠1 := fun h => thin ⟨j,i,h⟩
    rw [←rd _ j 0]; omega
  have disj (j x y) (h : x≠y) : Disjoint (sel j x) (sel j y) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => h (((Finset.mem_filter.mp h₁).2).symm.trans (Finset.mem_filter.mp h₂).2))
  push_neg at all
  obtain ⟨i₁,j₁,h⟩ := all
  let a := M 0 0
  let b := M j₁ i₁
  have ab : a≠b := Ne.symm h
  have pal (j i) : M j i=a ∨ M j i=b := by
    by_contra! bad
    have d := Finset.disjoint_union_left.mpr ⟨disj 0 a _ bad.1.symm,disj 0 b _ bad.2.symm⟩
    have cap := Finset.card_le_univ ((sel 0 a ∪ sel 0 b) ∪ sel 0 (M j i))
    rw [Finset.card_union_of_disjoint d,Finset.card_union_of_disjoint (disj _ _ _ ab),Fintype.card_fin] at cap
    have ha : 2≤(sel 0 a).card := minimum 0 0
    have hb : 2≤(sel 0 b).card := minimum j₁ i₁
    have hc := minimum j i
    omega
  have total : (sel 0 a).card+(sel 0 b).card=5 := by
    have eq : sel 0 a ∪ sel 0 b=Finset.univ := Finset.eq_univ_of_forall fun i =>
      Finset.mem_union.mpr ((pal 0 i).imp (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩) (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    simpa only [Finset.card_union_of_disjoint (disj _ _ _ ab),Finset.card_univ,Fintype.card_fin] using congrArg Finset.card eq
  have chosen : ∃ t w, (∀ j, (sel j t).card=2) ∧ ∀ j i, M j i=t ∨ M j i=w := by
    have ha : 2≤(sel 0 a).card := minimum 0 0
    have hb : 2≤(sel 0 b).card := minimum j₁ i₁
    by_cases h : (sel 0 a).card=2
    · exact ⟨a,b,fun j => (rd _ _ 0).trans h,pal⟩
    · exact ⟨b,a,fun j => (rd _ _ 0).trans (by omega),fun j i => Or.symm (pal j i)⟩
  obtain ⟨t,w,two,palette⟩ := chosen
  have repr : ∀ u : Finset V, u.card=2 → ∃ e : Edge, edge e=u := by native_decide
  choose b hb using fun j => repr _ (two j)
  have flag (i j) : B t j i=true ↔ i∈edge (b j) := by simp [B,hb,sel]
  have row (i) : (Finset.univ.filter (fun j => i∈edge (b j))).card=(Finset.univ.filter (fun j => 0∈edge (b j))).card := by
    simpa only [flag] using Block.degree_eq (sourceLaws (closure G)) (Block.flip (sourceLaws _) (block t)) i 0
  have gram (j z) : Block.overlap (B t) j z=2 ↔ b j=b z := by
    have eq (k) : FiberRectangles.degree (B t k)=2 := by simpa only [FiberRectangles.degree,B,sel,decide_eq_true_eq] using two k
    refine (OddHalfPartition.full_inter _ _ (eq j) (eq z)).trans ?_
    constructor
    · intro h
      apply edge_injective
      ext i; rw [←flag,←flag,h]
    · intro h; funext i; apply Bool.eq_iff_iff.mpr; rw [flag,flag,h]
  have mult (i j) : (Finset.univ.filter (fun k => b k=b i)).card=(Finset.univ.filter (fun k => b k=b j)).card := by
    have h := Block.hist_eq (sourceLaws (closure G)) (Block.gram (sourceLaws _) (block t)) i j 2
    have cv (i k) : Block.overlap (B t) i k=2 ↔ b k=b i := (gram i k).trans eq_comm
    simpa only [Block.hist,cv] using h
  obtain ⟨q,has⟩ := cycle_support b row mult
  choose rep hr using has
  let sl := q.toEmbedding.trans (emb F)
  have test (k i) : M (rep k) (q i)=t ↔ i∈cycle k := by
    have cv : M (rep k) (q i)=t ↔ q i∈edge (b (rep k)) := by simpa only [B,decide_eq_true_eq] using flag (q i) (rep k)
    rw [hr] at cv; exact cv.trans (Finset.mem_map' q.toEmbedding)
  refine ⟨q,rep,t,w,?_,?_⟩
  · intro k
    ext z
    constructor
    · intro h
      have active : c (atPoint Y (rep k)) (sl k)=t := (test k k).mpr (Finset.mem_insert_self _ _)
      have tag := (Relations.end_colors (closure G) ((Finset.mem_filter.mp h).2.trans active.symm)).2.trans (F (q k)).property
      obtain ⟨i,hi⟩ := (range_emb F _).mpr tag
      obtain ⟨i,rfl⟩ := q.surjective i
      exact Finset.mem_map.mpr ⟨i,(test k i).mp ((congrArg (c (atPoint Y (rep k))) hi).trans (Finset.mem_filter.mp h).2),hi⟩
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(test k i).mpr hi⟩
  · intro k i
    by_cases h : i∈cycle k
    · exact ((test k i).mpr h).trans (if_pos h).symm
    · rw [if_neg h]; exact (palette (rep k) (q i)).resolve_left (mt (test k i).mp h)

end QGI.Coherent.FivePointInterface
