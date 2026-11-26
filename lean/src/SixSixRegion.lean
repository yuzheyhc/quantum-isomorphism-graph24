import SixCrossShape
import SixSixCycle
import SixSixAttachment
import LargeOrderBlocks

noncomputable section
namespace QGI.Coherent.SixSixRegion
open FourTwelveFunctional (source transport_thin)
open SixTenCoordinates (Shore atPoint)
open SmallUnion SmallFiberExtension StrategyColorLaws ZivAvSix
open private small_map uniform_merge bundle convert_real from SmallFiberExtension
open SixSixCycle (point size)

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

abbrev cells {c : Table n} {a b} (A : Shore c a S) (B : Shore c b S) : M :=
  fun i j => c (atPoint A i) (atPoint B j)

/-- The two shores have six points each. Their single-color cross sections
satisfy the divisibility and disjointness tests from the intersection numbers. -/
theorem pair_shape {a b} (A : Shore (source G) a S) (B : Shore (source G) b S) (_diff : a≠b) :
    Shape (cells A A) (cells B B) (cells A B) :=
  SixCross.shape_of_shores (closure G) A B

theorem pair_size {c : Table n} {a b} (A : Shore c a S) (B : Shore c b S) :
    (vertices c (fun t => t=a ∨ t=b)).card ≤ 13 := by
  have eq : vertices c (fun t => t=a ∨ t=b)=vertices c (fun t => t=a) ∪ vertices c (fun t => t=b) := by
    ext z; simp only [mem_vertices,Finset.mem_union]
  rw [eq]
  have bound := Finset.card_union_le (vertices c (fun t => t=a)) (vertices c (fun t => t=b))
  rw [size A,size B] at bound
  omega

theorem thin_extend (old : Nat → Prop) {a s} (ha : old a) {I J : Type}
    (A : Shore (source G) a I) (Y : Shore (source G) s J)
    (thin : ∃ i j, ∀ z, source G (atPoint A i) (atPoint Y z)=source G (atPoint A i) (atPoint Y j) → z=j)
    (given : Realizes p old) : Realizes p (fun t => old t ∨ t=s) := by
  classical
  let c := source G
  obtain ⟨i,j,h⟩ := thin
  let x := atPoint A i
  let y := atPoint Y j
  have one (z : Fin n) (eq : c x z=c x y) : z=y := by
    obtain ⟨k,rfl⟩ := point Y ((Relations.end_colors (closure G) eq).2.trans (Y j).property)
    exact congrArg (atPoint Y) (h k eq)
  let reg := fun t => old t ∨ t=s
  let U := Region c reg
  have covered (k : U) : ∃ i : Region c old, ∀ z, c i.val z=c i.val k.val → z=k.val := by
    by_cases inside : old (c k.val k.val)
    · exact ⟨⟨k.val,(mem_vertices _ _ _).mpr inside⟩,fun _ eq => (Relations.diagonal _ eq).symm⟩
    have ks : c k.val k.val=s := ((mem_vertices _ _ _).mp k.property).resolve_left inside
    have diag := (Y j).property.trans ks.symm
    obtain ⟨w,_,hit⟩ := PartialFunctional.middle c c (fun r t => Relations.products (closure G) r t _ _ _ _ diag) x
    have row := (Relations.end_colors (closure G) hit).1
    have owned : old (c w w) := (congrArg old (row.symm.trans (A i).property)).mpr ha
    exact ⟨⟨w,(mem_vertices _ _ _).mpr owned⟩,fun z hz =>
      transport_thin row one z k.val (hz.trans hit.symm) hit.symm⟩
  obtain ⟨e,he⟩ := given
  obtain ⟨f,_,name,_⟩ := PartialFunctional.extend p (fun x : U => x.val) Subtype.val_injective
    (fun i : Region c old => i.val) (fun i => (e i).val) he covered
  obtain ⟨g,hg⟩ := bundle p reg f name
  exact ⟨g,fun i j => (name i j).trans (congrArg₂ (targetName p) (hg i).symm (hg j).symm)⟩

private theorem marked_extend (old : Nat → Prop) {a s} (ha : old a)
    (A : Shore (source G) a S) (Y : Shore (source G) s S)
    (mark : Marked (cells A A) (cells Y Y) (cells A Y))
    (stable : ∀ z x : S, part (cells Y Y) z x → ∀ i, old (source G i i) →
      source G i (atPoint Y z)=source G i (atPoint Y x))
    (given : Realizes p old) : Realizes p (fun t => old t ∨ t=s) := by
  obtain ⟨h,j₀,r₀,r₁,row,col⟩ := mark
  apply SixSixAttachment.attach p old (fun v => v=cells A Y h j₀) ha (pair_size A Y)
    (atPoint A r₀) (atPoint A r₁) (A r₀).property (A r₁).property _ _ given
  · intro i j hi hj
    obtain ⟨i,rfl⟩ := point A hi
    obtain ⟨j,rfl⟩ := point A hj
    intro left right k hk
    obtain ⟨k,rfl⟩ := point Y hk
    exact row i j k left right
  · intro x hx
    obtain ⟨x,rfl⟩ := point Y hx
    obtain ⟨i,hi,dist⟩ := col x
    refine ⟨atPoint A i,(A i).property,hi,fun z eq => ?_⟩
    obtain ⟨z,rfl⟩ := point Y ((Relations.end_colors (closure G) eq).2.trans (Y x).property)
    exact stable z x (dist z eq)

private theorem inner {a b s} (A : Shore (source G) a S) (B : Shore (source G) b S)
    (Y : Shore (source G) s S) (as' : a≠s) (bs : b≠s) :
    Realizes p (fun t => (t=a ∨ t=b) ∨ t=s) ∨ Cyclic (cells Y Y) := by
  let old := fun t => t=a ∨ t=b
  have given := small_map p old (pair_size A B)
  rcases pair_shape A Y as' with thin|cyc|⟨left,cl⟩
  · exact Or.inl (thin_extend p old (Or.inl rfl) A Y thin given)
  · exact Or.inr cyc
  rcases pair_shape B Y bs with thin|cyc|⟨right,cr⟩
  · exact Or.inl (thin_extend p old (Or.inr rfl) B Y thin given)
  · exact Or.inr cyc
  left
  have stable (z x : S) (h : part (cells Y Y) z x) (i : Fin n) (inside : old (source G i i)) :
      source G i (atPoint Y z)=source G i (atPoint Y x) := by
    rcases inside with hi|hi
    · obtain ⟨i,rfl⟩ := point A hi; exact left x z i h
    · obtain ⟨i,rfl⟩ := point B hi; exact right x z i h
  rcases cl with cl|mark
  swap
  · exact marked_extend p old (Or.inl rfl) A Y mark stable given
  rcases cr with cr|mark
  swap
  · exact marked_extend p old (Or.inr rfl) B Y mark stable given
  obtain ⟨e,he⟩ := given
  obtain ⟨q,hq⟩ := small_map p (fun t => t=s) (by rw [size Y]; decide)
  obtain ⟨f,hf,_⟩ := uniform_merge p old s e he q hq (by
    intro i j x y oi sj xi sy
    obtain ⟨j,rfl⟩ := point Y sj
    obtain ⟨y,rfl⟩ := point Y sy
    rcases oi with hi|hi
    · obtain ⟨x,rfl⟩ := point A (xi.trans hi)
      obtain ⟨i,rfl⟩ := point A hi; exact cl i j x y
    · obtain ⟨x,rfl⟩ := point B (xi.trans hi)
      obtain ⟨i,rfl⟩ := point B hi; exact cr i j x y)
  obtain ⟨g,hg⟩ := bundle p _ f hf
  exact ⟨g,fun i j => (hf i j).trans (congrArg₂ (targetName p) (hg i).symm (hg j).symm)⟩

/-- Three named six-point fibers in a perfect strategy on any number of vertices. -/
theorem realize {a b s} (A : Shore (source G) a S) (B : Shore (source G) b S)
    (Y : Shore (source G) s S) (ab : a≠b) (as' : a≠s) (bs : b≠s) :
    Realizes p (fun t => (t=a ∨ t=b) ∨ t=s) := by
  classical
  rcases inner p A B Y as' bs with ok|cy; exact ok
  rcases inner p A Y B ab bs.symm with ok|cb
  · exact convert_real p (fun _ => by tauto) ok
  rcases inner p B Y A ab.symm as'.symm with ok|ca
  · exact convert_real p (fun _ => by tauto) ok
  let reg := fun t => (t=a ∨ t=b) ∨ t=s
  let tag (i : Region (source G) reg) : Fin 3 :=
    if source G i.val i.val=a then 0 else if source G i.val i.val=b then 1 else 2
  apply SixSixAtoms.realize_of_commuting p reg tag (atPoint A 0)
  intro i j eq
  have ci := (mem_vertices _ _ _).mp i.property
  have cj := (mem_vertices _ _ _).mp j.property
  change (source G i.val i.val=a ∨ source G i.val i.val=b) ∨ source G i.val i.val=s at ci
  change (source G j.val j.val=a ∨ source G j.val j.val=b) ∨ source G j.val j.val=s at cj
  by_cases ia : source G i.val i.val=a <;> by_cases ja : source G j.val j.val=a
  · exact SixSixCycle.commuting p A ca _ _ ia ja
  · by_cases jb : source G j.val j.val=b <;> simp [tag,Ne.symm ab,ia,ja,jb] at eq
  · by_cases ib : source G i.val i.val=b <;> simp [tag,Ne.symm ab,ia,ja,ib] at eq
  · by_cases ib : source G i.val i.val=b <;> by_cases jb : source G j.val j.val=b
    · exact SixSixCycle.commuting p B cb _ _ ib jb
    · simp [tag,Ne.symm ab,ia,ja,ib,jb] at eq
    · simp [tag,Ne.symm ab,ia,ja,ib,jb] at eq
    · exact SixSixCycle.commuting p Y cy _ _ (by tauto) (by tauto)

/-- A named region consisting of eighteen vertices in six-point fibers. -/
theorem realize_of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=18)
    (six : ∀ t, reg t → (vertices (source G) (fun w => w=t)).card=6) : Realizes p reg := by
  classical
  let c := source G
  let d := fun i : Fin n => c i i
  let names := (vertices c reg).image d
  have mem (v : Nat) : v∈names ↔ reg v := by
    constructor
    · rintro hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_vertices _ _ _).mp hi
    · intro hv
      have pos : 0 < (vertices c (fun w => w=v)).card := by rw [six v hv]; decide
      obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
      have eq := (mem_vertices _ _ _).mp hi
      exact Finset.mem_image.mpr ⟨i,(mem_vertices _ _ _).mpr (eq ▸ hv),eq⟩
  have bound := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) names d
  have sixAt (v) (hv : v∈names) : (Finset.univ.filter (fun i => d i=v)).card=6 := by
    have eq : Finset.univ.filter (fun i => d i=v) = vertices c (fun w => w=v) := by
      ext i; simp [d]
    rw [eq]; exact six v ((mem v).mp hv)
  have all : (Finset.univ.filter (fun i => d i∈names)) = vertices c reg := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_vertices,mem,d]
  rw [all,total,Finset.sum_congr rfl sixAt] at bound
  simp only [Finset.sum_const,smul_eq_mul] at bound
  have sz : names.card=3 := by omega
  obtain ⟨a,b,s,ab,as',bs,namesEq⟩ := Finset.card_eq_three.mp sz
  have within (w : Nat) : ((w=a ∨ w=b) ∨ w=s) ↔ reg w := by
    rw [←mem,namesEq]; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  have frame (v) (hv : reg v) : Nonempty (Shore c v S) := by
    let m := Fintype.equivOfCardEq (show Fintype.card S=Fintype.card (Region c (fun w => w=v)) by
      rw [Fintype.card_fin,Fintype.card_coe,six v hv])
    exact ⟨m.trans (Equiv.subtypeEquivRight (fun i => mem_vertices c (fun t => t=v) i))⟩
  obtain ⟨A⟩ := frame a ((within _).mp (Or.inl (Or.inl rfl)))
  obtain ⟨B⟩ := frame b ((within _).mp (Or.inl (Or.inr rfl)))
  obtain ⟨Y⟩ := frame s ((within _).mp (Or.inr rfl))
  exact convert_real p within (realize p A B Y ab as' bs)

open LargeFourteenRegion CoprimeProfiles
open private card_core from LargeFourteenRegion

/-- Any ambient order with exactly three six-point fibers after removing
all fibers of size at most three. This includes the profile [6,6,6] at order eighteen. -/
theorem isomorphic {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (shape : xs.filter (fun k => 3<k)=[6,6,6]) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  have total : (vertices (source G) (large G)).card=18 := by rw [card_core P,shape]; decide
  have six (v : Nat) (hv : large G v) : (vertices (source G) (fun w => w=v)).card=6 := by
    have pos : 0 < (vertices (source G) (fun w => w=v)).card := (by decide : 0<3).trans hv
    obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
    have eq := (mem_vertices _ _ _).mp hi
    have same : vertices (source G) (fun w => w=v)=fiber G i := by
      ext j; simp only [mem_vertices,FourTwelveFunctional.fiber_eq,eq]
    have occurs : (fiber G i).card ∈ xs := by rw [P.fiber_size]; exact List.getElem_mem _
    have big : 3<(fiber G i).card := (LargeOrderBlocks.large_iff _).mp (eq ▸ hv)
    have mem : (fiber G i).card ∈ xs.filter (fun k => 3<k) := List.mem_filter.mpr ⟨occurs,decide_eq_true big⟩
    rw [same]
    simpa only [shape,List.mem_cons,List.not_mem_nil,or_false,or_self] using mem
  obtain ⟨e,he⟩ := of_large_region p (realize_of_size p (large G) total six)
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩

end QGI.Coherent.SixSixRegion



