import NineTwelveSteiner
import NineTwelvePartition
import NinePointRigidity
import LargeOrderFourteen

noncomputable section
namespace QGI.Coherent.NineTwelveRegion
open NineTwelveDesign NineTwelvePartition
open SixTenCoordinates (Shore atPoint Block Laws)
open SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private uniform_merge bundle convert_real from SmallFiberExtension
open private disjoint_degrees from FiberRectangles

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

def Weight (b : Inc) (k : Nat) := ∀ i x y, b i x=true → b i y=true → x≠y → concurrence b x y=k

theorem degrees {c : Table n} {a b} (law : Laws c c) (A : Shore c a P) (Y : Shore c b L) (v)
    (r : L) (i : P) (hit : cells A Y r i=v) (small : FiberRectangles.degree (mark A Y v r)≤4) :
    (∀ j, (line (mark A Y v) j).card=3) ∧ ∀ x, FiberRectangles.degree (fun z => mark A Y v z x)=4 := by
  let s := mark A Y v
  have h : Block Y Y A A s s := Block.map Block.names (fun t => decide (t=v))
  have rr (j) : FiberRectangles.degree (s j)=FiberRectangles.degree (s r) := Block.degree_eq law h j r
  have cc (x) : FiberRectangles.degree (fun z => s z x)=FiberRectangles.degree (fun z => s z i) :=
    Block.degree_eq law (Block.flip law h) x i
  have bound := FiberRectangles.balance s rr cc
  change 12*FiberRectangles.degree (s r)=9*FiberRectangles.degree (fun z => s z i) at bound
  have pos : 0<FiberRectangles.degree (s r) := Finset.card_pos.mpr
    ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true hit⟩⟩
  change FiberRectangles.degree (s r)≤4 at small
  exact ⟨fun j => (rr j).trans (by omega),fun x => (cc x).trans (by omega)⟩

private theorem weights {c : Table n} {a b} (law : Laws c c) (A : Shore c a P) (Y : Shore c b L) (v)
    (rd : ∀ j, (line (mark A Y v) j).card=3) (cd : ∀ x, FiberRectangles.degree (fun z => mark A Y v z x)=4) :
    ∃ k, (k=1 ∨ k=2 ∨ k=4) ∧ Weight (mark A Y v) k := by
  have h : Block Y Y A A (mark A Y v) (mark A Y v) := Block.map Block.names (fun t => decide (t=v))
  exact pair_weight _ rd cd (fun _ _ _ _ x y => score_block law h ((of_decide_eq_true x).trans (of_decide_eq_true y).symm))

private theorem strong {a b v k} (ab : a≠b) (A : Shore (source G) a P) (Y : Shore (source G) b L)
    (kv : k=1 ∨ k=2) (rd : ∀ j, (line (mark A Y v) j).card=3)
    (cd : ∀ x, FiberRectangles.degree (fun z => mark A Y v z x)=4) (w : Weight (mark A Y v) k) :
    Realizes p (fun t => t=a ∨ t=b) := by
  classical
  obtain ⟨e,he⟩ := realize_region p (fun t => t=a) (by rw [SixSixCycle.size A]; decide)
    (by rw [SixSixCycle.size A]; decide)
  let S : Shore (targetName p) a P := ((SixSixCycle.regEquiv A).trans e).trans
    (Equiv.subtypeEquivRight (fun x => mem_vertices (targetName p) (fun t => t=a) x))
  have colors (i j) : source G (atPoint A i) (atPoint A j)=targetName p (atPoint S i) (atPoint S j) := he (SixSixCycle.regEquiv A i) (SixSixCycle.regEquiv A j)
  obtain ⟨f,hf⟩ := diagonal_names p
  let Z := Y.trans (Equiv.subtypeEquiv (p:=fun i => source G i i=b) (q:=fun i => targetName p i i=b)
    f (fun i => ⟨fun h => (hf i).symm.trans h,fun h => (hf i).trans h⟩))
  let s := mark A Y v
  let t := mark S Z v
  have h : Block Y Z A S s t := Block.map Block.names (fun z => decide (z=v))
  let law := SixTenCoordinates.commonLaws p
  have gram : Block A S A S (concurrence s) (concurrence t) :=
    Block.fold law (Block.flip law h) h (fun x y => if x && y then 1 else 0)
  have equal (x y) : concurrence s x y=concurrence t x y := gram (colors x y)
  have td (j) : (line t j).card=3 := (Block.degree_eq law h 0 j).symm.trans (rd 0)
  have tc (x) : FiberRectangles.degree (fun z => t z x)=4 :=
    (Block.degree_eq law (Block.flip law h) 0 x).symm.trans (cd 0)
  have tw : Weight t k := by
    intro j x y hx hy xy
    have pos := (hit_iff t x y).mpr ⟨j,hx,hy⟩
    rw [←equal] at pos ⊢
    obtain ⟨r,rx,ry⟩ := (hit_iff s x y).mp pos
    exact w r x y rx ry xy
  apply SevenFourteenAnchor.realize p ab A Y S Z
  · rcases kv with rfl|rfl
    · exact NineTwelveSteiner.commuting p A S Y Z s t h rd td
        (fun _ _ xy => steiner rd cd w xy) (fun _ _ xy => steiner td tc tw xy)
    · let g := fun x y => decide (concurrence s x y=2)
      have hs : Block Y Y A A s s := Block.map Block.names (fun z => decide (z=v))
      have sl := SixTenCoordinates.sourceLaws (closure G)
      have sg : Block A A A A (concurrence s) (concurrence s) :=
        Block.fold sl (Block.flip sl hs) hs (fun x y => if x && y then 1 else 0)
      have degree (x) : FiberRectangles.degree (g x)=4 := by
        have number : 2*(touching s x).card=8 := neighbor_count rd cd w x
        have sets : Finset.univ.filter (fun y => g x y)=touching s x := by
          ext y
          simp only [g,touching,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,decide_eq_true_eq,and_true]
          constructor
          · intro eq
            refine ⟨fun h => ?_,by omega⟩
            subst y; rw [diag s cd] at eq; contradiction
          · rintro ⟨yx,pos⟩
            obtain ⟨r,hx,hy⟩ := (hit_iff s x y).mp pos; exact w r x y hx hy yx.symm
        unfold FiberRectangles.degree; rw [sets]; omega
      have co := NinePointRigidity.commuting p A g (fun x => by simp [g,diag s cd])
        (fun x y => Bool.decide_congr (by rw [symmetry s x y])) degree (Block.map sg (fun z => decide (z=2)))
      exact fun i j x y => co i j _ _
  · intro j
    let c := Finset.univ.filter (fun z => t z=t j)
    have size : c.card≤2 := (max_copies td tw j).trans (by rcases kv with rfl|rfl <;> decide)
    have hj : j∈c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    have left : (c.erase j).card≤1 := by rw [Finset.card_erase_of_mem hj]; omega
    obtain ⟨u,only⟩ := Finset.card_le_one_iff_subset_singleton.mp left
    refine ⟨j,u,fun z eq => ?_⟩
    by_cases same : z=j
    · exact Or.inl same
    · apply Or.inr; apply Finset.mem_singleton.mp (only ?_)
      refine Finset.mem_erase.mpr ⟨same,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      funext i; exact Bool.decide_congr (by change cells S Z z i=v ↔ cells S Z j i=v; rw [show cells S Z z i=cells S Z j i from eq i])


theorem realize {a b} (A : Shore (source G) a P) (Y : Shore (source G) b L) (ab : a≠b) :
    Realizes p (fun t => t=a ∨ t=b) := by
  classical
  let law := SixTenCoordinates.sourceLaws (closure G)
  by_cases universal : ∀ r i s j, cells A Y r i=cells A Y s j
  · obtain ⟨e,he⟩ := LargeOrderBlocks.small p (·=a) (by rw [SixSixCycle.size A]; decide)
    obtain ⟨g,hg⟩ := LargeOrderBlocks.small p (·=b) (by rw [SixSixCycle.size Y]; decide)
    obtain ⟨f,hf,_⟩ := uniform_merge p (·=a) b e he g hg (by
      intro i j x y hi hj hx hy
      obtain ⟨i,rfl⟩ := SixSixCycle.point A hi
      obtain ⟨j,rfl⟩ := SixSixCycle.point Y hj
      obtain ⟨x,rfl⟩ := SixSixCycle.point A (hx.trans hi)
      obtain ⟨y,rfl⟩ := SixSixCycle.point Y hy
      exact Relations.transpose _ (universal j i y x))
    obtain ⟨q,hq⟩ := bundle p _ f hf
    exact ⟨q,fun i j => (hf i j).trans (congrArg₂ (targetName p) (hq i).symm (hq j).symm)⟩
  by_cases easy : ∃ r i k, let u := cells A Y r i
      FiberRectangles.degree (mark A Y u r)≤4 ∧ (k=1 ∨ k=2) ∧ Weight (mark A Y u) k
  · obtain ⟨r,i,k,small,kv,w⟩ := easy
    obtain ⟨rd,cd⟩ := degrees law A Y _ r i rfl small
    exact strong p ab A Y kv rd cd w
  have other (r i) (small : FiberRectangles.degree (mark A Y (cells A Y r i) r)≤4) :
      Nonempty (Split (mark A Y (cells A Y r i))) := by
    obtain ⟨rd,cd⟩ := degrees law A Y _ r i rfl small
    obtain ⟨k,kv,w⟩ := weights law A Y _ rd cd
    rcases kv with rfl|rfl|rfl
    · exact (easy ⟨r,i,1,small,Or.inl rfl,w⟩).elim
    · exact (easy ⟨r,i,2,small,Or.inr rfl,w⟩).elim
    · exact NineTwelvePartition.split rd cd w
  push_neg at universal
  obtain ⟨r,i,s,j,diff⟩ := universal
  have limit := disjoint_degrees (cells A Y r) diff
  let v := cells A Y s j
  have marked : Block Y Y A A (mark A Y v) (mark A Y v) := Block.map Block.names (fun t => decide (t=v))
  have eq : FiberRectangles.degree (mark A Y v r)=FiberRectangles.degree (mark A Y v s) := Block.degree_eq law marked r s
  change FiberRectangles.degree (mark A Y (cells A Y r i) r)+FiberRectangles.degree (mark A Y v r)≤9 at limit
  obtain ⟨r,i,low⟩ : ∃ w q, FiberRectangles.degree (mark A Y (cells A Y w q) w)≤4 := by
    by_cases h : FiberRectangles.degree (mark A Y (cells A Y r i) r)≤4
    · exact ⟨r,i,h⟩
    · exact ⟨s,j,by change FiberRectangles.degree (mark A Y v s)≤4; omega⟩
  obtain ⟨part⟩ := other r i low
  have twins := palette law A Y part other
  let F := SixSixCycle.regEquiv Y
  let R := SixSixCycle.regEquiv A
  apply convert_real p (fun _ => by tauto)
    (ThreeRectangleExtension.three p (a:=b) (s:=a) (v:=cells A Y r i) (by rw [SixSixCycle.size A]; decide)
      (part.ln ∘ F.symm) (part.pt ∘ R.symm) (part.onto.comp F.symm.surjective)
      ((pointOnto part).comp R.symm.surjective) ?_ ?_ (LargeOrderBlocks.small p _ (by rw [SixSixCycle.size Y]; decide)))
  · intro z x; obtain ⟨z,rfl⟩ := F.surjective z; obtain ⟨x,rfl⟩ := R.surjective x
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,NineTwelvePartition.mark,decide_eq_true_eq] using part.flag z x
  · intro x y eq z
    obtain ⟨z,rfl⟩ := F.surjective z
    obtain ⟨x,rfl⟩ := R.surjective x
    obtain ⟨y,rfl⟩ := R.surjective y
    exact twins x y (by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using eq) z


open LargeFourteenRegion CoprimeProfiles
open private card_core from LargeFourteenRegion

theorem realize_of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=21)
    (x y : Fin n) (rx : reg (source G x x)) (ry : reg (source G y y))
    (sx : (fiber G x).card=9) (sy : (fiber G y).card=12) : Realizes p reg := by
  classical
  let c := source G
  let a := c x x
  let b := c y y
  have same (z : Fin n) : vertices c (fun t => t=c z z)=fiber G z := by
    ext i; simp only [mem_vertices,FourTwelveFunctional.fiber_eq,c]
  have ca : (vertices c (·=a)).card=9 := (congrArg Finset.card (same x)).trans sx
  have cb : (vertices c (·=b)).card=12 := (congrArg Finset.card (same y)).trans sy
  have ab : a≠b := fun eq => (by decide : (9:Nat)≠12) (ca.symm.trans
    ((congrArg (fun t => (vertices c (fun w => w=t)).card) eq).trans cb))
  let frame (u k : Nat) (hu : (vertices c (·=u)).card=k) : Shore c u (Fin k) :=
    let e : Fin k ≃ Region c (·=u) := Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_coe,hu])
    e.trans (Equiv.subtypeEquivRight (fun i => mem_vertices c (·=u) i))
  let A := frame a 9 ca
  let Y := frame b 12 cb
  let keep := fun t => t=a ∨ t=b
  have sub : vertices c keep ⊆ vertices c reg := by
    intro i hi
    rcases (mem_vertices _ _ _).mp hi with h|h
    · exact (mem_vertices _ _ _).mpr ((congrArg reg h).mpr rx)
    · exact (mem_vertices _ _ _).mpr ((congrArg reg h).mpr ry)
  obtain ⟨F,_,_⟩ := SevenFourteenAnchor.coordinates A Y ab
  have count : (vertices c keep).card=21 := by
    simpa only [Fintype.card_coe,Fintype.card_sum,Fintype.card_fin] using (Fintype.card_congr F).symm
  have eq := Finset.eq_of_subset_of_card_le sub (by rw [count,total])
  let cast (i : Region c reg) : Region c keep := ⟨i.val,eq.symm ▸ i.property⟩
  obtain ⟨e,he⟩ := realize p A Y ab
  let f (i : Region c reg) := (e (cast i)).val
  have names (i j) : c i.val j.val=targetName p (f i) (f j) := he (cast i) (cast j)
  obtain ⟨q,hq⟩ := bundle p reg f names
  exact ⟨q,fun i j => (names i j).trans (congrArg₂ (targetName p) (hq i).symm (hq j).symm)⟩

theorem isomorphic {n} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (shape : xs.filter (fun k => 3<k)=[9,12]) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  have inA : 9∈xs.filter (fun k => 3<k) := by rw [shape]; decide
  have inB : 12∈xs.filter (fun k => 3<k) := by rw [shape]; decide
  obtain ⟨x,hx⟩ := P.fiber_of_mem (List.mem_filter.mp inA).1 (by decide)
  obtain ⟨y,hy⟩ := P.fiber_of_mem (List.mem_filter.mp inB).1 (by decide)
  have total : (vertices (source G) (large G)).card=21 := by rw [card_core P,shape]; decide
  obtain ⟨e,he⟩ := of_large_region p (realize_of_size p (large G) total x y
    ((LargeOrderBlocks.large_iff _).mpr (by omega)) ((LargeOrderBlocks.large_iff _).mpr (by omega)) hx hy)
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩

end QGI.Coherent.NineTwelveRegion









