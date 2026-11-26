import SevenFourteenDesign
import SevenFourteenCensus
import SevenFourteenAnchor
import SevenFourteenHeawood
import LargeOrderFourteen
import SixSixRegion
import SingletonSwitch

noncomputable section
namespace QGI.Coherent.SevenFourteenRegion
open QGI.SevenFourteen QGI.SevenFourteen.Design
open QGI.SevenFourteen.Regular (rows transpose)
open SmallUnion SmallFiberExtension StrategyColorLaws
open SixTenCoordinates (Shore atPoint Block Laws)
open FourTwelveFunctional (source)
open private incompatible outside from RegionalPlanar
open private uniform_merge bundle convert_real from SmallFiberExtension
open private disjoint_degrees from FiberRectangles
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)
abbrev X := V ⊕ W
private def line (x : W) : V := ⟨x.val/2,by omega⟩
private def tag : X → Heawood.Index := Sum.elim Sum.inl (Sum.inr ∘ line)
private def rep : Heawood.Index → X := Sum.elim Sum.inl (fun x => Sum.inr ⟨2*x.val,by omega⟩)
private theorem split : ∀ i, tag (rep i)=i := by native_decide
private theorem singleton (a : V) : ∀ x : X, tag x=Sum.inl a → x=rep (Sum.inl a) := by
  intro x h; cases x <;> simp_all [tag,rep]
private theorem incidence : ∀ (i : W) (j : V), matrix fanoRows i j=Heawood.fano (line i) j := by native_decide
private theorem identify : ∀ i j : W, Block.overlap (matrix fanoRows) i j=3 ↔ line i=line j := by native_decide
private theorem two : ∀ i : W, ∃ u w : W, ∀ j,
    (∀ k, matrix fanoRows j k=matrix fanoRows i k) → j=u ∨ j=w := by native_decide

theorem fano {a b v : Nat} (ab : a≠b) (A : Shore (source G) a V) (Y : Shore (source G) b W)
    (S : Shore (targetName p) a V) (Z : Shore (targetName p) b W)
    (src : rows (mark Y A v)=fanoRows) (tgt : rows (mark Z S v)=fanoRows) :
    Realizes p (fun t => t=a ∨ t=b) := by
  classical
  let reg := fun t => t=a ∨ t=b
  obtain ⟨F,FL,FR⟩ := SevenFourteenAnchor.coordinates A Y ab
  obtain ⟨T,TL,TR⟩ := SevenFourteenAnchor.coordinates S Z ab
  have m : mark Y A v=matrix fanoRows := (matrix_rows _).symm.trans (congrArg matrix src)
  have m' : mark Z S v=matrix fanoRows := (matrix_rows _).symm.trans (congrArg matrix tgt)
  have records (i j x y) (h : cells Y A i j=cells Z S x y) :
      Heawood.fano (line i) j=Heawood.fano (line x) y := by
    rw [←incidence i j,←incidence x y,←congrFun (congrFun m i) j,←congrFun (congrFun m' x) y]
    exact Bool.decide_congr (by rw [h])
  have classes (i j x y : W) (h : source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z x) (atPoint Z y)) :
      line i=line j ↔ line x=line y := by
    have hb : Block Y Z A S (mark Y A v) (mark Z S v) := Block.map Block.names (fun t => decide (t=v))
    have gr := Block.gram (SixTenCoordinates.commonLaws p) hb h
    rw [m,m'] at gr
    rw [←identify,←identify,gr]
  let label : X → Nat := Sum.elim (fun _ => a) (fun _ => b)
  have srcDiag (i) : source G (F i).val (F i).val=label i := by
    cases i with
    | inl i => rw [FL]; exact (A i).property
    | inr i => rw [FR]; exact (Y i).property
  have tgtDiag (i) : targetName p (T i).val (T i).val=label i := by
    cases i with
    | inl i => rw [TL]; exact (S i).property
    | inr i => rw [TR]; exact (Z i).property
  have both (i j x y : X) (eq : source G (F i).val (F j).val=targetName p (T x).val (T y).val) :
      (tag i=tag j ↔ tag x=tag y) ∧
      Heawood.relation (tag i) (tag j)=Heawood.relation (tag x) (tag y) := by
    obtain ⟨hh,tt⟩ := SmallShore.endpoints p eq
    have hi := (srcDiag i).symm.trans (hh.trans (tgtDiag x))
    have hj := (srcDiag j).symm.trans (tt.trans (tgtDiag y))
    have diag : i=j ↔ x=y :=
      (F.injective.eq_iff.symm.trans Subtype.val_injective.eq_iff.symm).trans
        ((SingletonSwitch.diagonal_iff p eq).trans (Subtype.val_injective.eq_iff.trans T.injective.eq_iff))
    cases i <;> cases j <;> cases x <;> cases y <;> simp only [label,Sum.elim_inl,Sum.elim_inr] at hi hj
    all_goals first | exact (ab hi).elim | exact (ab hj).elim | exact (ab hi.symm).elim | exact (ab hj.symm).elim | skip
    all_goals simp only [tag,Sum.elim_inl,Sum.elim_inr,Function.comp_apply,Sum.inl.injEq,Sum.inr.injEq,
      reduceCtorEq,iff_self,true_and,and_true,Heawood.relation] at diag ⊢
    all_goals simp only [FL,FR,TL,TR] at eq
    all_goals first | exact diag | exact records _ _ _ _ eq | exact records _ _ _ _ (common_transpose p eq) |
      exact classes _ _ _ _ eq
  let P := fun i j : X => ColorTensor.P p (F i).val (T j).val
  obtain ⟨hp,rr,cc⟩ := ColorTensor.quantumPermutation p
  have point {c : Table n} (L : X ≃ Region c reg) (x : Fin n) (hx : reg (c x x)) :
      ∃ i, (L i).val=x := ⟨L.symm ⟨x,(mem_vertices _ _ _).mpr hx⟩,congrArg Subtype.val (L.apply_symm_apply _)⟩
  have row (i) : ∑ j, P i j=1 := by
    apply Eq.trans _ (rr (F i).val)
    apply Fintype.sum_of_injective (fun j => (T j).val) (fun _ _ e => T.injective (Subtype.ext e))
      (P i) (ColorTensor.P p (F i).val) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (point T z (eq ▸ (mem_vertices _ _ _).mp (F i).property)))
  have col (j) : ∑ i, P i j=1 := by
    apply Eq.trans _ (cc (T j).val)
    apply Fintype.sum_of_injective (fun i => (F i).val) (fun _ _ e => F.injective (Subtype.ext e))
      (fun i => P i j) (fun x => ColorTensor.P p x (T j).val) _ (fun _ => rfl)
    intro z absent
    exact outside p _ _ (fun eq => absent (point F z ((congrArg reg (show source G z z=targetName p (T j).val (T j).val from eq)).mpr ((mem_vertices _ _ _).mp (T j).property))))
  obtain ⟨e,he⟩ := Heawood.numbering
  apply SevenFourteenAnchor.realize p ab A Y S Z
  · intro i j x y
    have h := SevenFourteenQuotient.commuting tag rep split P (fun i j => hp _ _) row col
      (fun i a b ne => incompatible p _ _ _ _ (fun eq => ne (T.injective (Subtype.ext ((SingletonSwitch.diagonal_iff p eq).mp rfl)))))
      (fun i j a b bad => incompatible p _ _ _ _ (fun eq => bad (both i j a b eq).1))
      Heawood.relation (fun i j a b bad => incompatible p _ _ _ _ (fun eq => bad (both i j a b eq).2))
      (Literature.schmidt_heawood _ e he) (.inl i) (.inl x) (.inl j) (.inl y) (singleton x) (singleton y)
    simpa only [rep,Sum.elim_inl,P,FL,TL] using h
  · intro j
    obtain ⟨u,w,only⟩ := two j
    refine ⟨u,w,fun t same => only t (fun i => ?_)⟩
    rw [←m']
    apply Bool.decide_congr
    change targetName p (atPoint Z t) (atPoint S i)=v ↔ targetName p (atPoint Z j) (atPoint S i)=v
    rw [same i]

private theorem one {a b} (A : Shore (source G) a V) (Y : Shore (source G) b W)
    (thin : Thin (cells Y A)) : Realizes p (fun t => t=a ∨ t=b) := by
  have big := LargeOrderBlocks.fourteen p (fun t => t=b)
    (fun i h => by rw [h]; change 3<(vertices (source G) (·=b)).card; rw [SixSixCycle.size Y]; decide) (SixSixCycle.size Y)
  exact convert_real p (fun _ => by tauto) (SixSixRegion.thin_extend p (·=b) rfl Y A thin big)

private theorem marked_degree {c d : Table n} {a b} (law : Laws c d) (Y : Shore c b W) (A : Shore c a V)
    (Z : Shore d b W) (S : Shore d a V) (v) (i x : W) :
    FiberRectangles.degree (mark Y A v i)=FiberRectangles.degree (mark Z S v x) :=
  Block.degree_eq law (Block.map Block.names (fun t => decide (t=v))) i x

private theorem thin_degree {c : N} {v} {i : W} (one : FiberRectangles.degree (fun j => decide (c i j=v))=1) :
    Thin c := by
  obtain ⟨j,only⟩ := Finset.card_eq_one.mp one
  have hit := (Finset.ext_iff.mp only j).mpr (by simp)
  have eq : c i j=v := of_decide_eq_true (Finset.mem_filter.mp hit).2
  refine ⟨i,j,fun k hk => Finset.mem_singleton.mp ((Finset.ext_iff.mp only k).mp ?_)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true (hk.trans eq)⟩

private theorem regular {c : Table n} {a b} (law : Laws c c) (Y : Shore c b W) (A : Shore c a V) (v) :
    let d := FiberRectangles.degree (mark Y A v 0)
    (∀ i, FiberRectangles.degree (mark Y A v i)=d) ∧
    ∀ j, FiberRectangles.degree (transpose (mark Y A v) j)=2*d := by
  let z := mark Y A v
  have f := Block.map (Block.names (L:=Y) (L':=Y) (R:=A) (R':=A)) (fun t => decide (t=v))
  have rr (i : W) : FiberRectangles.degree (z i)=FiberRectangles.degree (z 0) := Block.degree_eq law f i 0
  have cc (j : V) : FiberRectangles.degree (transpose z j)=FiberRectangles.degree (transpose z 0) := Block.degree_eq law (Block.flip law f) j 0
  have balance := FiberRectangles.balance z rr cc
  change 14*FiberRectangles.degree (z 0)=7*FiberRectangles.degree (transpose z 0) at balance
  have ratio : FiberRectangles.degree (transpose z 0)=2*FiberRectangles.degree (z 0) := by omega
  exact ⟨rr,fun j => (cc j).trans ratio⟩

private theorem pull_thin {c d : Table n} {a b} (law : Laws c d) (Y : Shore c b W) (A : Shore c a V)
    (Z : Shore d b W) (S : Shore d a V) (thin : Thin (cells Z S)) : Thin (cells Y A) := by
  obtain ⟨i,j,one⟩ := thin
  let v := cells Z S i j
  have single : FiberRectangles.degree (mark Z S v i)=1 := by
    apply Finset.card_eq_one.mpr; refine ⟨j,?_⟩; ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Design.mark,decide_eq_true_eq,Finset.mem_singleton]
    exact ⟨fun h => one _ h,fun h => h ▸ rfl⟩
  exact thin_degree ((marked_degree law Y A Z S v 0 i).trans single)

theorem realize {a b} (A : Shore (source G) a V) (Y : Shore (source G) b W) (ab : a≠b) :
    Realizes p (fun t => t=a ∨ t=b) := by
  classical
  by_cases all : ∀ i j x y, cells Y A i j=cells Y A x y
  · obtain ⟨e,he⟩ := LargeOrderBlocks.small p (·=a) (by rw [SixSixCycle.size A]; decide)
    obtain ⟨g,hg⟩ := LargeOrderBlocks.fourteen p (·=b) (fun i h => by
      rw [h]; change 3<(vertices (source G) (·=b)).card; rw [SixSixCycle.size Y]; decide) (SixSixCycle.size Y)
    obtain ⟨f,hf,_⟩ := uniform_merge p (·=a) b e he g hg (by
      intro i j x y hi hj hx hy
      obtain ⟨i,rfl⟩ := SixSixCycle.point A hi
      obtain ⟨j,rfl⟩ := SixSixCycle.point Y hj
      obtain ⟨x,rfl⟩ := SixSixCycle.point A (hx.trans hi)
      obtain ⟨y,rfl⟩ := SixSixCycle.point Y hy
      exact Relations.transpose _ (all j i y x))
    obtain ⟨q,hq⟩ := bundle p _ f hf
    exact ⟨q,fun i j => (hf i j).trans (congrArg₂ (targetName p) (hq i).symm (hq j).symm)⟩
  push_neg at all
  obtain ⟨i,j,x,y,diff⟩ := all
  let u := cells Y A i j
  let v := cells Y A x y
  have limit := disjoint_degrees (cells Y A i) diff
  change FiberRectangles.degree (mark Y A u i)+FiberRectangles.degree (mark Y A v i)≤7 at limit
  have reg := (regular (SixTenCoordinates.sourceLaws (closure G)) Y A v).1
  have common : FiberRectangles.degree (mark Y A v i)=FiberRectangles.degree (mark Y A v x) := (reg i).trans (reg x).symm
  obtain ⟨u,i,j,hit,small⟩ : ∃ w l r, cells Y A l r=w ∧ FiberRectangles.degree (mark Y A w l)≤3 := by
    by_cases hu : FiberRectangles.degree (mark Y A u i)≤3
    · exact ⟨u,i,j,rfl,hu⟩
    · exact ⟨v,x,y,rfl,by omega⟩
  let d := FiberRectangles.degree (mark Y A u 0)
  obtain ⟨rr,cc⟩ := regular (SixTenCoordinates.sourceLaws (closure G)) Y A u
  have pos : 0<FiberRectangles.degree (mark Y A u i) :=
    Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true hit⟩⟩
  have r0 : FiberRectangles.degree (mark Y A u i)=d := rr i
  by_cases d1 : d=1
  · exact one p A Y (thin_degree (i:=0) d1)
  have deg : d=2 ∨ d=3 := by omega
  rcases alternatives Enum.enumerate (SixTenCoordinates.sourceLaws (closure G)) Y A u d deg rr cc with thin|⟨q,w,src⟩
  · exact one p A Y thin
  obtain ⟨e,he⟩ := diagonal_names p
  let transfer (s : Nat) := Equiv.subtypeEquiv (p:=fun i => source G i i=s)
    (q:=fun i => targetName p i i=s) e (fun i => ⟨fun h => (he i).symm.trans h,fun h => (he i).trans h⟩)
  let S := A.trans (transfer a)
  let Z := Y.trans (transfer b)
  have base := (marked_degree (SixTenCoordinates.commonLaws p) Y A Z S u 0 0).symm
  obtain ⟨r',c'⟩ := regular (SixTenCoordinates.targetLaws p) Z S u
  rcases alternatives Enum.enumerate (SixTenCoordinates.targetLaws p) Z S u d deg (fun i => (r' i).trans base)
      (fun j => (c' j).trans (congrArg (2*·) base)) with thin|⟨t,h,tgt⟩
  · exact one p A Y (pull_thin (SixTenCoordinates.commonLaws p) Y A Z S thin)
  · exact fano p ab (w.trans A) (q.trans Y) (h.trans S) (t.trans Z) src tgt

open LargeFourteenRegion CoprimeProfiles
open private card_core from LargeFourteenRegion

theorem realize_of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=21)
    (x y : Fin n) (rx : reg (source G x x)) (ry : reg (source G y y))
    (sx : (fiber G x).card=7) (sy : (fiber G y).card=14) : Realizes p reg := by
  classical
  let c := source G
  let a := c x x
  let b := c y y
  have same (z : Fin n) : vertices c (fun t => t=c z z)=fiber G z := by
    ext i; simp only [mem_vertices,FourTwelveFunctional.fiber_eq,c]
  have ca : (vertices c (·=a)).card=7 := (congrArg Finset.card (same x)).trans sx
  have cb : (vertices c (·=b)).card=14 := (congrArg Finset.card (same y)).trans sy
  have ab : a≠b := fun eq => (by decide : (7:Nat)≠14) (ca.symm.trans
    ((congrArg (fun t => (vertices c (fun w => w=t)).card) eq).trans cb))
  let frame (u k : Nat) (hu : (vertices c (·=u)).card=k) : Shore c u (Fin k) :=
    let e : Fin k ≃ Region c (·=u) := Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_coe,hu])
    e.trans (Equiv.subtypeEquivRight (fun i => mem_vertices c (·=u) i))
  let A := frame a 7 ca
  let Y := frame b 14 cb
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
    (shape : xs.filter (fun k => 3<k)=[7,14]) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  have inA : 7∈xs.filter (fun k => 3<k) := by rw [shape]; decide
  have inB : 14∈xs.filter (fun k => 3<k) := by rw [shape]; decide
  obtain ⟨x,hx⟩ := P.fiber_of_mem (List.mem_filter.mp inA).1 (by decide)
  obtain ⟨y,hy⟩ := P.fiber_of_mem (List.mem_filter.mp inB).1 (by decide)
  have total : (vertices (source G) (large G)).card=21 := by rw [card_core P,shape]; decide
  obtain ⟨e,he⟩ := of_large_region p (realize_of_size p (large G) total x y
    ((LargeOrderBlocks.large_iff _).mpr (by omega)) ((LargeOrderBlocks.large_iff _).mpr (by omega)) hx hy)
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩

end QGI.Coherent.SevenFourteenRegion





