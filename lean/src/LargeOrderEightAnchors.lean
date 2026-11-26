import LargeOrderEightCycles
import LargeOrderFiveAnchors
import RegionalThreeClasses

noncomputable section
namespace QGI.Coherent.LargeOrderEightAnchors
open LargeOrderEightCycles StrategyColorLaws SixTenCoordinates SmallUnion SmallFiberExtension FiberPairExtension
open FourEightGeometry (L Eight)
open FourTwelveFunctional (source)
open RegionalCycleExtension (emb range_emb)
open private bundle from SmallFiberExtension
open private rectangle from FiberPairExtension
open private narrow from TwoAnchorUnionGlue

def Uniform {n l r X Y} {c : Fin n → Fin n → Nat} (F : Shore c l X) (S : Shore c r Y) :=
  ∀ i j x y, c (atPoint F i) (atPoint S j)=c (atPoint F x) (atPoint S y)

variable {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)
local notation "c₀" => source G
local notation "d₀" => targetName p

private def sync {k v : Nat} (Y : Shore c₀ v (Fin k)) :
    Shore d₀ v (Fin k) :=
  let m := Classical.choose (diagonal_names p)
  let hm := Classical.choose_spec (diagonal_names p)
  Y.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))

private theorem two {k v : Nat} (Y : Shore c₀ v (Fin k)) (small : k≤13) (a b : Fin k) (u w : Fin n)
    (eq : c₀ (atPoint Y a) (atPoint Y b)=d₀ u w) : ∃ Z : Shore d₀ v (Fin k),
    atPoint Z a=u ∧ atPoint Z b=w ∧ ∀ i j, c₀ (atPoint Y i) (atPoint Y j)=d₀ (atPoint Z i) (atPoint Z j) := by
  let T := sync p Y
  let x := T.symm ⟨u,(SmallShore.endpoints p eq).1.symm.trans (Y a).property⟩
  let y := T.symm ⟨w,(SmallShore.endpoints p eq).2.symm.trans (Y b).property⟩
  have hx : atPoint T x=u := congrArg Subtype.val (T.apply_symm_apply _)
  have hy : atPoint T y=w := congrArg Subtype.val (T.apply_symm_apply _)
  obtain ⟨e,ea,eb,he⟩ := RegionalThreeClasses.small_pair p Y T small a b x y (by rw [hx,hy]; exact eq)
  refine ⟨e.trans T,?_,?_,he⟩
  · change atPoint T (e a)=u; rw [ea,hx]
  · change atPoint T (e b)=w; rw [eb,hy]

private theorem cycle_map {l v : Nat} (F : Shore c₀ l L) (Y : Shore c₀ v Eight) (D : CycleData F Y)
    (Z : Shore d₀ v Eight) (hz : ∀ i j, c₀ (atPoint Y i) (atPoint Y j)=d₀ (atPoint Z i) (atPoint Z j)) :
    ∃ T : Shore d₀ l L, (∀ i j, c₀ (atPoint F i) (atPoint F j)=d₀ (atPoint T i) (atPoint T j)) ∧
      ∀ i j, c₀ (atPoint F i) (atPoint Y j)=d₀ (atPoint T i) (atPoint Z j) := by
  let T := sync p F
  let sl := D.cycle.points.toEmbedding.trans (emb F)
  have rangeS (x) : x∈Set.range sl ↔ c₀ x x=l := by
    refine Iff.trans ?_ (range_emb F x)
    exact ⟨fun ⟨i,h⟩ => ⟨D.cycle.points i,h⟩,fun ⟨i,h⟩ => ⟨D.cycle.points.symm i,by simpa [sl] using h⟩⟩
  obtain ⟨a,z,az,rows,names⟩ := RegionalCycleExtension.edges F Y D.mark D.other D.palette D.code D.cells D.cycle
  have full (k) : ∃ i, D.cycle.label i=k := by
    obtain ⟨j,h⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun j => D.cycle.label j=k)).card by rw [D.cycle.twice]; decide)
    exact ⟨j,(Finset.mem_filter.mp h).2⟩
  obtain ⟨e,ll,yl⟩ := RegionalFourTwelve.cycle_named p az sl (emb T) (emb Y) (emb Z) rangeS (range_emb T)
    hz D.cycle.label full rows names
  let G' := D.cycle.points.symm.trans (e.trans T)
  refine ⟨G',fun i j => ?_,fun i j => ?_⟩
  · simpa only [sl,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
      using ll (D.cycle.points.symm i) (D.cycle.points.symm j)
  · simpa only [sl,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
      using common_transpose p (yl j (D.cycle.points.symm i))

private theorem uniform_map {l r k m} (F : Shore c₀ l (Fin k)) (S : Shore c₀ r (Fin m))
    (T : Shore d₀ l (Fin k)) (W : Shore d₀ r (Fin m)) (un : Uniform F S) (i j) :
    c₀ (atPoint F i) (atPoint S j)=d₀ (atPoint T i) (atPoint W j) := by
  obtain ⟨x,y,support⟩ := StrategyColors.exists_source p (atPoint T i) (atPoint W j)
  have eq := (associated p).mpr (StrategyColors.maps_support p support)
  let a := F.symm ⟨x,(SmallShore.endpoints p eq).1.trans (T i).property⟩
  let b := S.symm ⟨y,(SmallShore.endpoints p eq).2.trans (W j).property⟩
  exact (un i j a b).trans (by simpa only [a,b,atPoint,Equiv.apply_symm_apply] using eq)

private theorem twin_map {l r k m} (F : Shore c₀ l (Fin k)) (S : Shore c₀ r (Fin m))
    (T : Shore d₀ l (Fin k)) (W : Shore d₀ r (Fin m))
    (lf : ∀ i j, c₀ (atPoint F i) (atPoint F j)=d₀ (atPoint T i) (atPoint T j))
    (rs : ∀ i j, c₀ (atPoint S i) (atPoint S j)=d₀ (atPoint W i) (atPoint W j))
    (a : Fin k) (b : Fin m) (mark : c₀ (atPoint F a) (atPoint S b)=d₀ (atPoint T a) (atPoint W b))
    (tw : twins c₀ l r) (i j) : c₀ (atPoint F i) (atPoint S j)=d₀ (atPoint T i) (atPoint W j) := by
  let f := F.symm.trans T
  have local' (z w : Cell c₀ l) : c₀ z.val w.val=d₀ (f z).val (f w).val := by
    simpa only [f,Equiv.trans_apply,atPoint,Equiv.apply_symm_apply] using lf (F.symm z) (F.symm w)
  have root : c₀ (F a).val (atPoint S b)=d₀ (f (F a)).val (atPoint W b) := by simpa [f] using mark
  simpa only [f,Equiv.trans_apply,Equiv.symm_apply_apply] using
    rectangle p (atPoint S) (atPoint W) f local' rs (F a) b (S b).property root tw (F i) j (S j).property

/-- Source anchors consist of one point in each of the three four-point
fibers and two points in the eight-point fiber. -/
def anchors {l : Fin 3 → Nat} {v : Nat} (F : ∀ i : Fin 3, Shore c₀ (l i) L)
    (Y : Shore c₀ v Eight) (a b : Eight) : Fin 5 → Fin n :=
  ![atPoint (F 0) 0,atPoint (F 1) 0,atPoint (F 2) 0,atPoint Y a,atPoint Y b]

private theorem four_anchor {l : Fin 3 → Nat} {v : Nat} (F : ∀ i : Fin 3, Shore c₀ (l i) L)
    (Y : Shore c₀ v Eight) (a b : Eight) (i : Fin 3) : anchors F Y a b (i.castLE (by decide))=atPoint (F i) 0 := by fin_cases i <;> rfl

theorem solve {l : Fin 3 → Nat} {v : Nat} (F : ∀ i : Fin 3, Shore c₀ (l i) L) (Y : Shore c₀ v Eight)
    (reg : Nat → Prop) (cover : ∀ x, reg (c₀ x x) → (∃ i, c₀ x x=l i) ∨ c₀ x x=v)
    (a b : Eight) (w : Fin 5 → Fin n) (matched : ∀ i j, c₀ (anchors F Y a b i) (anchors F Y a b j)=d₀ (w i) (w j))
    (square : ∀ i j : Fin 3, i≠j → twins c₀ (l i) (l j))
    (rules : ∀ i, twins c₀ (l i) v ∨ (Nonempty (CycleData (F i) Y) ∧
      (sharp (F i) Y a b ∨ ∀ j, i≠j → Uniform (F i) (F j)))) : Realizes p reg := by
  classical
  let idx (i : Fin 3) : Fin 5 := i.castLE (by decide)
  let root := fun i => w (idx i)
  have usual (i) : anchors F Y a b (idx i)=atPoint (F i) 0 := four_anchor F Y a b i
  have ff (i j) : c₀ (atPoint (F i) 0) (atPoint (F j) 0)=d₀ (root i) (root j) := by
    simpa only [usual] using matched (idx i) (idx j)
  obtain ⟨Z,za,zb,zz⟩ := two p Y (by decide) a b (w 3) (w 4) (matched 3 4)
  have ax (i) : c₀ (atPoint (F i) 0) (atPoint Y a)=d₀ (root i) (atPoint Z a) := by
    rw [za,←usual]; exact matched _ 3
  have bx (i) : c₀ (atPoint (F i) 0) (atPoint Y b)=d₀ (root i) (atPoint Z b) := by
    rw [zb,←usual]; exact matched _ 4
  have frames (i) : ∃ T : Shore d₀ (l i) L, (∀ s t, c₀ (atPoint (F i) s) (atPoint (F i) t)=d₀ (atPoint T s) (atPoint T t)) ∧
      (∀ s t, c₀ (atPoint (F i) s) (atPoint Y t)=d₀ (atPoint T s) (atPoint Z t)) ∧
      (atPoint T 0=root i ∨ ∀ j, i≠j → Uniform (F i) (F j)) := by
    rcases rules i with tw|⟨⟨D⟩,use⟩
    · obtain ⟨T,t0,_,names⟩ := two p (F i) (by decide) 0 0 (root i) (root i) (ff i i)
      exact ⟨T,names,fun s t => twin_map p (F i) Y T Z names zz 0 a (by rw [t0]; exact ax i) tw s t,Or.inl t0⟩
    · obtain ⟨T,tt,ty⟩ := cycle_map p (F i) Y D Z zz
      refine ⟨T,tt,ty,use.imp (fun sep => ?_) id⟩
      let j := T.symm ⟨root i,(ff i i).symm.trans (F i 0).property⟩
      have eq : atPoint T j=root i := congrArg Subtype.val (T.apply_symm_apply _)
      have ja := ty j a
      have jb := ty j b
      rw [eq] at ja jb
      exact (congrArg (atPoint T) (sep 0 j ((ax i).trans ja.symm) ((bx i).trans jb.symm))).trans eq
  choose T tt ty pin using frames
  have pairs (i j : Fin 3) (s t : L) : c₀ (atPoint (F i) s) (atPoint (F j) t)=d₀ (atPoint (T i) s) (atPoint (T j) t) := by
    by_cases same : i=j
    · subst j; exact tt i s t
    rcases pin i with hi|hi
    swap
    · exact uniform_map p _ _ (T i) (T j) (hi _ same) s t
    rcases pin j with hj|hj
    · exact twin_map p _ _ _ _ (tt i) (tt j) 0 0 (by rw [hi,hj]; exact ff i j) (square i j same) s t
    · exact common_transpose p (uniform_map p _ _ (T j) (T i) (hj _ (Ne.symm same)) t s)
  let X := Region c₀ reg
  have loc (x : X) : (∃ i s, atPoint (F i) s=x.val) ∨ ∃ j, atPoint Y j=x.val := by
    rcases cover x.val ((mem_vertices _ _ _).mp x.property) with ⟨i,h⟩|h
    · exact Or.inl ⟨i,(range_emb (F i) _).mpr h⟩
    · exact Or.inr ((range_emb Y _).mpr h)
  let Q := Fin 3 × L ⊕ Eight
  let f (s : Q) : Fin n := s.elim (fun z => atPoint (F z.1) z.2) (atPoint Y)
  let g (s : Q) : Fin n := s.elim (fun z => atPoint (T z.1) z.2) (atPoint Z)
  have pick (x : X) : ∃ h, f h=x.val := by
    rcases loc x with ⟨i,s,h⟩|⟨j,h⟩
    · exact ⟨Sum.inl (i,s),h⟩
    · exact ⟨Sum.inr j,h⟩
  choose h hh using pick
  have all (i j : Q) : c₀ (f i) (f j)=d₀ (g i) (g j) := by
    cases i with
    | inl i => cases j with
      | inl j => exact pairs _ _ _ _
      | inr j => exact ty _ _ _
    | inr i => cases j with
      | inl j => exact common_transpose p (ty _ _ _)
      | inr j => exact zz _ _
  have hit (x y : X) : c₀ x.val y.val=d₀ (g (h x)) (g (h y)) := by rw [←hh x,←hh y]; exact all _ _
  obtain ⟨e,he⟩ := bundle p reg (fun x => g (h x)) hit
  exact ⟨e,fun i j => by rw [he,he]; exact hit i j⟩

end QGI.Coherent.LargeOrderEightAnchors
