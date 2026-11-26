import RegionalEightTwelveAdjustment
import RegionalEightTwelveThin
import RegionalEightTwelvePartitions

noncomputable section
namespace QGI.Coherent.RegionalEightTwelve
open SmallUnion SmallFiberExtension StrategyColorLaws SixTenCoordinates RegionalEightTwelveGeometry RegionalEightTwelveStats
open RegionalEightTwelvePartitions (Split Label)
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
open private bundle from SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

theorem of_common_triples {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) (split : Split (family F Y v))
    (constant : ∀ i j k, split.column j=split.column k → color F Y j i=color F Y k i) : Realizes p reg := by
  classical
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) l Point := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let Z : Shore (targetName p) r Index := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨h,_,names⟩ := SmallShore.realize_at p (by decide : 0<8) (by decide) (atPoint F) (atPoint W) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp W.injective) (range F) (range W) 0 0
  let T := h.trans W
  let law := commonLaws p
  have count (j) : (family F Y v j).card=2 := by
    have eq : family F Y v j=Finset.univ.filter (fun i => split.point i=split.column j) := by ext i; simp [split.pair]
    exact (congrArg Finset.card eq).trans (split.two _)
  have weight (j) : (family T Z v j).card=2 := by
    have x := Block.degree_eq law (incidence F Y T Z v) 0 j
    simpa using x.symm.trans (by simpa using count 0)
  have coords := degrees (targetLaws p) T Z v
  have degree (i) : (incident (family T Z v) i).card=3 := by
    have x := coords.2.2; rw [weight] at x
    exact (coords.2.1 i).trans (by omega)
  obtain ⟨b,member,three⟩ := RegionalEightTwelvePartitions.transported law F Y T Z v split names weight degree
  have onto {I : Type} [Fintype I] (u : I → Label) {k : Nat} (pos : 0<k) (c : ∀ s, (Finset.univ.filter (fun i => u i=s)).card=k) :
      Function.Surjective u := by
    intro s; obtain ⟨i,hi⟩ := Finset.card_pos.mp (pos.trans_eq (c s).symm); exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  have pointAll := onto split.point (by decide : 0<2) split.two
  have columnAll := onto split.column (by decide : 0<3) split.three
  have targetAll := onto b (by decide : 0<3) three
  obtain ⟨i₀,hi₀⟩ := pointAll (split.column 0)
  have first : source G (atPoint Y 0) (atPoint F i₀)=v := (Finset.mem_filter.mp ((split.pair 0 i₀).mpr hi₀)).2
  let u := source G (atPoint F i₀) (atPoint Y 0)
  have src (i j) : source G (atPoint F i) (atPoint Y j)=u ↔ split.column j=split.point i := by
    rw [eq_comm (a:=split.column j),←split.pair]
    change _ ↔ _∈Finset.univ.filter _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun eq => ((sourceLaws _).rev eq).trans first,fun eq => (sourceLaws _).rev (eq.trans first.symm)⟩
  have tgt (i j) : targetName p (atPoint T i) (atPoint Z j)=u ↔ b j=split.point i := by
    rw [eq_comm (a:=b j),←member]
    change _ ↔ _∈Finset.univ.filter _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun eq => (law.rev eq.symm).symm.trans first,fun eq => (law.rev (first.trans eq.symm)).symm⟩
  have eqClass {i j x y : Index} (same : targetName p (atPoint Z i) (atPoint Z j)=targetName p (atPoint Z x) (atPoint Z y)) :
      b i=b j ↔ b x=b y := by
    have gram := mixed_counts (targetLaws p) T Z T Z v v same
    have eq (i j) : 0<((family T Z v i)∩(family T Z v j)).card ↔ b i=b j := by
      rw [Finset.card_pos]
      constructor
      · rintro ⟨o,ho⟩; obtain ⟨hi,hj⟩ := Finset.mem_inter.mp ho; exact ((member i o).mp hi).symm.trans ((member j o).mp hj)
      · intro e; obtain ⟨o,ho⟩ := pointAll (b i); exact ⟨o,Finset.mem_inter.mpr ⟨(member i o).mpr ho,(member j o).mpr (ho.trans e)⟩⟩
    rw [←eq,←eq,gram]
  have q := SmallShore.correspondence p (atPoint Y) (atPoint Z) r (Subtype.val_injective.comp Y.injective)
    (Subtype.val_injective.comp Z.injective) (range Y) (range Z)
  rcases EightTwelveCatalog.thin_or_closed _ q.2.1 b three (fun _ _ _ _ h => eqClass h) with thin|closed
  · exact RegionalEightTwelveThin.realize p Y F Z T reg (fun i hi => (cover i hi).symm) split.column b split.point
      columnAll split.two src tgt thin
  obtain ⟨e,rr,cross⟩ := RegionalEightTwelveAdjustment.adjust_closed p Y F Z T names split.column b split.point
    columnAll targetAll pointAll src tgt (fun i j k h => (sourceLaws _).rev (constant i j k h)) closed
  let s : Point ⊕ Index → Fin n := Sum.elim (atPoint F) (atPoint Y)
  let t : Point ⊕ Index → Fin n := Sum.elim (atPoint T) (fun j => atPoint Z (e j))
  have eq (i j) : source G (s i) (s j)=targetName p (t i) (t j) := by
    cases i with
    | inl i => cases j with | inl j => exact names i j | inr j => exact cross i j
    | inr i => cases j with | inl j => exact common_transpose p (cross j i) | inr j => exact rr i j
  have pick (x : Region (source G) reg) : ∃ i, s i=x.val := by
    rcases cover _ ((mem_vertices _ _ _).mp x.property) with left|right
    · obtain ⟨i,hi⟩ := (range F _).mpr left; exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := (range Y _).mpr right; exact ⟨.inr i,hi⟩
  choose k hk using pick
  have both (i j) : source G i.val j.val=targetName p (t (k i)) (t (k j)) := by rw [←hk i,←hk j]; exact eq _ _
  obtain ⟨u,hu⟩ := bundle p reg (fun i => t (k i)) both
  exact ⟨u,fun i j => by rw [hu,hu]; exact both i j⟩

end QGI.Coherent.RegionalEightTwelve

