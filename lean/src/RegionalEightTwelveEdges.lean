import RegionalEightTwelveStats
import RegionalSixTwelveDispatch

noncomputable section
namespace QGI.Coherent.RegionalEightTwelve
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws RegionalEightTwelveGeometry RegionalEightTwelveStats
open FourTwelveFunctional (source)
open FourTwelveCycle (neighbors)
open private bundle from SmallFiberExtension
open private range from RegionalSixTwelveDispatch

private def embed {n v : Nat} {c : Fin n → Fin n → Nat} {X : Type} (F : Shore c v X) : X ↪ Fin n :=
  ⟨atPoint F,fun _ _ h => F.injective (Subtype.ext h)⟩

private theorem rows {n l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r Index) (v : Nat) (present : ∃ j i, color F Y j i=v) (j : Index) :
    neighbors c v (atPoint Y j)=(family F Y v j).map (embed F) := by
  obtain ⟨k,i,hit⟩ := present
  ext z
  constructor
  · intro hz
    have same : c (atPoint Y j) z=c (atPoint Y k) (atPoint F i) := (Finset.mem_filter.mp hz).2.trans hit.symm
    let x : {x // c x x=l} := ⟨z,(law.last same).trans (F i).property⟩
    let t := F.symm x
    have ht : atPoint F t=z := congrArg Subtype.val (F.apply_symm_apply x)
    exact Finset.mem_map.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [ht]; exact (Finset.mem_filter.mp hz).2⟩,ht⟩
  · intro hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K)

theorem named_connected_simple {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index)
    (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r Index)
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (weight : (family F Y v 0).card=2) (simple : Function.Injective (family F Y v))
    (connected : crosses (Finset.univ.image (family F Y v))) :
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) := by
  classical
  let a := family F Y v
  let b := family T Z v
  have gram (i j) : (a i∩a j).card=(b i∩b j).card := mixed_counts (commonLaws p) F Y T Z v v (right i j)
  have src := degrees (sourceLaws _) F Y v
  have dst := degrees (targetLaws p) T Z v
  have aw (j) : (a j).card=2 := (src.1 j).trans weight
  have bw (i) : (b i).card=2 := (by simpa only [Finset.inter_self] using (gram i i).symm : (b i).card=(a i).card).trans (aw i)
  have ad : (incident a 0).card=3 := by have h := src.2.2; rw [weight] at h; change 12*2=8*(incident a 0).card at h; omega
  have bd : (incident b 0).card=3 := by have h := dst.2.2; change 12*(b 0).card=8*(incident b 0).card at h; rw [bw] at h; omega
  have bt : Function.Injective b := by
    intro j k eq
    apply simple
    have same := gram j k
    rw [eq,Finset.inter_self,bw] at same
    exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (same.trans (aw j).symm).ge).symm.trans
      (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (same.trans (aw k).symm).ge)
  obtain ⟨e,member⟩ := align_connected a b aw bw simple bt (fun i => (src.2.1 i).trans ad)
    (fun i => (dst.2.1 i).trans bd) connected gram
  let T' := e.trans T
  have reindex (j) : a j=family T' Z v j := by
    ext i
    simpa only [b,family,T',Finset.mem_filter,Finset.mem_univ,true_and,atPoint,Equiv.trans_apply] using member j i
  have existsSrc : ∃ k i, color F Y k i=v := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (aw 0).symm)
    exact ⟨0,i,(Finset.mem_filter.mp hi).2⟩
  have existsDst : ∃ k i, color T' Z k i=v := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (aw 0).symm)
    exact ⟨0,i,(Finset.mem_filter.mp ((member 0 i).mp hi)).2⟩
  have cells (j) : neighbors (targetName p) v (atPoint Z j)=(a j).map (embed T') := by
    rw [reindex]; exact rows (targetLaws p) T' Z _ existsDst j
  have wf (s) (hs : s∈Finset.univ.image a) : s.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact aw j
  have dist (s t : Cell) (eq : ∀ j, (a j∩s).card=(a j∩t).card) : (∃ i : Point, i∈s ↔ i∈t) → s=t := by
    apply determines_connected _ wf connected s t
    intro u hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hu
    exact eq j
  have get (x y : Fin n) (same : ∀ j, source G (atPoint Y j) x=targetName p (atPoint Z j) y)
      (anchor : ∃ i, source G x (atPoint F i)=targetName p y (atPoint T' i)) :
      ∀ i, source G x (atPoint F i)=targetName p y (atPoint T' i) :=
    RegionalPairShores.recover p (embed F) (embed T') (atPoint Y) (atPoint Z) (fun _ => v) a
      (rows (sourceLaws _) F Y _ existsSrc) cells dist same anchor
  have cross (j) : ∀ i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T' i) := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (aw j).symm)
    exact get _ _ (fun k => right k j) ⟨i,((Finset.mem_filter.mp hi).2).trans (Finset.mem_filter.mp ((member j i).mp hi)).2.symm⟩
  exact ⟨e,fun i j => get _ _ (fun k => cross k i) ⟨i,(F i).property.trans (T' i).property.symm⟩ j,cross⟩

theorem on_pair {l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (solve : ∀ (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r Index),
      (∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j)) →
      ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
        ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i))) : Realizes p reg := by
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l Point := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let W : Shore (targetName p) r Index := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨h,_,names⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide) (atPoint Y) (atPoint W) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp W.injective) (range Y) (range W) 0 0
  let Z := h.trans W
  obtain ⟨e,ll,rl⟩ := solve T Z names
  let s : Point ⊕ Index → Fin n := Sum.elim (atPoint F) (atPoint Y)
  let t : Point ⊕ Index → Fin n := Sum.elim (fun i => atPoint T (e i)) (atPoint Z)
  have eq (i j) : source G (s i) (s j)=targetName p (t i) (t j) := by
    cases i with
    | inl i => cases j with | inl j => exact ll i j | inr j => exact common_transpose p (rl j i)
    | inr i => cases j with | inl j => exact rl i j | inr j => exact names i j
  have pick (x : Region (source G) reg) : ∃ i, s i=x.val := by
    rcases cover _ ((mem_vertices _ _ _).mp x.property) with left|right
    · obtain ⟨i,hi⟩ := (range F _).mpr left; exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := (range Y _).mpr right; exact ⟨.inr i,hi⟩
  choose k hk using pick
  have both (i j) : source G i.val j.val=targetName p (t (k i)) (t (k j)) := by rw [←hk i,←hk j]; exact eq _ _
  obtain ⟨u,hu⟩ := bundle p reg (fun i => t (k i)) both
  exact ⟨u,fun i j => by rw [hu,hu]; exact both i j⟩

theorem of_connected_simple {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) (simple : Function.Injective (family F Y v))
    (connected : crosses (Finset.univ.image (family F Y v))) : Realizes p reg :=
  on_pair p F Y reg cover (fun T Z same => named_connected_simple p F Y T Z same weight simple connected)

end QGI.Coherent.RegionalEightTwelve

