import RegionalSixTwelve
import RegionalSixTwelveStats

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open SixTenCoordinates StrategyColorLaws
open RegionalSixTwelveGeometry (Point Family degree Determines)
open RegionalSixTwelveStats
open FourTwelveFunctional (source)
open FourTwelveCycle (neighbors)

private def embed {n v : Nat} {c : Fin n → Fin n → Nat} {X : Type} (F : Shore c v X) : X ↪ Fin n :=
  ⟨atPoint F,fun _ _ h => F.injective (Subtype.ext h)⟩

private theorem rows {n m l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r (Fin m)) (v : Nat) (present : ∃ j i, color F Y j i=v) (j : (Fin m)) :
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

private theorem align_regular_more {I : Type} [Fintype I] (a b : I → Cell)
    (aw : ∀ j, (a j).card=2) (bw : ∀ j, (b j).card=2)
    (gram : ∀ i j, (a i∩a j).card=(b i∩b j).card)
    (regA : RegionalSixTwelveGeometry.Regular (Finset.univ.image a))
    (regB : RegionalSixTwelveGeometry.Regular (Finset.univ.image b))
    (size : ((Finset.univ.image a).card=6 ∨ (Finset.univ.image a).card=12) ∨ (Finset.univ.image a).card=15) :
    ∃ e : Equiv.Perm Point, ∀ j i, i∈a j ↔ e i∈b j := by
  have wf (s) (hs : s∈Finset.univ.image a) : s.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact aw j
  have wg (s) (hs : s∈Finset.univ.image b) : s.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact bw j
  obtain ⟨h,hh⟩ := label_equiv a b aw bw gram
  have cs : (Finset.univ.image a).card=(Finset.univ.image b).card := by simpa only [Fintype.card_coe] using Fintype.card_congr h
  have hs := regular_degree (Finset.univ.image a) wf regA
  have ht := regular_degree (Finset.univ.image b) wg regB
  let d := degree (Finset.univ.image a) 0
  have ds : (d=2 ∨ d=4) ∨ d=5 := by change (degree (Finset.univ.image a) 0=_ ∨ degree (Finset.univ.image a) 0=_) ∨ degree (Finset.univ.image a) 0=_; change ((Finset.univ.image a).card=6 ∨ (Finset.univ.image a).card=12) ∨ (Finset.univ.image a).card=15 at size; omega
  have targetDeg (i) : degree (Finset.univ.image b) i=d := (regB i).trans (by change degree (Finset.univ.image b) 0=degree (Finset.univ.image a) 0; omega)
  have src (s : Member (Finset.univ.image a)) : ∃ j, a j=s.val := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp s.property; exact ⟨j,hj⟩
  have hgram (s t : Member (Finset.univ.image a)) : (s.val∩t.val).card=((h s).val∩(h t).val).card := by
    obtain ⟨j,hj⟩ := src s
    obtain ⟨k,hk⟩ := src t
    have sj : (⟨a j,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ : Member (Finset.univ.image a))=s := Subtype.ext hj
    have tk : (⟨a k,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ : Member (Finset.univ.image a))=t := Subtype.ext hk
    rw [←sj,←tk,hh,hh]
    exact gram j k
  obtain ⟨e,he⟩ := align_degrees h wf wg ds regA targetDeg hgram
  have member (j i) : i∈a j ↔ e i∈b j := by
    have h := he i ⟨a j,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    rwa [hh] at h
  exact ⟨e,member⟩

theorem mixed_counts {n m l r : Nat} {c d : Fin n → Fin n → Nat} (law : Laws c d)
    (F : Shore c l Point) (Y : Shore c r (Fin m)) (T : Shore d l Point) (Z : Shore d r (Fin m))
    (v w : Nat) {i j x y : (Fin m)} (hit : c (atPoint Y i) (atPoint Y j)=d (atPoint Z x) (atPoint Z y)) :
    (family F Y v i ∩ family F Y w j).card=(family T Z v x ∩ family T Z w y).card := by
  have h := Block.fold law (incidence F Y T Z v) (Block.flip law (incidence F Y T Z w))
    (fun a b => if a=true ∧ b=true then 1 else 0) hit
  simpa only [decide_eq_true_eq,Finset.sum_boole,←Finset.mem_inter,Finset.filter_mem_eq_inter,Finset.univ_inter] using h

/-- Several named colors may serve as edge probes. Their common right-shore
identification fixes all of the directed colors on the two shores. -/
theorem named_from_probes_more {m l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r (Fin m))
    (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r (Fin m))
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    {I : Type} [Fintype I] (index : I → (Fin m)) (v : I → Nat) (onto : Function.Surjective index)
    (aw : ∀ j, (family F Y (v j) (index j)).card=2)
    (regA : RegionalSixTwelveGeometry.Regular (Finset.univ.image fun j => family F Y (v j) (index j)))
    (regB : RegionalSixTwelveGeometry.Regular (Finset.univ.image fun j => family T Z (v j) (index j)))
    (size : ((Finset.univ.image fun j => family F Y (v j) (index j)).card=6 ∨
      (Finset.univ.image fun j => family F Y (v j) (index j)).card=12) ∨ (Finset.univ.image fun j => family F Y (v j) (index j)).card=15) :
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) := by
  classical
  let a := fun j => family F Y (v j) (index j)
  let b := fun j => family T Z (v j) (index j)
  have gram (i j) : (a i∩a j).card=(b i∩b j).card := mixed_counts (commonLaws p) F Y T Z _ _ (right (index i) (index j))
  have bw (i) : (b i).card=2 := (by simpa only [Finset.inter_self] using (gram i i).symm : (b i).card=(a i).card).trans (aw i)
  obtain ⟨e,member⟩ := align_regular_more a b aw bw gram regA regB size
  let T' := e.trans T
  have reindex (j) : a j=family T' Z (v j) (index j) := by
    ext i
    simpa only [b,family,T',Finset.mem_filter,Finset.mem_univ,true_and,atPoint,Equiv.trans_apply] using member j i
  have existsSrc (j) : ∃ k i, color F Y k i=v j := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (aw j).symm)
    exact ⟨index j,i,(Finset.mem_filter.mp hi).2⟩
  have existsDst (j) : ∃ k i, color T' Z k i=v j := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (aw j).symm)
    exact ⟨index j,i,(Finset.mem_filter.mp ((member j i).mp hi)).2⟩
  have cells (j) : neighbors (targetName p) (v j) (atPoint Z (index j))=(a j).map (embed T') :=
    (reindex j) ▸ rows (targetLaws p) T' Z _ (existsDst j) (index j)
  have wf (s) (hs : s∈Finset.univ.image a) : s.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact aw j
  have determines := RegionalSixTwelveGeometry.determines_more (Finset.univ.image a) wf size regA
  have dist (s t : Cell) (eq : ∀ j, (a j∩s).card=(a j∩t).card) : (∃ i : Point, i∈s ↔ i∈t) → s=t := by
    apply determines s t
    intro u hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hu
    exact eq j
  have get (x y : Fin n) (same : ∀ j, source G (atPoint Y j) x=targetName p (atPoint Z j) y)
      (anchor : ∃ i, source G x (atPoint F i)=targetName p y (atPoint T' i)) :
      ∀ i, source G x (atPoint F i)=targetName p y (atPoint T' i) :=
    RegionalPairShores.recover p (embed F) (embed T') (atPoint Y ∘ index) (atPoint Z ∘ index) v a
      (fun j => rows (sourceLaws _) F Y _ (existsSrc j) (index j)) cells dist (fun j => same (index j)) anchor
  have cross (j) : ∀ i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T' i) := by
    obtain ⟨k,rfl⟩ := onto j
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (aw k).symm)
    exact get _ _ (fun j => right j (index k)) ⟨i,((Finset.mem_filter.mp hi).2).trans (Finset.mem_filter.mp ((member k i).mp hi)).2.symm⟩
  exact ⟨e,fun i j => get _ _ (fun k => cross k i) ⟨i,(F i).property.trans (T' i).property.symm⟩ j,cross⟩

theorem named_from_probes {m l r : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r (Fin m))
    (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r (Fin m))
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    {I : Type} [Fintype I] (index : I → (Fin m)) (v : I → Nat) (onto : Function.Surjective index)
    (aw : ∀ j, (family F Y (v j) (index j)).card=2)
    (regA : RegionalSixTwelveGeometry.Regular (Finset.univ.image fun j => family F Y (v j) (index j)))
    (regB : RegionalSixTwelveGeometry.Regular (Finset.univ.image fun j => family T Z (v j) (index j)))
    (size : (Finset.univ.image fun j => family F Y (v j) (index j)).card=6 ∨
      (Finset.univ.image fun j => family F Y (v j) (index j)).card=12) :
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) :=
  named_from_probes_more p F Y T Z right index v onto aw regA regB (Or.inl size)

/-- A color with six or twelve distinct two-point columns aligns the six
points while keeping any prescribed named realization of the twelve points.
Every additional directed cross color and every internal color is recovered. -/
theorem edge_named {m l r v : Nat} [NeZero m] (F : Shore (source G) l Point) (Y : Shore (source G) r (Fin m))
    (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r (Fin m))
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (weight : (family F Y v 0).card=2)
    (size : (support (family F Y v)).card=6 ∨ (support (family F Y v)).card=12) :
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) := by
  obtain ⟨wt,_,_,ra⟩ := statistics (sourceLaws _) F Y v
  exact named_from_probes p F Y T Z right id (fun _ => v) Function.surjective_id
    (fun j => (wt j).trans weight) ra (statistics (targetLaws p) T Z v).2.2.2 size

end QGI.Coherent.RegionalSixTwelve


