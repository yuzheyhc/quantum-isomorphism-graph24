import RegionalThreeClasses
import RegionalSixTwelveDispatch

noncomputable section
namespace QGI.Coherent.RegionalSixTwelve
open SixTenCoordinates SmallFiberExtension StrategyColorLaws RegionalSixTwelveStats
open RegionalSixTwelveGeometry (Point Family degree)
open FourTwelveFunctional (source)
open private star_degree from RegionalSixTwelve

private theorem partition (f : Family) (weights : ∀ s∈f, s.card=2) (one : ∀ i, degree f i=1) :
    ∃ which : Point → Member f, Function.Surjective which ∧ ∀ i (s : Member f), i∈s.val ↔ which i=s := by
  classical
  have each (i : Point) := Finset.card_eq_one.mp ((star_degree f i).trans (one i))
  choose idx hi using each
  have mem (i : Point) (s : Member f) : i∈s.val ↔ idx i=s := by
    have m : s∈star f i ↔ idx i=s := by rw [hi]; simp only [Finset.mem_singleton,eq_comm]
    simpa only [star,Finset.mem_filter,Finset.mem_univ,true_and] using m
  refine ⟨idx,fun s => ?_,mem⟩
  obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (weights _ s.property).symm)
  exact ⟨i,(mem i s).mp hi⟩

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

theorem matching_named {m l r v : Nat} [NeZero m] (F : Shore (source G) l Point) (Y : Shore (source G) r (Fin m))
    (T : Shore (targetName p) l Point) (Z : Shore (targetName p) r (Fin m))
    (right : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j))
    (weight : (family F Y v 0).card=2) (size : (support (family F Y v)).card=3)
    (constant : ∀ j i x, (∀ t, i∈family F Y v t ↔ x∈family F Y v t) → color F Y j i=color F Y j x) :
    ∃ e : Equiv.Perm Point, (∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T (e i)) (atPoint T (e j))) ∧
      ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint Z j) (atPoint T (e i)) := by
  classical
  let a := family F Y v
  let b := family T Z v
  let f := support a
  let g := support b
  let A (j : (Fin m)) : Member f := ⟨a j,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let B (j : (Fin m)) : Member g := ⟨b j,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have gram (i j) : (a i∩a j).card=(b i∩b j).card := overlap_names (commonLaws p) F Y T Z v (right i j)
  obtain ⟨weights,_,_,regA⟩ := statistics (sourceLaws _) F Y v
  obtain ⟨_,_,_,regB⟩ := statistics (targetLaws p) T Z v
  have aw (i) : (a i).card=2 := (weights i).trans weight
  have bw (i) : (b i).card=2 := (by simpa only [Finset.inter_self] using (gram i i).symm : (b i).card=(a i).card).trans (aw i)
  have wf (s) (hs : s∈f) : s.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact aw j
  have wg (s) (hs : s∈g) : s.card=2 := by obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs; exact bw j
  obtain ⟨h,hh⟩ := label_equiv a b aw bw gram
  have step (j) : h (A j)=B j := Subtype.ext (hh j)
  have cs : f.card=g.card := by simpa only [Fintype.card_coe] using Fintype.card_congr h
  have ds := regular_degree f wf regA
  have dt := regular_degree g wg regB
  change f.card=3 at size
  obtain ⟨cl,onto,sm⟩ := partition f wf (fun i => (regA i).trans (by change degree f 0=1; omega))
  obtain ⟨dl,_,tm⟩ := partition g wg (fun i => (regB i).trans (by change degree g 0=1; omega))
  let q : Member f ≃ Fin 3 := Fintype.equivOfCardEq (by rw [Fintype.card_coe,Fintype.card_fin,size])
  let d := h.symm.trans q
  let tag := fun j => q (A j)
  have sur : Function.Surjective tag := by
    intro s
    let x := q.symm s
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp x.property
    have hit : A j=x := Subtype.ext eq
    exact ⟨j,(congrArg q hit).trans (q.apply_symm_apply s)⟩
  apply RegionalThreeClasses.align p F Y T Z (by decide) right (q ∘ cl) (d ∘ dl) tag (q.surjective.comp onto) sur
  · intro j i
    change color F Y j i=v ↔ q (cl i)=q (A j)
    rw [q.injective.eq_iff,←sm]
    simp [color,A,a,family]
  · intro j i
    change color T Z j i=v ↔ q (h.symm (dl i))=q (A j)
    rw [q.injective.eq_iff,h.symm_apply_eq,step,←tm]
    simp [color,B,b,family]
  · intro j i x eq
    apply constant j i x
    intro t
    change i∈(A t).val ↔ x∈(A t).val
    rw [sm,sm,q.injective eq]

theorem of_matching {l r v : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Right) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (weight : (family F Y v 0).card=2) (size : (support (family F Y v)).card=3)
    (constant : ∀ j i x, (∀ t, i∈family F Y v t ↔ x∈family F Y v t) → color F Y j i=color F Y j x) : Realizes p reg :=
  on_pair p F Y reg cover (fun T Z right => matching_named p F Y T Z right weight size constant)

end QGI.Coherent.RegionalSixTwelve

