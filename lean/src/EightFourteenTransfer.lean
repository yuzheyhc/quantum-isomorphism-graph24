import EightFourteenReduction
import EightFourteenPlacement

noncomputable section
namespace QGI.Coherent.EightFourteenTransfer
open SixTenCoordinates EightFourteenReduction
open EightFourteenWords (I J Word Axis bit axis side incident)
open EightFourteenPlacement (Key Rep rightName key inside)
open FourTwelveFunctional (source)
open SmallUnion SmallFiberExtension StrategyColorLaws
open private range from RegionalSixTwelveDispatch

def coarse (d : EightFourteenCatalog.RK) : Key := if d=7 then 1 else if d=13 then 2 else 0
attribute [local irreducible] ZivAv.cores14
theorem colors : ∀ d, EightFourteenCatalog.hard d → ∀ i j x y : J,
    (EightFourteenCatalog.right d i j=EightFourteenCatalog.right d x y → rightName (coarse d) i j=rightName (coarse d) x y) ∧
    (rightName (coarse d) i j=rightName (coarse d) x y →
      EightFourteenCatalog.right d i j=EightFourteenCatalog.right d x y ∨ EightFourteenCatalog.right d j i=EightFourteenCatalog.right d x y) := by native_decide
private theorem split_encode (B : I → J → Bool)
    (split : ∀ i q, B i (EightFourteenCatalog.point q false)=true ↔ B i (EightFourteenCatalog.point q true)≠true) :
    ∀ i, ∃ w : Word, ∀ j, B i j=incident w j := by
  intro i
  obtain ⟨w,hw⟩ := EightFourteenWords.encode (fun q => B i (EightFourteenCatalog.point q true))
  have cs : ∀ j : J, ∃ q b, EightFourteenCatalog.point q b=j := by decide
  have index : ∀ q b, axis (EightFourteenCatalog.point q b)=q ∧ side (EightFourteenCatalog.point q b)=b := by decide
  refine ⟨w,fun j => ?_⟩
  obtain ⟨q,b,rfl⟩ := cs j
  rw [incident,(index q b).1,(index q b).2,hw]
  have h := split i q
  cases b <;> cases x : B i (EightFourteenCatalog.point q false) <;> cases y : B i (EightFourteenCatalog.point q true) <;> simp_all

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] (p : PerfectStrategy G H K)
  (F : Shore (source G) l I) (Y : Shore (source G) r J)
  (T : Shore (targetName p) l I) (Z : Shore (targetName p) r J)
  {d : EightFourteenCatalog.RK} {v w : Nat}

structure Data {c : Fin n → Fin n → Nat} (F : Shore c l I) (Y : Shore c r J) (v : Nat) (k : Key) where
  rep : Rep
  sameKey : key rep=k
  rows : Equiv.Perm I
  cols : Equiv.Perm J
  flags : ∀ i j, flag F Y v (rows i) (cols j)=inside rep i j
  names : ∀ i j, rightName k (cols i) (cols j)=rightName k i j

include p in
theorem target_palette (two : ∀ i j, entry F Y i j=v ∨ entry F Y i j=w) (i : I) (j : J) : entry T Z i j=v ∨ entry T Z i j=w := by
  let u := entry T Z i j
  have named : Block F T Y Z (flag F Y u) (flag T Z u) := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=u)) eq
  have deg := Block.degree_eq (commonLaws p) named i i
  have hm : j∈Finset.univ.filter (fun y => flag T Z u i y=true) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [flag,u]⟩
  obtain ⟨k,hk⟩ := Finset.card_pos.mp ((Finset.card_pos.mpr ⟨j,hm⟩).trans_eq deg.symm)
  have h : entry F Y i k=u := of_decide_eq_true (Finset.mem_filter.mp hk).2
  change u=v ∨ u=w
  rw [←h]; exact two i k

theorem layouts (D : HardData F Y d v w)
    (ll : ∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j))
    (rr : ∀ i j, source G (atPoint Y i) (atPoint Y j)=targetName p (atPoint Z i) (atPoint Z j)) :
    Nonempty (Data F Y v (coarse d)) ∧ Nonempty (Data T Z v (coarse d)) := by
  let B := flag F Y v
  let C := flag T Z v
  have named : Block F T Y Z B C := fun ⦃_ _ _ _⦄ eq => congrArg (fun t => decide (t=v)) eq
  have tg (i j : I) (ne : i≠j) : Block.overlap C i j=3 := (Block.gram (commonLaws p) named (ll i j)).symm.trans (D.overlap i j ne)
  have ts (i : I) (q : Axis) : C i (EightFourteenCatalog.point q false)=true ↔ C i (EightFourteenCatalog.point q true)≠true := by
    let j := EightFourteenCatalog.point q false
    let k := EightFourteenCatalog.point q true
    have neg (b : Bool) : ¬(C i j=b ∧ C i k=b) := by
      intro ⟨h₁,h₂⟩
      let L := fun j i => decide (B i j=b)
      let R := fun j i => decide (C i j=b)
      have same : Block.overlap L j k=Block.overlap R j k :=
        Block.gram (commonLaws p) (Block.flip (commonLaws p) (Block.map named (fun z => decide (z=b)))) (rr j k)
      have blank : Block.overlap L j k=0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro x h
        have values := (Finset.mem_filter.mp h).2
        simp only [L,decide_eq_true_eq] at values
        have sp := D.splitRows x q
        change B x j=true ↔ B x k≠true at sp
        rw [values.1,values.2] at sp
        cases b <;> simp_all
      have pos : 0<Block.overlap R j k := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [R,h₁,h₂]⟩⟩
      omega
    have a := neg true
    have b := neg false
    change C i j=true ↔ C i k≠true
    cases hj : C i j <;> cases hk : C i k <;> simp_all
  obtain ⟨a,ha,e,g,hb,hn⟩ := EightFourteenPlacement.present (coarse d) B (split_encode B D.splitRows) D.overlap
  obtain ⟨z,hz,f,t,hc,hm⟩ := EightFourteenPlacement.present (coarse d) C (split_encode C ts) tg
  exact ⟨⟨⟨a,ha,e,g,hb,hn⟩⟩,⟨⟨z,hz,f,t,hc,hm⟩⟩⟩
end QGI.Coherent.EightFourteenTransfer
