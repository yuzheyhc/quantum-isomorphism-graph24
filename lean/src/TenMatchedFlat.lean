import TenMatchedCounts
import TenMatchedSigns

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross.MatchedCatalog SixTenCoordinates SmallFiberExtension SmallUnion StrategyColorLaws TenMatchedSquares
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension
open private range from RegionalSixTwelveDispatch

private theorem gram_read {m : Rect} {v u w : Nat} (uv : u≠v) (uw : u≠w) (o : Outside m v u w) (i j : Q) :
    Block.overlap (fun i j => decide (m i j=u)) (i,false) (j,false) = TenMatchedSigns.agree (matrixSign m u) i j := by
  unfold Block.overlap TenMatchedSigns.agree
  simp only [decide_eq_true_eq]
  have count {X : Type} [Fintype X] (q : X → Prop) [DecidablePred q] : (Finset.univ.filter q).card=∑ x, if q x then 1 else 0 := by simp
  rw [count,count,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hi : k=i
  · subst k; simp [o.diag,Ne.symm uv]
  by_cases hj : k=j
  · subst k; simp [o.diag,Ne.symm uv]
  rw [Fintype.sum_bool]
  simp only [o.off i k (Ne.symm hi),o.off j k (Ne.symm hj),hi,hj,not_false_eq_true,true_and]
  cases matrixSign m u i k <;> cases matrixSign m u j k <;> simp [pick,Ne.symm uw,hi,hj]

private theorem flipOutside {m : Rect} {v u w : Nat} (h : Outside m v u w) : Outside (Function.swap m) v u w := by
  refine ⟨fun i s t => h.diag i t s,?_⟩
  intro i j ij s t
  change m (j,t) (i,s)=pick u w (matrixSign m u j i) s t
  rw [h.off j i (Ne.symm ij)]
  cases s <;> cases t <;> rfl

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (A : Frames (l:=l) (r:=r) (c:=source G) (d:=targetName p) v)

theorem sign_map {u w : Nat} (uv : u≠v) (uw : u≠w)
    (S : Outside (rect A.F A.Y) v u w) (D : Outside (rect A.T A.Z) v u w) :
    ∃ π : Equiv.Perm Q, ∃ flip : Bool, ∀ i j, i≠j →
      matrixSign (rect A.T A.Z) u (π i) (π j)=xor flip (matrixSign (rect A.F A.Y) u i j) := by
  let a := rect A.F A.Y
  let b := rect A.T A.Z
  let M := matrixSign a u
  let N := matrixSign b u
  let h : Block A.F A.T A.Y A.Z (fun i j => decide (a i j=u)) (fun x y => decide (b x y=u)) :=
    fun ⦃_ _ _ _⦄ e => congrArg (fun z => decide (z=u)) e
  have lr (i j x y : Q) (ij : i≠j) (xy : x≠y) : TenMatchedSigns.agree M i j=TenMatchedSigns.agree N x y :=
    (gram_read uv uw S i j).symm.trans ((Block.gram (commonLaws p) h (A.ll (i,false) (j,false) (x,false) (y,false)
      ⟨iff_of_false ij xy,Iff.rfl⟩)).trans (gram_read uv uw D x y))
  have rl (i j x y : Q) (ij : i≠j) (xy : x≠y) :
      TenMatchedSigns.agree (Function.swap M) i j=TenMatchedSigns.agree (Function.swap N) x y :=
    (gram_read uv uw (flipOutside S) i j).symm.trans ((Block.gram (commonLaws p) (Block.flip (commonLaws p) h)
      (A.rr (i,false) (j,false) (x,false) (y,false) ⟨iff_of_false ij xy,Iff.rfl⟩)).trans (gram_read uv uw (flipOutside D) x y))
  have n01 : (0:Q)≠1 := by decide
  have m := TenMatchedSigns.canonical M (fun i j ne => (lr i j 0 1 ne n01).trans (lr 0 1 0 1 n01 n01).symm)
    (fun i j ne => (rl i j 0 1 ne n01).trans (rl 0 1 0 1 n01 n01).symm)
  have b := TenMatchedSigns.canonical N (fun i j ne => (lr 0 1 i j n01 ne).symm.trans (lr 0 1 0 1 n01 n01))
    (fun i j ne => (rl 0 1 i j n01 ne).symm.trans (rl 0 1 0 1 n01 n01))
  exact TenMatchedSigns.align M N _ m ((lr 0 1 0 1 n01 n01).symm ▸ b)

include A in
theorem flat_solve (reg : Nat → Prop) (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r) :
    Realizes p reg := by
  obtain ⟨u,w,uv,_,a,b⟩ := palettes A (commonLaws p)
  have align : ∃ π : Equiv.Perm Q, ∃ f : Bool, ∀ i j s t,
      rect A.F A.Y (i,s) (j,t)=rect A.T A.Z (π i,s) (π j,xor f t) := by
    by_cases uw : u=w
    · subst w; refine ⟨Equiv.refl _,false,fun i j s t => ?_⟩
      by_cases ij : i=j
      · subst j; exact (a.diag _ _ _).trans (b.diag _ _ _).symm
      · simpa only [Equiv.refl_apply,a.off _ _ ij,b.off _ _ ij,pick,ite_self]
    obtain ⟨π,f,h⟩ := sign_map p A uv uw a b
    refine ⟨π,f,fun i j s t => ?_⟩
    by_cases ij : i=j
    · subst j; exact (a.diag _ _ _).trans (b.diag _ _ _).symm
    · rw [a.off _ _ ij,b.off _ _ (π.injective.ne ij),h _ _ ij,TenMatchedSquares.flip]
  obtain ⟨π,f,read⟩ := align
  let g : Slot → Slot := fun i => (π i.1,i.2)
  let h : Slot → Slot := fun j => (π j.1,xor f j.2)
  let srcPt :=  Sum.elim (atPoint A.F) (atPoint A.Y)
  let dest := Sum.elim (atPoint A.T ∘ g) (atPoint A.Z ∘ h)
  have matching (i j : Slot ⊕ Slot) : source G (srcPt i) (srcPt j)=targetName p (dest i) (dest j) := by
    rcases i with i|i <;> rcases j with j|j
    · exact A.ll _ _ _ _ ⟨π.injective.eq_iff.symm,Iff.rfl⟩
    · exact read _ _ _ _
    · exact common_transpose p (read _ _ _ _)
    · apply A.rr
      refine ⟨π.injective.eq_iff.symm,?_⟩
      change (i.2=j.2 ↔ xor f i.2=xor f j.2)
      cases f <;> simp
  have choosePt (z : Region (source G) reg) : ∃ i : Slot⊕Slot, srcPt i=z.val := by
    rcases cover _ ((mem_vertices _ _ _).mp z.property) with tag|tag
    · obtain ⟨x,hx⟩ := SixSixCycle.point A.F tag; exact ⟨.inl x,hx⟩
    · obtain ⟨x,hx⟩ := SixSixCycle.point A.Y tag; exact ⟨.inr x,hx⟩
  choose index hi using choosePt
  have same (i j : Region (source G) reg) : source G i.val j.val=targetName p (dest (index i)) (dest (index j)) := by
    rw [←hi i,←hi j]; exact matching _ _
  obtain ⟨e,he⟩ := bundle p reg (fun i => dest (index i)) same
  exact ⟨e,fun i j => by rw [he,he]; exact same i j⟩

end QGI.Coherent.TenPointMatched
