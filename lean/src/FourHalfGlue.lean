import FourHalfRealize

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open FourTwelveCycle (Edge edge)

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
   (p : PerfectStrategy G H K)

theorem glue (P : Chart (source G) r v) {TX : Shore (targetName p) r Eight} {TY : Shore (targetName p) v Eight}
    {q : Eight → Four} (D : Aligned p P.X TX l q) (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (bal : balanced q) (can : canonical q)
    (old : ∀ i j, source G (vertex P.X P.Y i) (vertex P.X P.Y j)=targetName p (vertex TX TY i) (vertex TX TY j))
    (nt : ¬FiberPairExtension.twins (source G) r v) (tw : FiberPairExtension.twins (source G) l v)
    (a z : Nat) (two : ∀ i j, source G (atPoint D.F i) (atPoint P.Y j)=a ∨ source G (atPoint D.F i) (atPoint P.Y j)=z)
    (edges : Eight → Edge) (mark : ∀ i j, source G (atPoint D.F i) (atPoint P.Y j)=a ↔ i∈edge (edges j)) :
    Realizes p (fun k => k=l ∨ k=r ∨ k=v) := by
  let M := markColumn D.F P.Y a
  let N := markColumn D.T TY a
  have hc := named_cycle p D
  have hn : Block P.Y TY D.F D.T M N := fun ⦃i j x y⦄ e => (col_names p D.F P.Y D.T TY a z two i j x y).mp e
  have gm := Block.gram (commonLaws p) hn
  have gram (i j : Eight) : dot (M i) (M j)=dot (N i) (N j) := gm (old (.inr i) (.inr j))
  have full (k : Four) : ∃ i,q i=k := by
    have h := bal k
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun j => q j=k)).card by omega)
    exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  have mix (k : Four) (j : Eight) : dot (fun i => hit i k) (M j)=dot (fun i => hit i k) (N j) := by
    obtain ⟨i,rfl⟩ := full k
    exact mixed p P.X TX P.Y TY D.F D.T _ _ _ hc hn (fun x y => old (.inl x) (.inr y)) i j
  rcases dichotomy M N (col_two D.F P.Y a edges mark) (col_parts D.F P.Y a z two tw) gram mix with eq|⟨s,b,zero,ms,ns⟩
  · exact equal_realization p P.X P.Y D.F TX TY D.T old
      (fun j i => (D.sourceRow j i).trans (D.targetRow j i).symm)
      (fun j i => (col_names p D.F P.Y D.T TY a z two j i j i).mpr (congrFun (eq j) i))
      (fun i j => D.four i j i j rfl)
  · have leftMark : Block P.Y P.Y D.F D.F M M := by
      intro i j x y e
      exact congrArg (fun t => decide (t=a)) (Relations.transpose (closure G) e)
    have size := Block.degree_eq (sourceLaws _) (Block.flip (sourceLaws _) leftMark) (0 : Four) 1
    change (Finset.univ.filter (fun j => M j 0=true)).card=(Finset.univ.filter (fun j => M j 1=true)).card at size
    simp only [ms] at size
    have hs := halves_balanced s b size
    have qn (i j x y : Eight) (eq : internal P.key P.swap false i j=internal P.key P.swap false x y) :
        pos (q i) (q j)=pos (q x) (q y) := by
      have e := (P.names (.inl i) (.inl j) (.inl x) (.inl y)).mp (by simpa only [index_val.1] using eq)
      exact cycle_detect _ _ _ _ (Block.gram (commonLaws p) hc (e.trans (old (.inl x) (.inl y))))
    have sn (i j x y : Eight) (eq : internal P.key P.swap true i j=internal P.key P.swap true x y) : s i=s j ↔ s x=s y := by
      have e := (P.names (.inr i) (.inr j) (.inr x) (.inr y)).mp (by simpa only [index_val.2] using eq)
      have d : dot (M i) (M j)=dot (M x) (M y) := Block.gram (sourceLaws _) leftMark e
      rw [ms,ms,ms,ms] at d
      exact halves_detect _ _ _ _ _ d
    apply opposite_realization p P D lr lv rv old s b _ (support P.key P.swap q s (nonTwin P nt) bal can zero hs qn sn)
    intro i j x y
    have e := col_names p D.F P.Y D.T TY a z two i j x y
    change _ ↔ M i j=N x y at e
    simpa only [ms,ns] using e

end QGI.Coherent.FourHalfModel
