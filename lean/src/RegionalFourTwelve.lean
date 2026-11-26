import RegionalFourTwelveInputs
import RegionalFourTwelveGeometry

noncomputable section
namespace QGI.Coherent.RegionalFourTwelve
open FourTwelveCycle FourTwelveTypes FourTwelveCycleGraph LargeFourteenRegion SmallUnion StrategyColorLaws
open FourTwelveFunctional (source)
open private shore_range from RegionalSixTen
open private card_core from LargeFourteenRegion

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private theorem one_column (p : PerfectStrategy G H K) (reg : Nat → Prop) (F T : V → Fin n) (D : DataFor p reg F T)
    (f : Frame (restricted (source G) F)) (g : Frame (restricted (targetName p) T))
    (same : ∀ i j, source G (F (f.right i)) (F (f.right j))=targetName p (T (g.right i)) (T (g.right j)))
    (j₀ : R) (i₀ : L) (one : (line f (crosses f j₀ i₀) j₀).card=1) :
    ∃ e : Equiv.Perm V, ∀ i j, source G (F i) (F j)=targetName p (T (e i)) (T (e j)) := by
  let c := restricted (source G) F
  have law : SixTenCoordinates.Laws c c := ⟨fun h => Relations.transpose _ h,fun h => (Relations.end_colors _ h).2,
    fun a b i j x y eq => D.srcConfig.products a b i j x y eq⟩
  apply LargeOrderSixteen.anchored p D f.right g.right same
  intro x
  obtain ⟨x,rfl⟩ := f.points.surjective x
  cases x with
  | inr j => exact ⟨j,fun z eq => (D.srcConfig.diagonal _ _ _ eq).symm⟩
  | inl i =>
    let v := crosses f j₀ i₀
    obtain ⟨m,hm⟩ := law.middle ((f.leftDiag i₀).trans (f.leftDiag i).symm)
    have h := (hm (f.right j₀)).2
    obtain ⟨j,hj⟩ := (f.right_iff _).mpr ((Relations.end_colors (closure G) h).1.symm.trans (f.rightDiag j₀))
    have xv : crosses f j i=v := by rw [←hj] at h; exact h.symm
    have constant (k) : (line f v k).card=(line f v 0).card := by
      simpa [line,active,FiberRectangles.degree] using (regular law f v).1 k
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp ((constant j).trans ((constant j₀).symm.trans one))
    have value (x : L) (hx : crosses f j x=v) : x=t := by
      have mem : x ∈ line f v j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
      simpa only [ht,Finset.mem_singleton] using mem
    refine ⟨j,fun z eq => ?_⟩
    obtain ⟨u,rfl⟩ := (f.left_iff z).mpr ((Relations.end_colors (closure G) eq).2.trans (f.leftDiag i))
    exact congrArg f.left ((value u (eq.trans xv)).trans (value i xv).symm)

theorem solve (p : PerfectStrategy G H K) (reg : Nat → Prop) (F T : V → Fin n) (D : DataFor p reg F T)
    {l r : Nat} (four : (SixTenCoordinates.named (restricted (source G) F) l).card=4)
    (twelve : (SixTenCoordinates.named (restricted (source G) F) r).card=12) :
    ∃ e : Equiv.Perm V, ∀ i j, source G (F i) (F j)=targetName p (T (e i)) (T (e j)) := by
  classical
  let c := restricted (source G) F
  let d := restricted (targetName p) T
  obtain ⟨f⟩ := frame four twelve
  let g₀ : Frame d := ⟨f.points,f.l,f.r,f.ne,fun i => (D.sameDiag _).symm.trans (f.leftDiag i),
    fun j => (D.sameDiag _).symm.trans (f.rightDiag j)⟩
  obtain ⟨h,_,rightNames⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide)
    (fun j => F (f.right j)) (fun j => T (g₀.right j)) f.r (D.injF.comp f.right.injective)
    (D.injG.comp g₀.right.injective) (shore_range _ _ _ _ 0 _ D.src f.right_iff)
    (shore_range _ _ _ _ 0 _ D.tgt g₀.right_iff) 0 0
  let g : Frame d := ⟨(Equiv.sumCongr (Equiv.refl L) h).trans g₀.points,f.l,f.r,f.ne,
    g₀.leftDiag,fun j => g₀.rightDiag (h j)⟩
  let sf : V ↪ Fin n := ⟨F,D.injF⟩
  let tf : V ↪ Fin n := ⟨T,D.injG⟩
  let sl := f.left.trans sf
  let tl := g.left.trans tf
  let Y := f.right.trans sf
  let Z := g.right.trans tf
  have sr (z) : z∈Set.range sl ↔ source G z z=f.l := shore_range _ _ F _ 0 _ D.src f.left_iff z
  have tr (z) : z∈Set.range tl ↔ targetName p z z=f.l := shore_range _ _ T _ 0 _ D.tgt g.left_iff z
  have sy (z) : z∈Set.range Y ↔ source G z z=f.r := shore_range _ _ F _ 0 _ D.src f.right_iff z
  have tz (z) : z∈Set.range Z ↔ targetName p z z=f.r := shore_range _ _ T _ 0 _ D.tgt g.right_iff z
  have ns (i j) : source G (Y i) (Y j)=targetName p (Z i) (Z j) := rightNames i j
  have law : SixTenCoordinates.Laws c c := ⟨fun h => Relations.transpose _ h,fun h => (Relations.end_colors _ h).2,
    fun a b i j x y eq => D.srcConfig.products a b i j x y eq⟩
  rcases classify f law with twins | other
  · exact twins_named p reg F T D f g rfl rfl twins
  rcases other with ⟨j,i,one⟩ | binary
  · exact one_column p reg F T D f g ns j i one
  obtain ⟨B⟩ := binary
  have present : ∃ j i, crosses f j i=B.v := by
    let i := (FourTwelveCycle.ends (B.col 0)).1
    have mem : i ∈ line f B.v 0 := by rw [←B.cells]; simp [i,edge]
    exact ⟨0,i,(Finset.mem_filter.mp mem).2⟩
  obtain ⟨j₀,i₀,hv⟩ := present
  have cells (j) : neighbors (source G) B.v (Y j)=(edge (B.col j)).map sl := by
    ext z
    constructor
    · intro hz
      have hit := (Finset.mem_filter.mp hz).2.trans hv.symm
      obtain ⟨i,rfl⟩ := (sr z).mpr ((Relations.end_colors _ hit).2.trans (f.leftDiag i₀))
      exact Finset.mem_map.mpr ⟨i,(B.cells j).symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩,rfl⟩
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
      rw [B.cells] at hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have data : FourPointInterface.PairColumns (closure G) B.v sl Y B.col :=
    ⟨fun i => (f.leftDiag i).trans (f.leftDiag 0).symm,fun z => (sy z).trans
      (by change (source G z z=f.r) ↔ source G z z=source G (Y 0) (Y 0)
          exact Iff.of_eq (congrArg (source G z z=·) (f.rightDiag 0).symm)),cells⟩
  obtain ⟨degrees,moments⟩ := FourPointInterface.of_coherent data
  rcases shapes B.col degrees with ⟨e,matchShape⟩ | ⟨u,inside,allEdges⟩ | full
  · exact twins_named p reg F T D f g rfl rfl (matching B e matchShape)
  · choose idx hi using inside
    have sur : Function.Surjective idx := by
      intro k
      obtain ⟨j,hj⟩ := allEdges k
      have hcol := FourTwelveTypes.edge_inj (Finset.map_injective u.toEmbedding ((hi j).symm.trans hj))
      exact ⟨j,(show Function.Injective cycle by decide) hcol⟩
    let sl' := u.toEmbedding.trans sl
    have mapped (j) : neighbors (source G) B.v (Y j)=(edge (cycle (idx j))).map sl' := by
      rw [cells,hi,Finset.map_map]
    have range' (z) : z∈Set.range sl' ↔ source G z z=f.l := by
      refine Iff.trans ?_ (sr z)
      exact ⟨fun ⟨i,h⟩ => ⟨u i,h⟩,fun ⟨i,h⟩ => ⟨u.symm i,by simpa [sl'] using h⟩⟩
    have cellName (j i) : source G (Y j) (sl' i)=if i∈edge (cycle (idx j)) then B.v else B.w := by
      have equiv : source G (Y j) (sl' i)=B.v ↔ i∈edge (cycle (idx j)) := by
        have mem : sl' i∈neighbors (source G) B.v (Y j) ↔ i∈edge (cycle (idx j)) := by
          rw [mapped,Finset.mem_map']
        simpa only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and] using mem
      by_cases yes : i∈edge (cycle (idx j))
      · simp [yes,equiv.mpr yes]
      · rw [if_neg yes]
        exact (B.palette j (u i)).resolve_left (equiv.not.mpr yes)
    obtain ⟨e,ll,rl⟩ := cycle_named p B.vw sl' tl Y Z range' tr ns idx sur mapped cellName
    let left := u.symm.trans e
    have internal (i j) : source G (sl i) (sl j)=targetName p (tl (left i)) (tl (left j)) := by
      simpa [sl',left] using ll (u.symm i) (u.symm j)
    have cross (j i) : source G (Y j) (sl i)=targetName p (Z j) (tl (left i)) := by
      simpa [sl',left] using rl j (u.symm i)
    refine ⟨f.points.symm.trans ((Equiv.sumCongr left (Equiv.refl R)).trans g.points),?_⟩
    intro i j
    obtain ⟨i,rfl⟩ := f.points.surjective i
    obtain ⟨j,rfl⟩ := f.points.surjective j
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    cases i with
    | inl i => cases j with | inl j => exact internal i j | inr j => exact common_transpose p (cross j i)
    | inr i => cases j with | inl j => exact cross i j | inr j => exact ns i j
  · obtain ⟨b,hb,gram⟩ := transport p sl tl Y Z sr tr ns B.col cells
    have eq (k : Edge) : mult B.col k=mult B.col (B.col 0) := by
      obtain ⟨j,rfl⟩ := full k
      exact FourPointInterface.equal_multiplicities B.col degrees moments j 0
    have total : ∑ e, mult B.col e=12 := by
      simpa [mult] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset R) (Finset.univ : Finset Edge) B.col
    simp only [eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
    have twice (k) : mult B.col k=2 := (eq k).trans (by omega)
    have bt := transfer_twice B.col b full twice (fun i j => by rw [←edge_overlap,←edge_overlap,gram])
    exact doubled p sf tf f g rfl rfl tr tz B.v b hb bt

theorem realize (p : PerfectStrategy G H K) (reg : Nat → Prop)
    (active : ∀ i, reg (source G i i) → large G (source G i i))
    (size : (vertices (source G) reg).card=16)
    (four : ∃ i, reg (source G i i) ∧ (fiber G i).card=4)
    (twelve : ∃ i, reg (source G i i) ∧ (fiber G i).card=12) : SmallFiberExtension.Realizes p reg := by
  apply LargeOrderBlocks.of_solver p reg active size
  intro F T D
  obtain ⟨u,hu,su⟩ := four
  obtain ⟨v,hv,sv⟩ := twelve
  obtain ⟨i,rfl⟩ := (D.src _).mpr hu
  obtain ⟨j,rfl⟩ := (D.src _).mpr hv
  exact solve p reg F T D ((LargeOrderBlocks.fiber_card F D.injF D.src i).trans su)
    ((LargeOrderBlocks.fiber_card F D.injF D.src j).trans sv)

theorem isomorphic {xs : List Nat} (P : CoprimeProfiles.Profile G xs)
    (total : (xs.filter (fun k => 3<k)).sum=16) (four : 4∈xs) (twelve : 12∈xs)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  obtain ⟨x,hx⟩ := P.fiber_of_mem four (by decide)
  obtain ⟨y,hy⟩ := P.fiber_of_mem twelve (by decide)
  have region := realize p (large G) (fun _ h => h) ((card_core P).trans total)
    ⟨x,(LargeOrderBlocks.large_iff _).mpr (by rw [hx]),hx⟩
    ⟨y,(LargeOrderBlocks.large_iff _).mpr (by rw [hy]; decide),hy⟩
  obtain ⟨e,he⟩ := SmallFiberExtension.of_large_region p region
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩

end QGI.Coherent.RegionalFourTwelve
