import FourSixteenRegion
import RegionalSignatureBound
import LargeOrderEighteen

noncomputable section
namespace QGI.Coherent.FourEighteenRegion
open Relations SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveCycle (Edge edge ends neighbors overlap)
open FourTwelveFunctional (source fiber_eq)
open RegionalCycleExtension (emb range_emb)
open Intertwiner Synchrony
open private shore from RegionalFourFourEight
open private cell from FourSixteenRegion

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

/-- Source rows with four-point neighborhoods that are edges carry a
single transpose name, including in an ambient graph with other fibers. -/
theorem reverse_edges {m l r : Nat} [NeZero m] (F : Shore (source G) l (Fin 4)) (Y : Shore (source G) r (Fin m))
    (v : Nat) (b : Fin m → Edge) (cells : ∀ i j, source G (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) :
    ∃ z, ∀ j, neighbors (source G) z (atPoint Y j)=(edge (b j)).map (emb F) := by
  classical
  let i₀ := (FourTwelveCycle.ends (b 0)).1
  have start : source G (atPoint F i₀) (atPoint Y 0)=v := (cells _ _).mpr (by simp [edge,i₀])
  let z := source G (atPoint Y 0) (atPoint F i₀)
  have flip (i j) : source G (atPoint Y j) (atPoint F i)=z ↔ i∈edge (b j) := by
    rw [←cells,←start]
    exact ⟨Relations.transpose _,Relations.transpose _⟩
  refine ⟨z,fun j => ?_⟩
  ext x
  constructor
  · intro hx
    have h := (Finset.mem_filter.mp hx).2
    have tag := (end_colors (closure G) h).2.trans (F i₀).property
    obtain ⟨i,hi⟩ := (range_emb F x).mpr tag
    have loc : atPoint F i=x := hi
    exact Finset.mem_map.mpr ⟨i,(flip i j).mp (by rw [loc]; exact h),hi⟩
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(flip _ _).mpr hi⟩

theorem extend {l r : Nat} (F : Shore (source G) l (Fin 4)) (Y : Shore (source G) r (Fin 18))
    (old : Realizes p (·=r)) : Realizes p (fun t => t=r ∨ t=l) := by
  rcases FourPointGeneral.interface_all F Y with thin|twin|⟨v,w,pal,b,marks,cycle|full⟩
  · exact FourSixteenRegion.extend_cases p F Y old (Or.inl thin)
  · exact FourSixteenRegion.extend_cases p F Y old (Or.inr (Or.inl twin))
  · exact FourSixteenRegion.extend_cases p F Y old (Or.inr (Or.inr ⟨v,w,pal,b,marks,cycle⟩))
  classical
  let c := source G
  let d := targetName p
  obtain ⟨e,he⟩ := old
  let W := Y.trans (cell c r).symm
  let Z := (W.trans e).toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨m,hm⟩ := diagonal_names p
  let T : Shore d l (Fin 4) := F.trans (Equiv.subtypeEquiv m (fun x => ⟨fun h => (hm x).symm.trans h,fun h => (hm x).trans h⟩))
  obtain ⟨z,rows⟩ := reverse_edges F Y v b marks
  obtain ⟨b',targetRows,gram⟩ := RegionalFourTwelve.transport p (emb F) (emb T) (emb Y) Z (range_emb F) (range_emb T)
    (fun i j => he (W i) (W j)) b rows
  have same (i j) : b i=b j ↔ b' i=b' j := by rw [←FourTwelveTypes.edge_overlap,←FourTwelveTypes.edge_overlap,gram]
  choose rep hrep using full.1
  have inj : Function.Injective (fun a => b' (rep a)) := by
    intro i j eq; simpa only [hrep] using (same _ _).mpr eq
  have onto : Function.Surjective b' := fun a => by
    obtain ⟨q,hq⟩ := (Finite.injective_iff_bijective.mp inj).2 a
    exact ⟨rep q,hq⟩
  have pairs : ∀ i j : Fin 4, i≠j → ∃ e : Edge, edge e={i,j} := by decide
  obtain ⟨ξ,f,nz,fixed⟩ := DoubledEdges.fixed_block p (emb F) (emb T)
    (fun i a ξ h => (range_emb T a).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans (F i).property))
    (fun i j a b => DoubledEdges.pair_commute p z _ _ _ _ (fun ne => by
      obtain ⟨t,ht⟩ := pairs a b (fun eq => ne (congrArg (emb T) eq))
      obtain ⟨j,hj⟩ := onto t
      exact ⟨Z j,by simpa only [hj,ht,Finset.map_insert,Finset.map_singleton] using targetRows j⟩))
  let reg := fun t => t=r ∨ t=l
  apply LargeOrderBlocks.of_solver p reg (fun i hi => by
    rcases hi with hr|hl <;> change 3<(vertices (source G) (·=source G i i)).card
    · rw [hr,RegionalTwoAnchor.card Y]; decide
    · rw [hl,RegionalTwoAnchor.card F]; decide) rfl
  intro a g D
  apply RegionalTernaryChoice.source_pins p D ξ nz (emb F) (fun j => emb T (f j)) fixed
  intro i
  rcases (D.src _).mp ⟨i,rfl⟩ with yr|fl
  · let j := Y.symm ⟨a i,yr⟩
    have loc : atPoint Y j=a i := congrArg Subtype.val (Y.apply_symm_apply _)
    have size : (Finset.univ.filter (fun k => b k=b j)).card≤3 := by
      have := full.2 (b j); change 6*(Finset.univ.filter (fun k => b k=b j)).card=18 at this; omega
    apply (RegionalSignatureBound.bound_set a D.injF (atPoint Y) _ _ ?_).trans size
    intro k h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h
    obtain ⟨t,ht⟩ := (range_emb Y (a k)).mpr (h.1.trans yr)
    refine ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,FourTwelveTypes.edge_inj ?_⟩,ht⟩
    ext q
    rw [←marks,←marks]
    change (source G (atPoint F q) (atPoint Y t)=v ↔ source G (atPoint F q) (atPoint Y j)=v)
    rw [show atPoint Y t=a k from ht,loc]
    exact Iff.of_eq (congrArg (·=v) (Relations.transpose _ (h.2 q)))
  · let j := F.symm ⟨a i,fl⟩
    have loc : emb F j=a i := congrArg Subtype.val (F.apply_symm_apply _)
    refine (Finset.card_le_card (t:=({i} : Finset (Fin _))) ?_).trans (by simp)
    intro k h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h
    have eq := h.2 j
    rw [loc] at eq
    exact Finset.mem_singleton.mpr (D.injF (Relations.diagonal _ eq))

variable [CompleteSpace K]
theorem realize (reg : Nat → Prop) (size : (vertices (source G) reg).card=22)
    (four : ∃ i, reg (source G i i) ∧ (fiber G i).card=4)
    (eighteen : ∃ i, reg (source G i i) ∧ (fiber G i).card=18) : Realizes p reg := by
  classical
  let c := source G
  obtain ⟨a,ha,sa⟩ := four; obtain ⟨b,hb,sb⟩ := eighteen
  obtain ⟨F⟩ := shore a sa; obtain ⟨Y⟩ := shore b sb
  have old := LargeOrderBlocks.of_solver p (·=c b b) (fun i h => by
    change source G i i=source G b b at h; change 3 < (vertices (source G) (·=source G i i)).card
    rw [h,RegionalTwoAnchor.card Y]; decide)
    (RegionalTwoAnchor.card Y) (fun f g D => LargeOrderEighteen.solve p f g D (fun i j =>
      ((D.src _).mp ⟨i,rfl⟩).trans ((D.src _).mp ⟨j,rfl⟩).symm))
  have ne : c b b≠c a a := by
    intro eq
    have same : fiber G b=fiber G a := by ext z; rw [fiber_eq,fiber_eq]; change (c z z=c b b ↔ c z z=c a a); rw [eq]
    have h := congrArg Finset.card same; omega
  let R := fun t => t=c b b ∨ t=c a a
  have all : vertices c R=vertices c reg := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi; apply (mem_vertices _ _ _).mpr
      rcases (mem_vertices _ _ _).mp hi with h|h
      · exact h.symm ▸ hb
      · exact h.symm ▸ ha
    · rw [size,RegionalFourSixEight.pair_card ne Y F]
  apply RegionalFourFourEight.restrict_map p (extend p F Y old)
  intro i hi
  apply (mem_vertices c R i).mp
  rw [all]; exact (mem_vertices _ _ _).mpr hi

end QGI.Coherent.FourEighteenRegion
