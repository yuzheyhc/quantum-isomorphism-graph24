import SevenSevenPair
import SevenSevenFano
import SixSixRegion

noncomputable section
namespace QGI.Coherent.SevenSevenRegion
open SevenSevenCatalog SevenSevenPair
open SixTenCoordinates (Shore atPoint)
open FourTwelveFunctional (source)
open SmallUnion SmallFiberExtension StrategyColorLaws
open private uniform_merge bundle convert_real from SmallFiberExtension
open SixSixCycle (point size)
variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

private theorem pair {a b} (A : Shore (source G) a V) (B : Shore (source G) b V) (ab : a≠b) :
    Realizes p (fun t => t=a ∨ t=b) := by
  apply LargeOrderBlocks.fourteen
  · intro i hi
    rcases hi with h|h
    · rw [h]; change 3 < (vertices (source G) (fun t => t=a)).card; rw [size A]; decide
    · rw [h]; change 3 < (vertices (source G) (fun t => t=b)).card; rw [size B]; decide
  · exact SevenSevenPair.pair_card ab A B

private theorem reversed {a b} (A : Shore (source G) a V) (B : Shore (source G) b V)
    (h : Uniform (cells A B)) : Uniform (cells B A) :=
  fun i j => Relations.transpose (closure G) (h j i)

private theorem attach {a b s} (A : Shore (source G) a V) (B : Shore (source G) b V)
    (Y : Shore (source G) s V) (ab : a≠b)
    (left : Uniform (cells A Y)) (right : Uniform (cells B Y)) :
    Realizes p (fun t => (t=a ∨ t=b) ∨ t=s) := by
  let old := fun t => t=a ∨ t=b
  obtain ⟨e,he⟩ := pair p A B ab
  obtain ⟨q,hq⟩ := LargeOrderBlocks.small p (fun t => t=s) (by rw [size Y]; decide)
  obtain ⟨f,hf,_⟩ := uniform_merge p old s e he q hq (by
    intro i j x y oi sj xi sy
    obtain ⟨j,rfl⟩ := point Y sj
    obtain ⟨y,rfl⟩ := point Y sy
    rcases oi with hi|hi
    · obtain ⟨x,rfl⟩ := point A (xi.trans hi)
      obtain ⟨i,rfl⟩ := point A hi
      exact (left i j).trans (left x y).symm
    · obtain ⟨x,rfl⟩ := point B (xi.trans hi)
      obtain ⟨i,rfl⟩ := point B hi
      exact (right i j).trans (right x y).symm)
  obtain ⟨g,hg⟩ := bundle p _ f hf
  exact ⟨g,fun i j => (hf i j).trans (congrArg₂ (targetName p) (hg i).symm (hg j).symm)⟩

private theorem path {a b s} (A : Shore (source G) a V) (B : Shore (source G) b V)
    (Y : Shore (source G) s V) (ab : a≠b) (as' : a≠s) (bs : b≠s)
    (first : ¬Uniform (cells A B)) (second : ¬Uniform (cells B Y)) :
    Realizes p (fun t => (t=a ∨ t=b) ∨ t=s) := by
  rcases (classify ab A B).resolve_left first with thin|left
  · exact convert_real p (fun _ => by tauto)
      (SixSixRegion.thin_extend p (fun t => t=a ∨ t=s) (Or.inl rfl) A B thin (pair p A Y as'))
  rcases (classify bs B Y).resolve_left second with thin|right
  · exact SixSixRegion.thin_extend p (fun t => t=a ∨ t=b) (Or.inr rfl) B Y thin (pair p A B ab)
  rcases classify as' A Y with outer|thin|outer
  · exact (SevenSevenFano.no_chain (SixTenCoordinates.sourceLaws (closure G)) A B Y left right (Or.inl outer)).elim
  · exact SixSixRegion.thin_extend p (fun t => t=a ∨ t=b) (Or.inl rfl) A Y thin (pair p A B ab)
  · exact (SevenSevenFano.no_chain (SixTenCoordinates.sourceLaws (closure G)) A B Y left right (Or.inr outer)).elim

theorem realize {a b s} (A : Shore (source G) a V) (B : Shore (source G) b V)
    (Y : Shore (source G) s V) (ab : a≠b) (as' : a≠s) (bs : b≠s) :
    Realizes p (fun t => (t=a ∨ t=b) ∨ t=s) := by
  classical
  by_cases ay : Uniform (cells A Y)
  · by_cases by' : Uniform (cells B Y)
    · exact attach p A B Y ab ay by'
    by_cases ba : Uniform (cells B A)
    · exact convert_real p (fun _ => by tauto) (attach p B Y A bs ba (reversed A Y ay))
    · exact path p A B Y ab as' bs (fun h => ba (reversed A B h)) by'
  · by_cases ba : Uniform (cells B A)
    · by_cases by' : Uniform (cells B Y)
      · exact convert_real p (fun _ => by tauto) (attach p A Y B as' (reversed B A ba) (reversed B Y by'))
      · exact convert_real p (fun _ => by tauto) (path p A Y B as' ab bs.symm ay (fun h => by' (reversed Y B h)))
    · exact convert_real p (fun _ => by tauto) (path p B A Y ab.symm bs as' ba ay)

/-- A named region consisting of twenty-one vertices in seven-point fibers. -/
theorem realize_of_size (reg : Nat → Prop) (total : (vertices (source G) reg).card=21)
    (seven : ∀ t, reg t → (vertices (source G) (fun w => w=t)).card=7) : Realizes p reg := by
  classical
  let c := source G
  let d := fun i : Fin n => c i i
  let names := (vertices c reg).image d
  have mem (v : Nat) : v∈names ↔ reg v := by
    constructor
    · rintro hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_vertices _ _ _).mp hi
    · intro hv
      have pos : 0 < (vertices c (fun w => w=v)).card := by rw [seven v hv]; decide
      obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
      have eq := (mem_vertices _ _ _).mp hi
      exact Finset.mem_image.mpr ⟨i,(mem_vertices _ _ _).mpr (eq ▸ hv),eq⟩
  have bound := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) names d
  have sevenAt (v) (hv : v∈names) : (Finset.univ.filter (fun i => d i=v)).card=7 := by
    have eq : Finset.univ.filter (fun i => d i=v) = vertices c (fun w => w=v) := by
      ext i; simp [d]
    rw [eq]; exact seven v ((mem v).mp hv)
  have all : (Finset.univ.filter (fun i => d i∈names)) = vertices c reg := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_vertices,mem,d]
  rw [all,total,Finset.sum_congr rfl sevenAt] at bound
  simp only [Finset.sum_const,smul_eq_mul] at bound
  have sz : names.card=3 := by omega
  obtain ⟨a,b,s,ab,as',bs,namesEq⟩ := Finset.card_eq_three.mp sz
  have within (w : Nat) : ((w=a ∨ w=b) ∨ w=s) ↔ reg w := by
    rw [←mem,namesEq]; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  have frame (v) (hv : reg v) : Nonempty (Shore c v V) := by
    let m := Fintype.equivOfCardEq (show Fintype.card V=Fintype.card (Region c (fun w => w=v)) by
      rw [Fintype.card_fin,Fintype.card_coe,seven v hv])
    exact ⟨m.trans (Equiv.subtypeEquivRight (fun i => mem_vertices c (fun t => t=v) i))⟩
  obtain ⟨A⟩ := frame a ((within _).mp (Or.inl (Or.inl rfl)))
  obtain ⟨B⟩ := frame b ((within _).mp (Or.inl (Or.inr rfl)))
  obtain ⟨Y⟩ := frame s ((within _).mp (Or.inr rfl))
  exact convert_real p within (realize p A B Y ab as' bs)

open LargeFourteenRegion CoprimeProfiles
open private card_core from LargeFourteenRegion

/-- Any ambient order with exactly three seven-point fibers after removing
all fibers of size at most three. This includes the profile [7,7,7] at order twenty-one. -/
theorem isomorphic {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (shape : xs.filter (fun k => 3<k)=[7,7,7]) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,gn,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gn
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  have total : (vertices (source G) (large G)).card=21 := by rw [card_core P,shape]; decide
  have seven (v : Nat) (hv : large G v) : (vertices (source G) (fun w => w=v)).card=7 := by
    have pos : 0 < (vertices (source G) (fun w => w=v)).card := (by decide : 0<3).trans hv
    obtain ⟨i,hi⟩ := Finset.card_pos.mp pos
    have eq := (mem_vertices _ _ _).mp hi
    have same : vertices (source G) (fun w => w=v)=fiber G i := by
      ext j; simp only [mem_vertices,FourTwelveFunctional.fiber_eq,eq]
    have occurs : (fiber G i).card ∈ xs := by rw [P.fiber_size]; exact List.getElem_mem _
    have big : 3<(fiber G i).card := (LargeOrderBlocks.large_iff _).mp (eq ▸ hv)
    have mem : (fiber G i).card ∈ xs.filter (fun k => 3<k) := List.mem_filter.mpr ⟨occurs,decide_eq_true big⟩
    rw [same]
    simpa only [shape,List.mem_cons,List.not_mem_nil,or_false,or_self] using mem
  obtain ⟨e,he⟩ := of_large_region p (realize_of_size p (large G) total seven)
  exact ⟨⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩⟩


end QGI.Coherent.SevenSevenRegion


