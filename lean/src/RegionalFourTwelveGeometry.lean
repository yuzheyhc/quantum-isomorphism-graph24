import RegionalBinaryChoice
import FourPointCycleGlue
import FourPointInterface
import RegionalSixTen

noncomputable section
namespace QGI.Coherent.RegionalFourTwelve
open FourTwelveCycle FourTwelveTypes FourTwelveCycleGraph
open SmallUnion StrategyColorLaws LargeFourteenRegion
open FourTwelveFunctional (source)
open Intertwiner Synchrony
open private shore_range from RegionalSixTen
open private all_pairs from DoubledEdges

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

/-- A double copy of each target edge makes the four-point block commute.
A joint fixed vector then supports at most two target labels per regional row. -/
theorem doubled (F T : Fin 16 ↪ Fin n) (f : Frame (restricted (source G) F)) (g : Frame (restricted (targetName p) T))
    (hl : f.l=g.l) (hr : f.r=g.r)
    (leftRange : ∀ z, (∃ i, T (g.left i)=z) ↔ targetName p z z=g.l)
    (rightRange : ∀ z, (∃ i, T (g.right i)=z) ↔ targetName p z z=g.r)
    (v : Nat) (b : Fin 12 → Edge)
    (cells : ∀ j, neighbors (targetName p) v (T (g.right j))=(edge (b j)).map (g.left.trans T))
    (twice : ∀ e, mult b e=2) :
    ∃ h : Equiv.Perm (Fin 16), ∀ i j, source G (F i) (F j)=targetName p (T (h i)) (T (h j)) := by
  classical
  let sl := f.left.trans F
  let tl := g.left.trans T
  have pairs (a z : Fin 4) (ne : a≠z) : ∃ y, neighbors (targetName p) v y={tl a,tl z} := by
    obtain ⟨e,he⟩ := all_pairs a z ne
    have pos : 0 < (Finset.univ.filter fun j => b j=e).card := (by decide : 0<2).trans_eq (twice e).symm
    obtain ⟨j,hj⟩ := Finset.card_pos.mp pos
    exact ⟨T (g.right j),by simp only [cells,(Finset.mem_filter.mp hj).2,he,Finset.map_insert,Finset.map_singleton,tl]⟩
  obtain ⟨ξ,e,nz,fixed⟩ := DoubledEdges.fixed_block p sl tl (fun i a ξ h =>
    (leftRange a).mpr ((DoubledEdges.diag_of_nonzero p h).symm.trans ((f.leftDiag i).trans hl)))
    (fun i j a z => DoubledEdges.pair_commute p v _ _ _ _ (fun ne => pairs a z (fun eq => ne (congrArg tl eq))))
  have named {x a} (active : U p x a ξ ≠ 0) (i : Fin 4) :
      source G x (sl i)=targetName p a (tl (e i)) := by
    apply (associated p).mpr
    apply StrategyColors.maps_support
    intro zero
    have eq := congrArg (fun z : Module.End ℂ (cyclic p) => z ξ) zero
    change U p x a (U p (sl i) (tl (e i)) ξ)=0 at eq
    exact active ((congrArg (U p x a) (fixed i)).symm.trans eq)
  apply RegionalBinaryChoice.solve p F T F.injective T.injective ξ nz
  intro x
  obtain ⟨x,rfl⟩ := f.points.surjective x
  cases x with
  | inl i =>
    refine ⟨g.left (e i),g.left (e i),fun a act => Or.inl ?_⟩
    by_cases ne : a=tl (e i)
    · exact ne
    have eq := congrArg (fun z : Module.End ℂ (cyclic p) => z ξ)
      (magic_orthogonal p (sl i) a (tl (e i)) ne).1
    change U p (sl i) a (U p (sl i) (tl (e i)) ξ)=0 at eq
    rw [fixed] at eq
    exact False.elim (act eq)
  | inr j =>
    have onRight {a} (act : U p (F (f.right j)) a ξ ≠ 0) : ∃ t, T (g.right t)=a :=
      (rightRange _).mpr ((DoubledEdges.diag_of_nonzero p act).symm.trans ((f.rightDiag j).trans hr))
    obtain ⟨a,ha⟩ := DoubledEdges.nonzero_row p ξ nz (F (f.right j))
    obtain ⟨j₀,rfl⟩ := onRight ha
    obtain ⟨u,w,_,classes⟩ := Finset.card_eq_two.mp (twice (b j₀))
    refine ⟨g.right u,g.right w,?_⟩
    intro z active
    obtain ⟨t,rfl⟩ := onRight active
    have equal (i : Fin 4) : targetName p (T (g.right t)) (tl i)=targetName p (T (g.right j₀)) (tl i) := by
      obtain ⟨i,rfl⟩ := e.surjective i
      exact (named active i).symm.trans (named ha i)
    have member (s : Fin 12) (i : Fin 4) : i ∈ edge (b s) ↔ targetName p (T (g.right s)) (tl i)=v := by
      rw [←Finset.mem_map' tl,←cells]; simp [neighbors]
    have eq : edge (b t)=edge (b j₀) := by ext i; rw [member,member,equal]
    have mem : t ∈ ({u,w} : Finset (Fin 12)) :=
      classes ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,FourTwelveTypes.edge_inj eq⟩
    rcases (Finset.mem_insert.mp mem) with rfl | h
    · exact Or.inl rfl
    · obtain rfl := Finset.mem_singleton.mp h
      exact Or.inr rfl

/-- Transport the size and all pairwise intersection sizes of two-element
neighborhoods along an independently chosen named realization of the twelve points. -/
theorem transport {m l v : Nat} (F T : Fin 4 ↪ Fin n) (Y Z : Fin m ↪ Fin n)
    (sl : ∀ z, z ∈ Set.range F ↔ source G z z=l) (tl : ∀ z, z ∈ Set.range T ↔ targetName p z z=l)
    (rnames : ∀ i j, source G (Y i) (Y j)=targetName p (Z i) (Z j))
    (a : Fin m → Edge) (sc : ∀ j, neighbors (source G) v (Y j)=(edge (a j)).map F) :
    ∃ b : Fin m → Edge, (∀ j, neighbors (targetName p) v (Z j)=(edge (b j)).map T) ∧
      ∀ i j, overlap (a i) (a j)=overlap (b i) (b j) := by
  classical
  let src := fun j => neighbors (source G) v (Y j)
  let dst := fun j => neighbors (targetName p) v (Z j)
  have desc (j : Fin m) : ∃ e : Edge, dst j=(edge e).map T := by
    obtain ⟨q,hq⟩ := (SixTenCoordinates.commonLaws p).middle (rnames j j)
    let S := Finset.univ.filter (fun i => T i ∈ dst j)
    have mapped : S.map T=dst j := by
      ext z
      constructor
      · rintro hz
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
        exact (Finset.mem_filter.mp hi).2
      · intro hz
        obtain ⟨k,rfl⟩ := q.surjective z
        have incl : k ∈ src j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hq k).1.trans (Finset.mem_filter.mp hz).2⟩
        change k ∈ neighbors (source G) v (Y j) at incl
        rw [sc] at incl
        obtain ⟨i,_,hi⟩ := Finset.mem_map.mp incl
        have reg := ((SmallShore.endpoints p (hq k).1).2).symm.trans ((sl k).mp ⟨i,hi⟩)
        obtain ⟨t,ht⟩ := (tl _).mpr reg
        exact Finset.mem_map.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht ▸ hz⟩,ht⟩
    have cs : (src j).card=(dst j).card := by simpa only [Finset.inter_self] using (shared_counts p v (rnames j j)).1
    change (neighbors (source G) v (Y j)).card=_ at cs
    rw [sc,←mapped,Finset.card_map,Finset.card_map] at cs
    have len : ∀ e : Edge, (edge e).card=2 := by decide
    obtain ⟨t,ht⟩ := (show ∀ s : Finset (Fin 4), s.card=2 → ∃ t : Edge, edge t=s by decide) S (cs.symm.trans (len _))
    exact ⟨t,ht.symm ▸ mapped.symm⟩
  choose b hb using desc
  refine ⟨b,hb,fun i j => ?_⟩
  have h : (src i ∩ src j).card=(dst i ∩ dst j).card := (shared_counts p v (rnames i j)).1
  simpa only [src,sc,hb,←Finset.map_inter,Finset.card_map,overlap] using h

/-- A repeated four-cycle, with the original right-shore identification
fixed. The point map on the four vertices preserves every internal and cross name. -/
theorem cycle_named {m l v w : Nat} (vw : v≠w) (F T : Fin 4 ↪ Fin n) (Y Z : Fin m ↪ Fin n)
    (sl : ∀ z, z ∈ Set.range F ↔ source G z z=l) (tl : ∀ z, z ∈ Set.range T ↔ targetName p z z=l)
    (same : ∀ i j, source G (Y i) (Y j)=targetName p (Z i) (Z j))
    (a : Fin m → Fin 4) (full : Function.Surjective a)
    (rows : ∀ j, neighbors (source G) v (Y j)=(edge (cycle (a j))).map F)
    (names : ∀ j i, source G (Y j) (F i)=if i∈edge (cycle (a j)) then v else w) :
    ∃ e : Equiv.Perm (Fin 4), (∀ i j, source G (F i) (F j)=targetName p (T (e i)) (T (e j))) ∧
      ∀ j i, source G (Y j) (F i)=targetName p (Z j) (T (e i)) := by
  classical
  choose rep hr using full
  have S : FourPointCycleGlue.Frame (source G) F (fun k => Y (rep k)) v w :=
    ⟨fun k => by simpa only [hr] using rows (rep k),fun k i => by simpa only [hr] using names (rep k) i⟩
  obtain ⟨e,P⟩ := FourPointCycleGlue.align_frame p S sl tl (fun i j => same (rep i) (rep j))
  let T' := e.toEmbedding.trans T
  have diag (i j : Fin 4) : source G (F i) (F i)=targetName p (T' j) (T' j) :=
    ((sl _).mp ⟨i,rfl⟩).trans ((tl _).mp ⟨e j,rfl⟩).symm
  refine ⟨e,fun i j => FourPointCycleGlue.internal_names S P (Relations.products (closure G))
    (fun u v _ _ _ _ h => common_products p u v h) diag (i:=i) (j:=j) rfl,?_⟩
  intro j i
  let s := source G (Y j) (F i)
  let subset := FourPointCycleGlue.sectionAt (source G) F s (Y j)
  have safe : ¬FourPointCycleGlue.ambiguous subset := by
    have forms : subset = (if v=s then edge (cycle (a j)) else (edge (cycle (a j)))ᶜ) := by
      ext k
      have sv : s=v ∨ s=w := by simp only [s,names]; split <;> simp
      rcases sv with sv|sw
      · by_cases h : k∈edge (cycle (a j)) <;> simp [subset,FourPointCycleGlue.sectionAt,names,sv,vw,Ne.symm vw,h]
      · by_cases h : k∈edge (cycle (a j)) <;> simp [subset,FourPointCycleGlue.sectionAt,names,sw,vw,Ne.symm vw,h]
    have allowed : ∀ k : Fin 4, ¬FourPointCycleGlue.ambiguous (edge (cycle k)) ∧
        ¬FourPointCycleGlue.ambiguous (edge (cycle k))ᶜ := by unfold FourPointCycleGlue.ambiguous; decide
    rw [forms]
    split
    · exact (allowed _).1
    · exact (allowed _).2
  have h := FourPointCycleGlue.recover_section p S P s (fun k => same (rep k) j) safe
  have incl : i∈FourPointCycleGlue.sectionAt (targetName p) T' s (Z j) := h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  exact (Finset.mem_filter.mp incl).2.symm

end QGI.Coherent.RegionalFourTwelve
