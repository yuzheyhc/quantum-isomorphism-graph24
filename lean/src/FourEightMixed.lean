import FourCycleVectors
import ThreeFiberCoordinates

noncomputable section
namespace QGI.Coherent.FourEightMixed
open Relations StrategyColorLaws SixTenCoordinates FourEightGeometry FourTwelveCycle

abbrev Four := Fin 4
abbrev Eight := Fin 8

/-- Complete column patterns in a nonuniform coherent four-by-four
rectangle have multiplicity at most two. -/
theorem small_patterns {n} {c : Fin n → Fin n → Nat} (law : Laws c c) {l r : Nat}
    (F : Shore c l Four) (S : Shore c r Four)
    (mixed : ∃ i j, c (atPoint F i) (atPoint S j) ≠ c (atPoint F 0) (atPoint S 0)) :
    ∀ j : Four, ∃ a b : Four, ∀ k, (∀ i, c (atPoint F i) (atPoint S k) =
      c (atPoint F i) (atPoint S j)) → k=a ∨ k=b := by
  classical
  let M := fun i j => c (atPoint F i) (atPoint S j)
  let row (v : Nat) (i : Four) := Finset.univ.filter (fun j => M i j=v)
  let col (v : Nat) (j : Four) := Finset.univ.filter (fun i => M i j=v)
  have block (t : Nat) : Block F F S S (fun i j => decide (M i j=t)) (fun i j => decide (M i j=t)) :=
    fun ⦃_ _ _ _⦄ h => congrArg (fun u => decide (u=t)) h
  have rd (t i) : (row t i).card=(row t 0).card := by
    simpa only [row,decide_eq_true_eq] using Block.degree_eq law (block t) i 0
  have cd (t j k) : (col t j).card=(col t k).card := by
    simpa only [col,decide_eq_true_eq] using Block.degree_eq law (Block.flip law (block t)) j k
  obtain ⟨i,j,diff⟩ := mixed
  let v := M 0 0
  let w := M i j
  have ne : w≠v := diff
  have disj : Disjoint (row v 0) (row w 0) := Finset.disjoint_left.mpr
    fun _ a b => ne (((Finset.mem_filter.mp b).2).symm.trans (Finset.mem_filter.mp a).2)
  have lim := Finset.card_le_univ (row v 0 ∪ row w 0)
  rw [Finset.card_union_of_disjoint disj] at lim
  change _ ≤ 4 at lim
  have exist : ∃ t i j, M i j=t ∧ (row t 0).card≤2 := by
    by_cases small : (row v 0).card≤2
    · exact ⟨v,0,0,rfl,small⟩
    · exact ⟨w,i,j,rfl,by omega⟩
  obtain ⟨t,i₀,j₀,hit,short⟩ := exist
  intro j
  have pos : 0 < (col t j₀).card := Finset.card_pos.mpr ⟨i₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩⟩
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (pos.trans_eq (cd t j₀ j))
  obtain ⟨a,b,cover⟩ := DegreeClassRigidity.two_labels (row t k) 0 ((rd _ _).trans_le short)
  exact ⟨a,b,fun i same => cover i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(same k).trans (Finset.mem_filter.mp hk).2⟩)⟩

theorem patterns_at {n} {G : Graph n} {l r v : Nat} (F : Shore (color (closure G)) l Four)
    (S : Shore (color (closure G)) r Four) (Y : Shore (color (closure G)) v Eight)
    (a : Fin n) (cover : color (closure G) a a=l ∨ color (closure G) a a=r ∨ color (closure G) a a=v ∨
      ∀ z, color (closure G) z z=color (closure G) a a → z=a)
    (mixed : ∃ i j, color (closure G) (atPoint F i) (atPoint S j) ≠ color (closure G) (atPoint F 0) (atPoint S 0))
    (u : Nat) (b : Eight → Edge) (cells : ∀ i j, color (closure G) (atPoint F i) (atPoint Y j)=u ↔ i∈edge (b j))
    (C : RepeatedCycle b) :
    ∃ s t : Fin n, ∀ z, color (closure G) a a=color (closure G) z z →
      (∀ i, color (closure G) a (atPoint F i)=color (closure G) z (atPoint F i)) → z=s ∨ z=t := by
  let c := color (closure G)
  have loc {kSize : Nat} {k} (T : Shore c k (Fin kSize)) (z : Fin n) (inside : c z z=k) : ∃ i, atPoint T i=z :=
    ⟨T.symm ⟨z,inside⟩,congrArg Subtype.val (T.apply_symm_apply _)⟩
  rcases cover with ha|ha|ha|ha
  · obtain ⟨i,hi⟩ := loc F a ha
    refine ⟨a,a,fun z _ same => Or.inl ?_⟩
    have eq := (same i).symm
    rw [hi] at eq
    exact Relations.diagonal _ eq
  · obtain ⟨j,hj⟩ := loc S a ha
    obtain ⟨s,t,h⟩ := small_patterns (sourceLaws _) F S mixed j
    refine ⟨atPoint S s,atPoint S t,fun z hz same => ?_⟩
    obtain ⟨k,hk⟩ := loc S z (hz.symm.trans ha)
    have same' (i) := (Relations.transpose (closure G) (same i)).symm
    rcases h k (fun i => by rw [hj,hk]; exact same' i) with h|h
    · exact Or.inl (hk.symm.trans (congrArg (atPoint S) h))
    · exact Or.inr (hk.symm.trans (congrArg (atPoint S) h))
  · obtain ⟨j,hj⟩ := loc Y a ha
    let labels := Finset.univ.filter (fun k => C.label k=C.label j)
    obtain ⟨s,t,short⟩ := DegreeClassRigidity.two_labels labels 0 (le_of_eq (C.twice (C.label j)))
    refine ⟨atPoint Y s,atPoint Y t,fun z hz same => ?_⟩
    obtain ⟨k,hk⟩ := loc Y z (hz.symm.trans ha)
    have eq : edge (b k) = edge (b j) := by
      ext i
      rw [←cells,←cells,hk,hj,Relations.transpose _ (same i)]
    have cycleInj : Function.Injective (fun t : Fin 4 => edge (cycle t)) := by native_decide
    have label := cycleInj (Finset.map_injective _ ((C.edges k).symm.trans (eq.trans (C.edges j))))
    rcases short k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,label⟩) with h|h
    · exact Or.inl (hk.symm.trans (congrArg (atPoint Y) h))
    · exact Or.inr (hk.symm.trans (congrArg (atPoint Y) h))

  · exact ⟨a,a,fun z h _ => Or.inl (ha z h.symm)⟩

private theorem target_patterns {n} {G : Graph n} {l r v : Nat} (F : Shore (color (closure G)) l Four)
    (S : Shore (color (closure G)) r Four) (Y : Shore (color (closure G)) v Eight)
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v ∨
      ∀ z, color (closure G) z z=color (closure G) x x → z=x)
    (mixed : ∃ i j, color (closure G) (atPoint F i) (atPoint S j) ≠ color (closure G) (atPoint F 0) (atPoint S 0))
    (u : Nat) (b : Eight → Edge) (cells : ∀ i j, color (closure G) (atPoint F i) (atPoint Y j)=u ↔ i∈edge (b j))
    (C : RepeatedCycle b) :
    ∀ a : Fin n, ∃ s t : Fin n, ∀ z, color (closure G) a a=color (closure G) z z →
      (∀ i, color (closure G) a (atPoint F i)=color (closure G) z (atPoint F i)) → z=s ∨ z=t := fun a => patterns_at F S Y a (cover a) mixed u b cells C

/-- A doubled four-cycle attached to one four-point fiber forces graph
isomorphism whenever the two four-point fibers interact nonuniformly. -/
theorem isomorphic_with_singletons {n} {G H : Graph n} {l r v : Nat}
    (F : Shore (color (closure G)) l Four) (S : Shore (color (closure G)) r Four)
    (Y : Shore (color (closure G)) v Eight)
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v ∨
      ∀ z, color (closure G) z z=color (closure G) x x → z=x)
    (mixed : ∃ i j, color (closure G) (atPoint F i) (atPoint S j) ≠ color (closure G) (atPoint F 0) (atPoint S 0))
    (u : Nat) (b : Eight → Edge) (cells : ∀ i j, color (closure G) (atPoint F i) (atPoint Y j)=u ↔ i∈edge (b j))
    (C : RepeatedCycle b) (quantum : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,gr,ip,_,⟨p⟩⟩ := quantum.symm
  letI : NormedAddCommGroup K := gr
  letI : InnerProductSpace ℂ K := ip
  let c := color (closure G)
  let d := targetName p
  let tl : Four ↪ Fin n := F.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  have every (t : Four) : ∃ j, C.label j=t := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun j => C.label j=t)).card by rw [C.twice]; decide)
    exact ⟨j,(Finset.mem_filter.mp hj).2⟩
  obtain ⟨j₀,hj₀⟩ := every 0
  let i₀ := C.points 0
  have cell₀ : c (atPoint F i₀) (atPoint Y j₀)=u := (cells _ _).mpr (by
    rw [C.edges,hj₀]; exact Finset.mem_map.mpr ⟨0,by decide,rfl⟩)
  let mark := d (atPoint Y j₀) (tl i₀)
  have marked (i j) : d (atPoint Y j) (tl i)=mark ↔ i∈edge (b j) := by
    rw [←cells,←cell₀]
    exact (target_same p _ _ _ _).trans ⟨Relations.transpose _,Relations.transpose _⟩
  have rowSet (j) : FourTwelveCycle.neighbors d mark (atPoint Y j) = (edge (b j)).map tl := by
    ext z
    constructor
    · intro hz
      have h := (target_same p _ _ _ _).mp (Finset.mem_filter.mp hz).2
      have endz := (end_colors (closure G) h).2.trans (F i₀).property
      let i := F.symm ⟨z,endz⟩
      have loc : tl i=z := congrArg Subtype.val (F.apply_symm_apply _)
      exact Finset.mem_map.mpr ⟨i,(marked i j).mp (loc.symm ▸ (Finset.mem_filter.mp hz).2),loc⟩
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(marked i j).mpr hi⟩
  have cyclePairs : ∀ i : Four, ∃ t : Four, ∀ z, i≠z → z≠t → ∃ k, edge (cycle k)={i,z} := by native_decide
  obtain ⟨m,hm⟩ := SmallUnion.diagonal_names p
  let sl := tl.trans m.symm.toEmbedding
  apply Isomorphic.symm
  apply FourCycleVectors.isomorphic_of_patterns p sl tl mark
  · intro i a ξ h
    have name : color (closure H) (sl i) (sl i) = d (tl i) (tl i) := by
      simpa only [sl,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using hm (sl i)
    have tag := (target_same p _ _ _ _).mp (name.symm.trans (DoubledEdges.diag_of_nonzero p h))
    let e : {z // c z z=l} := ⟨a,tag.symm.trans (F i).property⟩
    exact ⟨F.symm e,congrArg Subtype.val (F.apply_symm_apply e)⟩
  · intro i
    obtain ⟨i,rfl⟩ := C.points.surjective i
    obtain ⟨exc,hs⟩ := cyclePairs i
    refine ⟨C.points exc,fun z h₁ h₂ => ?_⟩
    obtain ⟨z,rfl⟩ := C.points.surjective z
    obtain ⟨k,hk⟩ := hs z (fun eq => h₁ (congrArg C.points eq)) (fun eq => h₂ (congrArg C.points eq))
    obtain ⟨j,hj⟩ := every k
    refine ⟨atPoint Y j,?_⟩
    change FourTwelveCycle.neighbors d mark (atPoint Y j) = _
    simp only [rowSet,C.edges,hj,hk,Finset.map_insert,Finset.map_singleton,Equiv.toEmbedding_apply]
  · intro a
    obtain ⟨s,t,h⟩ := target_patterns F S Y cover mixed u b cells C a
    exact ⟨s,t,fun z hz hp => h z ((target_same p _ _ _ _).mp hz) (fun i => (target_same p _ _ _ _).mp (hp i))⟩

theorem isomorphic {G H : Graph 16} {l r v : Nat}
    (F : Shore (color (closure G)) l Four) (S : Shore (color (closure G)) r Four)
    (Y : Shore (color (closure G)) v Eight)
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v)
    (mixed : ∃ i j, color (closure G) (atPoint F i) (atPoint S j) ≠ color (closure G) (atPoint F 0) (atPoint S 0))
    (u : Nat) (b : Eight → Edge) (cells : ∀ i j, color (closure G) (atPoint F i) (atPoint Y j)=u ↔ i∈edge (b j))
    (C : RepeatedCycle b) (quantum : QuantumIso G H) : Isomorphic G H :=
  isomorphic_with_singletons F S Y (fun x => (cover x).imp_right (Or.imp_right Or.inl)) mixed u b cells C quantum

end QGI.Coherent.FourEightMixed
