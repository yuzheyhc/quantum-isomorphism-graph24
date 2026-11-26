import SeventeenComponents
import RegionalPlanar
import FourAnchorTetra

noncomputable section

namespace QGI.Literature
open Coherent.SmallUnion Coherent.StrategyColorLaws

/-- Fuhlbrück, Köbler and Verbitsky, Theorem 11.1(2) and Figure 17,
arXiv:1907.02892, pp. 62–64. Their classification applies to arbitrary
coherent configurations. The unique nonseparable sixteen-point type
of maximum fiber size four has four F₄ cells, in each of which the
colors in any one row are pairwise distinct (Figure 1 and Lemma 5.2).
Corollary 4.9 covers configurations with maximum fiber size at most three.
This is the configuration-table version of `fkv_sixteen_small_cells`. -/
axiom fkv_sixteen_small_configuration {c d : Table 16}
    (src : Configuration c) (tgt : Configuration d)
    (small : ∀ i, (Finset.univ.filter (fun j => c j j = c i i)).card ≤ 4)
    (used : ∀ a, (∃ i j, c i j=a) ↔ ∃ i j, d i j=a)
    (numbers : ∀ a b i j x y, c i j=d x y → count c a b i j = count d a b x y) :
    (∃ e : Equiv.Perm (Fin 16), ∀ i j, c i j=d (e i) (e j)) ∨
    ∀ i j k, c j j = c i i → c k k = c i i → c i j = c i k → j=k

end QGI.Literature

namespace QGI.Coherent.SeventeenHard
open Certificate StrategyColorLaws
open FourTwelveFunctional (source)
open private matrix entry names sixEdges positive_iff from FourAnchorTetra

private theorem tetra {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (p : PerfectStrategy G H K)
    (region : Nat → Prop) (f g : Fin 16 → Fin n) (hf : Function.Injective f) (hg : Function.Injective g)
    (sf : ∀ z, (∃ i, f i=z) ↔ region (source G z z))
    (sg : ∀ z, (∃ i, g i=z) ↔ region (targetName p z z)) (u : Fin 4 → Fin 16) :
    ∃ v : Fin 4 → Fin 16, ∀ i j,
      source G (f (u i)) (f (u j)) = targetName p (g (v i)) (g (v j)) := by
  let c := SmallShore.restrict (source G) f
  let d := SmallShore.restrict (targetName p) g
  have tr := RegionalPlanar.homCount_region p (by decide : 0 < 16) region f g hf hg sf sg
    (matrix c) (matrix d) rfl rfl .tetra (drawing_of_tetraPrism (by decide))
    (names c u) rfl id (fun i j a b hit s _ => by
      rw [entry,entry]; exact congrArg (fun z => z=s) hit |> Iff.of_eq)
  rw [homCount_eq_binaryCspCount,homCount_eq_binaryCspCount,List.map_id_fun] at tr
  have pos := (positive_iff c c u).mpr ⟨u 0,u 1,u 2,u 3,by simp [sixEdges]⟩
  rw [tr] at pos
  obtain ⟨a,b,e,t,h01,h02,h03,h12,h13,h23⟩ := (positive_iff c d u).mp pos
  let v : Fin 4 → Fin 16 := ![a,b,e,t]
  have pair (i j : Fin 4) (lt : i < j) : c (u i) (u j) = d (v i) (v j) := by
    fin_cases i <;> fin_cases j <;> first
      | exact h01.symm | exact h02.symm | exact h03.symm
      | exact h12.symm | exact h13.symm | exact h23.symm
      | exfalso; norm_num [Fin.lt_def] at lt
  refine ⟨v,fun i j => ?_⟩
  rcases lt_trichotomy i j with lt | rfl | gt
  · exact pair i j lt
  · by_cases lt : i < 3
    · exact (SmallShore.endpoints p (pair i 3 lt)).1
    · exact (SmallShore.endpoints p (pair 0 i (by omega))).2
  · exact common_transpose p (pair j i gt)

open private root_unique from SingletonSwitch

/-- The one-point fiber is kept throughout the planar argument. On the
sixteen other points FKV either realizes all colors, or supplies four
thin cells whose anchors synchronize on the colored tetrahedron. -/
theorem four_fours {G H : Graph 17} (P : CoprimeProfiles.Profile G [1,4,4,4,4])
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,ng,ip,complete,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := complete
  have pos : ∀ i : Fin 5, 0 < ([1,4,4,4,4] : List Nat)[i.val] := by decide
  choose rep repTag using fun i : Fin 5 => P.occurs i (pos i)
  let x := rep 0
  let root := source G x x
  have one : (fiber G x).card=1 := by rw [P.fiber_size,show P.tag x=(0 : Fin 5) from repTag 0]; rfl
  have unique (z : Fin 17) (eq : source G z z=root) : z=x := root_unique x one z eq
  obtain ⟨m,hm⟩ := SmallUnion.diagonal_names p
  let f : Fin 16 → Fin 17 := x.succAbove
  let g := fun i => m (f i)
  have hf : Function.Injective f := Fin.succAbove_right_injective
  have hg : Function.Injective g := m.injective.comp hf
  let region := fun t : Nat => t ≠ root
  have sf (z) : (∃ i, f i=z) ↔ region (source G z z) := by
    change (∃ i, x.succAbove i=z) ↔ source G z z ≠ root
    rw [Fin.exists_succAbove_eq_iff]
    exact ⟨fun ne eq => ne (unique z eq),fun ne eq => ne (eq ▸ rfl)⟩
  have sg (z) : (∃ i, g i=z) ↔ region (targetName p z z) := by
    obtain ⟨z,rfl⟩ := m.surjective z
    simpa only [g,Equiv.apply_eq_iff_eq,←hm] using sf z
  let c := SmallShore.restrict (source G) f
  let d := SmallShore.restrict (targetName p) g
  obtain ⟨cc,dd,used,num⟩ := SmallUnion.correspondence p region f g hf hg sf sg
  have small (i : Fin 16) : (Finset.univ.filter (fun j => c j j = c i i)).card ≤ 4 := by
    have bound : ∀ i : Fin 5, ([1,4,4,4,4] : List Nat)[i.val] ≤ 4 := by decide
    apply le_trans _ (show (fiber G (f i)).card ≤ 4 by rw [P.fiber_size]; exact bound _)
    apply Finset.card_le_card_of_injOn f _ hf.injOn
    intro z hz
    exact (FourTwelveFunctional.fiber_eq _ _).mpr (Finset.mem_filter.mp hz).2
  have extend {I : Type} [Nonempty I] (a b : I → Fin 16)
      (pairs : ∀ i j, c (a i) (a j) = d (b i) (b j))
      (covered : ∀ j, ∃ i, ∀ k, c (a i) k = c (a i) j → k=j) : Isomorphic G H := by
    obtain ⟨e,he⟩ := FourTwelveFunctional.extend p (f ∘ a) (g ∘ b) pairs (by
      intro z
      by_cases rz : source G z z=root
      · exact ⟨Classical.ofNonempty,fun w h =>
          (unique w ((Relations.end_colors (closure G) h).2.trans rz)).trans (unique z rz).symm⟩
      · obtain ⟨j,rfl⟩ := (sf z).mpr rz
        obtain ⟨i,h⟩ := covered j
        refine ⟨i,fun w eq => ?_⟩
        obtain ⟨k,rfl⟩ := (sf w).mpr (fun hit => rz ((Relations.end_colors (closure G) eq).2.symm.trans hit))
        exact congrArg f (h k eq))
    exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩
  rcases Literature.fkv_sixteen_small_configuration cc dd small used num with ⟨e,he⟩ | thin
  · exact extend id e he (fun j => ⟨j,fun k eq => hf ((Relations.diagonal (closure G) eq).symm)⟩)
  · have away (i : Fin 4) : rep i.succ ≠ x := by
      intro h
      have tag := congrArg P.tag h
      rw [repTag,show P.tag x=(0 : Fin 5) from repTag 0] at tag
      exact Fin.succ_ne_zero _ tag
    choose u hu using fun i : Fin 4 => Fin.exists_succAbove_eq (away i)
    obtain ⟨v,hv⟩ := tetra p region f g hf hg sf sg u
    apply extend u v hv
    intro j
    have tag : P.tag (f j) ≠ (0 : Fin 5) := fun zero =>
      Fin.succAbove_ne x j (unique _ ((P.same _ _).mp (zero.trans (repTag 0).symm)))
    obtain ⟨i,hi⟩ : ∃ i : Fin 4, i.succ=P.tag (f j) := by
      simpa only [Fin.succAbove_zero] using Fin.exists_succAbove_eq tag
    have name : c j j = c (u i) (u i) := by
      change source G (f j) (f j)=source G (x.succAbove (u i)) (x.succAbove (u i))
      rw [hu]
      exact (P.same _ _).mp (hi.symm.trans (repTag _).symm)
    refine ⟨i,fun k eq => thin (u i) k j ?_ name eq⟩
    exact ((Relations.end_colors (closure G) eq).2).trans name

end QGI.Coherent.SeventeenHard
