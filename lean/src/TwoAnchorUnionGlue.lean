import SmallUnionRealization
import SixTenCoordinates

noncomputable section
namespace QGI.Coherent.TwoAnchorUnionGlue
open Relations StrategyColorLaws SixTenCoordinates

abbrev V := Fin 16
abbrev Region {n} (c : Fin n → Fin n → Nat) (keep : Nat → Prop) := {x // x∈SmallUnion.vertices c keep}

private def narrow {n} {c d : Fin n → Fin n → Nat} {keep : Nat → Prop}
    (e : Region c keep ≃ Region d keep) (he : ∀ i j, c i.val j.val=d (e i).val (e j).val)
    {v : Nat} (hv : keep v) : {x // c x x=v} ≃ {x // d x x=v} where
  toFun x := by
    let i : Region c keep := ⟨x.val,(SmallUnion.mem_vertices _ _ _).mpr (x.property.symm ▸ hv)⟩
    exact ⟨(e i).val,(he i i).symm.trans x.property⟩
  invFun x := by
    let j : Region d keep := ⟨x.val,(SmallUnion.mem_vertices _ _ _).mpr (x.property.symm ▸ hv)⟩
    refine ⟨(e.symm j).val,?_⟩
    have eq := he (e.symm j) (e.symm j)
    rw [Equiv.apply_symm_apply] at eq
    exact eq.trans x.property
  left_inv x := Subtype.ext (congrArg (fun z : Region c keep => z.val)
    (e.symm_apply_apply ⟨x.val,(SmallUnion.mem_vertices _ _ _).mpr (x.property.symm ▸ hv)⟩))
  right_inv x := Subtype.ext (congrArg (fun z : Region d keep => z.val)
    (e.apply_symm_apply ⟨x.val,(SmallUnion.mem_vertices _ _ _).mpr (x.property.symm ▸ hv)⟩))

/-- Two points form a base of the permutation group preserving all named
relations induced on the overlap. -/
def TwoBase (M : Fin 8 → Fin 8 → Nat) : Prop :=
  ∃ i j, ∀ σ : Equiv.Perm (Fin 8), σ i=i → σ j=j → (∀ x y, M x y=M (σ x) (σ y)) → ∀ x, σ x=x

theorem isomorphic_with_singletons {n} {G H : Graph n} (lo : 5≤n) (hi : n≤17) {l r v : Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (F : Shore (color (closure G)) l (Fin 4)) (S : Shore (color (closure G)) r (Fin 4))
    (Y : Shore (color (closure G)) v (Fin 8))
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v ∨
      ∀ y, color (closure G) y y=color (closure G) x x → y=x)
    (uniform : ∀ i j, color (closure G) (atPoint F i) (atPoint S j) =
      color (closure G) (atPoint F 0) (atPoint S 0))
    (base : TwoBase (fun i j => color (closure G) (atPoint Y i) (atPoint Y j))) (q : QuantumIso G H) :
    Isomorphic G H := by
  classical
  obtain ⟨K,gr,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := gr
  letI : InnerProductSpace ℂ K := ip
  let c := color (closure G)
  let d := targetName p
  let ka (n : Nat) := n≠r
  let kb (n : Nat) := n≠l
  have num {z} (T : Shore c z (Fin 4)) :
      (SmallUnion.vertices c (fun t => t≠z)).card=n-4 := by
    let f := Equiv.subtypeEquivRight (p := fun i => i ∈ SmallUnion.vertices c (fun t => t=z))
      (q := fun i => c i i=z) (fun i => SmallUnion.mem_vertices _ _ i)
    have size : (SmallUnion.vertices c (fun t => t=z)).card=4 := by
      simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_congr (f.trans T.symm)
    have eq : SmallUnion.vertices c (fun t => t≠z)=(SmallUnion.vertices c (fun t => t=z))ᶜ := by
      ext i; simp only [SmallUnion.mem_vertices,Finset.mem_compl]
    rw [eq,Finset.card_compl,size,Fintype.card_fin]
  have sa : (SmallUnion.vertices c ka).card=n-4 := num S
  have sb : (SmallUnion.vertices c kb).card=n-4 := num F
  obtain ⟨e,he⟩ := SmallUnion.realize_region p ka (by change 0 < (SmallUnion.vertices c ka).card; omega) (by change (SmallUnion.vertices c ka).card ≤ 13; omega)
  let L (x : Fin n) (h : ka (c x x)) : Region c ka := ⟨x,(SmallUnion.mem_vertices _ _ _).mpr h⟩
  let R (x : Fin n) (h : kb (c x x)) : Region c kb := ⟨x,(SmallUnion.mem_vertices _ _ _).mpr h⟩
  have onL (x y : Fin n) (hx : ka (c x x)) (hy : ka (c y y)) :
      c x y=d (e (L x hx)).val (e (L y hy)).val := he (L x hx) (L y hy)
  let A := Y.trans (narrow e he (show ka v from Ne.symm rv))
  let sx (i) := R (atPoint Y i) (fun bad => lv (bad.symm.trans (Y i).property))
  let tx (i) : Region d kb := ⟨(A i).val,(SmallUnion.mem_vertices _ _ _).mpr (fun bad => lv (bad.symm.trans (A i).property))⟩
  obtain ⟨i,j,rigid⟩ := base
  have namedA (i j) : c (atPoint Y i) (atPoint Y j)=d (A i).val (A j).val :=
    he (L _ (fun bad => rv (bad.symm.trans (Y i).property))) (L _ (fun bad => rv (bad.symm.trans (Y j).property)))
  obtain ⟨f,fi,fj,hf⟩ := SmallUnion.realize_region_pair p kb (by change 0 < (SmallUnion.vertices c kb).card; omega) (by change (SmallUnion.vertices c kb).card ≤ 13; omega)
    (sx i) (sx j) (tx i) (tx j) (namedA i j)
  have onR (x y : Fin n) (hx : kb (c x x)) (hy : kb (c y y)) :
      c x y=d (f (R x hx)).val (f (R y hy)).val := hf (R x hx) (R y hy)
  let B := Y.trans (narrow f hf (show kb v from Ne.symm lv))
  let σ := A.trans B.symm
  have namedB (i j) : c (atPoint Y i) (atPoint Y j)=d (B i).val (B j).val := hf (sx i) (sx j)
  have fix (k) (hk : f (sx k)=tx k) : σ k=k :=
    B.injective (by rw [show B (σ k)=A k from B.apply_symm_apply _]; exact Subtype.ext (congrArg Subtype.val hk).symm)
  have all := rigid σ (fix i fi) (fix j fj) (fun x y => (namedA x y).trans (by
    have shift (z) : B (σ z)=A z := B.apply_symm_apply _
    simpa only [shift] using (namedB (σ x) (σ y)).symm))
  have agreeY (k : Fin 8) :
      (e (L (atPoint Y k) (fun eq => rv (eq.symm.trans (Y k).property)))).val =
      (f (R (atPoint Y k) (fun eq => lv (eq.symm.trans (Y k).property)))).val :=
    congrArg Subtype.val ((B.apply_symm_apply (A k)).symm.trans (congrArg B (all k)))
  have agreement (x : Fin n) (name : c x x=v) :
      (e (L x (fun eq => rv (eq.symm.trans name)))).val=(f (R x (fun eq => lv (eq.symm.trans name)))).val := by
    simpa only [atPoint,Equiv.apply_symm_apply] using agreeY (Y.symm ⟨x,name⟩)
  let point (x : Fin n) := if h : c x x=r then (f (R x (fun bad => lr (bad.symm.trans h)))).val
    else (e (L x h)).val
  have useA (x) (inside : ka (c x x)) : point x=(e (L x inside)).val := dif_neg inside
  obtain ⟨m,hm⟩ := SmallUnion.diagonal_names p
  have useB (x) (inside : kb (c x x)) : point x=(f (R x inside)).val := by
    rcases cover x with h|h|h|h
    · exact (inside h).elim
    · exact dif_pos h
    · rw [useA x (fun eq => rv (eq.symm.trans h))]; exact agreement x h
    · by_cases hr : c x x=r
      · exact dif_pos hr
      rw [useA x hr]
      let u := (e (L x hr)).val
      let t := (f (R x inside)).val
      have unique (w : Fin n) (hw : c x x=d w w) : m x=w := by
        obtain ⟨y,rfl⟩ := m.surjective w
        exact congrArg m (h y ((hm y).trans hw.symm)).symm
      exact (unique u (onL x x hr hr)).symm.trans (unique t (onR x x inside inside))
  have diagonalName (x) : c x x=d (point x) (point x) := by
    by_cases h : c x x=r
    · have k : kb (c x x) := fun bad => lr (bad.symm.trans h)
      rw [useB x k]; exact onR x x k k
    · rw [useA x h]; exact onL x x h h
  have srcCross (x y : Fin n) (hx : c x x=l) (hy : c y y=r) :
      c x y=c (atPoint F 0) (atPoint S 0) := by
    simpa only [atPoint,Equiv.apply_symm_apply] using uniform (F.symm ⟨x,hx⟩) (S.symm ⟨y,hy⟩)
  have cross (x y : Fin n) (hx : c x x=l) (hy : c y y=r) : c x y=d (point x) (point y) := by
    obtain ⟨a,b,hit⟩ := StrategyColors.exists_source p (point x) (point y)
    have eq := (associated p).mpr (StrategyColors.maps_support p hit)
    obtain ⟨ha,hb⟩ := SmallShore.endpoints p eq
    exact (srcCross x y hx hy).trans ((srcCross a b (ha.trans ((diagonalName x).symm.trans hx))
        (hb.trans ((diagonalName y).symm.trans hy))).symm.trans eq)
  have names (x y) : c x y=d (point x) (point y) := by
    by_cases hx : c x x=r
    · by_cases hl : c y y=l
      · exact common_transpose p (cross y x hl hx)
      · have k : kb (c x x) := fun bad => lr (bad.symm.trans hx)
        rw [useB x k,useB y hl]; exact onR x y k hl
    · by_cases hy : c y y=r
      · by_cases hl : c x x=l
        · exact cross x y hl hy
        · have k : kb (c y y) := fun bad => lr (bad.symm.trans hy)
          rw [useB x hl,useB y k]; exact onR x y hl k
      · rw [useA x hx,useA y hy]; exact onL x y hx hy
  have inj : Function.Injective point := by
    intro x y hit
    have same := names x y
    rw [hit] at same
    exact Relations.diagonal _ (same.trans (names y y).symm)
  let out := Equiv.ofBijective point (Finite.injective_iff_bijective.mp inj)
  exact ⟨out,out.symm,out.symm_apply_apply,out.apply_symm_apply,fun i j => common_edge p (names i j)⟩

theorem isomorphic {G H : Graph 16} {l r v : Nat} (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (F : Shore (color (closure G)) l (Fin 4)) (S : Shore (color (closure G)) r (Fin 4))
    (Y : Shore (color (closure G)) v (Fin 8))
    (cover : ∀ x, color (closure G) x x=l ∨ color (closure G) x x=r ∨ color (closure G) x x=v)
    (uniform : ∀ i j, color (closure G) (atPoint F i) (atPoint S j) =
      color (closure G) (atPoint F 0) (atPoint S 0))
    (base : TwoBase (fun i j => color (closure G) (atPoint Y i) (atPoint Y j))) (q : QuantumIso G H) :
    Isomorphic G H :=
  isomorphic_with_singletons (by decide) (by decide) lr lv rv F S Y
    (fun x => (cover x).imp_right (Or.imp_right Or.inl)) uniform base q

end QGI.Coherent.TwoAnchorUnionGlue
