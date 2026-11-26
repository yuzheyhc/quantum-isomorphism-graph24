import TenMatchedRealize

noncomputable section
namespace QGI.Coherent.TenPointMatched
open TenPointCross TenPointCross.MatchedCatalog TenPointCrossLaws
open SixTenCoordinates (Shore atPoint Laws commonLaws targetLaws sourceLaws)
open SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
abbrev Slot := Q × Bool
def Alike (i j x y : Slot) := (i.1=j.1 ↔ x.1=y.1) ∧ (i.2=j.2 ↔ x.2=y.2)
def Preserves {n l : Nat} {c d : Fin n → Fin n → Nat} (F : Shore c l Slot) (T : Shore d l Slot) :=
  ∀ i j x y, Alike i j x y → c (atPoint F i) (atPoint F j)=d (atPoint T x) (atPoint T y)
def Linked {n l r : Nat} {c : Fin n → Fin n → Nat} (F : Shore c l Slot) (Y : Shore c r Slot) (v : Nat) :=
  ∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i.1=j.1

theorem reverse {n l r v : Nat} {c : Fin n → Fin n → Nat} {F : Shore c l V} {Y : Shore c r V}
    (S : Pairs F Y v) (law : Laws c c) :
    ∃ u, ∃ D : Pairs Y F u, D.left=S.right ∧ D.right=S.left ∧
    ∀ i j, entry Y F j i=u ↔ entry F Y i j=v := by
  obtain ⟨k,hk⟩ := label_onto S.right_two (S.left 0)
  let u := entry Y F k 0
  have eq := (S.member_iff 0 k).mpr hk.symm
  have cells (i j) : entry Y F j i=u ↔ entry F Y i j=v :=
    ⟨fun h => (law.rev h).trans eq,fun h => law.rev (h.trans eq.symm)⟩
  exact ⟨u,⟨S.right,S.left,S.right_two,S.left_two,fun i j => (cells j i).trans ((S.member_iff j i).trans eq_comm)⟩,rfl,rfl,cells⟩

private theorem numberSide {a : Key} (key : a=1 ∨ a=5) (label : V → Q) (onto : Function.Surjective label)
    (same : ∀ i j, label i=label j ↔ together a 1 i j) :
    ∃ g : Slot ≃ V, (∀ i, label (g i)=i.1) ∧
      ∀ i j x y, Alike i j x y → cell a (g i) (g j)=cell a (g x) (g y) := by
  let base := Equiv.ofBijective (fun p : Slot => site a p.1 p.2) (flat a key).1
  let f (i : Q) := label (site a i false)
  have tag (i : Q) (b : Bool) : label (site a i b)=f i := (same _ _).mpr (((flat a key).2.2 _ _ _ _).mpr rfl)
  have surj : Function.Surjective f := by
    intro q; obtain ⟨j,rfl⟩ := onto q; obtain ⟨⟨i,b⟩,rfl⟩ := base.surjective j
    exact ⟨i,(tag i b).symm⟩
  let e := Equiv.ofBijective f (Finite.surjective_iff_bijective.mp surj)
  let g := (Equiv.prodCongr e.symm (Equiv.refl Bool)).trans base
  refine ⟨g,fun i => (tag _ _).trans (e.apply_symm_apply _),?_⟩
  rintro ⟨i,s⟩ ⟨j,t⟩ ⟨x,b⟩ ⟨y,d⟩ ⟨labels,bits⟩
  change cell a (site a (e.symm i) s) (site a (e.symm j) t)=cell a (site a (e.symm x) b) (site a (e.symm y) d)
  change (i=j ↔ x=y) at labels
  change (s=t ↔ b=d) at bits
  simp only [(flat a key).2.1,flatName,e.symm.injective.eq_iff,labels,bits]

/-- Independent labelings of corresponding shores realize the same names whenever
equality of the labels and equality of the two signs are respected. -/
private theorem coordinated {a : Key} (key : a=1 ∨ a=5) (q q' : V → Q)
    (onto : Function.Surjective q) (onto' : Function.Surjective q')
    (same : ∀ i j, q i=q j ↔ together a 1 i j) (same' : ∀ i j, q i=q j ↔ q' i=q' j) :
    ∃ g h : Slot ≃ V, (∀ i, q (g i)=i.1) ∧ (∀ i, q' (h i)=i.1) ∧
    (∀ i j x y, Alike i j x y → cell a (g i) (g j)=cell a (h x) (h y)) := by
  obtain ⟨g,hg,cg⟩ := numberSide key q onto same
  let f (i : Q) := q' (g (i,false))
  have tag (i : Slot) : q' (g i)=f i.1 := (same' _ _).mp ((hg i).trans (hg (i.1,false)).symm)
  have surj : Function.Surjective f := by
    intro v; obtain ⟨u,rfl⟩ := onto' v; obtain ⟨i,rfl⟩ := g.surjective u; exact ⟨_,(tag i).symm⟩
  let e := Equiv.ofBijective f (Finite.surjective_iff_bijective.mp surj)
  let next := Equiv.prodCongr e.symm (Equiv.refl Bool)
  refine ⟨g,next.trans g,hg,fun i => (tag _).trans (e.apply_symm_apply _),?_⟩
  intro i j x y near
  apply cg
  exact ⟨near.1.trans e.symm.injective.eq_iff.symm,near.2⟩

structure Frames {n l r : Nat} {c d : Fin n → Fin n → Nat} (v : Nat) where
  F : Shore c l Slot
  Y : Shore c r Slot
  T : Shore d l Slot
  Z : Shore d r Slot
  src : Linked F Y v
  tgt : Linked T Z v
  ll : Preserves F T
  rr : Preserves Y Z

variable {n l r : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (p : PerfectStrategy G H K)

theorem frames {a b : Key} {v : Nat} (F : Shore (source G) l V) (Y : Shore (source G) r V)
    (S : Pairs F Y v) (ca : Chart F a) (cb : Chart Y b) (af : a=1 ∨ a=5) (bf : b=1 ∨ b=5)
    (pairA : ∀ i j, S.left i=S.left j ↔ together a 1 i j) (pairB : ∀ i j, S.right i=S.right j ↔ together b 1 i j) :
    Nonempty (Frames (l:=l) (r:=r) (c:=source G) (d:=targetName p) v) := by
  obtain ⟨m,diag⟩ := diagonal_names p
  let W : Shore (targetName p) l V := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let U : Shore (targetName p) r V := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨e,_,he⟩ := SmallShore.realize_at p (by decide : 0<10) (by decide) (atPoint F) (atPoint W) l
    (Subtype.val_injective.comp F.injective) (Subtype.val_injective.comp W.injective) (range F) (range W) 0 0
  obtain ⟨f,_,hf⟩ := SmallShore.realize_at p (by decide : 0<10) (by decide) (atPoint Y) (atPoint U) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp U.injective) (range Y) (range U) 0 0
  let T := e.trans W
  let Z := f.trans U
  obtain ⟨D,dl⟩ := transport (T:=T) (Z:=Z) S (commonLaws p) (targetLaws p) he
  obtain ⟨u,S',sl,sr,sc⟩ := reverse S (sourceLaws _)
  obtain ⟨w,D',tl,tr,tc⟩ := reverse D (targetLaws p)
  obtain ⟨k,hk⟩ := label_onto S.right_two (S.left 0)
  have link := (S.member_iff 0 k).mpr hk.symm
  obtain ⟨y,hy⟩ := label_onto D.right_two (D.left 0)
  have equal : u=w := ((sc 0 k).mpr link).symm.trans ((common_transpose p (link.trans ((D.member_iff 0 y).mpr hy.symm).symm)).trans
    ((tc 0 y).mpr ((D.member_iff 0 y).mpr hy.symm)))
  subst w
  have same (i j) : S.right i=S.right j ↔ D.right i=D.right j := by
    rw [←sl,←tl]; exact internal S' D' (commonLaws p) (hf i j)
  obtain ⟨g,h,sg,th,read⟩ := coordinated af S.left D.left (label_onto S.left_two) (label_onto D.left_two) pairA
    (fun _ _ => by rw [dl])
  obtain ⟨z,t,sz,tt,rr⟩ := coordinated bf S.right D.right (label_onto S.right_two) (label_onto D.right_two) pairB same
  exact ⟨⟨g.trans F,z.trans Y,h.trans T,t.trans Z,
    fun i j => (S.member_iff _ _).trans (by rw [sg,sz]),fun i j => (D.member_iff _ _).trans (by rw [th,tt]),
    fun i j x y a => ((ca _ _ _ _).mpr (read _ _ _ _ a)).trans (he _ _),
    fun i j x y a => ((cb _ _ _ _).mpr (rr _ _ _ _ a)).trans (hf _ _)⟩⟩

end QGI.Coherent.TenPointMatched
