import FourHalfPorts
import FourHalfSemantics

noncomputable section
namespace QGI.Coherent.FourHalfComparison
open QGI.FourHalfCatalog StrategyColorLaws
open FourTwelveFunctional (source)
open SmallUnion SmallFiberExtension

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K)

structure Fields (f g : Site → Fin n) (a : Key) (sw : Bool) (q s : Nat) (b : Bool) : Prop where
  tags : ∀ i j x y, source G (f i) (f j)=targetName p (g x) (g y) → (port i j).kind=(port x y).kind
  old : ∀ i j x y : Old, source G (f (.inl i)) (f (.inl j))=targetName p (g (.inl x)) (g (.inl y)) ↔
    base a sw (oldIndex i) (oldIndex j)=base a sw (oldIndex x) (oldIndex y)
  cycle : ∀ i j x y, source G (f (X i)) (f (F j))=targetName p (g (X x)) (g (F y)) ↔
    hit j (QGI.FourHalfCatalog.cycle q i)=hit y (QGI.FourHalfCatalog.cycle q x)
  halves : ∀ i j x y, source G (f (Y i)) (f (F j))=targetName p (g (Y x)) (g (F y)) ↔ half s b j i=half s (!b) y x
  four : ∀ i j x y, pos i j=pos x y → source G (f (F i)) (f (F j))=targetName p (g (F x)) (g (F y))

private theorem numEq (k : Nat) (x y : Bool) : k+x.toNat=k+y.toNat ↔ x=y := by cases x <;> cases y <;> simp

theorem fields {f g : Site → Fin n} {a : Key} {sw b : Bool} {q s : Nat} (h : Fields p f g a sw q s b)
    (u v : Port) (tag : u.kind=v.kind) :
    (u.word a sw q s b=v.word a sw q s (!b) → source G (f u.ends.1) (f u.ends.2)=targetName p (g v.ends.1) (g v.ends.2)) ∧
    (source G (f u.ends.1) (f u.ends.2)=targetName p (g v.ends.1) (g v.ends.2) →
     u.word a sw q s b=v.word a sw q s (!b) ∨ 108≤u.word a sw q s b ∧ 108≤v.word a sw q s (!b)) := by
  cases u <;> cases v <;> simp only [Port.kind] at tag <;> try contradiction
  case old.old i j x y =>
    exact ⟨(h.old i j x y).mpr,fun eq => Or.inl ((h.old i j x y).mp eq)⟩
  case xf.xf i j x y =>
    exact ⟨fun eq => (h.cycle i j x y).mpr ((numEq _ _ _).mp eq),fun eq => Or.inl ((numEq _ _ _).mpr ((h.cycle i j x y).mp eq))⟩
  case yf.yf i j x y =>
    exact ⟨fun eq => (h.halves i j x y).mpr ((numEq _ _ _).mp eq),fun eq => Or.inl ((numEq _ _ _).mpr ((h.halves i j x y).mp eq))⟩
  case fx.fx i j x y =>
    refine ⟨fun eq => common_transpose p ((h.cycle j i y x).mpr ((numEq _ _ _).mp eq)),?_⟩
    exact fun eq => Or.inl ((numEq _ _ _).mpr ((h.cycle j i y x).mp (common_transpose p eq)))
  case fy.fy i j x y =>
    refine ⟨fun eq => common_transpose p ((h.halves j i y x).mpr ((numEq _ _ _).mp eq)),?_⟩
    exact fun eq => Or.inl ((numEq _ _ _).mpr ((h.halves j i y x).mp (common_transpose p eq)))
  case ff.ff i j x y =>
    exact ⟨fun eq => h.four i j x y (Nat.add_left_cancel eq),fun _ => Or.inr ⟨Nat.le_add_right _ _,Nat.le_add_right _ _⟩⟩

variable [CompleteSpace K]
theorem realize {a : Key} {sw b : Bool} {q s : Nat} (reg : Nat → Prop) (f g : Site → Fin n)
    (fi : Function.Injective f) (gi : Function.Injective g)
    (src : ∀ z, (∃ i,f i=z) ↔ reg (source G z z)) (tgt : ∀ z, (∃ i,g i=z) ↔ reg (targetName p z z))
    (h : Fields p f g a sw q s b) (input : ∃ r, Supports a sw q s r) : Realizes p reg := by
  let l := f ∘ number.symm
  let r := g ∘ number.symm
  have range {k : Site → Fin n} (z) : (∃ i, (k ∘ number.symm) i=z) ↔ ∃ i, k i=z :=
    ⟨fun ⟨i,hi⟩ => ⟨number.symm i,hi⟩,fun ⟨i,hi⟩ => ⟨number i,by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hi⟩⟩
  have word (v : Bool) (i j : Site) : value a sw q s v (number i) (number j)=(port i j).word a sw q s v := by
    have eq := word_read a sw q s v (port i j)
    rwa [unpack] at eq
  apply FourHalfSemantics.apply_certificate p reg l r (fi.comp number.symm.injective) (gi.comp number.symm.injective)
    (fun z => (range z).trans (src z)) (fun z => (range z).trans (tgt z)) a sw q s b input
  · intro i j x y c
    obtain ⟨i,rfl⟩ := number.surjective i; obtain ⟨j,rfl⟩ := number.surjective j
    obtain ⟨x,rfl⟩ := number.surjective x; obtain ⟨y,rfl⟩ := number.surjective y
    rw [word,word] at c
    have tags : (port i j).kind=(port x y).kind := (kind_of_word _ _ _ _ b _).symm.trans ((congrArg wordKind c).trans (kind_of_word _ _ _ _ (!b) _))
    simpa only [unpack,l,r,Function.comp_apply,Equiv.symm_apply_apply] using (fields p h _ _ tags).1 c
  · intro i j x y c
    obtain ⟨i,rfl⟩ := number.surjective i; obtain ⟨j,rfl⟩ := number.surjective j
    obtain ⟨x,rfl⟩ := number.surjective x; obtain ⟨y,rfl⟩ := number.surjective y
    simp only [l,r,Function.comp_apply,Equiv.symm_apply_apply] at c
    rw [word,word]
    apply (fields p h _ _ (h.tags i j x y c)).2
    simpa only [unpack] using c

end QGI.Coherent.FourHalfComparison
