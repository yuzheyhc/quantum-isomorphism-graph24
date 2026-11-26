import FourHalfCatalog
import SplitRectangleGluing

namespace QGI.FourHalfCatalog
set_option maxRecDepth 16000
attribute [local irreducible] FourHalfInput.rows DoubleEight.Prepared.row

def balanced (q : Eight → Four) : Prop :=
  ∀ v, (Finset.univ.filter (fun i => q i=v)).card=2
def canonical (q : Eight → Four) : Prop :=
  q 0=0 ∧ ∃ i, q i=1 ∧ ∀ j, j < i → q j≠3
def halfSize (s : Eight → Bool) : Prop := (Finset.univ.filter (fun i => s i=true)).card=4

private instance (q : Eight → Four) : Decidable (balanced q) := by unfold balanced; infer_instance
private instance (q : Eight → Four) : Decidable (canonical q) := by unfold canonical; infer_instance
private instance (s : Eight → Bool) : Decidable (halfSize s) := by unfold halfSize; infer_instance

/-- Dihedral changes of coordinates take each twice-repeated cycle to a canonical chart. -/
def transform (reflection : Bool) (r i : Four) : Four := if reflection then r-i else i+r
def pointTransform (reflection : Bool) (r i : Four) : Four := if reflection then r+1-i else i+r

theorem change_chart : ∀ q : Eight → Four, balanced q → ∃ f : Bool, ∃ r : Four, canonical (transform f r ∘ q) := by native_decide
theorem transform_ok : ∀ f r, Function.Bijective (transform f r) ∧ Function.Bijective (pointTransform f r) ∧
    (∀ i j, hit (pointTransform f r i) (transform f r j)=hit i j) ∧
    (∀ i j, pos (transform f r i) (transform f r j)=pos i j) ∧
    (∀ i j, pos (pointTransform f r i) (pointTransform f r j)=pos i j) := by decide

def encode (q : Eight → Four) : Nat := ∑ i, (q i).val * 4^i.val
def bits (s : Eight → Bool) : Nat := ∑ i, (s i).toNat * 2^i.val

theorem encode_ok : ∀ q : Eight → Four, encode q<65536 ∧ ∀ i, cycle (encode q) i=q i := by native_decide
theorem bits_ok : ∀ s : Eight → Bool, bits s<256 ∧ ∀ i, side (bits s) i=s i := by native_decide

def cross (a : Key) (sw : Bool) (i j : Eight) := base a sw (eight false i) (eight true j)
def internal (a : Key) (sw shore : Bool) (i j : Eight) := base a sw (eight shore i) (eight shore j)
def Twin (t : Eight → Eight → Nat) : Prop :=
  (∀ i j x, t i x=t j x → ∀ y, t i y=t j y) ∧
  ∀ x i j, t x i=t x j → ∀ y, t y i=t y j
private instance (t : Eight → Eight → Nat) : Decidable (Twin t) := by unfold Twin; infer_instance

abbrev Z := Fin 64
def fst (i : Z) : Eight := ⟨i.val/8,by omega⟩
def snd (i : Z) : Eight := Fin.ofNat' 8 i.val
def representatives (m : Eight → Eight → Nat) : Vector Z 64 :=
  Vector.ofFn fun i => ((List.finRange 64).find? (fun j => m (fst j) (snd j)=m (fst i) (snd i))).getD i
theorem rep_ok (m : Eight → Eight → Nat) (i : Z) :
    let j := (representatives m).get i
    m (fst j) (snd j)=m (fst i) (snd i) := by
  change m (fst ((Vector.ofFn _).get i)) (snd ((Vector.ofFn _).get i))=_
  simp only [show ∀ (f : Z → Z) (x : Z), (Vector.ofFn f).get x=f x from fun f x => by change (Vector.ofFn f)[x.val]=_; simp]
  cases h : (List.finRange 64).find? (fun j => decide (m (fst j) (snd j)=m (fst i) (snd i))) with
  | none => simp
  | some j =>
    change m (fst j) (snd j)=m (fst i) (snd i)
    exact of_decide_eq_true (List.find?_some (p:=fun k => decide (m (fst k) (snd k)=m (fst i) (snd i))) h)

def agrees {α : Type} [DecidableEq α] (rep : Vector Z 64) (v : Eight → Eight → α) : Bool :=
  (List.finRange 64).all fun i => v (fst i) (snd i)=v (fst (rep.get i)) (snd (rep.get i))

theorem agrees_of {α} [DecidableEq α] (m : Eight → Eight → Nat) (v : Eight → Eight → α)
    (named : ∀ i j x y, m i j=m x y → v i j=v x y) : agrees (representatives m) v=true :=
  List.all_eq_true.mpr (fun i _ => decide_eq_true (named _ _ _ _ (rep_ok m i).symm))

private def qs := (List.range 65536).filter (fun q => decide (balanced (cycle q) ∧ canonical (cycle q)))
private def ss := (List.range 256).filter (fun s => decide (side s 0=false ∧ halfSize (side s)))
def hitRow (a : Key) (sw : Bool) (q s : Nat) (i : Fin FourHalfInput.rows.size) : Bool :=
  let r := FourHalfInput.rows[i]
  r.id=a.val ∧ r.swap=sw ∧ r.cycle=q ∧ r.halves=s

def covers (a : Key) (sw : Bool) : Bool :=
  let x := representatives (internal a sw false)
  let y := representatives (internal a sw true)
  decide (Twin (cross a sw)) ||
    ((qs.filter (fun q => agrees x (fun i j => pos (cycle q i) (cycle q j)))).all fun q =>
      ((ss.filter (fun s => agrees y (fun i j => side s i == side s j))).all fun s =>
        (List.finRange FourHalfInput.rows.size).any (hitRow a sw q s)))

attribute [local irreducible] qs ss
private theorem checked : ∀ a sw, covers a sw=true := by native_decide

theorem support (a : Key) (sw : Bool) (q : Eight → Four) (s : Eight → Bool) (nb : ¬Twin (cross a sw))
    (bal : balanced q) (can : canonical q) (zero : s 0=false) (hs : halfSize s)
    (qn : ∀ i j x y, internal a sw false i j=internal a sw false x y → pos (q i) (q j)=pos (q x) (q y))
    (sn : ∀ i j x y, internal a sw true i j=internal a sw true x y → (s i=s j ↔ s x=s y)) :
    ∃ r, Supports a sw (encode q) (bits s) r := by
  have cq : cycle (encode q)=q := funext (encode_ok q).2
  have cs : side (bits s)=s := funext (bits_ok s).2
  have mq : encode q∈qs := by
    unfold qs
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (encode_ok q).1,decide_eq_true (by rw [cq]; exact ⟨bal,can⟩)⟩
  have ms : bits s∈ss := by
    unfold ss
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (bits_ok s).1,decide_eq_true (by rw [cs]; exact ⟨zero,hs⟩)⟩
  have h := checked a sw
  simp only [covers,decide_eq_false nb,Bool.false_or,List.all_eq_true,List.mem_filter] at h
  have aq := agrees_of (internal a sw false) (fun i j => pos (q i) (q j)) qn
  have as' := agrees_of (internal a sw true) (fun i j => s i == s j) (fun i j x y e => by
    have same := sn i j x y e
    by_cases a : s i=s j <;> by_cases b : s x=s y <;> simp_all)
  rw [←cq] at aq
  rw [←cs] at as'
  obtain ⟨i,_,hi⟩ := List.any_eq_true.mp (h _ ⟨mq,aq⟩ _ ⟨ms,as'⟩)
  have same := of_decide_eq_true hi
  change FourHalfInput.rows[i].id=a.val ∧ _ at same
  obtain ⟨id,hsw,hq,hh⟩ := same
  have val : Fin.ofNat' 636 FourHalfInput.rows[i].id=a := by rw [id]; exact Fin.ext (Nat.mod_eq_of_lt a.isLt)
  refine ⟨FourHalfInput.rows[i].proof,?_⟩
  simpa only [val,hsw,hq,hh] using verified i

end QGI.FourHalfCatalog
