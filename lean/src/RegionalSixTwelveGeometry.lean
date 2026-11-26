import SixTenCrossNormal

namespace QGI.Coherent.RegionalSixTwelveGeometry

abbrev Point := Fin 6
abbrev Block := Finset Point
abbrev Family := Finset Block

def degree (f : Family) (i : Point) := (f.filter fun s => i∈s).card

def cubic (f : Family) (i : Point) (s : Block) :=
  ∑ t ∈ f, if i∈t then (s∩t).card else 0

def Regular (f : Family) := ∀ i, degree f i=degree f 0

instance (f : Family) : Decidable (Regular f) := inferInstanceAs (Decidable (∀ i, _))

def TwoValues (f : Family) := ∀ s∈f, ∀ t∈f, ∀ i j : Point,
  (i∈s ↔ j∈t) → cubic f i s=cubic f j t

instance (f : Family) : Decidable (TwoValues f) :=
  inferInstanceAs (Decidable (∀ s∈f, ∀ t∈f, ∀ i j : Point, _))

/-- A subset of the six points is determined by its intersection sizes
with the edges, as soon as membership at one point is known. -/
def Determines (f : Family) := ∀ s t : Block, (∀ e∈f, (e∩s).card=(e∩t).card) →
  (∃ i : Point, i∈s ↔ i∈t) → s=t

instance (f : Family) : Decidable (Determines f) := inferInstanceAs (Decidable (∀ s t : Block, _))

def blocks (k : Nat) : Family := (Finset.univ : Finset Point).powersetCard k

private def check (test : Family → Bool) (pre : Family) : List Block → Bool
  | [] => test pre
  | t::rest => check test pre rest && check test (insert t pre) rest

private theorem checked_subset (test : Family → Bool) (f : Family) (xs : List Block) (pre : Family)
    (good : check test pre xs=true) : test (pre ∪ (xs.filter (fun t => decide (t∈f))).toFinset)=true := by
  induction xs generalizing pre with
  | nil => simpa [check] using good
  | cons t xs ih =>
    simp only [check,Bool.and_eq_true] at good
    obtain ⟨a,b⟩ := good
    by_cases h : t∈f
    · simpa [h,Finset.insert_union,Finset.union_insert] using ih (insert t pre) b
    · simpa [h] using ih pre a

private def asBlock (v : Nat) : Block := Finset.univ.filter fun i => v.testBit i.val
private def pool (k : Nat) := ((List.range 64).map asBlock).filter fun s => decide (s.card=k)

private theorem pool_all {k : Nat} (s : Block) (size : s.card=k) : s∈pool k := by
  let f := fun i : Point => decide (i∈s)
  let v := QGI.SixTen.Cross.encode f
  have eq : asBlock v=s := by ext i; simp [asBlock,v,f,QGI.SixTen.Cross.decode]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨v,List.mem_range.mpr (QGI.SixTen.Cross.encode_lt f),eq⟩,decide_eq_true size⟩

private theorem sound {k : Nat} (test : Family → Bool) (h : check test ∅ (pool k)=true)
    (f : Family) (weights : ∀ s∈f, s.card=k) : test f=true := by
  have eq : ((pool k).filter (fun t => decide (t∈f))).toFinset=f := by
    ext t
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun ht => pool_all _ (weights _ ht)
  simpa only [eq,Finset.empty_union] using checked_subset test f (pool k) ∅ h

private def pairPass (f : Family) : Bool :=
  if f.card=6 ∨ f.card=12 then if Regular f then decide (Determines f) else true else true

private def halfPass (f : Family) : Bool :=
  if f.card∣12 ∧ f.Nonempty then if Regular f then if TwoValues f then
    decide ((f.card=2 ∧ ∀ s∈f, sᶜ∈f) ∨
      (f.card=4 ∧ ∀ s∈f, ∀ t∈f, s≠t → (s∩t).card=1)) else true else true else true

set_option maxRecDepth 10000 in
private theorem pairs_checked : check pairPass ∅ (pool 2)=true := by native_decide

set_option maxRecDepth 10000 in
private theorem halves_checked : check halfPass ∅ (pool 3)=true := by native_decide

theorem determines_of_edges (f : Family) (weights : ∀ s∈f, s.card=2)
    (size : f.card=6 ∨ f.card=12) (regular : Regular f) : Determines f := by
  simpa [pairPass,size,regular] using sound pairPass pairs_checked f weights

theorem half_shapes (f : Family) (weights : ∀ s∈f, s.card=3) (size : f.card∣12)
    (pos : f.Nonempty) (regular : Regular f) (twoval : TwoValues f) :
    (f.card=2 ∧ ∀ s∈f, sᶜ∈f) ∨ (f.card=4 ∧ ∀ s∈f, ∀ t∈f, s≠t → (s∩t).card=1) := by
  simpa [halfPass,size,pos,regular,twoval] using sound halfPass halves_checked f weights

private def starPass (f : Family) : Bool := if f.card=2 ∨ f.card=4 then
  if ∀ a∈f, ∀ b∈f, (a∩b).Nonempty then decide (∃ i : Point, ∀ a∈f, i∈a) else true else true

private theorem stars_checked : check starPass ∅ (pool 2)=true := by native_decide

/-- Two or four distinct pairwise intersecting edges share a vertex. -/
theorem star_center (f : Family) (weights : ∀ s∈f, s.card=2) (size : f.card=2 ∨ f.card=4)
    (overlap : ∀ a∈f, ∀ b∈f, (a∩b).Nonempty) : ∃ i : Point, ∀ a∈f, i∈a := by
  simpa only [starPass,if_pos size,if_pos overlap,decide_eq_true_eq] using sound starPass stars_checked f weights

def touch (f : Family) (i j : Point) : Bool := decide (∃ e∈f, i∈e ∧ j∈e)

private def neighborPass (f : Family) : Bool := decide (∀ i, (∃ e∈f, i∈e) →
  (Finset.univ.filter (fun j => touch f i j=true)).card=degree f i+1)

private theorem neighbors_checked : check neighborPass ∅ (pool 2)=true := by native_decide

theorem neighbor_degree (f : Family) (weights : ∀ s∈f, s.card=2) (i) (covered : ∃ e∈f, i∈e) :
    (Finset.univ.filter (fun j => touch f i j=true)).card=degree f i+1 :=
  of_decide_eq_true (sound neighborPass neighbors_checked f weights) i covered

end QGI.Coherent.RegionalSixTwelveGeometry

