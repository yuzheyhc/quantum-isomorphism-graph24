import FourHalfCore
import SixTenCoordinates

namespace QGI.FourHalfCatalog

abbrev Col := Four → Bool
def dot (p q : Col) := (Finset.univ.filter fun i => p i=true ∧ q i=true).card
def comp (p : Col) : Col := fun i => !p i
def parityColumn (b : Bool) : Col := fun i => decide (i.val%2=b.toNat)

private theorem detect : ∀ p q : Col, (∀ k, dot (fun i => hit i k) p=dot (fun i => hit i k) q) →
    p=q ∨ ∃ b, p=parityColumn b ∧ q=parityColumn (!b) := by decide

private theorem extremes : ∀ a b : Col, dot a a=2 → dot b b=2 →
    (dot a b=2 → b=a) ∧ (dot a b=0 → b=comp a) := by decide
private theorem disjoint : ∀ a : Col, dot a (comp a)=0 := by decide

private theorem same_part : ∀ a b p q : Col, dot a a=2 → dot b b=2 → dot q q=2 →
    dot a p=dot b q → (p=a ∨ p=comp a) → q=(if p=a then b else comp b) := by
  intro a b p q aa bb qq ab part
  by_cases h : p=a
  · rw [if_pos h]
    exact (extremes b q bb qq).1 (ab.symm.trans (h ▸ aa))
  · rw [if_neg h]
    rw [part.resolve_left h,disjoint] at ab
    exact (extremes b q bb qq).2 ab.symm

private theorem flip_column : ∀ b, comp (parityColumn b)=parityColumn (!b) := by decide
private theorem complement_size : ∀ p : Col, dot p p=2 → dot (comp p) (comp p)=2 := by decide

/-- With the doubled cycle already aligned, the only undetected change is
a global interchange of the two opposite pairs. The overlap from the
first column then fixes the orientation of every other column. -/
theorem dichotomy (M N : Eight → Col) (two : dot (M 0) (M 0)=2) (parts : ∀ j, M j=M 0 ∨ M j=comp (M 0))
    (gram : ∀ i j, dot (M i) (M j)=dot (N i) (N j))
    (edge : ∀ k j, dot (fun i => hit i k) (M j)=dot (fun i => hit i k) (N j)) :
    (∀ j, M j=N j) ∨ ∃ s : Eight → Bool, ∃ b : Bool, s 0=false ∧
      (∀ j, M j=parityColumn (xor (s j) b)) ∧ ∀ j, N j=parityColumn (xor (s j) (!b)) := by
  have size (j) : dot (M j) (M j)=2 := by
    rcases parts j with h|h
    · rw [h]; exact two
    · rw [h]; exact complement_size _ two
  have link (j) := same_part (M 0) (N 0) (M j) (N j) two ((gram 0 0).symm.trans two)
    ((gram j j).symm.trans (size j)) (gram 0 j) (parts j)
  rcases detect (M 0) (N 0) (fun k => edge k 0) with eq|⟨b,hp,hn⟩
  · left
    intro j
    by_cases h : M j=M 0
    · rw [link,if_pos h,←eq,h]
    · rw [link,if_neg h,←eq]
      exact (parts j).resolve_left h
  · right
    let s (j : Eight) := decide (M j≠M 0)
    refine ⟨s,b,by simp [s],?_,?_⟩
    · intro j
      by_cases h : M j=M 0
      · simpa [s,h] using hp
      · have left := (parts j).resolve_left h
        simpa [s,h] using left.trans ((congrArg comp hp).trans (flip_column b))
    · intro j
      by_cases h : M j=M 0
      · simpa [s,h] using (link j).trans (by rw [if_pos h,hn])
      · simpa [s,h] using (link j).trans (by rw [if_neg h,hn,flip_column,Bool.not_not])

theorem halves_balanced : ∀ (s : Eight → Bool) (b : Bool),
    (Finset.univ.filter (fun j => parityColumn (xor (s j) b) 0=true)).card =
      (Finset.univ.filter (fun j => parityColumn (xor (s j) b) 1=true)).card →
    (Finset.univ.filter (fun j => s j=true)).card=4 := by native_decide

theorem halves_detect : ∀ a b p q k : Bool,
    dot (parityColumn (xor a k)) (parityColumn (xor b k))=dot (parityColumn (xor p k)) (parityColumn (xor q k)) →
    (a=b ↔ p=q) := by decide

theorem cycle_detect : ∀ i j a b : Four, dot (fun v => hit v i) (fun v => hit v j)=dot (fun v => hit v a) (fun v => hit v b) →
    pos i j=pos a b := by decide

end QGI.FourHalfCatalog
