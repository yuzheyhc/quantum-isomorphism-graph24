import QuantumGraph

namespace QGI

/-- Up-to-order form of the lower bound. Includes the empty graph. -/
def Through (n : Nat) : Prop := ∀ k, k ≤ n → NoSeparation k

theorem through_succ_iff (n : Nat) :
    Through (n+1) ↔ Through n ∧ NoSeparation (n+1) := by
  constructor
  · intro all
    exact ⟨fun k hk => all k (by omega), all (n+1) (by omega)⟩
  · rintro ⟨low, last⟩ k hk
    by_cases eq : k = n+1
    · simpa [eq] using last
    · exact low k (by omega)

/-- This is the assembly rule. Inputs are deliberately visible in the type.
It is distinct from a closed proof of Through 23. -/
theorem assembleLower23 (base : Through 15)
    (h16 : NoSeparation 16) (h17 : NoSeparation 17)
    (h18 : NoSeparation 18) (h19 : NoSeparation 19)
    (h20 : NoSeparation 20) (h21 : NoSeparation 21)
    (h22 : NoSeparation 22) (h23 : NoSeparation 23) : Through 23 :=
  (through_succ_iff 22).2 ⟨
    (through_succ_iff 21).2 ⟨
      (through_succ_iff 20).2 ⟨
        (through_succ_iff 19).2 ⟨
          (through_succ_iff 18).2 ⟨
            (through_succ_iff 17).2 ⟨
              (through_succ_iff 16).2 ⟨
                (through_succ_iff 15).2 ⟨base, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩

end QGI
