import TenPointCrossLaws
import RegionalShorePins

namespace QGI.TenPointCross.Edges
def decode (m : Nat) : Cell := Finset.univ.filter fun i => m.testBit i.val=true
private def masks : Array (List Nat) := #[
  [],
  [3, 12, 48, 192, 768],
  [],
  [],
  [3, 12, 48, 192, 768],
  [3, 68, 136, 272, 544],
  [],
  [],
  [3, 17, 33, 257, 513, 6, 10, 66, 130, 20, 36, 260, 516, 24, 40, 264, 520, 80, 144, 96, 160, 320, 576, 384, 640],
  [3, 260, 520, 144, 96],
  [3, 12, 48, 192, 768],
  [3, 9, 33, 129, 513, 6, 18, 66, 258, 12, 36, 132, 516, 24, 72, 264, 48, 144, 528, 96, 288, 192, 576, 384, 768],
  [3, 12, 48, 192, 768]]
private def shapes (a : Key) := ((masks[a.val]?).getD []).map decode
def candidates (a : Key) := (shapes a).toFinset

def bank (a : Key) (s : Cell) := (candidates a).filter fun t => ∃ i∈t, sig a t i=sig a s 0
def Short (a : Key) (b : Finset Cell) :=
  (∀ i : V, (Finset.univ.filter (fun k => cell a k 0=cell a i 0)).card≤3) ∧
  ∀ t∈b, (b.filter (fun u => sig a u 0=sig a t 0)).card≤3
instance (a : Key) (b : Finset Cell) : Decidable (Short a b) := by unfold Short; infer_instance
attribute [local irreducible] matrices masks
private theorem exhaust : ∀ a : Key, ((Finset.univ.powersetCard 2).filter
    (fun s => Admits a 2 s ∧ s∉candidates a)).card=0 := by native_decide
private def tested (a : Key) (s : Cell) :=
  let b := bank a s
  decide ((0:V)∉s ∨ b.card<10 ∨ Short a b)
private theorem checks : ∀ a : Key, (shapes a).all (tested a)=true := by native_decide
theorem occurs {a : Key} {s : Cell} (h : Admits a 2 s) : s∈candidates a := by
  by_contra outside
  apply (Nat.ne_of_gt ?_) (exhaust a)
  exact Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h.1⟩,h,outside⟩⟩
theorem short_of_full {a : Key} {s : Cell} (h : Admits a 2 s) (zero : (0:V)∈s) (ten : 10≤(bank a s).card) :
    Short a (bank a s) := by
  have test := of_decide_eq_true (List.all_eq_true.mp (checks a) s (List.mem_toFinset.mp (occurs h)))
  exact (test.resolve_left (not_not_intro zero)).resolve_left (Nat.not_lt_of_ge ten)

end QGI.TenPointCross.Edges
