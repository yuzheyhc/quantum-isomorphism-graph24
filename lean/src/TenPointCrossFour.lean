import TenPointCrossLaws

namespace QGI.Coherent.TenPointCrossLaws
open TenPointCross
open SixTenCoordinates hiding V

private def candidates (a : Key) := (Finset.univ.powersetCard 4).filter (Admits a 4)
private def unitPair (a : Key) (s : Cell) := ∃ i∈s, ∃ k z : V, cell a i k=cell a 0 z ∧
  0<valency a (cell a 0 z) ∧ 4*sig a s i z=valency a (cell a 0 z)
private instance (a : Key) (s : Cell) : Decidable (unitPair a s) := by unfold unitPair; infer_instance
attribute [local irreducible] matrices
private def decode (mask : Nat) : Cell := Finset.univ.filter fun i => mask.testBit i.val=true
private def listFor (a : Key) : List Cell :=
  ((if a=1 then [15,51,195,771,60,204,780,240,816,960] else [71,139,275,547,204,340,612,408,680,816]) : List Nat).map decode
private def covers (a : Key) := ((Finset.univ.powersetCard 4).filter (fun s => Admits a 4 s ∧ s∉listFor a)).card=0
private instance (a : Key) : Decidable (covers a) := by unfold covers; infer_instance
private theorem covered : covers 1 ∧ covers 5 := by native_decide
private theorem listed : ∀ a : Key, a=1 ∨ a=5 →
    (listFor a).all (fun s => decide (unitPair a s) && (listFor a).all (fun t => decide ((s∩t).card≠1)))=true := by native_decide
private theorem four_checks (a : Key) (ha : a=1 ∨ a=5) :
    (∀ s∈candidates a, unitPair a s) ∧ ∀ s∈candidates a, ∀ t∈candidates a, (s∩t).card≠1 := by
  have cover : covers a := ha.elim (fun h => h ▸ covered.1) (fun h => h ▸ covered.2)
  have inside (s) (h : s∈candidates a) : s∈listFor a := by
    apply Classical.byContradiction; intro out
    have hs := Finset.mem_filter.mp h
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨hs.1,And.intro hs.2 out⟩⟩) cover
  have info (s) (h : s∈candidates a) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (listed a ha) s (inside s h))
  exact ⟨fun s hs => of_decide_eq_true (info s hs).1,fun s hs t ht => of_decide_eq_true (List.all_eq_true.mp (info s hs).2 t (inside t ht))⟩
private theorem mem_candidates {a : Key} {s : Cell} (h : Admits a 4 s) : s∈candidates a :=
  Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h.1⟩,h⟩

variable {n l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l V) (Y : Shore c r V)

include law

theorem row_transpose (i x j : V) : row F Y (entry F Y x j) i=col Y F (entry Y F j x) i := by
  ext k; simp only [row,col,Finset.mem_filter,Finset.mem_univ,true_and]; exact swap F Y law _ _ _ _

theorem four_shore {a b : Key} (left : Chart F a) (right : Chart Y b) (x y : V)
    (d : Nat) (hd : d=3 ∨ d=4) (weight : (row F Y (entry F Y x y) x).card=d)
    (smallest : ∀ i j, d≤(row F Y (entry F Y i j) i).card) : d=4 ∧ (a=2 ∨ b=2) := by
  let v := entry F Y x y
  let w := entry Y F y x
  have sizes (u i k) : (row F Y u i).card=(row F Y u k).card := (col_size F Y law u i 0).symm.trans (col_size F Y law u k 0)
  have sz (i) : (row F Y v i).card=d := (sizes v i x).trans weight
  have sz' (j) : (row Y F w j).card=d := by
    rw [row_transpose law Y F j y x]
    exact (col_size F Y law v x j).trans weight
  have first := constraints F Y law left v d y sz (fun i j => (smallest i j).trans_eq (col_size F Y law _ i j).symm)
  have second (i) := constraints Y F law right w d i sz' (fun j t => (smallest t j).trans_eq (congrArg Finset.card (row_transpose law F Y t t j)))
  obtain ⟨d4,kind⟩ := small_degree hd first.1
  clear weight
  subst d
  refine ⟨rfl,?_⟩
  by_contra neither
  have notA : a≠2 := fun h => neither (Or.inl h)
  have notB : b≠2 := fun h => neither (Or.inr h)
  have kinds := (small_degree (Or.inr rfl) (second 0).1).2
  have ka : a=1 ∨ a=5 := kind.imp_right (fun h => h.resolve_left notA)
  have kb : b=1 ∨ b=5 := kinds.imp_right (fun h => h.resolve_left notB)
  obtain ⟨i,hi,k,z,e,pos,unit⟩ := (four_checks a ka).1 _ (mem_candidates first.1)
  have mass := first.2 i hi k z e
  rw [unit] at mass
  have one : (row F Y v i∩row F Y v k).card=1 := Nat.eq_of_mul_eq_mul_left pos (by simpa only [Nat.mul_one] using mass.symm)
  exact (four_checks b kb).2 _ (mem_candidates (second i).1) _ (mem_candidates (second k).1)
    (by simpa only [v,row_transpose law F Y,w] using one)

end QGI.Coherent.TenPointCrossLaws
