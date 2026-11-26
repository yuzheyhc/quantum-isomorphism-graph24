import DoubleEightInterfaceTransport
import DoubleEightColumnEnum

namespace QGI.DoubleEight.ColumnMaps

open ShoreCensus FixedInterface InterfaceTransport

def color (cols : List Nat) : Coloring := fun i j => ColumnEnum.letter (cols.getD j.val 0) i.val

def splitRows (c : Coloring) : Prop := ∃ i x : V, ∀ j : V, c i j ≠ c x j

def Oriented (c d : Coloring) : Prop := CrossIso c d ∨ CrossIso (transpose c) d

theorem splitRows_iff {c d : Coloring} (h : CrossIso c d) : splitRows c ↔ splitRows d := by
  obtain ⟨p,q,h⟩ := h
  constructor
  · rintro ⟨i,x,hx⟩
    refine ⟨p i,p x,fun j eq => hx (q.symm j) ((h _ _ _ _).mpr ?_)⟩
    simpa using eq
  · rintro ⟨i,x,hx⟩
    refine ⟨p.symm i,p.symm x,fun j eq => hx (q j) ?_⟩
    simpa using (h _ _ _ _).mp eq

theorem dualIso {c d : Coloring} (h : CrossIso c d) : CrossIso (transpose c) (transpose d) := by
  obtain ⟨p,q,h⟩ := h
  exact ⟨q,p,fun i j x y => h j i y x⟩

private def records : List (List Nat) :=
  (((include_str "data/double-eight-column-leaves.txt").trim.splitOn "\n").mapM
    (fun (line : String) => (line.trim.splitOn " ").mapM String.toNat?)).getD []

private instance (c : Coloring) : Decidable (splitRows c) := by unfold splitRows; infer_instance

def keys : List (Nat × Nat × List Nat) := records.map fun r => (r[0]!,r[1]!, (r.drop 2).take 8)

private def point (r : List Nat) (o : Nat) (i : V) : V :=
  ⟨(r.getD (o+i.val) 8) % 8, Nat.mod_lt _ (by decide)⟩

private def targetIndex (r : List Nat) : Fin 88 := ⟨r[10]! % 88, Nat.mod_lt _ (by decide)⟩



private def verified (r : List Nat) : Bool :=
  let c := color ((r.drop 2).take 8)
  if r[10]! = 88 then decide (splitRows c ∧ ¬splitRows (transpose c)) else
    let target := named (Nonuniform.layer (targetIndex r)).word
    let dest := if r[11]! = 0 then target else transpose target
    let p := point r 12
    let q := point r 20
    decide ((∀ i j, p i = p j → i = j) ∧ (∀ i j, q i = q j → i = j) ∧
      ∀ i j x y : V, c i j = c x y ↔ dest (p i) (q j) = dest (p x) (q y))

private theorem checked : records.all verified = true := by native_decide

/-- Count the point maps and residual obstructions in the checked input. -/
theorem witness_counts :
    records.length = 375 ∧ (records.filter (fun r => r[10]! < 88)).length = 343 ∧
    (records.filter (fun r => r[10]! = 88)).length = 32 ∧
    ((records.filter (fun r => r[10]! < 88)).map (fun r => r[10]!)).eraseDups.length = 15 := by
  native_decide
theorem key_sound {s k : Nat} {cols : List Nat} (h : (s,k,cols) ∈ keys) :
    (∃ l : Fin 88, Oriented (color cols) (named (Nonuniform.layer l).word)) ∨
       (splitRows (color cols) ∧ ¬splitRows (transpose (color cols))) := by
  obtain ⟨r,mem,eq⟩ := List.mem_map.mp h
  have e := congrArg (fun p : Nat × Nat × List Nat => p.2.2) eq
  change (r.drop 2).take 8 = cols at e
  subst cols
  have ch := List.all_eq_true.mp checked r mem
  unfold verified at ch
  split at ch
  · exact Or.inr (of_decide_eq_true ch)
  · obtain ⟨hp,hq,hl⟩ := of_decide_eq_true ch
    let p := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hp)
    let q := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hq)
    left
    refine ⟨targetIndex r,?_⟩
    split at hl
    · exact Or.inl ⟨p,q,hl⟩
    · exact Or.inr ⟨q,p,fun i j x y => hl j i y x⟩

end QGI.DoubleEight.ColumnMaps