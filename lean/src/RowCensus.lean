import Mathlib

namespace QGI.RowCensus

abbrev Table (n : Nat) (α : Type) := Fin n → Fin n → α

structure Laws {n : Nat} [NeZero n] {α : Type} (m : Table n α) : Prop where
  diagonal : ∀ i j, m i j = m 0 0 ↔ i = j
  reverse : ∀ i j x y, m i j = m x y → m j i = m y x
  pairs : ∀ i j x y, m i j = m x y →
    (List.ofFn (fun z => (m i z,m j z))).Perm (List.ofFn (fun z => (m x z,m y z)))

def Iso {n : Nat} {α β : Type} (a : Table n α) (b : Table n β) :=
  ∃ e : Equiv.Perm (Fin n), ∀ i j x y, a i j=a x y ↔ b (e i) (e j)=b (e x) (e y)

theorem Laws.row_perm {n : Nat} [NeZero n] {α : Type} {m : Table n α} (h : Laws m) (i : Fin n) :
    (List.ofFn (m i)).Perm (List.ofFn (m 0)) := by
  have hp := (h.pairs i i 0 0 ((h.diagonal i i).mpr rfl)).map Prod.fst
  simpa [List.map_ofFn, Function.comp_def] using hp

theorem Laws.transport {n : Nat} [NeZero n] {α β : Type} {m : Table n α} (h : Laws m)
    (p : Equiv.Perm (Fin n)) (g : α → β)
    (faithful : ∀ i j x y, g (m i j)=g (m x y) → m i j=m x y) :
    Laws (fun i j => g (m (p i) (p j))) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    have diag := (h.diagonal (p 0) (p 0)).mpr rfl
    exact ⟨fun eq => p.injective ((h.diagonal _ _).mp ((faithful _ _ _ _ eq).trans diag)),
      fun eq => congrArg g (((h.diagonal _ _).mpr (congrArg p eq)).trans diag.symm)⟩
  · exact fun i j x y eq => congrArg g (h.reverse _ _ _ _ (faithful _ _ _ _ eq))
  · intro i j x y eq
    let tag := fun v : α × α => (g v.1,g v.2)
    have step := (h.pairs _ _ _ _ (faithful _ _ _ _ eq)).map tag
    simp only [List.map_ofFn,Function.comp_def] at step
    exact (p.ofFn_comp_perm (fun z => tag (m (p i) z,m (p j) z))).trans
      (step.trans (p.ofFn_comp_perm (fun z => tag (m (p x) z,m (p y) z))).symm)

private theorem count_ofFn {α : Type} [DecidableEq α] {n : Nat} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i=a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,Fin.sum_univ_succ,List.count_cons,ih]
    by_cases eq : f 0 = a <;> simp [eq, Nat.add_comm]

/-- Replace the second color in an intersection number by its transpose.
Hence the multiset of pairs of colors in two rows depends only on the
color between their origins. -/
theorem of_intersections {n : Nat} [NeZero n] (m : Table n Nat)
    (diag : ∀ i j, m i j=m 0 0 ↔ i=j)
    (rev : ∀ i j x y, m i j=m x y → m j i=m y x)
    (mul : ∀ a b i j x y, m i j=m x y →
      (∑ z, if m i z=a ∧ m z j=b then 1 else 0 : Nat) =
      (∑ z, if m x z=a ∧ m z y=b then 1 else 0 : Nat)) : Laws m := by
  refine ⟨diag,rev,?_⟩
  intro i j x y eq
  apply List.perm_iff_count.mpr
  rintro ⟨a,b⟩
  rw [count_ofFn,count_ofFn]
  simp only [Prod.mk.injEq]
  by_cases occurs : ∃ u v, m u v=b
  · obtain ⟨u,v,rfl⟩ := occurs
    have flip (l z : Fin n) : m l z=m u v ↔ m z l=m v u :=
      ⟨rev _ _ _ _, rev _ _ _ _⟩
    simp only [flip]
    exact mul _ _ _ _ _ _ eq
  · push_neg at occurs
    simp [occurs]

def encode (n : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x+n*encode n xs

def digit (n w j : Nat) := (w/n^j)%n
def entry (n : Nat) (rows : List Nat) (i j : Nat) := digit n (rows.getD i 0) j
def word {n : Nat} (m : Table n (Fin n)) (i : Fin n) :=
  encode n (List.ofFn fun j => (m i j).val)

theorem digit_encode {n : Nat} (hn : 0<n) (r : List Nat) (small : ∀ x∈r, x<n)
    (i : Nat) (hi : i<r.length) : digit n (encode n r) i = r[i] := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    have ha := small a List.mem_cons_self
    cases i with
    | zero => simp [digit,encode,Nat.add_mod, Nat.mod_eq_of_lt ha]
    | succ i =>
      rw [List.getElem_cons_succ]
      have rec := ih (fun x h => small x (List.mem_cons_of_mem _ h)) i (by simpa using hi)
      change ((a+n*encode n as)/n^(i+1))%n=_
      rw [pow_succ',← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hn,Nat.div_eq_of_lt ha, Nat.zero_add]
      exact rec

@[simp] theorem digit_word {n : Nat} [NeZero n] (m : Table n (Fin n)) (i j : Fin n) :
    digit n (word m i) j.val = (m i j).val := by
  unfold word
  rw [digit_encode (Nat.pos_of_ne_zero (NeZero.ne n)) _ (by simp [List.mem_ofFn]) _ (by simp)]
  simp

abbrev Tag := Nat × Nat × Nat

def signature (n u v : Nat) : Nat :=
  ∑ z : Fin n, 2 ^ (5 * (digit n u z.val * n + digit n v z.val))

def fact (n : Nat) (rs : List Nat) (i j : Nat) : Tag :=
  (entry n rs i j,entry n rs j i,signature n (rs.getD i 0) (rs.getD j 0))

def facts (n : Nat) (rs : List Nat) := (List.range rs.length).flatMap fun i =>
  (List.range rs.length).map fun j => fact n rs i j

def required (n : Nat) (rs : List Nat) (known : List Tag) : List (Option Nat) :=
  List.ofFn fun j : Fin n =>
    if j.val=rs.length then some (entry n rs 0 0)
    else if j.val<rs.length then (known.lookup (entry n rs j.val rs.length)).map Prod.fst else none

def arrange : List (Option Nat) → List Nat → List (List Nat)
  | [], _ => [[]]
  | opt::opts, left =>
    let names := match opt with
      | none => left.dedup
      | some v => if v ∈ left then [v] else []
    names.flatMap fun v => (arrange opts (left.erase v)).map (v :: ·)

def freshOK (n : Nat) (rs : List Nat) (known : List Tag) (w : Nat) : Bool :=
  let k := rs.length
  let ext := rs ++ [w]
  let fresh := (List.range (k+1)).flatMap fun i => [fact n ext i k, fact n ext k i]
  let allTags := known ++ fresh
  fresh.all fun v => allTags.lookup v.1 == some v.2

def nextRows (n : Nat) (rs : List Nat) : List Nat :=
  let known := facts n rs
  let first := List.ofFn fun j : Fin n => entry n rs 0 j.val
  ((arrange (required n rs known) first).map (encode n)).filter (freshOK n rs known)

def choices : List (List Nat) → List (List Nat)
  | [] => [[]]
  | ns::rest => ns.flatMap fun x => (choices rest).map (x :: ·)

def roots (n : Nat) : List Nat :=
  let limits := List.ofFn fun j : Fin n => if j.val=0 then [0] else (List.range j.val).map (·+1)
  ((choices limits).filter fun r => r.all (fun x => r.getD x 0 == x)).map (encode n)

structure Move where
  row : Nat
  child : Nat
  points : Nat
  colors : Nat
  deriving Inhabited

structure Node where
  rows : List Nat
  model : Nat
  pointMap : Nat
  moves : Array Move
  deriving Inhabited

private def readMoves (words : List Nat) : List Move := collect words []
where
  collect : List Nat → List Move → List Move
  | r::i::p::g::tail, acc => collect tail (⟨r,i,p,g⟩ :: acc)
  | _, acc => acc.reverse

def decode (s : String) : Array Node := ((s.splitOn "\n").map fun line =>
  let words := (line.splitOn " ").map String.toNat!
  let k := words.head!
  let tail := words.tail!.drop k
  ⟨words.tail!.take k, tail.getD 0 0, tail.getD 1 0,(readMoves (tail.drop 2)).toArray⟩).toArray

def mapOf (n : Nat) [NeZero n] (w : Nat) (i : Fin n) : Fin n :=
  ⟨digit n w i.val, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

abbrev Mono {n : Nat} [NeZero n] (w : Nat) :=
  ∀ i j : Fin n, mapOf n w i = mapOf n w j → i=j

def validMove (n : Nat) [NeZero n] (rs : List Nat) (target : Node) (t : Move) : Bool :=
  let ext := rs ++ [t.row]
  decide (target.rows.length=ext.length ∧ Mono (n:=n) t.points ∧ Mono (n:=n) t.colors ∧
    ∀ i j : Fin n, i.val<ext.length →
      mapOf n t.points i=i ∧ entry n target.rows i.val j.val =
        digit n t.colors (entry n ext i.val (mapOf n t.points j).val))

def findMove (node : Node) (w : Nat) :=
  node.moves.binSearch ⟨w,0,0,0⟩ (fun a b => a.row < b.row)

def verifiedBy {n h : Nat} [NeZero n] [NeZero h] (cells : Fin h → Table n Nat)
    (optionsFor : List Nat → List Nat) (nodes : Array Node) (i : Nat) : Bool :=
  let v := nodes[i]?.getD default
  if n ≤ v.rows.length then
    let f := mapOf n v.pointMap
    let a : Fin h := ⟨v.model%h,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne h))⟩
    decide (v.rows.length=n ∧ Mono (n:=n) v.pointMap ∧ ∀ j k x y : Fin n,
      cells a j k=cells a x y ↔ entry n v.rows (f j).val (f k).val=entry n v.rows (f x).val (f y).val)
  else
    let options := optionsFor v.rows
    options.all fun w => match findMove v w with
      | none => false
      | some t => t.row==w && t.child<nodes.size && validMove n v.rows (nodes[t.child]?.getD default) t

def verified {n h : Nat} [NeZero n] [NeZero h] (cells : Fin h → Table n Nat)
    (nodes : Array Node) (i : Nat) : Bool :=
  verifiedBy cells (fun rs => if rs.isEmpty then roots n else nextRows n rs) nodes i

end QGI.RowCensus
