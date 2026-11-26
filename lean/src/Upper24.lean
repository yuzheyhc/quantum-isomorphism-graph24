import Lean
import GraphTypes
import Mathlib.Data.Fintype.Basic

/-!
The explicit Atserias et al. 24-vertex magic-square pair.
A matrix entry of the integer-valued numerator table represents four times
the corresponding operator entry on C^4. Only integer arithmetic occurs below.
The finite computations use native_decide, which trusts Lean's native
compiler. No classical choice is invoked by the finite decision procedures.
-/
namespace Upper24
set_option maxHeartbeats 0
set_option maxRecDepth 16384

abbrev V := Fin 24
abbrev M := Nat → Nat → Int

def delta (i j : Nat) : Int := if i = j then 1 else 0
def xpos (i j : Nat) : Int := if i + j = 1 then 1 else 0
def zpos (i j : Nat) : Int :=
  if i = j then (if i = 0 then 1 else -1) else 0
def zx (i j : Nat) : Int := (if i = 0 then 1 else -1) * xpos i j
def kron (a b : M) : M := fun i j =>
  a (i/2) (j/2) * b (i%2) (j%2)

def obs : Nat → M
  | 0 => kron zpos delta
  | 1 => kron delta zpos
  | 2 => kron zpos zpos
  | 3 => kron delta xpos
  | 4 => kron xpos delta
  | 5 => kron xpos xpos
  | 6 => kron zpos xpos
  | 7 => kron xpos zpos
  | _ => fun i j => -(kron zx zx i j)

def cell (c t : Nat) : Nat :=
  if c < 3 then 3*c + t else c-3 + 3*t

def bitAt (twisted : Bool) (x t : Nat) : Nat :=
  let b := x % 4
  let p := if twisted && (x/4 == 5) then 1 else 0
  if t = 0 then b/2 else if t = 1 then b%2 else (b/2 + b%2 + p)%2

/-- Equality, inconsistency on a shared cell, distinct consistent assignments. -/
def kind (twisted : Bool) (x y : V) : Nat :=
  if x = y then 0
  else if (List.range 3).any (fun i => (List.range 3).any (fun j =>
        cell (x.val/4) i == cell (y.val/4) j &&
          bitAt twisted x.val i != bitAt twisted y.val j)) then 1
  else 2

theorem simpleKinds : ∀ b : Bool, ∀ x y : V,
    (kind b x y = 0 ↔ x = y) ∧ kind b x y = kind b y x := by
  native_decide

def sign (n : Nat) : Int := if n % 2 = 0 then 1 else -1

def mul (a b : M) (i j : Nat) : Int :=
  a i 0*b 0 j + a i 1*b 1 j + a i 2*b 2 j + a i 3*b 3 j

/-- Numerator of u_(x,a); the actual projection is this matrix divided by 4. -/
def num (x a : Nat) : M :=
  if x/4 = a/4 then
    let c := x/4
    let factor := fun t i j =>
      delta i j + sign (bitAt false x t + bitAt true a t) * obs (cell c t) i j
    mul (factor 0) (factor 1)
  else fun _ _ => 0

def sum24 (f : Nat → Int) : Int :=
  (List.range 24).foldl (fun s n => s + f n) 0

theorem projectors : ∀ x a : V, ∀ i j : Fin 4,
    num x.val a.val i.val j.val = num x.val a.val j.val i.val ∧
    mul (num x.val a.val) (num x.val a.val) i.val j.val =
        4 * num x.val a.val i.val j.val := by
  native_decide

theorem rowColumn : ∀ x : V, ∀ i j : Fin 4,
    sum24 (fun a => num x.val a i.val j.val) = 4 * delta i.val j.val ∧
    sum24 (fun a => num a x.val i.val j.val) = 4 * delta i.val j.val := by
  native_decide

/-- For graph-game types, this includes same-row and same-column orthogonality. -/
theorem mismatch : ∀ x a y b : V,
    kind false x y ≠ kind true a b → ∀ i j : Fin 4,
    mul (num x.val a.val) (num y.val b.val) i.val j.val = 0 := by
  native_decide

abbrev consistent (s : Bool) (x y : V) := kind s x y = 2

/-- Nesting constraints before the next existential prunes impossible tuples. -/
def HasSix (s : Bool) : Prop :=
  ∃ a b : V, consistent s a b ∧
    ∃ c : V, consistent s a c ∧ consistent s b c ∧
    ∃ d : V, consistent s a d ∧ consistent s b d ∧ consistent s c d ∧
    ∃ e : V, consistent s a e ∧ consistent s b e ∧ consistent s c e ∧
      consistent s d e ∧
    ∃ f : V, consistent s a f ∧ consistent s b f ∧ consistent s c f ∧
      consistent s d f ∧ consistent s e f

set_option synthInstance.maxSize 8192 in
instance (s : Bool) : Decidable (HasSix s) := by
  unfold HasSix consistent
  infer_instance

theorem evenHas : HasSix false := by
  refine ⟨0,4,?_,8,?_,?_,12,?_,?_,?_,16,?_,?_,?_,?_,20,?_,?_,?_,?_,?_⟩ <;> decide

theorem oddHasNot : ¬ HasSix true := by native_decide

/-- In particular the graphs are nonisomorphic: any graph isomorphism
preserves the three kinds (equality, edge, distinct nonedge). -/
theorem noTypePreservingMap :
    ¬ ∃ F : V → V, ∀ x y : V, kind false x y = kind true (F x) (F y) := by
  intro h
  obtain ⟨F,hF⟩ := h
  have push {x y : V} (hc : consistent false x y) : consistent true (F x) (F y) :=
    (hF x y).symm.trans hc
  obtain ⟨a,b,ab,c,ac,bc,d,ad,bd,cd,e,ae,be,ce,de,
    f,af,bf,cf,df,ef⟩ := evenHas
  exact oddHasNot ⟨F a,F b,push ab,F c,push ac,push bc,F d,push ad,push bd,
    push cd,F e,push ae,push be,push ce,push de,F f,push af,push bf,push cf,
    push df,push ef⟩


/-- The third kind is completely determined by inequality and absence of an edge. -/
theorem thirdKind : ∀ s : Bool, ∀ x y : V,
    x ≠ y → kind s x y ≠ 1 → kind s x y = 2 := by
  native_decide

/-- The adjacency of our *uncolored* simple graphs is the kind-1 relation.
Even an injective map preserving adjacency in both directions is impossible. -/
theorem noClassicalIso :
    ¬ ∃ F : V → V,
      (∀ x y, F x = F y → x = y) ∧
      (∀ x y, kind false x y = 1 ↔ kind true (F x) (F y) = 1) := by
  intro h
  obtain ⟨F, inj, edges⟩ := h
  apply noTypePreservingMap
  refine ⟨F, ?_⟩
  intro x y
  by_cases eq : x = y
  · exact ((simpleKinds false x y).1.mpr eq).trans
      ((simpleKinds true (F x) (F y)).1.mpr (congrArg F eq)).symm
  · by_cases edge : kind false x y = 1
    · exact edge.trans ((edges x y).mp edge).symm
    · have nonEq : F x ≠ F y := fun same => eq (inj x y same)
      have nonEdge : kind true (F x) (F y) ≠ 1 :=
        fun adjacent => edge ((edges x y).mpr adjacent)
      exact (thirdKind false x y eq edge).trans
        (thirdKind true (F x) (F y) nonEq nonEdge).symm


def edge (s : Bool) (x y : V) : Bool := decide (kind s x y = 1)

theorem edgeLaws : ∀ s : Bool, ∀ x y : V,
    edge s x y = edge s y x ∧ edge s x x = false := by native_decide

/-- Both sides are genuine instances of the project's simple-graph type. -/
def graph (s : Bool) : QGI.Graph 24 where
  edge := edge s
  symm x y := (edgeLaws s x y).1
  loopless x := (edgeLaws s x x).2

theorem graphsNotIsomorphic : ¬ QGI.Isomorphic (graph false) (graph true) := by
  intro hi
  obtain ⟨e⟩ := hi
  apply noClassicalIso
  refine ⟨e.toFun, ?_, ?_⟩
  · intro x y he
    have same := congrArg e.invFun he
    simpa only [e.leftInv] using same
  · intro x y
    have he := e.edge_eq x y
    change decide (kind false x y = 1) =
      decide (kind true (e.toFun x) (e.toFun y) = 1) at he
    constructor
    · intro hs
      by_cases ht : kind true (e.toFun x) (e.toFun y) = 1
      · exact ht
      · simp [hs, ht] at he
    · intro ht
      by_cases hs : kind false x y = 1
      · exact hs
      · simp [hs, ht] at he

end Upper24
