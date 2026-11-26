import RegionalTetraLayout
import TernaryVectorChoice

noncomputable section
namespace QGI.Coherent.RegionalTetraTriples
open SixTenCoordinates StrategyColorLaws RegionalSixTwelveStats RegionalTetraLayout
open FourTwelveCycle (Edge edge)
open RegionalSixTwelveGeometry (Point)
open FourTwelveFunctional (source)
open private all_pairs from DoubledEdges

abbrev Vertex := Face × Slot
abbrev Table := Vertex → Vertex → Nat

def degree (m : Table) (s : Nat) (j : Vertex) (q : Face) :=
  (Finset.univ.filter (fun k : Slot => m j (q,k)=s)).card

private theorem doubled_degree (row : Face → Nat) (q : Face) (b : Nat)
    (sums : ∀ e : Edge, q∉edge e → ∑ t∈edge e, row t=b) (t : Face) (ne : t≠q) : 2*row t=b := by
  obtain ⟨u,w,uq,wq,tu,tw,uw⟩ := (show ∀ q t : Face, t≠q →
    ∃ u w : Face, u≠q ∧ w≠q ∧ t≠u ∧ t≠w ∧ u≠w by decide) q t ne
  have add (i j : Face) (iq : i≠q) (jq : j≠q) (ij : i≠j) : row i+row j=b := by
    obtain ⟨e,he⟩ := all_pairs i j ij
    have h := sums e (by simp [he,iq.symm,jq.symm])
    simpa only [he,Finset.sum_pair ij] using h
  have a := add t u ne uq tu
  have c := add t w ne wq tw
  have d := add u w uq wq uw
  omega

private theorem expand (m : Table) (s : Nat) (j : Vertex) (e : Edge) :
    (∑ t : Vertex, if m j t=s ∧ t.1∈edge e then 1 else 0)=∑ q∈edge e, degree m s j q := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ q : Face, if q∈edge e then degree m s j q else 0 := Finset.sum_congr rfl (fun q _ => by
      by_cases h : q∈edge e <;> simp [h,degree])
    _ = _ := by rw [←Finset.sum_filter]; simp

def table {n l r : Nat} {c : Fin n → Fin n → Nat} {F : Shore c l Point} {Y : Shore c r Right}
    {v w : Nat} (P : Layout F Y v w) : Table :=
  fun i j => c (atPoint Y (P.right i)) (atPoint Y (P.right j))

def turn (rev : Bool) (m : Table) : Table := if rev then fun x y => m y x else m

theorem degree_corresponds {n l r : Nat} {c d : Fin n → Fin n → Nat} (law : Laws c d)
    {F : Shore c l Point} {Y : Shore c r Right} {T : Shore d l Point} {Z : Shore d r Right}
    {v w : Nat} (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w)
    (rev : Bool) (s : Nat) (i j : Vertex) (t u : Face) (ti : t≠i.1) (uj : u≠j.1) :
    degree (turn rev (table P)) s i t=degree (turn rev (table Q)) s j u := by
  let A := P.right.trans Y
  let B := Q.right.trans Z
  let L := P.left.trans F
  let R := Q.left.trans T
  have rect : Block A B A B (fun x y => decide (turn rev (table P) x y=s)) (fun x y => decide (turn rev (table Q) x y=s)) := by
    intro i j x y h
    cases rev with
    | false => exact congrArg (fun t => decide (t=s)) h
    | true => exact congrArg (fun t => decide (t=s)) (law.rev h)
  have inc : Block A B L R (fun x e => decide (x.1∈edge e)) (fun y f => decide (y.1∈edge f)) := by
    intro ⟨a,k⟩ e ⟨b,t⟩ f hit
    change color F Y (P.right (a,k)) (P.left e)=color T Z (Q.right (b,t)) (Q.left f) at hit
    rw [P.names,Q.names] at hit
    by_cases ha : a∈edge e <;> by_cases hb : b∈edge f <;> simp_all
  have value {x y : Vertex} {e f : Edge} (no : x.1∉edge e) (nt : y.1∉edge f) :
      ∑ a∈edge e, degree (turn rev (table P)) s x a=∑ b∈edge f, degree (turn rev (table Q)) s y b := by
    have hit : c (atPoint A x) (atPoint L e)=d (atPoint B y) (atPoint R f) := by
      obtain ⟨a,k⟩ := x; obtain ⟨b,t⟩ := y
      exact ((P.names a k e).trans (if_neg no)).trans ((Q.names b t f).trans (if_neg nt)).symm
    have folded := Block.fold law rect inc (fun v w => if v=true ∧ w=true then 1 else 0) hit
    simpa only [decide_eq_true_eq,expand] using folded
  have missed : ∀ x : Face, ∃ e : Edge, x∉edge e := by decide
  obtain ⟨e,he⟩ := missed i.1
  obtain ⟨f,hf⟩ := missed j.1
  let k := ∑ t∈edge f, degree (turn rev (table Q)) s j t
  have a := doubled_degree (degree (turn rev (table P)) s i) i.1 k (fun e he => value he hf) t ti
  have b := doubled_degree (degree (turn rev (table Q)) s j) j.1 k (fun f' hf' => (value he hf').symm.trans (value he hf)) u uj
  omega

def Uniform (m : Table) (s : Nat) := ∀ a b : Face, a≠b → ∀ i j : Slot, m (a,i) (b,j)=s
def Match (m : Table) (s : Nat) := ∀ a b : Face, a≠b → ∃ e : Equiv.Perm Slot,
  ∀ i j : Slot, m (a,i) (b,j)=s ↔ e i=j

private theorem matrix_perm : ∀ u : Slot → Slot → Bool,
    (∀ i, (Finset.univ.filter (fun j => u i j=true)).card=1) →
    (∀ j, (Finset.univ.filter (fun i => u i j=true)).card=(Finset.univ.filter (fun i => u i 0=true)).card) →
    ∃ e : Equiv.Perm Slot, ∀ i j, u i j=true ↔ e i=j := by native_decide

private theorem row_split (u : Slot → Nat) : (∀ i, u i=u 0) ∨ ∃ k, (Finset.univ.filter (fun j => u j=u k)).card=1 := by
  by_cases a : u 0=u 1
  · by_cases b : u 0=u 2
    · left; intro i; fin_cases i <;> simp_all
    · right; refine ⟨2,?_⟩
      have eq : Finset.univ.filter (fun j => u j=u 2)={2} := by ext i; fin_cases i <;> simp_all
      rw [eq,Finset.card_singleton]
  · by_cases b : u 0=u 2
    · right; refine ⟨1,?_⟩
      have eq : Finset.univ.filter (fun j => u j=u 1)={1} := by ext i; fin_cases i <;> simp_all
      rw [eq,Finset.card_singleton]
    · right; refine ⟨0,?_⟩
      have eq : Finset.univ.filter (fun j => u j=u 0)={0} := by ext i; fin_cases i <;> simp_all [Ne.symm a,Ne.symm b]
      rw [eq,Finset.card_singleton]

theorem off_diagonal {n l r : Nat} {c d : Fin n → Fin n → Nat} (src : Laws c c) (dst : Laws d d) (law : Laws c d)
    {F : Shore c l Point} {Y : Shore c r Right} {T : Shore d l Point} {Z : Shore d r Right}
    {v w : Nat} (vw : v≠w) (P : Layout F Y v w) (Q : Layout T Z v w) :
    (∃ s, Uniform (table P) s ∧ Uniform (table Q) s) ∨ (∃ s, Match (table P) s ∧ Match (table Q) s) := by
  let base := fun j : Slot => table P (0,0) (1,j)
  have source (s) (i : Vertex) (a : Face) (ne : a≠i.1) : degree (table P) s i a=degree (table P) s (0,0) 1 :=
    degree_corresponds src vw P P false s i (0,0) a 1 ne (by decide)
  have target (s) (i : Vertex) (a : Face) (ne : a≠i.1) : degree (table Q) s i a=degree (table P) s (0,0) 1 :=
    (degree_corresponds law vw P Q false s (0,0) i 1 a (by decide) ne).symm
  rcases row_split base with all|⟨i,one⟩
  · left
    have basic : degree (table P) (base 0) (0,0) 1=3 := by
      change (Finset.univ.filter (fun j => base j=base 0)).card=3; simp [all]
    have get (m : Table) (h : ∀ (i : Vertex) a, a≠i.1 → degree m (base 0) i a=3) : Uniform m (base 0) := by
      intro a b ne i j
      have eq := Finset.eq_univ_of_card (Finset.univ.filter (fun k => m (a,i) (b,k)=base 0)) (h (a,i) b ne.symm)
      have incl : j∈Finset.univ.filter (fun k => m (a,i) (b,k)=base 0) := by rw [eq]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp incl).2
    exact ⟨base 0,get _ (fun i a ne => (source _ i a ne).trans basic),get _ (fun i a ne => (target _ i a ne).trans basic)⟩
  · right
    let s := base i
    have get (m : Table) (row : ∀ (j : Vertex) a, a≠j.1 → degree m s j a=1)
        (col : ∀ (a b : Face), a≠b → ∀ j : Slot, degree (turn true m) s (b,j) a=degree (turn true m) s (b,0) a) :
        Match m s := by
      intro a b ne
      let binary := fun i j : Slot => decide (m (a,i) (b,j)=s)
      obtain ⟨e,he⟩ := matrix_perm binary (fun i => by simpa only [binary,decide_eq_true_eq] using row (a,i) b ne.symm)
        (fun j => by simpa only [binary,decide_eq_true_eq] using col a b ne j)
      exact ⟨e,fun i j => by simpa only [binary,decide_eq_true_eq] using he i j⟩
    exact ⟨s,get _ (fun j a ne => (source s j a ne).trans one)
      (fun a b ne j => degree_corresponds src vw P P true s (b,j) (b,0) a a ne ne),
      get _ (fun j a ne => (target s j a ne).trans one)
      (fun a b ne j => degree_corresponds dst vw Q Q true s (b,j) (b,0) a a ne ne)⟩

end QGI.Coherent.RegionalTetraTriples

