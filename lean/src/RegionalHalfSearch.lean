import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace QGI.RegionalHalfSearch

/-- Exact-cardinality constraints on a subset of a finite collection. -/
structure Rule (X : Type) where
  keep : X → Bool
  need : Nat

def cut {X : Type} (q : Rule X) (s : Finset X) := s.filter fun x => q.keep x=true

def viable {X : Type} (q : Rule X) (e r : Finset X) : Bool :=
  decide ((cut q e).card≤q.need ∧ q.need≤(cut q e).card+(cut q r).card)

private def score {X : Type} (q : Rule X) (e r : Finset X) : Nat × Nat :=
  let s := (cut q r).card
  if s=0 then (2^r.card+1,0) else (Nat.choose s (q.need-(cut q e).card),r.card-s)

private def first {X : Type} {m : Nat} (q : Fin (m+1) → Rule X) (e r : Finset X) : Fin (m+1) :=
  ((List.finRange (m+1)).foldl (fun (best : Fin (m+1) × (Nat × Nat)) i =>
    let v := score (q i) e r
    if v.1<best.2.1 ∨ (v.1=best.2.1 ∧ v.2<best.2.2) then (i,v) else best) (0,score (q 0) e r)).1

def search {X : Type} [DecidableEq X] {m : Nat} (q : Fin (m+1) → Rule X) (accept : Finset X → Bool) :
    Nat → Finset X → Finset X → Bool
  | 0, e, r =>
    if r=∅ then accept e || !(List.finRange (m+1)).all (fun i => decide ((cut (q i) e).card=(q i).need)) else false
  | fuel+1, e, r =>
    if r=∅ then accept e || !(List.finRange (m+1)).all (fun i => decide ((cut (q i) e).card=(q i).need)) else
    if !(List.finRange (m+1)).all (fun i => viable (q i) e r) then true else
    let p := q (first q e r)
    let block := cut p r
    let choices := block.powersetCard (p.need-(cut p e).card)
    decide ((choices.filter (fun t => search q accept fuel (e∪t) (r\block)=false)).card=0)

private theorem bounds {X : Type} [DecidableEq X] (p : Rule X) (f e r : Finset X) (inside : e⊆f) (outside : f⊆e∪r)
    (fit : (cut p f).card=p.need) : viable p e r=true := by
  have left : cut p e⊆cut p f := Finset.filter_subset_filter _ inside
  have right : cut p f ⊆ cut p e ∪ cut p r := by
    intro x hx
    obtain ⟨hf,hx⟩ := Finset.mem_filter.mp hx
    rcases Finset.mem_union.mp (outside hf) with he|hr
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,hx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr,hx⟩)
  exact decide_eq_true ⟨(Finset.card_le_card left).trans_eq fit,
    fit.symm.le.trans ((Finset.card_le_card right).trans (Finset.card_union_le _ _))⟩

theorem sound {X : Type} [DecidableEq X] {m : Nat} (q : Fin (m+1) → Rule X) (accept : Finset X → Bool)
    (f : Finset X) (fit : ∀ i, (cut (q i) f).card=(q i).need) (fuel : Nat) (e r : Finset X)
    (disj : Disjoint e r) (ine : e⊆f) (out : f⊆e∪r) (checked : search q accept fuel e r=true) : accept f=true := by
  classical
  induction fuel generalizing e r with
  | zero =>
    by_cases hr : r=∅
    · subst r
      have same : f=e := Finset.Subset.antisymm (by simpa using out) ine
      subst f
      simpa [search,fit] using checked
    · simp [search,hr] at checked
  | succ fuel ih =>
    by_cases hr : r=∅
    · subst r
      have same : f=e := Finset.Subset.antisymm (by simpa using out) ine
      subst f
      simpa [search,fit] using checked
    have all : (List.finRange (m+1)).all (fun i => viable (q i) e r)=true :=
      List.all_eq_true.mpr (fun i _ => bounds (q i) f e r ine out (fit i))
    let key := first q e r
    let p := q key
    let s := cut p r
    let t := f∩s
    have eq : cut p f=cut p e∪t := by
      ext x
      constructor
      · intro hx
        obtain ⟨hf,h⟩ := Finset.mem_filter.mp hx
        rcases Finset.mem_union.mp (out hf) with he|hr
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hf,Finset.mem_filter.mpr ⟨hr,h⟩⟩)
      · intro hx
        rcases Finset.mem_union.mp hx with he|ht
        · exact (Finset.filter_subset_filter _ ine) he
        · obtain ⟨hf,hm⟩ := Finset.mem_inter.mp ht; exact Finset.mem_filter.mpr ⟨hf,(Finset.mem_filter.mp hm).2⟩
    have sep : Disjoint (cut p e) t := Finset.disjoint_left.mpr fun _ he ht =>
      Finset.disjoint_left.mp disj (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp (Finset.mem_inter.mp ht).2).1
    have count : t.card=p.need-(cut p e).card := by
      have h := fit key
      change (cut p f).card=p.need at h
      rw [eq,Finset.card_union_of_disjoint sep] at h
      omega
    have belongs : t∈s.powersetCard (p.need-(cut p e).card) := Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right,count⟩
    have test : ((s.powersetCard (p.need-(cut p e).card)).filter (fun u => search q accept fuel (e∪u) (r\s)=false)).card=0 := by
      simpa [search,hr,all,key,s,p] using checked
    have next : search q accept fuel (e∪t) (r\s)=true := by
      by_contra no
      exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨belongs,Bool.eq_false_of_not_eq_true no⟩⟩) test
    apply ih (e∪t) (r\s) _ (Finset.union_subset ine Finset.inter_subset_left) _ next
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨hr,no⟩ := Finset.mem_sdiff.mp hy
      exact (Finset.mem_union.mp hx).elim (fun he => Finset.disjoint_left.mp disj he hr)
        (fun ht => no (Finset.mem_inter.mp ht).2)
    · intro x hx
      rcases Finset.mem_union.mp (out hx) with he|hr
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
      · by_cases hs : x∈s
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx,hs⟩))
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hr,hs⟩)

end QGI.RegionalHalfSearch

