import data.ZivAvEightTwelveHalf
import RegionalEightTwelveCatalog
import RegionalHalfSearch

namespace QGI.EightTwelveHalf
open EightTwelveCatalog (Row cell row)
abbrev P := Fin 8
abbrev C := Finset P
abbrev Family := Finset C

def decode (s : Nat) : C := Finset.univ.filter fun i => s.testBit i.val=true
def unpack (xs : List Nat) : Family := (xs.map decode).toFinset
def model (m : Fin 5) : Family := unpack ((prototypes[m.val]?).getD [])
def perm (w : Witness) (i : P) : P := Fin.ofNat' 8 (EightTwelveCatalog.digit w.mapWord i.val)
def valid (w : Witness) := decide (Function.Injective (perm w) ∧
  (unpack w.masks).image (fun s => s.image (perm w))=model w.model)
def candidates : Family := Finset.univ.powersetCard 4
def outer (s : C) : P := ((List.finRange 8).find? (fun i => decide (i∉s))).getD 0

def count (r : Row) (s : C) (i : P) (v : Nat) := (s.filter fun j => cell r i j=v).card
def valency (r : Row) (v : Nat) := count r Finset.univ 0 v
def allow (r : Row) (s t : C) := decide (∀ (i j : P),
  count r t i (cell r 0 j)=count r s (if i∈t then 0 else outer s) (cell r 0 j))
def same (r : Row) (s t : C) := decide (∀ j : P,
  count r s 0 (cell r 0 j)=count r t 0 (cell r 0 j) ∧
  count r s (outer s) (cell r 0 j)=count r t (outer t) (cell r 0 j))
def divisible (r : Row) (s : C) (m : Nat) := decide (∀ i j : P,
  valency r (cell r i j)*m ∣ 6*count r s 0 (cell r i j))
def seeds (a : Fin 21) := (((seedRows[a.val]?).getD []).map decode).toFinset

def rule (r : Row) (s : C) (m : Nat) (z : Fin 65) : RegionalHalfSearch.Rule C :=
  if z.val=0 then ⟨fun _ => true,12/m⟩ else
  let i : P := Fin.ofNat' 8 ((z.val-1)/8)
  let j : P := Fin.ofNat' 8 ((z.val-1)%8)
  let v := cell r i j
  ⟨fun t => decide (i∈t ∧ j∈t),6*count r s 0 v/(valency r v*m)⟩

def hist (f : Family) (s : C) (i : P) (k : Nat) :=
  (f.filter fun t => (s∩t).card=k ∧ i∈t).card
def Uniform (f : Family) := ∀ s∈f, ∀ t∈f, ∀ i j : P, (i∈s ↔ j∈t) →
  ∀ k : Fin 5, hist f s i k.val=hist f t j k.val
instance (f : Family) : Decidable (Uniform f) := by unfold Uniform; infer_instance
def witnessed (f : Family) := witnesses.any fun w => decide (f=unpack w.masks)
def gram (f : Family) (i j : P) := (f.filter fun t => i∈t ∧ j∈t).card
def Separates (r : Row) (f : Family) :=
  Function.Injective (fun i : P => f.filter (fun t => i∈t)) →
  ∀ i j x y : P, gram f i j=gram f x y → cell r i j=cell r x y
instance (r : Row) (f : Family) : Decidable (Separates r f) := by unfold Separates Function.Injective; infer_instance
def accept (r : Row) (f : Family) := (witnessed f && decide (Separates r f)) || !decide (Uniform f)

def run (r : Row) (s : C) (m : Nat) :=
  !divisible r s m || RegionalHalfSearch.search (rule r s m) (accept r) 65 ∅ (candidates.filter fun t => allow r s t=true)
def covers (a : Fin 21) (s : C) :=
  let r := row 8 a.val
  (0:P)∉s ∨ allow r s s=false ∨ divisible r s 1=false ∨ ∃ t∈seeds a, same r s t=true
instance (a : Fin 21) (s : C) : Decidable (covers a s) := by unfold covers; infer_instance

def checked (a : Fin 21) :=
  let r := row 8 a.val
  decide (∀ s∈candidates, covers a s) &&
  decide (∀ t∈seeds a, ∀ m∈([1,2,3,6] : List Nat), run r t m=true)

attribute [local irreducible] EightTwelveCatalog.rows8 EightTwelveCatalog.rows12 EightTwelveCatalog.row
  seedRows prototypes witnesses

set_option maxRecDepth 20000 in
private theorem witness_check : witnesses.all valid=true := by native_decide

set_option maxRecDepth 20000 in
private theorem exhaust : ∀ a : Fin 21, checked a=true := by native_decide

theorem model_of_constraints (a : Fin 21) (r := row 8 a.val) (hr : r=row 8 a.val)
    (s : C) (f : Family) (m : Nat) (mass : m∈([1,2,3,6] : List Nat))
    (balance : s∈candidates) (zero : (0:P)∈s) (self : allow r s s=true)
    (one : divisible r s 1=true) (eqs : ∀ t∈seeds a, same r s t=true →
      divisible r t m=true ∧ f⊆candidates.filter (fun b => allow r t b=true) ∧
      ∀ z, (RegionalHalfSearch.cut (rule r t m z) f).card=(rule r t m z).need)
    (histogram : Uniform f) : Separates r f ∧ ∃ h : Fin 5, ∃ e : Equiv.Perm P, f.image (fun t => t.image e)=model h := by
  subst r
  obtain ⟨cover,all⟩ := (by simpa only [checked,Bool.and_eq_true,decide_eq_true_eq] using exhaust a :
    (∀ s∈candidates, covers a s) ∧ ∀ t∈seeds a, ∀ m∈([1,2,3,6] : List Nat), run (row 8 a.val) t m=true)
  obtain ⟨t,mem,agree⟩ : ∃ t∈seeds a, same (row 8 a.val) s t=true := by
    simpa only [covers,zero,self,one,not_true_eq_false,Bool.true_eq_false,or_false,false_or] using cover s balance
  obtain ⟨divs,inside,fit⟩ := eqs t mem agree
  have search := all t mem m mass
  simp only [run,divs,Bool.not_true,false_or,Bool.false_or] at search
  have hit := RegionalHalfSearch.sound _ _ f fit 65 ∅ _ (Finset.disjoint_empty_left _) (Finset.empty_subset _)
    (by simpa using inside) search
  obtain ⟨hw,sep⟩ : witnessed f=true ∧ Separates (row 8 a.val) f := by simpa [accept,histogram] using hit
  obtain ⟨w,found,eq⟩ := List.any_eq_true.mp hw
  obtain ⟨mono,rep⟩ := of_decide_eq_true (List.all_eq_true.mp witness_check _ found)
  exact ⟨sep,w.model,Equiv.ofBijective (perm w) (Finite.injective_iff_bijective.mp mono),by rwa [of_decide_eq_true eq]⟩

end QGI.EightTwelveHalf

