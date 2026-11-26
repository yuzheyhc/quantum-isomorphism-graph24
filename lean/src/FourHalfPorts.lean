import FourHalfCore

namespace QGI.FourHalfCatalog

abbrev Old := Eight ⊕ Eight
abbrev Site := Old ⊕ Four
def oldIndex : Old ≃ Fin 16 := finSumFinEquiv
def number : Site ≃ W := (Equiv.sumCongr oldIndex (Equiv.refl Four)).trans finSumFinEquiv
abbrev X (i : Eight) : Site := .inl (.inl i)
abbrev Y (i : Eight) : Site := .inl (.inr i)
abbrev F (i : Four) : Site := .inr i
def half (s : Nat) (rev : Bool) (i : Four) (j : Eight) := decide (i.val%2=(xor (side s j) rev).toNat)

inductive Port
  | old (i j : Old)
  | xf (i : Eight) (j : Four)
  | yf (i : Eight) (j : Four)
  | fx (i : Four) (j : Eight)
  | fy (i : Four) (j : Eight)
  | ff (i j : Four)

def port : Site → Site → Port
  | .inl i, .inl j => .old i j
  | .inl (.inl i), .inr j => .xf i j
  | .inl (.inr i), .inr j => .yf i j
  | .inr i, .inl (.inl j) => .fx i j
  | .inr i, .inl (.inr j) => .fy i j
  | .inr i, .inr j => .ff i j

def Port.ends : Port → Site × Site
  | .old i j => (.inl i,.inl j)
  | .xf i j => (X i,F j)
  | .yf i j => (Y i,F j)
  | .fx i j => (F i,X j)
  | .fy i j => (F i,Y j)
  | .ff i j => (F i,F j)

theorem unpack : ∀ i j, (port i j).ends=(i,j) := by rintro ((i|i)|i) ((j|j)|j) <;> rfl

def Port.word (a : Key) (sw : Bool) (q s : Nat) (p : Bool) : Port → Nat
  | .old i j => base a sw (oldIndex i) (oldIndex j)
  | .xf i j => 100+(hit j (cycle q i)).toNat
  | .yf i j => 102+(half s p j i).toNat
  | .fx i j => 104+(hit i (cycle q j)).toNat
  | .fy i j => 106+(half s p i j).toNat
  | .ff i j => 108+pos i j

private theorem indexFacts :
    (∀ i, (number (X i)).val<8 ∧ (number (X i)).val<16 ∧ Fin.ofNat' 8 (number (X i)).val=i ∧ Fin.ofNat' 16 (number (X i)).val=oldIndex (.inl i)) ∧
    (∀ i, ¬(number (Y i)).val<8 ∧ (number (Y i)).val<16 ∧ Fin.ofNat' 8 (number (Y i)).val=i ∧ Fin.ofNat' 16 (number (Y i)).val=oldIndex (.inr i)) ∧
    ∀ i, ¬(number (F i)).val<8 ∧ ¬(number (F i)).val<16 ∧ Fin.ofNat' 4 (number (F i)).val=i := by decide

theorem word_read (a : Key) (sw : Bool) (q s : Nat) (p : Bool) (u : Port) :
    value a sw q s p (number u.ends.1) (number u.ends.2)=u.word a sw q s p := by
  obtain ⟨xh,yh,fh⟩ := indexFacts
  cases u with
  | old i j =>
    have lower (z : Old) : (number (.inl z)).val<16 ∧ Fin.ofNat' 16 (number (.inl z)).val=oldIndex z := by
      cases z with
      | inl i => exact ⟨(xh i).2.1,(xh i).2.2.2⟩
      | inr i => exact ⟨(yh i).2.1,(yh i).2.2.2⟩
    simp only [Port.ends,Prod.fst,Prod.snd,value,Port.word,(lower i).1,(lower j).1,(lower i).2,(lower j).2,if_true]
  | xf i j =>
    simp only [Port.ends,Prod.fst,Prod.snd,value,Port.word,(xh i).1,(xh i).2.1,(fh j).2.1,(xh i).2.2.1,(fh j).2.2,if_true,if_false]
  | yf i j =>
    simp only [Port.ends,Prod.fst,Prod.snd,value,Port.word,half,(yh i).1,(yh i).2.1,(fh j).2.1,(yh i).2.2.1,(fh j).2.2,if_true,if_false]
  | fx i j =>
    simp only [Port.ends,Prod.fst,Prod.snd,value,Port.word,(fh i).2.1,(xh j).1,(xh j).2.2.1,(fh i).2.2,if_true,if_false]
  | fy i j =>
    simp only [Port.ends,Prod.fst,Prod.snd,value,Port.word,half,(fh i).2.1,(yh j).1,(yh j).2.1,(yh j).2.2.1,(fh i).2.2,if_true,if_false]
  | ff i j =>
    simp only [Port.ends,Prod.fst,Prod.snd,value,Port.word,(fh i).2.1,(fh j).1,(fh j).2.1,(fh i).2.2,(fh j).2.2,if_false]

def Port.kind : Port → Nat
  | .old .. => 0 | .xf .. => 1 | .yf .. => 2 | .fx .. => 3 | .fy .. => 4 | .ff .. => 5

def wordKind (w : Nat) := if w<100 then 0 else if w<102 then 1 else if w<104 then 2 else if w<106 then 3 else if w<108 then 4 else 5
attribute [local irreducible] DoubleEight.Prepared.row
theorem base_lt : ∀ (a : Key) (sw : Bool) (i j : Fin 16), base a sw i j<100 := by native_decide

theorem kind_of_word (a : Key) (sw : Bool) (q s : Nat) (p : Bool) (u : Port) :
    wordKind (u.word a sw q s p)=u.kind := by
  have boolBound (b : Bool) : b.toNat≤1 := by cases b <;> decide
  cases u with
  | old i j => simp only [Port.word,Port.kind,wordKind,base_lt,if_true]
  | xf i j => have := boolBound (hit j (cycle q i)); simp only [Port.word,Port.kind,wordKind]; split_ifs <;> omega
  | yf i j => have := boolBound (half s p j i); simp only [Port.word,Port.kind,wordKind]; split_ifs <;> omega
  | fx i j => have := boolBound (hit i (cycle q j)); simp only [Port.word,Port.kind,wordKind]; split_ifs <;> omega
  | fy i j => have := boolBound (half s p i j); simp only [Port.word,Port.kind,wordKind]; split_ifs <;> omega
  | ff i j => simp only [Port.word,Port.kind,wordKind]; split_ifs <;> omega

end QGI.FourHalfCatalog
