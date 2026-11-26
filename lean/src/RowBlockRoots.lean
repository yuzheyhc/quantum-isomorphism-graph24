import RowCensusSound

namespace QGI.RowCensus

def blockLists (j prev : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k+1 => (if j≤1 then [j] else [prev,j]).flatMap fun x =>
      (blockLists (j+1) x k).map (x :: ·)
termination_by k => k

def blockRoots (n : Nat) := (blockLists 0 0 n).map (encode n)

private theorem gen {n : Nat} (f : Nat → Nat)
    (step : ∀ j, j<n → f j=j ∨ (1<j ∧ f j=f (j-1))) (k start prev : Nat)
    (le : start+k≤n) (hp : start=0 ∨ prev=f (start-1)) :
    (List.ofFn fun j : Fin k => f (start+j.val))∈blockLists start prev k := by
  induction k generalizing start prev with
  | zero => simp [blockLists]
  | succ k ih =>
    rw [List.ofFn_succ,blockLists]
    simp only [Fin.val_zero,Nat.add_zero,List.mem_flatMap,List.mem_map]
    refine ⟨f start,?_,_,ih (start+1) (f start) (by omega) (Or.inr (by simp)),?_⟩
    · rcases step start (by omega) with e|⟨a,b⟩
      · split <;> simp [e]
      · rcases hp with rfl|hp
        · omega
        · simp [show ¬start≤1 by omega,hp,b]
    · simp only [List.cons.injEq,true_and]
      congr 1
      funext i
      congr 1
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Sort the first row after moving its diagonal class to the smallest color.
Renaming each block by its first position leaves at most two choices at every
later position: repeat the last color, or begin a new block. -/
theorem normalize_blocks {n : Nat} [NeZero n] (c : Table n Nat) (h : Laws c) :
    ∃ (m : Matrix n) (p : Equiv.Perm (Fin n)) (g : Nat → Fin n), Laws m ∧ word m 0∈blockRoots n ∧
      (∀ i j, m i j=g (c (p i) (p j))) ∧
      ∀ i j x y, m i j=m x y ↔ c (p i) (p j)=c (p x) (p y) := by
  classical
  let code (a : Nat) := if a=c 0 0 then 0 else a+1
  have inject : Function.Injective code := by
    intro a b eq
    unfold code at eq
    split_ifs at eq <;> omega
  let f (j : Fin n) := code (c 0 j)
  let p := Tuple.sort f
  have mono : Monotone (f ∘ p) := Tuple.monotone_sort f
  have f0 : f 0=0 := by simp [f,code]
  have z : f (p 0)≤0 := by simpa [Function.comp_def,f0] using mono (show (0 : Fin n) ≤ p.symm 0 from Nat.zero_le _)
  have p0 : p 0=0 := ((h.diagonal 0 _).mp (inject ((Nat.eq_zero_of_le_zero z).trans f0.symm))).symm
  let s : Table n Nat := fun i j => code (c (p i) (p j))
  have hs : Laws s := h.transport p code (fun _ _ _ _ e => inject e)
  have sorted : Monotone (s 0) := by simpa [s,p0,f,Function.comp_def] using mono
  let fiber (a : Nat) := Finset.univ.filter (fun j : Fin n => s 0 j=a)
  have occurs (i j : Fin n) : (fiber (s i j)).Nonempty := by
    obtain ⟨y,hy⟩ := List.mem_ofFn.mp ((hs.row_perm i).mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
    exact ⟨y,by simpa [fiber] using hy⟩
  let label (a : Nat) : Fin n := if ha : (fiber a).Nonempty then (fiber a).min' ha else 0
  have spec (i j : Fin n) : s 0 (label (s i j))=s i j := by
    simpa [label,fiber,occurs] using (fiber (s i j)).min'_mem (occurs i j)
  let m : Matrix n := fun i j => label (s i j)
  have faithful (i j x y : Fin n) (eq : m i j=m x y) : s i j=s x y :=
    (spec i j).symm.trans ((congrArg (s 0) eq).trans (spec x y))
  have minpos (j : Fin n) : (m 0 j).val≤j.val := by
    simpa [m,label,occurs] using (fiber (s 0 j)).min'_le j (by simp [fiber])
  let atN (j : Nat) := if h : j<n then (m 0 ⟨j,h⟩).val else 0
  have steps (j : Nat) (hj : j<n) : atN j=j ∨ (1<j ∧ atN j=atN (j-1)) := by
    let x : Fin n := ⟨j,hj⟩
    by_cases e : (m 0 x).val=j
    · exact Or.inl (by simpa [atN,hj,x] using e)
    have before : (m 0 x).val<j := lt_of_le_of_ne (minpos x) e
    let y : Fin n := ⟨j-1,by omega⟩
    have between : s 0 y=s 0 x := le_antisymm (sorted (show y≤x by change j-1≤j; omega))
      ((spec 0 x) ▸ sorted (show m 0 x≤y by change (m 0 x).val≤j-1; omega))
    have notOne : j≠1 := by
      intro one
      have yz : y=0 := Fin.ext (by simp [y,one])
      have xz := (hs.diagonal 0 x).mp (between.symm.trans (congrArg (s 0) yz))
      have xv := congrArg Fin.val xz
      change 0=j at xv
      omega
    exact Or.inr ⟨by omega,by
      have eq := congrArg (fun a => (label a).val) between.symm
      simpa [atN,hj,show j-1<n by omega,m,x,y] using eq⟩
  have listed := gen atN steps n 0 0 (by simp) (Or.inl rfl)
  refine ⟨m,p,label ∘ code,hs.transport (Equiv.refl _) label faithful,?_,fun _ _ => rfl,?_⟩
  · apply List.mem_map.mpr
    exact ⟨_,by simpa [atN] using listed,rfl⟩
  · intro i j x y
    exact ⟨fun eq => inject (faithful _ _ _ _ eq),congrArg (label ∘ code)⟩

end QGI.RowCensus
