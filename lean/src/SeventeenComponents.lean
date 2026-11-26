import Orders.Order16

namespace QGI.Components
open private smaller_component cut_disconnected iso_of_complement from ComponentReduction

theorem disconnected_succ {n : Nat} (base : Through n) {G H : Graph (n+1)}
    (disc : ¬(simple G).Preconnected) (q : QuantumIso G H) : Isomorphic G H :=
  of_component_bound base (fun c => Nat.le_of_lt_succ (smaller_component G disc c)) q

theorem disconnected_seventeen {G H : Graph 17} (disc : ¬(simple G).Preconnected)
    (q : QuantumIso G H) : Isomorphic G H := disconnected_succ through16 disc q

theorem disconnected_complement_seventeen {G H : Graph 17}
    (disc : ¬(simple (complement G)).Preconnected) (q : QuantumIso G H) : Isomorphic G H :=
  iso_of_complement (disconnected_seventeen disc (complement_qc q))

private theorem of_cut {G H : Graph 17} (side : Fin 17 → Bool) (both : Function.Surjective side)
    (v : Bool) (cross : ∀ x y, side x ≠ side y → G.edge x y = v) (q : QuantumIso G H) : Isomorphic G H := by
  cases v with
  | false =>
    apply disconnected_seventeen (cut_disconnected G side both ?_) q
    intro x y adj; by_contra ne
    rw [cross x y ne] at adj; contradiction
  | true =>
    apply disconnected_complement_seventeen (cut_disconnected (complement G) side both ?_) q
    intro x y adj; by_contra ne
    simp [complement,cross x y ne] at adj

/-- In a two-fiber profile of coprime sizes, the entire cross rectangle
has a single adjacency value. The remaining component has size at most 16. -/
theorem of_coprime_pair {G H : Graph 17} {m n : Nat} (P : Coherent.CoprimeProfiles.Profile G [m,n])
    (hm : 0 < m) (hn : 0 < n) (cop : Nat.Coprime m n)
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨a,ha⟩ := P.occurs (0 : Fin 2) hm
  obtain ⟨b,hb⟩ := P.occurs (1 : Fin 2) hn
  let side := fun i => decide (P.tag i = (1 : Fin 2))
  have both : Function.Surjective side := by
    intro v; cases v
    · exact ⟨a,by simp [side,ha]⟩
    · exact ⟨b,by simp [side,hb]⟩
  have edge (x y) (hx : P.tag x = (0 : Fin 2)) (hy : P.tag y = (1 : Fin 2)) :
      G.edge x y = G.edge a b := by
    have inFiber (i j) (eq : P.tag i=P.tag j) : i ∈ Coherent.fiber G j :=
      (Coherent.FourTwelveFunctional.fiber_eq j i).mpr ((P.same i j).mp eq)
    have same := Coherent.CoprimeFibers.monochromatic G a b (by rw [P.fiber_size,P.fiber_size,ha,hb]; exact cop)
      (inFiber _ _ (hx.trans ha.symm)) (inFiber _ _ (hy.trans hb.symm))
    have h := (Coherent.Relations.same _ _ _ _ _).mp same _ (Coherent.adjacency_mem G)
    cases e : G.edge x y <;> cases f : G.edge a b <;> first | rfl | simp [Intertwiner.adjacency,e,f] at h
  have cross (x y) (diff : side x ≠ side y) : G.edge x y=G.edge a b := by
    have tags (i) : P.tag i = (0 : Fin 2) ∨ P.tag i = (1 : Fin 2) := by
      exact (show ∀ j : Fin 2, j=0 ∨ j=1 by decide) (P.tag i)
    rcases tags x with hx|hx <;> rcases tags y with hy|hy
    · simp [side,hx,hy] at diff
    · exact edge _ _ hx hy
    · exact (G.symm x y).trans (edge _ _ hy hx)
    · simp [side,hx,hy] at diff
  exact of_cut side both _ cross q

theorem two_singletons_fifteen {G H : Graph 17} (P : Coherent.CoprimeProfiles.Profile G [1,1,15])
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  have pos : ∀ i : Fin 3, 0 < ([1,1,15] : List Nat)[i.val] := by decide
  choose rep hrep using fun i : Fin 3 => P.occurs i (pos i)
  let bit := fun i j => G.edge (rep i) (rep j)
  have rect (x y) (ne : P.tag x ≠ P.tag y) : G.edge x y = bit (P.tag x) (P.tag y) := by
    have cop : ∀ i j : Fin 3, i≠j → ([1,1,15] : List Nat)[i.val].Coprime ([1,1,15] : List Nat)[j.val] := by decide
    have inc (i) : i ∈ Coherent.fiber G (rep (P.tag i)) :=
      (Coherent.FourTwelveFunctional.fiber_eq _ _).mpr ((P.same _ _).mp (hrep _).symm)
    have same := Coherent.CoprimeFibers.monochromatic G (rep (P.tag x)) (rep (P.tag y))
      (by rw [P.fiber_size,P.fiber_size,hrep,hrep]; exact cop _ _ ne) (inc x) (inc y)
    have val := (Coherent.Relations.same _ _ _ _ _).mp same _ (Coherent.adjacency_mem G)
    change G.edge x y=G.edge _ _
    cases a : G.edge x y <;> cases b : G.edge (rep (P.tag x)) (rep (P.tag y)) <;>
      first | rfl | simp [Intertwiner.adjacency,a,b] at val
  have sb (i j) : bit i j = bit j i := G.symm _ _
  have someRow : ∃ z : Fin 3, ∃ v : Bool, ∀ i : Fin 3, i≠z → bit z i=v := by
    by_cases e : bit 0 1=bit 0 2
    · exact ⟨0,bit 0 2,fun i ne => by fin_cases i <;> first | contradiction | exact e | rfl⟩
    by_cases k : bit 1 0=bit 1 2
    · exact ⟨1,bit 1 2,fun i ne => by fin_cases i <;> first | contradiction | exact k | rfl⟩
    have eq : bit 2 0=bit 2 1 := by
      rw [sb 2 0,sb 2 1]
      rw [sb 1 0] at k
      cases h : bit 0 1 <;> cases j : bit 0 2 <;> cases t : bit 1 2 <;> simp_all
    exact ⟨2,bit 2 1,fun i ne => by fin_cases i <;> first | contradiction | exact eq | rfl⟩
  obtain ⟨z,v,row⟩ := someRow
  let side := fun i => decide (P.tag i=z)
  have onto : Function.Surjective side := by
    intro b; cases b with
    | true => exact ⟨rep z,by simp [side,hrep]⟩
    | false =>
      obtain ⟨j,hj⟩ := (show ∀ k : Fin 3, ∃ i : Fin 3, i≠k by decide) z
      exact ⟨rep j,by simp [side,hrep,hj]⟩
  apply of_cut side onto v _ q
  intro x y diff
  by_cases hx : P.tag x=z <;> by_cases hy : P.tag y=z
  · simp [side,hx,hy] at diff
  · rw [rect x y (fun eq => hy (eq.symm.trans hx)),hx]; exact row _ hy
  · rw [G.symm,rect y x (fun eq => hx (eq.symm.trans hy)),hy]; exact row _ hx
  · simp [side,hx,hy] at diff

end QGI.Components

namespace QGI.Coherent.SingletonSwitch
open CoprimeProfiles

/-- Isolating the unique root and, if needed, complementing the first
remaining fiber internally distinguishes the two fibers by degree.
Their sizes may coincide. -/
theorem three_fibers {n m t : Nat} {G H : Graph n} (lower : Through (n-1))
    (P : Profile G [1,m,t]) (hm : 0 < m) (ht : 0 < t) (even : Even m)
    (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨x,hx⟩ := P.occurs (0 : Fin 3) (show 0 < (1:Nat) by decide)
  obtain ⟨a,ha⟩ := P.occurs (1 : Fin 3) hm
  obtain ⟨b,hb⟩ := P.occurs (2 : Fin 3) ht
  have colors {i j : Fin n} (h : P.tag i ≠ P.tag j) : Col G i i ≠ Col G j j :=
    fun eq => h ((P.same i j).mpr eq)
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  apply isomorphic_with_lower p lower x a b
  · rw [P.fiber_size,hx]; rfl
  · rw [P.fiber_size,ha]; exact even
  · apply colors; rw [ha,hx]; exact (by decide : (1:Fin 3) ≠ 0)
  · apply colors; rw [hb,hx]; exact (by decide : (2:Fin 3) ≠ 0)
  · apply colors; rw [hb,ha]; exact (by decide : (2:Fin 3) ≠ 1)
  · intro i
    have tags := (show ∀ v : Fin 3, v=0 ∨ v=1 ∨ v=2 by decide) (P.tag i)
    rcases tags with h|h|h
    · exact Or.inl ((P.same i x).mp (h.trans hx.symm))
    · exact Or.inr (Or.inl ((P.same i a).mp (h.trans ha.symm)))
    · exact Or.inr (Or.inr ((P.same i b).mp (h.trans hb.symm)))

end QGI.Coherent.SingletonSwitch
