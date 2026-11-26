import RowCensus
namespace QGI.RowCensus

variable {n : Nat} [NeZero n] {m : Table n (Fin n)}
def thinEdge (m : Table n (Fin n)) (i j : Fin n) := ∀ z, m i z=m i j → z=j

private theorem row_count (h : Laws m) (i : Fin n) (a : Fin n) :
    (List.ofFn (m i)).count a = (List.ofFn (m 0)).count a := (h.row_perm i).count_eq a

theorem length_filter_ofFn {q : Nat} {α : Type} (f : Fin q → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length=∑ i : Fin q, if p (f i) then 1 else 0 := by
  induction q with
  | zero => simp
  | succ q ih => rw [List.ofFn_succ,Fin.sum_univ_succ]; cases eq : p (f 0) <;> simp [eq,ih,Nat.add_comm]

omit [NeZero n] in
theorem countFiber {α : Type} [DecidableEq α] {f : Fin n → α} (a : α) :
    (List.ofFn f).count a=(Finset.univ.filter (fun z => f z=a)).card := by
  have eq : (List.ofFn f).count a = ((List.ofFn f).filter (· == a)).length := List.countP_eq_length_filter
  rw [eq,length_filter_ofFn]
  simp

private theorem thin_iff (h : Laws m) (i j : Fin n) : thinEdge m i j ↔
    (List.ofFn (m 0)).count (m i j)=1 := by
  rw [← row_count h i,countFiber,Finset.card_eq_one]
  constructor
  · intro u
    exact ⟨j,Finset.ext (by simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]; exact fun z => ⟨u z,fun e => e ▸ rfl⟩)⟩
  · rintro ⟨a,eq⟩ z hz
    have mem (x : Fin n) (hx : m i x=m i j) : x=a :=
      Finset.mem_singleton.mp (eq ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩))
    exact (mem z hz).trans (mem j rfl).symm

private theorem row_exists (h : Laws m) (i j k : Fin n) : ∃ z, m k z=m i j := by
  apply List.mem_ofFn.mp
  exact ((h.row_perm k).trans (h.row_perm i).symm).mem_iff.mpr (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem thinEdge_reverse (h : Laws m) {i j : Fin n} (u : thinEdge m i j) : thinEdge m j i := by
  classical
  choose f hf using fun k => row_exists h i j k
  have thin (k : Fin n) : thinEdge m k (f k) :=
    (thin_iff h _ _).mpr ((hf k).symm ▸ (thin_iff h _ _).mp u)
  have onto : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := row_exists h j i x
    exact ⟨y,((thin y) x ((h.reverse _ _ _ _ hy).trans (hf y).symm)).symm⟩
  have inj := (Finite.surjective_iff_bijective.mp onto).1
  intro z eq
  apply inj
  have fz : j=f z := thin z j ((h.reverse _ _ _ _ eq).trans (hf z).symm)
  exact fz.symm.trans (thin i j (hf i).symm)

theorem thinEdge_trans (h : Laws m) {i j k : Fin n} (u : thinEdge m i j) (v : thinEdge m j k) :
    thinEdge m i k := by
  intro z eq
  have p := h.pairs i k i z eq.symm
  obtain ⟨w,hw⟩ := List.mem_ofFn.mp (p.mem_iff.mp (List.mem_ofFn.mpr ⟨j,rfl⟩))
  obtain ⟨w1,w2⟩ := Prod.mk.inj hw
  rw [u w w1] at w2
  exact v z (h.reverse _ _ _ _ w2)

def thinCount (row : List Nat) : Nat := (row.filter fun a => row.count a == 1).length

/-- The classes of the valency-one relations form equal-sized blocks. -/
theorem thinCount_dvd (h : Laws m) : thinCount (List.ofFn fun j => (m 0 j).val) ∣ n := by
  classical
  let rel : Setoid (Fin n) := ⟨thinEdge m,fun i z hz => (h.diagonal i z).mp (hz.trans ((h.diagonal i i).mpr rfl)) |>.symm,
    fun u => thinEdge_reverse h u,fun u v => thinEdge_trans h u v⟩
  let key : Fin n → Quotient rel := Quotient.mk rel
  letI : Fintype (Quotient rel) := Fintype.ofFinite _
  let t := thinCount (List.ofFn fun j => (m 0 j).val)
  have equalCounts (x : Fin n) : (List.ofFn fun j => (m x j).val).count =
      (List.ofFn fun j => (m 0 j).val).count := by
    funext a
    exact (by simpa [List.map_ofFn,Function.comp_def] using ((h.row_perm x).map Fin.val).count_eq a)
  have cnt (x j : Fin n) : (List.ofFn fun z => (m x z).val).count (m x j).val =
      (List.ofFn (m x)).count (m x j) := by
    simpa [List.map_ofFn,Function.comp_def] using List.count_map_of_injective (List.ofFn (m x)) Fin.val Fin.val_injective (m x j)
  have size (x : Fin n) : Fintype.card {z : Fin n // key z=key x}=t := by
    let good (a : Nat) := (List.ofFn fun j => (m 0 j).val).count a == 1
    have perm := ((h.row_perm x).map Fin.val).filter good
    have e : (List.filter good (List.ofFn fun z => (m x z).val)).length=t := by
      simpa [t,thinCount,good,List.map_ofFn,Function.comp_def] using perm.length_eq
    rw [← e]
    have hk (z : Fin n) : key z=key x ↔ good (m x z).val=true := by
      change Quotient.mk rel z=Quotient.mk rel x ↔ _
      rw [Quotient.eq]
      change thinEdge m z x ↔ _
      rw [show thinEdge m z x ↔ thinEdge m x z from ⟨thinEdge_reverse h,thinEdge_reverse h⟩,thin_iff h]
      change _ ↔ ((List.ofFn fun j => (m 0 j).val).count (m x z).val == 1)=true
      rw [beq_iff_eq,← congrFun (equalCounts x) (m x z).val, cnt]
      rw [row_count h x]
    rw [Fintype.card_subtype,length_filter_ofFn]
    simp [hk]
  have all (q : Quotient rel) : Fintype.card {z : Fin n // key z=q}=t := Quotient.inductionOn q size
  have e := Fintype.card_congr (Equiv.sigmaFiberEquiv key)
  rw [Fintype.card_sigma,Fintype.card_fin] at e
  exact ⟨Fintype.card (Quotient rel),by simpa [all,Nat.mul_comm] using e.symm⟩

end QGI.RowCensus
