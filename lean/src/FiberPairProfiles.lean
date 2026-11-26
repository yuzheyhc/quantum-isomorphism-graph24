import HalfRectangle
import LargeOrderProfiles

noncomputable section
namespace QGI.Coherent.FiberPairProfiles
open CoprimeProfiles SmallFiberExtension SmallUnion LargeOrderProfiles LargeOrderBlocks
open StrategyColorLaws SixTenCoordinates LargeFourteenRegion
open FourTwelveFunctional (source fiber_eq)
open private bundle from SmallFiberExtension

private def directed (a b : Nat) : Prop := (a=4 ∧ (b=10 ∨ b=14)) ∨ (a=8 ∧ b=10) ∨ (a=6 ∧ b=14)
private instance (a b : Nat) : Decidable (directed a b) := by unfold directed; infer_instance
def compatible (a b : Nat) : Prop := a.Coprime b ∨ directed a b ∨ directed b a
instance (a b : Nat) : Decidable (compatible a b) := by unfold compatible; infer_instance

private theorem coord {n : Nat} (G : Graph n) (i : Fin n) {m : Nat} (h : (fiber G i).card=m) :
    Nonempty (Shore (source G) (source G i i) (Fin m)) := by
  let e := Fintype.equivOfCardEq (show Fintype.card (Fin m) = Fintype.card {z // z∈fiber G i} by simp [h])
  exact ⟨e.trans (Equiv.subtypeEquivRight (fiber_eq i))⟩

private theorem direction {n a b} {G : Graph n} (x y : Fin n) (ha : (fiber G x).card=a) (hb : (fiber G y).card=b)
    (h : directed a b) : FiberPairExtension.twins (source G) (source G x x) (source G y y) := by
  rcases h with ⟨hx,hy|hy⟩|⟨hx,hy⟩|⟨hx,hy⟩
  all_goals obtain ⟨F⟩ := coord G x (ha.trans hx); obtain ⟨Y⟩ := coord G y (hb.trans hy)
  · exact FourByEven.rectangle (sourceLaws _) F Y (Or.inl rfl)
  · exact FourByEven.rectangle (sourceLaws _) F Y (Or.inr rfl)
  · apply HalfRectangle.rectangle (p:=5) (sourceLaws _) F Y (by decide)
    · intro u v hu eq; by_contra! bad; interval_cases u <;> omega
    · intro d pos le a b
      exact (show ∀ k : Fin 9, 0<k.val → k.val∣8 → 5∣(8-k.val) → k.val=8 by decide) ⟨d,by omega⟩ pos a b
  · apply HalfRectangle.rectangle (p:=7) (sourceLaws _) F Y (by decide)
    · intro u v hu eq; by_contra! bad; interval_cases u <;> omega
    · intro d pos le a b
      exact (show ∀ k : Fin 7, 0<k.val → k.val∣6 → 7∣(6-k.val) → k.val=6 by decide) ⟨d,by omega⟩ pos a b

theorem rectangle {n : Nat} (G : Graph n) (x y : Fin n)
    (h : compatible (fiber G x).card (fiber G y).card) :
    FiberPairExtension.twins (source G) (source G x x) (source G y y) := by
  rcases h with h|h|h
  · have all (i : FiberPairExtension.Cell (source G) (source G x x))
        (j : FiberPairExtension.Cell (source G) (source G y y)) :
        source G i.val j.val = source G x y :=
      CoprimeFibers.monochromatic G x y h ((fiber_eq _ _).mpr i.property) ((fiber_eq _ _).mpr j.property)
    exact ⟨fun i k _ _ j => (all i j).trans (all k j).symm,fun _ j z _ i => (all i j).trans (all i z).symm⟩
  · exact direction x y rfl rfl h
  · have rev := direction y x rfl rfl h
    exact ⟨fun i k j eq t => Relations.transpose _ (rev.2 j i k (Relations.transpose _ eq) t),
      fun i j t eq k => Relations.transpose _ (rev.1 j t i (Relations.transpose _ eq) k)⟩

private theorem narrow {n} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {r s : Nat → Prop} (e : Realizes p r) (inside : ∀ i, s (source G i i) → r (source G i i)) :
    Realizes p s := by
  obtain ⟨f,hf⟩ := e
  let inc (x : Region (source G) s) : Region (source G) r := ⟨x.val,(mem_vertices _ _ _).mpr (inside _ ((mem_vertices _ _ _).mp x.property))⟩
  obtain ⟨g,hg⟩ := bundle p s (fun x => (f (inc x)).val) (fun i j => hf (inc i) (inc j))
  exact ⟨g,fun i j => by rw [hg,hg]; exact hf (inc i) (inc j)⟩

/-- The new fiber can interact with either or both of two previously
realized fibers. The two representatives may name the same fiber. -/
theorem realize {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (x y z : Fin n)
    (small : (fiber G x).card≤13)
    (xy : compatible (fiber G x).card (fiber G y).card)
    (xz : compatible (fiber G x).card (fiber G z).card)
    (reg : Nat → Prop) (inside : ∀ i, reg (source G i i) → source G i i=source G x x ∨
      source G i i=source G y y ∨ source G i i=source G z z)
    (old : Realizes p (fun v => v=source G y y ∨ v=source G z z)) : Realizes p reg := by
  let c := source G
  let keep := fun v => v=c y y ∨ v=c z z
  obtain ⟨F⟩ := coord G x (rfl : (fiber G x).card=(fiber G x).card)
  let a := F.symm ⟨x,rfl⟩
  let b : Region c keep := ⟨y,(mem_vertices _ _ _).mpr (Or.inl rfl)⟩
  let d : Region c keep := ⟨z,(mem_vertices _ _ _).mpr (Or.inr rfl)⟩
  apply narrow p (FiberPairExtension.attach p F a small keep old b d (fun j => ?_) (rectangle _ _ _ xy) (rectangle _ _ _ xz))
  · intro i hi; rcases inside i hi with h|h|h
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · exact ((mem_vertices _ _ _).mp j.property).imp_right Or.inl

def triple (xs : List Nat) (ids : Finset (Fin xs.length)) : Bool :=
  decide (∃ x y z : Fin xs.length, x∈ids ∧ y∈ids ∧ z∈ids ∧
    0<xs[x.val] ∧ xs[x.val]≤13 ∧ 0<xs[y.val] ∧ 0<xs[z.val] ∧
    (∀ i∈ids, i=x ∨ i=y ∨ i=z) ∧
    accepted 15 xs {y,z}=true ∧
    compatible xs[x.val] xs[y.val] ∧ compatible xs[x.val] xs[z.val])

/-- Solve a selected block using three profile indices; repeating the
second index covers a block consisting of just two fibers. -/
theorem solveWith {n : Nat} (nineteen : NineteenSolver n) {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K) (ids : Finset (Fin xs.length)) (h : triple xs ids=true)
    (reg : Nat → Prop) (shape : ∀ i, reg (source G i i) ↔ P.tag i∈ids)
    (active : ∀ i, reg (source G i i) → large G (source G i i)) : Realizes p reg := by
  classical
  obtain ⟨x,y,z,_,iy,iz,px,small,py,pz,cover,bound,one,two⟩ := of_decide_eq_true h
  obtain ⟨a,ha⟩ := P.occurs x px
  obtain ⟨b,hb⟩ := P.occurs y py
  obtain ⟨d,hd⟩ := P.occurs z pz
  let c := source G
  let keep := fun t => t=c b b ∨ t=c d d
  have sb : (fiber G b).card=xs[y.val] := (P.fiber_size b).trans (congrArg (fun t : Fin xs.length => xs[t.val]) hb)
  have sd : (fiber G d).card=xs[z.val] := (P.fiber_size d).trans (congrArg (fun t : Fin xs.length => xs[t.val]) hd)
  have sa : (fiber G a).card=xs[x.val] := (P.fiber_size a).trans (congrArg (fun t : Fin xs.length => xs[t.val]) ha)
  apply realize p a b d (sa.trans_le small) (by rw [sa,sb]; exact one) (by rw [sa,sd]; exact two) reg
  · intro i h
    rcases cover _ ((shape i).mp h) with eq|eq|eq
    · exact Or.inl ((P.same _ _).mp (eq.trans ha.symm))
    · exact Or.inr (Or.inl ((P.same _ _).mp (eq.trans hb.symm)))
    · exact Or.inr (Or.inr ((P.same _ _).mp (eq.trans hd.symm)))
  have incl (i : Fin n) (h : keep (c i i)) : reg (c i i) := by
    apply (shape _).mpr
    rcases h with h|h
    · exact (((P.same _ _).mpr h).trans hb).symm ▸ iy
    · exact (((P.same _ _).mpr h).trans hd).symm ▸ iz
  have tags (i : Fin n) : keep (c i i) ↔ P.tag i ∈ ({y,z} : Finset _) := by
    simp only [keep,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · exact fun h => h.elim (fun h => Or.inl (((P.same _ _).mpr h).trans hb)) (fun h => Or.inr (((P.same _ _).mpr h).trans hd))
    · exact fun h => h.elim (fun h => Or.inl ((P.same _ _).mp (h.trans hb.symm))) (fun h => Or.inr ((P.same _ _).mp (h.trans hd.symm)))
  have sz : (vertices c keep).card=weight xs {y,z} := by
    have eq : vertices c keep=Finset.univ.filter (fun i => P.tag i∈({y,z} : Finset _)) := by
      ext i; simp only [mem_vertices,Finset.mem_filter,Finset.mem_univ,true_and,tags]
    rw [eq,←Finset.sum_card_fiberwise_eq_card_filter Finset.univ ({y,z} : Finset _) P.tag]
    simp_rw [P.size]; rfl
  exact solveAccepted15With nineteen P p {y,z} bound keep tags (fun i h => active i (incl i h)) sz

theorem solve {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K) (ids : Finset (Fin xs.length)) (h : triple xs ids=true)
    (reg : Nat → Prop) (shape : ∀ i, reg (source G i i) ↔ P.tag i∈ids)
    (active : ∀ i, reg (source G i i) → large G (source G i i)) : Realizes p reg :=
  solveWith (unrestrictedNineteen n) P p ids h reg shape active

def covered (xs : List Nat) : Bool := checkWith xs (fun ids => accepted 15 xs ids || triple xs ids)

theorem isomorphic {n : Nat} {G H : Graph n} {xs : List Nat} (P : Profile G xs)
    (ok : covered xs=true) (q : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,hc,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := hc
  obtain ⟨e,he⟩ := LargeOrderProfiles.named P _ ok p (fun ids h reg shape active size => by
    simp only [Bool.or_eq_true] at h
    rcases h with old|new'
    · exact solveAccepted15 P p ids old reg shape active size
    · exact solve P p ids new' reg shape active)
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩

end QGI.Coherent.FiberPairProfiles

