import FourSixInterfaces
import FourSixSixQuantum
import ThreeFiberTwins
import ThreeFiberOverlap
import ThreeFiberCoordinates

noncomputable section
namespace QGI.Coherent.FourSixSix

open SixTenCoordinates StrategyColorLaws
open FourTwelveFunctional (source fiber_eq)
open Interfaces (flag cells)

private def maskVal (m : Nat) (j : E) := m.testBit j.val
private def edgeDegree (m : Nat) (i : I) : Nat := ∑ j : E, if flag i j=true ∧ maskVal m j=true then 1 else 0
private def pairGram (a b : E) := Block.overlap (fun j i => flag i j) a b

private theorem rowCheck : ∀ m ∈ List.range 64, ∀ x y : E,
    pairGram 0 x = pairGram 0 y → pairGram 1 x = pairGram 1 y →
    (∀ i : I, edgeDegree m i = edgeDegree m 0) → maskVal m x = maskVal m y := by native_decide

private theorem rest_card {G : Graph 16} {l k} (F : Shore (source G) l (Fin k)) (a : Fin k) :
    (SmallUnion.vertices (source G) (fun v => v ≠ l)).card = 16-k := by
  have eq : SmallUnion.vertices (source G) (fun v => v≠l) = (fiber G (atPoint F a))ᶜ := by
    ext x
    simp only [SmallUnion.mem_vertices,Finset.mem_compl,fiber_eq]
    rw [show source G (atPoint F a) (atPoint F a) = l from (F a).property]
  rw [eq,Finset.card_compl,card_shore F a]; rfl

private theorem point {c : Coloring} {v n} (S : Shore c v (Fin n)) (x : V) (h : c x x=v) :
    ∃ i, atPoint S i=x := ⟨S.symm ⟨x,h⟩,congrArg Subtype.val (S.apply_symm_apply _)⟩

private theorem one_tetra {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (F : Shore (source G) l I) (Y : Shore (source G) u E) (Z : Shore (source G) v E)
    (all : ∀ x, source G x x=l ∨ source G x x=u ∨ source G x x=v) {s t : Nat}
    (tetra : ∀ i j, cells F Y i j=s ↔ incident i j) (full : ∀ i j, cells F Z i j=t) :
    Isomorphic G H := by
  let c := source G
  have law := sourceLaws (closure G)
  have inc : Block F F Y Y flag flag := by
    intro i j x y eq
    apply Bool.decide_congr
    exact (tetra i j).symm.trans ((show cells F Y i j=s ↔ cells F Y x y=s by rw [show cells F Y i j=cells F Y x y from eq]).trans (tetra x y))
  have grams : Block Y Y Y Y pairGram pairGram := Block.gram law (Block.flip law inc)
  have eB := Block.edges_self G Y Z
  have mixed := Block.fold law inc eB (fun b d => if b=true ∧ d=true then 1 else 0)
  apply ThreeFiberOverlap.isomorphic p lu lv uv all (by rw [rest_card Z 0]; decide) (by rw [rest_card F 0]; decide)
    (atPoint Y 0) (atPoint Y 1) (Y 0).property (Y 1).property
  · intro i j x y hi hj hx hy
    obtain ⟨i,rfl⟩ := point F i hi
    obtain ⟨j,rfl⟩ := point Z j hj
    obtain ⟨x,rfl⟩ := point F x hx
    obtain ⟨y,rfl⟩ := point Z y hy
    exact Block.edges_self G F Z ((full i j).trans (full x y).symm)
  · intro i x j hi hx hj ha hb
    obtain ⟨i,rfl⟩ := point Y i hi
    obtain ⟨x,rfl⟩ := point Y x hx
    obtain ⟨j,rfl⟩ := point Z j hj
    let m := QGI.SixTen.Cross.encode (fun n : E => G.edge (atPoint Y n) (atPoint Z j))
    have bits (x : E) : maskVal m x = G.edge (atPoint Y x) (atPoint Z j) := QGI.SixTen.Cross.decode _ _
    have count (i : I) : edgeDegree m i = edgeDegree m 0 := by
      simpa only [edgeDegree,bits] using mixed ((full i j).trans (full 0 j).symm)
    exact (bits i).symm.trans ((rowCheck m (List.mem_range.mpr (QGI.SixTen.Cross.encode_lt _))
      i x (grams ha) (grams hb) count).trans (bits x))

private theorem twin_of_uniform {c l v} (F : Shore c l I) (S : Shore c v E)
    {n} (full : ∀ i j, cells F S i j=n) : ThreeFiberTwins.twinBlock c l v := by
  have h (i : ThreeFiberTwins.Points c l) (j : ThreeFiberTwins.Points c v) : c i.val j.val=n := by
    obtain ⟨i,rfl⟩ := F.surjective i
    obtain ⟨j,rfl⟩ := S.surjective j
    exact full i j
  exact ⟨fun i x _ _ y => (h i y).trans (h x y).symm,fun _ j y _ x => (h x j).trans (h x y).symm⟩

private theorem with_tetra {G H : Graph 16} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (quantum : QuantumIso G H) {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (F : Shore (source G) l I) (Y : Shore (source G) u E) (Z : Shore (source G) v E)
    (all : ∀ x, source G x x=l ∨ source G x x=u ∨ source G x x=v) {s : Nat}
    (q : Equiv.Perm E) (tetra : ∀ i j, cells F Y i j=s ↔ incident i (q j)) :
    Isomorphic G H := by
  let Y' := q.symm.trans Y
  have fy (i j) : cells F Y' i j=s ↔ incident i j := by
    simpa only [Equiv.apply_symm_apply] using tetra i (q.symm j)
  rcases Interfaces.next_to_tetra (sourceLaws _) F Y' Z fy with ⟨t,full⟩ | ⟨t,r,another⟩
  · exact one_tetra p lu lv uv F Y' Z all fy full
  · let Z' := r.symm.trans Z
    have fz (i j) : cells F Z' i j=t ↔ incident i j := by
      simpa only [Equiv.apply_symm_apply] using another i (r.symm j)
    exact isomorphic_of_two_tetrahedra F Y' Z' uv fy fz quantum

/-- All 4+6+6 coherent-fiber configurations force a classical isomorphism. -/
theorem isomorphic_of_frames {G H : Graph 16} {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (F : Shore (source G) l I) (Y : Shore (source G) u E) (Z : Shore (source G) v E)
    (all : ∀ x, source G x x=l ∨ source G x x=u ∨ source G x x=v)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  obtain ⟨K,ng,ip,compl,⟨p⟩⟩ := quantum
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  have qc : QuantumIso G H := ⟨K,ng,ip,compl,⟨p⟩⟩
  let c := source G
  let shape (m : Nat) (S : Shore c m E) : ThreeFiberTwins.twinBlock c l m ∨
      ∃ n, ∃ q : Equiv.Perm E, ∀ i j, cells F S i j=n ↔ incident i (q j) := by
    rcases Interfaces.classify (sourceLaws _) F S with ⟨n,h⟩ | other
    · exact Or.inl (twin_of_uniform F S h)
    · exact other
  rcases shape u Y with yl | ⟨s,q,h⟩
  · rcases shape v Z with zl | ⟨t,q,h⟩
    · let y : ThreeFiberTwins.Outside c l := ⟨atPoint Y 0,fun h => lu (h.symm.trans (Y 0).property)⟩
      let z : ThreeFiberTwins.Outside c l := ⟨atPoint Z 0,fun h => lv (h.symm.trans (Z 0).property)⟩
      apply ThreeFiberTwins.isomorphic p F 0 (by decide) y z (by rw [rest_card F 0]; decide)
      · intro j
        rcases all j.val with h | h | h
        · exact (j.property h).elim
        · exact Or.inl (h.trans (Y 0).property.symm)
        · exact Or.inr (h.trans (Z 0).property.symm)
      · change ThreeFiberTwins.twinBlock c l (c (atPoint Y 0) (atPoint Y 0))
        rwa [show c (atPoint Y 0) (atPoint Y 0)=u from (Y 0).property]
      · change ThreeFiberTwins.twinBlock c l (c (atPoint Z 0) (atPoint Z 0))
        rwa [show c (atPoint Z 0) (atPoint Z 0)=v from (Z 0).property]
    · exact with_tetra p qc lv lu (Ne.symm uv) F Z Y (fun x => (all x).imp_right Or.symm) q h
  · exact with_tetra p qc lu lv uv F Y Z all q h

theorem isomorphic_of_four_six_six {G H : Graph 16} (a b z : V) (four : (fiber G a).card=4)
    (six : (fiber G b).card=6) (six' : (fiber G z).card=6) (apart : b ∉ fiber G z)
    (quantum : QuantumIso G H) : Isomorphic G H := by
  have distinct (x : V) (hx : (fiber G x).card=6) : a ∉ fiber G x := by
    intro h
    have same := (fiber_eq x a).mp h
    have eq : fiber G a = fiber G x := by ext p; simp only [fiber_eq,same]
    have num := congrArg Finset.card eq
    omega
  obtain ⟨l,u,v,lu,lv,uv,⟨F⟩,⟨Y⟩,⟨Z⟩,all⟩ := ThreeFiberCoordinates.frames G a b z four six six' (by decide)
    (distinct b six) (distinct z six') apart
  exact isomorphic_of_frames lu lv uv F Y Z all quantum

end QGI.Coherent.FourSixSix
