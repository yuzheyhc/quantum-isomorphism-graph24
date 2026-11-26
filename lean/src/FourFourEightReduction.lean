import FourEightGeometry
import ThreeFiberCoordinates
import ThreeFiberTwins

noncomputable section
namespace QGI.Coherent.FourFourEight
open Relations SixTenCoordinates FourEightGeometry FourTwelveCycle

/-- A basic relation between a four-point and an eight-point fiber has
four-cycle neighborhoods, each occurring twice. -/
def HasDoubledCycle (G : Graph 16) : Prop :=
  let c := color (closure G)
  ∃ l r, l≠r ∧ ∃ (F : Shore c l (Fin 4)) (Y : Shore c r (Fin 8)) (v w : Nat),
    (∀ i j, c (atPoint F i) (atPoint Y j)=v ∨ c (atPoint F i) (atPoint Y j)=w) ∧
    ∃ b : Fin 8 → Edge, (∀ i j, c (atPoint F i) (atPoint Y j)=v ↔ i∈edge (b j)) ∧
      Nonempty (RepeatedCycle b)

theorem reverse_twins {G : Graph 16} {l r : Nat} {n m : Nat}
    (F : Shore (color (closure G)) l (Fin n)) (Y : Shore (color (closure G)) r (Fin m))
    (tw : SplitRectangle.Twins (fun i j => color (closure G) (atPoint F i) (atPoint Y j))) :
    ThreeFiberTwins.twinBlock (color (closure G)) r l := by
  have name (i : ThreeFiberTwins.Points (color (closure G)) l)
      (j : ThreeFiberTwins.Points (color (closure G)) r) :
      color (closure G) (atPoint F (F.symm i)) (atPoint Y (Y.symm j)) = color (closure G) i.val j.val := by
    simp only [atPoint,Equiv.apply_symm_apply]
  constructor
  · intro i x j h y
    apply Relations.transpose (closure G)
    have eq := tw.2 (F.symm j) (Y.symm i) (Y.symm x)
      (by simpa only [name] using Relations.transpose (closure G) h) (F.symm y)
    simpa only [name] using eq
  · intro i j y h x
    apply Relations.transpose (closure G)
    have eq := tw.1 (F.symm j) (F.symm y) (Y.symm i)
      (by simpa only [name] using Relations.transpose (closure G) h) (Y.symm x)
    simpa only [name] using eq

/-- Every unresolved 4+4+8 graph has a doubled four-cycle on at least
one of its two four-by-eight interfaces. The four-by-four interface may
be arbitrary. -/
theorem isomorphic_or_doubled_cycle {G H : Graph 16} (a b y : Fin 16)
    (ha : (fiber G a).card=4) (hb : (fiber G b).card=4) (hy : (fiber G y).card=8)
    (apart : a ∉ fiber G b) (q : QuantumIso G H) : Isomorphic G H ∨ HasDoubledCycle G := by
  classical
  obtain ⟨l,r,v,_,lv,rv,⟨F⟩,⟨S⟩,⟨Y⟩,cover⟩ :=
    ThreeFiberCoordinates.frames G a b y ha hb hy (by decide) apart
      (ThreeFiberCoordinates.disjoint_of_sizes (by omega))
      (ThreeFiberCoordinates.disjoint_of_sizes (by omega))
  rcases FourEightGeometry.dispatch lv F Y q with iso | ft | ⟨c,d,pal,z,hidden,hz⟩
  · exact Or.inl iso
  · rcases FourEightGeometry.dispatch rv S Y q with iso | st | ⟨c,d,pal,z,hidden,hz⟩
    · exact Or.inl iso
    · obtain ⟨K,gr,ip,_,⟨p⟩⟩ := q
      letI : NormedAddCommGroup K := gr
      letI : InnerProductSpace ℂ K := ip
      let c := color (closure G)
      let x : ThreeFiberTwins.Outside c v := ⟨atPoint F 0,fun eq => lv ((F 0).property.symm.trans eq)⟩
      let z : ThreeFiberTwins.Outside c v := ⟨atPoint S 0,fun eq => rv ((S 0).property.symm.trans eq)⟩
      have hx : c x.val x.val=l := (F 0).property
      have hz : c z.val z.val=r := (S 0).property
      have card : (SmallUnion.vertices c (fun t => t=v)).card=8 := by
        let e := Equiv.subtypeEquivRight (p := fun x => x∈SmallUnion.vertices c (fun t => t=v))
          (q := fun x => c x x=v) (fun x => SmallUnion.mem_vertices _ _ x)
        simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_congr (e.trans Y.symm)
      have compl : SmallUnion.vertices c (fun t => t≠v) = (SmallUnion.vertices c (fun t => t=v))ᶜ := by
        ext w; simp only [Finset.mem_compl,SmallUnion.mem_vertices]
      have rest : (SmallUnion.vertices c (fun t => t≠v)).card ≤ 13 := by
        rw [compl,Finset.card_compl,card]; decide
      apply Or.inl (ThreeFiberTwins.isomorphic p Y 0 (by decide) x z rest ?_ ?_ ?_)
      · intro j
        rcases cover j.val with h|h|h
        · exact Or.inl (h.trans hx.symm)
        · exact Or.inr (h.trans hz.symm)
        · exact (j.property h).elim
      · rw [show color (closure G) x.val x.val=l from hx]; exact reverse_twins F Y ft
      · rw [show color (closure G) z.val z.val=r from hz]; exact reverse_twins S Y st
    · exact Or.inr ⟨r,v,rv,S,Y,c,d,pal,z,hidden,hz⟩
  · exact Or.inr ⟨l,v,lv,F,Y,c,d,pal,z,hidden,hz⟩

end QGI.Coherent.FourFourEight
