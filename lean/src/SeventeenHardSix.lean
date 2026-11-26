import SeventeenHardRegion
import FourSixSixComplete
import CoprimeProfiles

noncomputable section
namespace QGI.Coherent.SeventeenHardSix
open StrategyColorLaws SixTenCoordinates FourSixSix SeventeenHardRegion
open FourTwelveFunctional (source fiber_eq)
open FourSixSix.Interfaces (flag cells)
open private maskVal edgeDegree rowCheck pairGram twin_of_uniform from FourSixSixComplete
open private root_unique from SingletonSwitch

variable {G H : Graph 17} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) (R : Core G)

private theorem flag_block {l u s} (F : Shore R.c l I) (Y : Shore R.c u E)
    (tetra : ∀ i j, cells F Y i j=s ↔ incident i j) : Block F F Y Y flag flag := by
  intro i j x y eq
  apply Bool.decide_congr
  exact (tetra i j).symm.trans ((show cells F Y i j=s ↔ cells F Y x y=s by
    rw [show cells F Y i j=cells F Y x y from eq]).trans (tetra x y))

include p in
private theorem both_tetra {l u v s t} (F : Shore R.c l I) (Y : Shore R.c u E) (Z : Shore R.c v E)
    (uv : u≠v) (vr : v≠R.rootName)
    (size : (fiber G (R.pointAt Z 0)).card=6)
    (fy : ∀ i j, cells F Y i j=s ↔ incident i j) (fz : ∀ i j, cells F Z i j=t ↔ incident i j) :
    Isomorphic G H := by
  let a := R.pointAt Y 0
  let b := R.pointAt Z 0
  have counts := Block.fold R.laws (Block.flip R.laws (flag_block R F Y fy)) (flag_block R F Z fz)
    (fun s t => if s=true ∧ t=true then (1:Nat) else 0)
  have pin : ∀ j : E, (∑ i : I, if flag i 0 = true ∧ flag i j = true then (1:Nat) else 0) =
    (∑ i : I, if flag i 0 = true ∧ flag i 0 = true then (1:Nat) else 0) → j=0 := by decide
  obtain ⟨e,he⟩ := SmallUnion.erase_of_column_one p a b
    (fun h => uv ((Y 0).property.symm.trans (((fiber_eq b a).mp h).trans (Z 0).property)))
    (by change 0 < 17-(fiber G (R.pointAt Z 0)).card; rw [size]; decide)
    (by change 17-(fiber G (R.pointAt Z 0)).card ≤ 13; rw [size]; decide) (by
      intro z eq
      obtain ⟨j,rfl⟩ := R.point vr Z ((Relations.end_colors (closure G) eq).2.trans (Z 0).property)
      exact congrArg (R.pointAt Z) (pin j (counts eq)))
  exact ⟨e,e.symm,e.symm_apply_apply,e.apply_symm_apply,fun i j => common_edge p (he i j)⟩

include p in
private theorem one_tetra {l u v s t} (F : Shore R.c l I) (Y : Shore R.c u E) (Z : Shore R.c v E)
    (lu : l≠u) (lv : l≠v) (uv : u≠v) (lr : l≠R.rootName) (ur : u≠R.rootName) (vr : v≠R.rootName)
    (all : ∀ i, source G i i = R.rootName ∨ source G i i=l ∨ source G i i=u ∨ source G i i=v)
    (sizeL : (SmallUnion.vertices (source G) (fun k => k≠l)).card ≤ 13)
    (sizeV : (SmallUnion.vertices (source G) (fun k => k≠v)).card ≤ 13)
    (tetra : ∀ i j, cells F Y i j=s ↔ incident i j) (full : ∀ i j, cells F Z i j=t) :
    Isomorphic G H := by
  have inc := flag_block R F Y tetra
  have grams : Block Y Y Y Y pairGram pairGram := Block.gram R.laws (Block.flip R.laws inc)
  have eb : Block Y Y Z Z (fun i j => G.edge (R.pointAt Y i) (R.pointAt Z j))
      (fun i j => G.edge (R.pointAt Y i) (R.pointAt Z j)) := fun ⦃_ _ _ _⦄ h => Core.same_edge h
  have mixed := Block.fold R.laws inc eb (fun b d => if b=true ∧ d=true then 1 else 0)
  apply SeventeenHardGlue.Overlap.isomorphic p lu lv uv sizeV sizeL
    (R.pointAt Y 0) (R.pointAt Y 1) (Y 0).property (Y 1).property
  · intro i j x y iu iv hj hi hy
    rcases all i with r | h | h | h
    · obtain rfl := root_unique R.root R.one i r
      obtain rfl := root_unique R.root R.one x (hi.trans rfl)
      exact Core.same_edge (Relations.transpose (closure G) (R.root_pair (hj.trans hy.symm)))
    · obtain ⟨i,rfl⟩ := R.point lr F h
      obtain ⟨j,rfl⟩ := R.point vr Z hj
      obtain ⟨x,rfl⟩ := R.point lr F (hi.trans h)
      obtain ⟨y,rfl⟩ := R.point vr Z hy
      exact Core.same_edge ((full i j).trans (full x y).symm)
    · exact (iu h).elim
    · exact (iv h).elim
  · intro i x j hi hx hj ha hb
    obtain ⟨i,rfl⟩ := R.point ur Y hi
    obtain ⟨x,rfl⟩ := R.point ur Y hx
    obtain ⟨j,rfl⟩ := R.point vr Z hj
    let m := QGI.SixTen.Cross.encode (fun n : E => G.edge (R.pointAt Y n) (R.pointAt Z j))
    have bits (x : E) : maskVal m x = G.edge (R.pointAt Y x) (R.pointAt Z j) := QGI.SixTen.Cross.decode _ _
    have count (i : I) : edgeDegree m i = edgeDegree m 0 := by
      simpa only [edgeDegree,bits] using mixed ((full i j).trans (full 0 j).symm)
    exact (bits i).symm.trans ((rowCheck m (List.mem_range.mpr (QGI.SixTen.Cross.encode_lt _))
      i x (grams ha) (grams hb) count).trans (bits x))

include p in
private theorem with_tetra {l u v s} (F : Shore R.c l I) (Y : Shore R.c u E) (Z : Shore R.c v E)
    (lu : l≠u) (lv : l≠v) (uv : u≠v) (lr : l≠R.rootName) (ur : u≠R.rootName) (vr : v≠R.rootName)
    (all : ∀ i, source G i i=R.rootName ∨ source G i i=l ∨ source G i i=u ∨ source G i i=v)
    (sizeL : (SmallUnion.vertices (source G) (fun k => k≠l)).card ≤ 13)
    (sizeV : ∀ x, source G x x=v → (fiber G x).card=6)
    (q : Equiv.Perm E) (tetra : ∀ i j, cells F Y i j=s ↔ incident i (q j)) : Isomorphic G H := by
  let Y' := q.symm.trans Y
  have fy (i j) : cells F Y' i j=s ↔ incident i j := by
    simpa only [Equiv.apply_symm_apply] using tetra i (q.symm j)
  rcases FourSixSix.Interfaces.next_to_tetra R.laws F Y' Z fy with ⟨t,full⟩ | ⟨t,r,another⟩
  · exact one_tetra p R F Y' Z lu lv uv lr ur vr all sizeL (by
      rw [Core.outside_card (Z 0).property,sizeV (R.pointAt Z 0) (Z 0).property]; decide) fy full
  · let Z' := r.symm.trans Z
    have fz (i j) : cells F Z' i j=t ↔ incident i j := by
      simpa only [Equiv.apply_symm_apply] using another i (r.symm j)
    exact both_tetra p R F Y' Z' uv vr (sizeV _ (Z' 0).property) fy fz

private theorem lift_twins {l v} (lr : l≠R.rootName) (vr : v≠R.rootName)
    (h : ThreeFiberTwins.twinBlock R.c l v) : SeventeenHardGlue.Twins.twinBlock (source G) l v := by
  constructor
  · intro i x j eq y
    obtain ⟨i,rfl⟩ := (R.points lr).surjective i
    obtain ⟨x,rfl⟩ := (R.points lr).surjective x
    obtain ⟨j,rfl⟩ := (R.points vr).surjective j
    obtain ⟨y,rfl⟩ := (R.points vr).surjective y
    exact h.1 i x j eq y
  · intro i j y eq x
    obtain ⟨i,rfl⟩ := (R.points lr).surjective i
    obtain ⟨x,rfl⟩ := (R.points lr).surjective x
    obtain ⟨j,rfl⟩ := (R.points vr).surjective j
    obtain ⟨y,rfl⟩ := (R.points vr).surjective y
    exact h.2 i j y eq x

theorem four_six_six {G H : Graph 17} (P : CoprimeProfiles.Profile G [1,4,6,6])
    (q : QuantumIso G H) : Isomorphic G H := by
  classical
  obtain ⟨K,ng,ip,_,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := ng
  letI : InnerProductSpace ℂ K := ip
  have pos : ∀ i : Fin 4, 0 < ([1,4,6,6] : List Nat)[i.val] := by decide
  choose rep tag using fun i : Fin 4 => P.occurs i (pos i)
  let name := fun i : Fin 4 => source G (rep i) (rep i)
  have ne {i j : Fin 4} (h : i≠j) : name i ≠ name j := by
    intro eq
    exact h ((tag i).symm.trans (((P.same _ _).mpr eq).trans (tag j)))
  have size (i : Fin 4) (x : Fin 17) (h : source G x x=name i) :
      (fiber G x).card = ([1,4,6,6] : List Nat)[i.val] := by
    rw [P.fiber_size,((P.same _ _).mpr h).trans (tag i)]
  let R : Core G := ⟨rep 0,size 0 _ rfl⟩
  let l := name 1
  let u := name 2
  let v := name 3
  have lr : l≠R.rootName := ne (by decide : (1 : Fin 4)≠0)
  have ur : u≠R.rootName := ne (by decide : (2 : Fin 4)≠0)
  have vr : v≠R.rootName := ne (by decide : (3 : Fin 4)≠0)
  have lu : l≠u := ne (by decide : (1 : Fin 4)≠2)
  have lv : l≠v := ne (by decide : (1 : Fin 4)≠3)
  have uv : u≠v := ne (by decide : (2 : Fin 4)≠3)
  obtain ⟨F⟩ := R.frame lr (a:=rep 1) rfl (k:=4) (size 1 _ rfl)
  obtain ⟨Y⟩ := R.frame ur (a:=rep 2) rfl (k:=6) (size 2 _ rfl)
  obtain ⟨Z⟩ := R.frame vr (a:=rep 3) rfl (k:=6) (size 3 _ rfl)
  have all (i : Fin 17) : source G i i=R.rootName ∨ source G i i=l ∨ source G i i=u ∨ source G i i=v := by
    have eq := (P.same i (rep (P.tag i))).mp (tag _).symm
    change source G i i=name (P.tag i) at eq
    have opts := (show ∀ t : Fin 4, t=0 ∨ t=1 ∨ t=2 ∨ t=3 by decide) (P.tag i)
    rcases opts with h|h|h|h <;> rw [h] at eq <;> tauto
  have sizeL : (SmallUnion.vertices (source G) (fun k => k≠l)).card ≤ 13 := by
    rw [Core.outside_card (i:=rep 1) (show source G (rep 1) (rep 1)=l from rfl),size 1 _ rfl]; decide
  have shape (m : Nat) (S : Shore R.c m E) : ThreeFiberTwins.twinBlock R.c l m ∨
      ∃ n, ∃ t : Equiv.Perm E, ∀ i j, cells F S i j=n ↔ incident i (t j) := by
    rcases FourSixSix.Interfaces.classify R.laws F S with ⟨n,h⟩ | other
    · exact Or.inl (twin_of_uniform F S h)
    · exact other
  rcases shape u Y with yt | ⟨s,t,hy⟩
  · rcases shape v Z with zt | ⟨s,t,hz⟩
    · let y : SeventeenHardGlue.Twins.Outside (source G) l := ⟨R.pointAt Y 0,
        fun h => lu (h.symm.trans (Y 0).property)⟩
      let z : SeventeenHardGlue.Twins.Outside (source G) l := ⟨R.pointAt Z 0,
        fun h => lv (h.symm.trans (Z 0).property)⟩
      apply SeventeenHardGlue.Twins.isomorphic p (F.trans (R.points lr)) 0 (by decide) y z sizeL
      · intro j
        rcases all j.val with h|h|h|h
        · refine Or.inr (Or.inr ?_)
          intro i x w hw
          have jroot := root_unique R.root R.one j.val h
          have wroot := root_unique R.root R.one w (hw.trans h)
          rw [jroot,wroot]
          exact R.root_pair (i.property.trans x.property.symm)
        · exact (j.property h).elim
        · exact Or.inl (h.trans (Y 0).property.symm)
        · exact Or.inr (Or.inl (h.trans (Z 0).property.symm))
      · change SeventeenHardGlue.Twins.twinBlock (source G) l (source G (R.pointAt Y 0) (R.pointAt Y 0))
        rw [show source G (R.pointAt Y 0) (R.pointAt Y 0)=u from (Y 0).property]
        exact lift_twins R lr ur yt
      · change SeventeenHardGlue.Twins.twinBlock (source G) l (source G (R.pointAt Z 0) (R.pointAt Z 0))
        rw [show source G (R.pointAt Z 0) (R.pointAt Z 0)=v from (Z 0).property]
        exact lift_twins R lr vr zt
    · exact with_tetra p R F Z Y lv lu uv.symm lr vr ur (fun i => (all i).imp_right (Or.imp_right Or.symm))
        sizeL (size 2) t hz
  · exact with_tetra p R F Y Z lu lv uv lr ur vr all sizeL (size 3) t hy

end QGI.Coherent.SeventeenHardSix
