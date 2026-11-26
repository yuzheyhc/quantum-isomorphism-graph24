import LargeOrderFourSixGlue
import LargeOrderSixteen

noncomputable section
namespace QGI.Coherent.LargeOrderFourSixSix
open SmallUnion StrategyColorLaws LargeFourteenRegion SixTenCoordinates FourSixSix
open FourTwelveFunctional (source)
open FourSixSix.Interfaces (flag cells)
open private maskVal edgeDegree rowCheck pairGram twin_of_uniform point from FourSixSixComplete

private theorem size_eq {c : Coloring} {k l : Nat} (F : Shore c l (Fin k)) :
    (vertices c (·=l)).card=k := by
  classical
  have e := Equiv.subtypeEquivRight (fun i => mem_vertices c (·=l) i)
  have eq := Fintype.card_congr (F.trans e.symm)
  simpa only [Fintype.card_fin,Fintype.card_coe] using eq.symm

private theorem outside_size {c : Coloring} {k l : Nat} (F : Shore c l (Fin k)) :
    (vertices c (·≠l)).card=16-k := by
  have eq : vertices c (·≠l)=(vertices c (·=l))ᶜ := by
    ext i; simp only [mem_vertices,Finset.mem_compl]
  rw [eq,Finset.card_compl,size_eq F]; rfl

private theorem flagBlock {c : Coloring} {l u s} (F : Shore c l I) (Y : Shore c u E)
    (tetra : ∀ i j, cells F Y i j=s ↔ incident i j) : Block F F Y Y flag flag := by
  intro i j x y eq
  apply Bool.decide_congr
  exact (tetra i j).symm.trans ((show cells F Y i j=s ↔ cells F Y x y=s by
    rw [show cells F Y i j=cells F Y x y from eq]).trans (tetra x y))

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (p : PerfectStrategy G H K) {reg : Nat → Prop} {src tgt : V → Fin n} (D : DataFor p reg src tgt)
local notation "c₀" => restricted (source G) src
local notation "d₀" => restricted (targetName p) tgt
private abbrev Named (c d : Coloring) := ∃ e : Equiv.Perm V, ∀ i j, c i j=d (e i) (e j)
local notation "Result" => Named c₀ d₀
include D
private theorem laws : Laws c₀ c₀ :=
  ⟨fun h => Relations.transpose _ h,fun h => (Relations.end_colors _ h).2,
    fun a b i j x y h => D.srcConfig.products a b i j x y h⟩

private theorem both_tetra {l u v s t : Nat} (F : Shore c₀ l I) (Y : Shore c₀ u E) (Z : Shore c₀ v E)
    (uv : u≠v) (fy : ∀ i j, cells F Y i j=s ↔ incident i j) (fz : ∀ i j, cells F Z i j=t ↔ incident i j) :
    Result := by
  let law := laws p D
  obtain ⟨e,he⟩ := LargeOrderSubregions.small p D (·≠v) (by rw [outside_size Z]; decide)
  apply LargeOrderSixteen.anchored p D (fun i : ThreeFiberTwins.Outside c₀ v => i.val) (fun i => (e i).val) he
  have counts := Block.fold law (Block.flip law (flagBlock F Y fy)) (flagBlock F Z fz)
    (fun s t => if s=true ∧ t=true then (1:Nat) else 0)
  have pin : ∀ j k : E, (∑ i : I, if flag i j=true ∧ flag i k=true then (1:Nat) else 0)=
    (∑ i : I, if flag i j=true ∧ flag i j=true then (1:Nat) else 0) → k=j := by decide
  intro x
  by_cases hx : c₀ x x=v
  · obtain ⟨j,rfl⟩ := point Z x hx
    let a : ThreeFiberTwins.Outside c₀ v := ⟨atPoint Y j,fun h => uv ((Y j).property.symm.trans h)⟩
    refine ⟨a,fun z h => ?_⟩
    obtain ⟨k,rfl⟩ := point Z z ((Relations.end_colors _ h).2.trans (Z j).property)
    exact congrArg (atPoint Z) (pin j k (counts h))
  · exact ⟨⟨x,hx⟩,fun z h => (D.srcConfig.diagonal x z x h).symm⟩

private theorem one_tetra {l u v s t : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (F : Shore c₀ l I) (Y : Shore c₀ u E) (Z : Shore c₀ v E)
    (all : ∀ x, c₀ x x=l ∨ c₀ x x=u ∨ c₀ x x=v)
    (tetra : ∀ i j, cells F Y i j=s ↔ incident i j) (full : ∀ i j, cells F Z i j=t) : Result := by
  let law := laws p D
  have inc := flagBlock F Y tetra
  have grams : Block Y Y Y Y pairGram pairGram := Block.gram law (Block.flip law inc)
  apply LargeOrderFourSixGlue.overlap p D lu lv uv all (by rw [outside_size Z]; decide) (by rw [outside_size F]; decide)
    (atPoint Y 0) (atPoint Y 1) (Y 0).property (Y 1).property
  · intro i j x y hi hj hx hy
    obtain ⟨i,rfl⟩ := point F i hi
    obtain ⟨j,rfl⟩ := point Z j hj
    obtain ⟨x,rfl⟩ := point F x hx
    obtain ⟨y,rfl⟩ := point Z y hy
    exact (full i j).trans (full x y).symm
  · intro i x j hi hx hj ha hb
    obtain ⟨i,rfl⟩ := point Y i hi
    obtain ⟨x,rfl⟩ := point Y x hx
    obtain ⟨j,rfl⟩ := point Z j hj
    let s := c₀ (atPoint Y i) (atPoint Z j)
    let bit (a b : E) := decide (c₀ (atPoint Y a) (atPoint Z b)=s)
    have eb : Block Y Y Z Z bit bit := fun ⦃_ _ _ _⦄ h => congrArg (fun k => decide (k=s)) h
    have mixed := Block.fold law inc eb (fun b d => if b=true ∧ d=true then 1 else 0)
    let m := QGI.SixTen.Cross.encode (fun a : E => bit a j)
    have bits (a : E) : maskVal m a=bit a j := QGI.SixTen.Cross.decode _ _
    have count (i : I) : edgeDegree m i=edgeDegree m 0 := by
      simpa only [edgeDegree,bits] using mixed ((full i j).trans (full 0 j).symm)
    have eq := (bits i).symm.trans ((rowCheck m (List.mem_range.mpr (QGI.SixTen.Cross.encode_lt _))
      i x (grams ha) (grams hb) count).trans (bits x))
    have yes : bit i j=true := decide_eq_true rfl
    exact (of_decide_eq_true (eq.symm.trans yes)).symm

private theorem with_tetra {l u v s : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (F : Shore c₀ l I) (Y : Shore c₀ u E) (Z : Shore c₀ v E)
    (all : ∀ x, c₀ x x=l ∨ c₀ x x=u ∨ c₀ x x=v)
    (q : Equiv.Perm E) (tetra : ∀ i j, cells F Y i j=s ↔ incident i (q j)) : Result := by
  let Y' := q.symm.trans Y
  have fy (i j) : cells F Y' i j=s ↔ incident i j := by simpa only [Equiv.apply_symm_apply] using tetra i (q.symm j)
  rcases Interfaces.next_to_tetra (laws p D) F Y' Z fy with ⟨t,full⟩ | ⟨t,r,another⟩
  · exact one_tetra p D lu lv uv F Y' Z all fy full
  · let Z' := r.symm.trans Z
    have fz (i j) : cells F Z' i j=t ↔ incident i j := by simpa only [Equiv.apply_symm_apply] using another i (r.symm j)
    exact both_tetra p D F Y' Z' uv fy fz

theorem frames {l u v : Nat} (lu : l≠u) (lv : l≠v) (uv : u≠v)
    (F : Shore c₀ l I) (Y : Shore c₀ u E) (Z : Shore c₀ v E)
    (all : ∀ x, c₀ x x=l ∨ c₀ x x=u ∨ c₀ x x=v) : Result := by
  have shape (m : Nat) (S : Shore c₀ m E) : ThreeFiberTwins.twinBlock c₀ l m ∨
      ∃ n, ∃ q : Equiv.Perm E, ∀ i j, cells F S i j=n ↔ incident i (q j) := by
    rcases Interfaces.classify (laws p D) F S with ⟨n,h⟩ | other
    · exact Or.inl (twin_of_uniform F S h)
    · exact other
  rcases shape u Y with yt | ⟨s,q,h⟩
  · rcases shape v Z with zt | ⟨s,q,h⟩
    · let y : ThreeFiberTwins.Outside c₀ l := ⟨atPoint Y 0,fun h => lu (h.symm.trans (Y 0).property)⟩
      let z : ThreeFiberTwins.Outside c₀ l := ⟨atPoint Z 0,fun h => lv (h.symm.trans (Z 0).property)⟩
      apply LargeOrderFourSixGlue.twins p D (F 0) y z (by rw [size_eq F]; decide) (by rw [outside_size F]; decide)
      · intro x
        rcases all x.val with h|h|h
        · exact (x.property h).elim
        · exact Or.inl (h.trans (Y 0).property.symm)
        · exact Or.inr (h.trans (Z 0).property.symm)
      · change ThreeFiberTwins.twinBlock c₀ l (c₀ (atPoint Y 0) (atPoint Y 0))
        rw [show c₀ (atPoint Y 0) (atPoint Y 0)=u from (Y 0).property]; exact yt
      · change ThreeFiberTwins.twinBlock c₀ l (c₀ (atPoint Z 0) (atPoint Z 0))
        rw [show c₀ (atPoint Z 0) (atPoint Z 0)=v from (Z 0).property]; exact zt
    · exact with_tetra p D lv lu uv.symm F Z Y (fun x => (all x).imp_right Or.symm) q h
  · exact with_tetra p D lu lv uv F Y Z all q h

theorem solve {l u v : Nat} (four : (named c₀ l).card=4) (six : (named c₀ u).card=6)
    (other : (named c₀ v).card=6) (uv : u≠v) : Result := by
  classical
  have shore (a k : Nat) (size : (named c₀ a).card=k) : Nonempty (Shore c₀ a (Fin k)) := by
    have h : Fintype.card {i : V // c₀ i i=a}=k := by simpa only [Fintype.card_subtype,named] using size
    exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_fin,h])⟩
  have lu : l≠u := by rintro rfl; omega
  have lv : l≠v := by rintro rfl; omega
  have disj (a b : Nat) (ne : a≠b) : Disjoint (named c₀ a) (named c₀ b) :=
    Finset.disjoint_left.mpr (fun _ ha hb => ne ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2))
  have all : (named c₀ l ∪ named c₀ u) ∪ named c₀ v = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨disj _ _ lv,disj _ _ uv⟩),
        Finset.card_union_of_disjoint (disj _ _ lu),four,six,other]; rfl)
  obtain ⟨F⟩ := shore l 4 four
  obtain ⟨Y⟩ := shore u 6 six
  obtain ⟨Z⟩ := shore v 6 other
  apply frames p D lu lv uv F Y Z
  intro i
  have h : i ∈ (named c₀ l ∪ named c₀ u) ∪ named c₀ v := all ▸ Finset.mem_univ _
  simpa only [Finset.mem_union,named,Finset.mem_filter,Finset.mem_univ,true_and,or_assoc] using h

omit D in
/-- A named region with three distinct diagonal fibers of sizes four, six
and six realizes its prescribed palette in any ambient order. -/
theorem realize (region : Nat → Prop)
    (active : ∀ i, region (source G i i) → large G (source G i i))
    (size : (vertices (source G) region).card=16)
    (four : ∃ i, region (source G i i) ∧ (fiber G i).card=4)
    (six : ∃ j k, region (source G j j) ∧ region (source G k k) ∧
      (fiber G j).card=6 ∧ (fiber G k).card=6 ∧ source G j j≠source G k k) :
    SmallFiberExtension.Realizes p region := by
  apply LargeOrderBlocks.of_solver p region active size
  intro f g D'
  obtain ⟨i,hi,ci⟩ := four
  obtain ⟨j,k,hj,hk,cj,ck,ne⟩ := six
  obtain ⟨i,rfl⟩ := (D'.src _).mpr hi
  obtain ⟨j,rfl⟩ := (D'.src _).mpr hj
  obtain ⟨k,rfl⟩ := (D'.src _).mpr hk
  exact solve p D' ((LargeOrderBlocks.fiber_card f D'.injF D'.src i).trans ci)
    ((LargeOrderBlocks.fiber_card f D'.injF D'.src j).trans cj)
    ((LargeOrderBlocks.fiber_card f D'.injF D'.src k).trans ck) ne

end QGI.Coherent.LargeOrderFourSixSix
