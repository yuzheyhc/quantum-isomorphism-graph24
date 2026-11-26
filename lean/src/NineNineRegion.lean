import NineNineCensus
import NineNineChecks
import SixSixRegion

noncomputable section
namespace QGI.Coherent.NineNineRegion
set_option maxRecDepth 12000
open QGI.NineNine QGI.NineNine.Checks
open SixTenCoordinates (Shore atPoint Laws Block)
open BareLex (V rows transpose)
open FourTwelveFunctional (source)
open StrategyColorLaws
variable {n : Nat} {c : Fin n → Fin n → Nat} {a b : Nat}
abbrev cells (A : Shore c a V) (Y : Shore c b V) : N := fun i j => c (atPoint A i) (atPoint Y j)
abbrev mark (A : Shore c a V) (Y : Shore c b V) (v : Nat) : B := fun i j => decide (cells A Y i j=v)

private theorem prod_block (law : Laws c c) {u w z : Nat} {A : Shore c u V} {Y : Shore c w V}
    {Z : Shore c z V} {f g : N} (hf : Block A A Y Y f f) (hg : Block Y Y Z Z g g) :
    Block A A Z Z (prod f g) (prod f g) := by
  intro i j x y eq
  simpa only [prod] using Block.fold law hf hg (fun t s => t*s) eq

private theorem gram_block (law : Laws c c) {A : Shore c a V} {Y : Shore c b V} {B₀ : B}
    (hb : Block A A Y Y B₀ B₀) : Block A A A A (gram B₀) (gram B₀) :=
  prod_block law (Block.map hb Bool.toNat) (Block.map (Block.flip law hb) Bool.toNat)

private theorem power_block (law : Laws c c) {A : Shore c a V} {g : N}
    (hg : Block A A A A g g) (k : Nat) : Block A A A A (power g k) (power g k) := by
  induction k with
  | zero => exact hg
  | succ k ih => exact prod_block law ih hg

private theorem uniform (law : Laws c c) {A : Shore c a V} {Y : Shore c b V} {B₀ : B}
    (hb : Block A A Y Y B₀ B₀) : Sieve.uniform (rows B₀)=true := by
  apply uniform_score
  intro i
  exact Block.diag (Block.fold law (Block.const (L:=A) (L':=A) (R:=A) (R':=A) ())
    (gram_block law hb) (fun _ v => 16^v)) i 0

private theorem belongs {d : Nat} {rs : List Nat} (mem : rs∈BareEnum.candidates d) (acc : Sieve.admissible rs=true) :
    rs∈Sieve.shortlist d := List.mem_filter.mpr ⟨mem,acc⟩

attribute [local irreducible] Sieve.shortlist BareEnum.candidates Short.entries

private theorem run (law : Laws c c) {A : Shore c a V} {Y : Shore c b V} (v : Nat) {d : Nat}
    (hd : d=2 ∨ d=3 ∨ d=4) (input : rows (mark A Y v) ∈ BareEnum.candidates d) :
    Thin (cells A Y) ∨ rows (mark A Y v)=pappusRows ∨ rows (mark A Y v)=rectangleRows := by
  let b := mark A Y v
  have hb : Block A A Y Y b b := Block.map Block.names (fun s => decide (s=v))
  have acc : Sieve.admissible (rows b)=true := by
    simp only [Sieve.admissible,Bool.and_eq_true,transpose_rows]
    exact ⟨uniform law hb,uniform law (Block.flip law hb)⟩
  have ins : rows b ∈ Sieve.shortlist d := belongs input acc
  have appears : rows b ∈ Sieve.shortlist 2 ++ Sieve.shortlist 3 ++ Sieve.shortlist 4 := by
    rcases hd with rfl|rfl|rfl
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ins)))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ins)))
    · exact List.mem_append.mpr (Or.inr ins)
  rw [Sieve.enumerate] at appears
  obtain ⟨entry,mem,he⟩ := List.mem_map.mp appears
  have pass := classify entry (c:=cells A Y) (by simpa using mem)
  rw [he,matrix_rows] at pass
  apply pass
  · intro i j x y hi hx
    exact (of_decide_eq_true hi).trans (of_decide_eq_true hx).symm
  · intro k i j x y eq
    exact prod_block law (power_block law (gram_block law hb) k) (Block.map hb Bool.toNat) eq
  · intro k i w
    have hg := power_block law (gram_block law hb) k
    exact Block.diag (Block.fold law hg (Block.const (L:=A) (L':=A) (R:=A) (R':=A) ())
      (fun f _ => if f=w then 1 else 0)) 0 i

theorem classify_color (law : Laws c c) (A : Shore c a V) (Y : Shore c b V) (v d : Nat)
    (hd : d=2 ∨ d=3 ∨ d=4)
    (rd : ∀ i, FiberRectangles.degree (mark A Y v i)=d)
    (cd : ∀ j, FiberRectangles.degree (transpose (mark A Y v) j)=d) :
    Thin (cells A Y) ∨ ∃ e f : Equiv.Perm V,
      rows (mark (e.trans A) (f.trans Y) v)=pappusRows ∨
      rows (mark (e.trans A) (f.trans Y) v)=rectangleRows := by
  obtain ⟨e,f,mem⟩ := BareNormal.exists_enumerated (mark A Y v) d rd cd
  rcases run law (A:=e.trans A) (Y:=f.trans Y) v hd mem with ⟨i,j,h⟩|eq|eq
  · left
    refine ⟨e i,f j,fun z hz => ?_⟩
    obtain ⟨z,rfl⟩ := f.surjective z
    exact congrArg f (h z hz)
  · exact Or.inr ⟨e,f,Or.inl eq⟩
  · exact Or.inr ⟨e,f,Or.inr eq⟩

end QGI.Coherent.NineNineRegion






