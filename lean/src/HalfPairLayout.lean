import RegionalEightTwelveHalfLaws
import SixEightGeometry

namespace QGI.Coherent.HalfPair
open EightTwelveHalf RegionalEightTwelveStats RegionalEightTwelveHalfLaws
open SixTenCoordinates (Shore atPoint Laws)
open private scaled from RegionalEightTwelveHalfLaws
abbrev Label := Fin 4

def group (i : P) : Label := ⟨i.val/2,by omega⟩
def roots (s : C) := s.image group
def omitted (a : Label) : Label := Fin.ofNat' 4 (a.val ^^^ 1)

structure Layout (A : J → C) where
  label : P → Label
  pattern : J → Finset Label
  two : ∀ a, (Finset.univ.filter (fun i => label i=a)).card=2
  mark : ∀ j i, i∈A j ↔ label i∈pattern j
  small : ∀ j, (Finset.univ.filter (fun k => pattern k=pattern j)).card≤3
  pairs : ∀ a b : Label, a≠b → b≠omitted a → ∃ j, pattern j={a,b}
  distinct : ∀ i k, (∀ j, i∈A j ↔ k∈A j) ↔ label i=label k

private theorem templates : ∀ k : Fin 5, k=1 ∨ k=2 →
    4≤(model k).card ∧ (∀ s∈model k, ∀ i : P, i∈s ↔ group i∈roots s) ∧
    (∀ a b : Label, a≠b → b≠omitted a → ∃ s∈model k, roots s={a,b}) ∧
    ∀ a b : Label, (∀ s∈model k, (a∈roots s ↔ b∈roots s)) → a=b := by native_decide

theorem layout {n l r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) (F : Shore c l P) (Y : Shore c r J)
    (v : Nat) (k : Fin 5) (hk : k=1 ∨ k=2) (e : Equiv.Perm P)
    (shape : (supports (family F Y v)).image (fun s => s.image e)=model k) : Nonempty (Layout (family F Y v)) := by
  let A := family F Y v
  let S (j : J) := (A j).image e
  let label := group ∘ e
  let pat (j : J) := roots (S j)
  have inside (j : J) : S j∈model k := shape ▸ Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have onto (s) (hs : s∈model k) : ∃ j,S j=s := by
    rw [←shape] at hs
    obtain ⟨s,mem,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp mem
    exact ⟨j,rfl⟩
  obtain ⟨num,sat,pair,dif⟩ := templates k hk
  have mark (j i) : i∈A j ↔ label i∈pat j := by
    have read : e i∈S j ↔ i∈A j := by simp [S]
    exact read.symm.trans (sat _ (inside j) (e i))
  have same (s t : J) : pat s=pat t ↔ A s=A t := by
    constructor
    · intro h; ext i; rw [mark,mark,h]
    · intro h; change roots ((A s).image e)=roots ((A t).image e); rw [h]
  have mass := scaled A (copies A 0) (uniform_copies law F Y v) (fun _ => True)
  simp only [Finset.filter_True,Finset.card_univ,Fintype.card_fin] at mass
  have imageCard : (supports A).card=(model k).card := by
    rw [←shape]
    exact (Finset.card_image_of_injective _ (fun i j eq => Finset.map_injective e.toEmbedding (by simpa only [Finset.map_eq_image] using eq))).symm
  have few : copies A 0≤3 := by
    rw [imageCard] at mass
    by_contra! big
    have le := Nat.mul_le_mul (show 4≤copies A 0 by omega) num
    omega
  refine ⟨⟨label,pat,?_,mark,?_,?_,?_⟩⟩
  · intro a; exact (SixEightGeometry.count_equiv e (fun i => label i=a) (fun i => group i=a) (fun _ => Iff.rfl)).trans
      ((by decide : ∀ a : Label, (Finset.univ.filter (fun i => group i=a)).card=2) a)
  · intro j; simp only [same]; exact (uniform_copies law F Y v j).le.trans few
  · intro a b ab ex
    obtain ⟨s,hs,eq⟩ := pair a b ab ex
    obtain ⟨j,hj⟩ := onto s hs
    exact ⟨j,(congrArg roots hj).trans eq⟩
  · intro i t
    constructor
    · intro h; apply dif
      intro S hs; obtain ⟨j,rfl⟩ := onto S hs
      exact (mark j i).symm.trans ((h j).trans (mark j t))
    · intro h j; rw [mark,mark,h]

end QGI.Coherent.HalfPair
