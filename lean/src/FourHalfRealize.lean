import FourHalfNormalize
import FourHalfComparison
import FourHalfMarks

noncomputable section
namespace QGI.Coherent.FourHalfModel
open QGI.FourHalfCatalog
open SixTenCoordinates SmallUnion SmallFiberExtension StrategyColorLaws
open FourTwelveFunctional (source)
open private bundle from SmallFiberExtension

private def role : Site → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

private def pairKind (u v : Fin 3) :=
  if u=2 then if v=2 then 5 else if v=0 then 3 else 4
  else if v=2 then if u=0 then 1 else 2 else 0

private theorem kind (u v : Site) : (port u v).kind=pairKind (role u) (role v) := by
  rcases u with (u|u)|u <;> rcases v with (v|v)|v <;> rfl

private def tag (l r v : Nat) (i : Fin 3) := if i=0 then r else if i=1 then v else l

private theorem roleTag {n l r v} {c : Fin n → Fin n → Nat} (X : Shore c r Eight) (Y : Shore c v Eight) (F : Shore c l Four)
    (u : Site) : c (pts X Y F u) (pts X Y F u)=tag l r v (role u) := by
  rcases u with (i|i)|i
  · exact (X i).property
  · exact (Y i).property
  · exact (F i).property

variable {n l r v : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
   (p : PerfectStrategy G H K)

theorem tags {X : Shore (source G) r Eight} {Y : Shore (source G) v Eight} {F : Shore (source G) l Four}
    {TX : Shore (targetName p) r Eight} {TY : Shore (targetName p) v Eight} {T : Shore (targetName p) l Four}
    (lr : l≠r) (lv : l≠v) (rv : r≠v) (i j x y : Site)
    (eq : source G (pts X Y F i) (pts X Y F j)=targetName p (pts TX TY T x) (pts TX TY T y)) :
    (port i j).kind=(port x y).kind := by
  have inj : Function.Injective (tag l r v) := by
    intro a b; fin_cases a <;> fin_cases b <;> simp_all [tag,Ne.symm lr,Ne.symm lv,Ne.symm rv]
  obtain ⟨a,b⟩ := SmallShore.endpoints p eq
  rw [kind,kind,inj ((roleTag X Y F i).symm.trans (a.trans (roleTag TX TY T x))),
    inj ((roleTag X Y F j).symm.trans (b.trans (roleTag TX TY T y)))]

theorem equal_realization (X : Shore (source G) r Eight) (Y : Shore (source G) v Eight) (F : Shore (source G) l Four)
    (TX : Shore (targetName p) r Eight) (TY : Shore (targetName p) v Eight) (T : Shore (targetName p) l Four)
    (old : ∀ i j, source G (vertex X Y i) (vertex X Y j)=targetName p (vertex TX TY i) (vertex TX TY j))
    (crossX : ∀ j i, source G (atPoint X j) (atPoint F i)=targetName p (atPoint TX j) (atPoint T i))
    (crossY : ∀ j i, source G (atPoint Y j) (atPoint F i)=targetName p (atPoint TY j) (atPoint T i))
    (internal : ∀ i j, source G (atPoint F i) (atPoint F j)=targetName p (atPoint T i) (atPoint T j)) :
    Realizes p (fun k => k=l ∨ k=r ∨ k=v) := by
  have names (i j : Site) : source G (pts X Y F i) (pts X Y F j)=targetName p (pts TX TY T i) (pts TX TY T j) := by
    rcases i with i|i <;> rcases j with j|j
    · exact old i j
    · cases i with | inl i => exact crossX i j | inr i => exact crossY i j
    · cases j with | inl j => exact common_transpose p (crossX j i) | inr j => exact common_transpose p (crossY j i)
    · exact internal i j
  let reg := fun k => k=l ∨ k=r ∨ k=v
  choose k hk using fun x : Region (source G) reg => (pts_range X Y F x.val).mpr ((mem_vertices _ _ _).mp x.property)
  obtain ⟨e,he⟩ := bundle p reg (fun x => pts TX TY T (k x)) (fun i j => by simpa only [hk] using names (k i) (k j))
  exact ⟨e,fun i j => by rw [he,he]; simpa only [hk] using names (k i) (k j)⟩

variable [CompleteSpace K]

theorem opposite_realization (P : Chart (source G) r v) {TX : Shore (targetName p) r Eight} {TY : Shore (targetName p) v Eight}
    {q : Eight → Four} (D : Aligned p P.X TX l q) (lr : l≠r) (lv : l≠v) (rv : r≠v)
    (old : ∀ i j, source G (vertex P.X P.Y i) (vertex P.X P.Y j)=targetName p (vertex TX TY i) (vertex TX TY j))
    (s : Eight → Bool) (b : Bool)
    (halves : ∀ i j x y, source G (atPoint P.Y i) (atPoint D.F j)=targetName p (atPoint TY x) (atPoint D.T y) ↔
      parityColumn (xor (s i) b) j=parityColumn (xor (s x) (!b)) y)
    (input : ∃ w, Supports P.key P.swap (encode q) (bits s) w) :
    Realizes p (fun k => k=l ∨ k=r ∨ k=v) := by
  apply FourHalfComparison.realize p _ (pts P.X P.Y D.F) (pts TX TY D.T)
    (pts_inj lr lv rv _ _ _) (pts_inj lr lv rv _ _ _) (pts_range _ _ _) (pts_range _ _ _) (b:=b) _ input
  constructor
  · exact tags p lr lv rv
  · intro i j x y
    change source G (vertex P.X P.Y i) (vertex P.X P.Y j)=targetName p (vertex TX TY x) (vertex TX TY y) ↔ _
    rw [←old x y]
    exact (P.names i j x y).symm
  · intro i j x y
    change source G (atPoint P.X i) (atPoint D.F j)=targetName p (atPoint TX x) (atPoint D.T y) ↔ _
    rw [D.sourceRow,D.targetRow,(encode_ok q).2,(encode_ok q).2]
    exact mark_iff D.distinct _ _
  · intro i j x y
    simpa only [half,parityColumn,(bits_ok s).2] using halves i j x y
  · exact D.four

end QGI.Coherent.FourHalfModel
