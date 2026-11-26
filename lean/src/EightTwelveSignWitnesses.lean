import FourHalfCore
import RegionalEightTwelveCatalog
import data.EightTwelveSigns
import FifteenNamed

namespace QGI.EightTwelveSigns
open Certificate
abbrev Rep := Fin 32
abbrev Key := Fin 59
abbrev J := Fin 12
abbrev I := Fin 8
abbrev V := Fin 20

def key (s : Rep) : Key := Fin.ofNat' 59 ((Input.reps[s.val]?).getD (0,0)).1
def mask (s : Rep) (i : I) := (((Input.reps[s.val]?).getD (0,0)).2 >>> (12*i.val))%4096
def inside (s : Rep) (i : I) (j : J) := (mask s i).testBit j.val
def rightName (a : Key) (i j : J) := EightTwelveCatalog.cell (EightTwelveCatalog.row 12 a.val) i j
def rowOverlap (s : Rep) (i j : I) := (Finset.univ.filter (fun k => inside s i k && inside s j k)).card

def value (s : Rep) (x y : V) : Nat :=
  let r (t : V) := Fin.ofNat' 12 t.val
  let l (t : V) := Fin.ofNat' 8 (t.val-12)
  if x.val<12 then
    if y.val<12 then rightName (key s) (r x) (r y) else 16+(inside s (l y) (r x)).toNat
  else if y.val<12 then 18+(inside s (l x) (r y)).toNat else 20+rowOverlap s (l x) (l y)

def matrix (s : Rep) : ColorMatrix :=
  FourHalfCatalog.fromFn 20 (fun k => value s (Fin.ofNat' 20 (k.val/20)) (Fin.ofNat' 20 k.val))

attribute [local irreducible] Input.reps Input.obstructions EightTwelveCatalog.row FourHalfCatalog.fromFn value
theorem read (s : Rep) (i j : V) : (matrix s).get i.val j.val=value s i j := by
  unfold matrix
  rw [FourHalfCatalog.fromFn_read _ i j (by omega)]
  have ar : ∀ i j : V, Fin.ofNat' 20 ((i.val*20+j.val)/20)=i ∧ Fin.ofNat' 20 (i.val*20+j.val)=j := by decide
  exact congrArg₂ (value s) (ar i j).1 (ar i j).2

def TrueCount (w : Input.Separation) : Prop :=
  (w.pattern=.tetra ∨ w.pattern=.nearClique ∨ w.pattern=.bipyramid) ∧
  w.colors.length=w.pattern.edges.length ∧ w.leftCount≠w.rightCount ∧
  homCount (matrix w.first) w.pattern w.colors=w.leftCount ∧
  homCount (matrix w.second) w.pattern w.colors=w.rightCount
instance (w : Input.Separation) : Decidable (TrueCount w) := by unfold TrueCount; infer_instance

set_option maxRecDepth 20000 in
theorem counts : ∀ i : Fin Input.obstructions.size, TrueCount Input.obstructions[i] := by native_decide

private theorem coverage : ∀ s t : Rep, key s=key t → s<t →
    ∃ i : Fin Input.obstructions.size, Input.obstructions[i].first=s ∧ Input.obstructions[i].second=t := by native_decide

theorem distinguish {s t : Rep} (eq : key s=key t) (ne : s≠t) :
    ∃ pat colors, (∃ points : Array PlanePoint, Draws pat points) ∧ colors.length=pat.edges.length ∧
    homCount (matrix s) pat colors≠homCount (matrix t) pat colors := by
  suffices inc : ∀ {u v : Rep}, key u=key v → u<v →
      ∃ pat colors, (∃ points : Array PlanePoint, Draws pat points) ∧ colors.length=pat.edges.length ∧
      homCount (matrix u) pat colors≠homCount (matrix v) pat colors by
    rcases lt_or_gt_of_ne ne with h|h
    · exact inc eq h
    · obtain ⟨p,c,d,a,b⟩ := inc eq.symm h
      exact ⟨p,c,d,a,Ne.symm b⟩
  intro u v same lt
  obtain ⟨i,hu,hv⟩ := coverage u v same lt
  let w := Input.obstructions[i]
  obtain ⟨pat,arity,ne,left,right⟩ := counts i
  refine ⟨w.pattern,w.colors,?_,arity,?_⟩
  · rcases pat with h|h|h
    · exact h ▸ (drawing_of_tetraPrism (p:=.tetra) rfl)
    · exact h ▸ RegionalPlanar.drawing_nearClique
    · exact h ▸ Fifteen.drawing_bipyramid
  · rw [←hu,←hv,left,right]
    exact ne

end QGI.EightTwelveSigns
