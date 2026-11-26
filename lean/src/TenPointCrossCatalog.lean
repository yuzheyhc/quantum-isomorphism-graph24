import SmallShoreLocal
import RowSupports
import RowBlockRoots
import RowValencies
import ThinRowOrbits
import data.RowCensus10
import Mathlib.Data.Finset.Powerset

namespace QGI.TenPointCross
abbrev V := Fin 10
abbrev Key := Fin 13
abbrev Cell := Finset V

/- The single-fiber rows of the published order-ten matrices, in archive order.
   ccs1_15n SHA-256: 083ed5646f8bbb35a2d0d9da09d42c21b6f62b93ee76bbfd98341654b233fc73. -/
def matrices : Array Nat := #[
  0x111111111101111111111011111111110111111111101111111111011111111110111111111101111111111011111111110,
  0x122222222102222222222012222222210222222222201222222221022222222220122222222102222222222012222222210,
  0x221121222201221122221021221221220212122121202221221212022121122220221221122202122221122012222221110,
  0x111122222101112222211011222221110122222111102222222222011112222210111222221101122222111012222211110,
  0x122223333102222333322013322332210332233223301332222331033223322330122332233102233332222013333222210,
  0x222133323202231332322023313232220333123133302223231332022323313220232333122203222223333013333222210,
  0x112233333102123333312021333332120133333221103333333333011223333310212333331202133333212013333322110,
  0x142355555201345555532041555551430255555432105555555555014235555520134555553204155555143025555543210,
  0x213243545203142534513023524543120534254243504152342534051233524150432534251403244552233015544332210,
  0x223451534203254513423034154253230144525545102234345152032431445230352415432305233225544015544332210,
  0x122553344102255334433012244553310224455443301552244331055222255440133225544103355443322015544332210,
  0x123456789109876543289012345673210987654678901234554321098764567890123765432109823456789019876543210,
  0x189674523109876543223018967453210987654452301896754321098766745230189765432109889674523019876543210]

def cell (a : Key) (i j : V) := (((matrices[a.val]?).getD 0) >>> (4*(10*i.val+j.val)))%16
def count (a : Key) (s : Cell) (i : V) (u : Nat) := (s.filter fun k => cell a i k=u).card
def valency (a : Key) (u : Nat) := count a Finset.univ 0 u
def sig (a : Key) (s : Cell) (i : V) := fun z : V => count a s i (cell a 0 z)

/-- A column of a color of smallest positive valency. Coherence forces the
same signature on flags, the indicated divisibilities, and large off-flag classes. -/
def Admits (a : Key) (d : Nat) (s : Cell) := s.card=d ∧
  (∀ i∈s, ∀ j∈s, sig a s i=sig a s j) ∧
  (∀ i∈s, ∀ z : V, valency a (cell a 0 z) ∣ d*sig a s i z) ∧
  ∀ i : V, i∉s → d≤(Finset.univ.filter (fun k => k∉s ∧ sig a s k=sig a s i)).card

instance (a : Key) (d : Nat) (s : Cell) : Decidable (Admits a d s) := by unfold Admits; infer_instance
attribute [local irreducible] matrices

private theorem checks (d : Nat) (hd : d=3 ∨ d=4) :
    ∀ a : Key, ((Finset.univ.powersetCard d).filter (fun s => Admits a d s ∧ ¬(d=4 ∧ (a=1 ∨ a=2 ∨ a=5)))).card=0 := by
  rcases hd with rfl|rfl <;> native_decide

theorem small_degree {a : Key} {d : Nat} {s : Cell} (hd : d=3 ∨ d=4) (h : Admits a d s) :
    d=4 ∧ (a=1 ∨ a=2 ∨ a=5) := by
  by_contra bad
  have inside := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s,h.1⟩
  have pos : 0<((Finset.univ.powersetCard d).filter (fun t => Admits a d t ∧ ¬(d=4 ∧ (a=1 ∨ a=2 ∨ a=5)))).card := Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨inside,And.intro h bad⟩⟩
  exact (Nat.ne_of_gt pos) (checks d hd a)

open RowCensus

private def orbitWitness (a : Fin 5) (b : V) : Key × Nat :=
  match 10*a.val+b.val with
  | 15 => (12,9483726150)
  | 16 => (12,7463529180)
  | 17 => (12,5493827160)
  | 18 => (12,8473625190)
  | 19 => (12,6453928170)
  | 45 => (11,9483726150)
  | _ => (0,0)

private theorem thinCheck : ∀ (a : Fin 5) (b : V), (∀ i j, otherRow a b i=otherRow a b j → i=j) →
    (∀ i j, orbitTable a b (otherRow a b i) (otherRow a b j)=orbitTable a b i j) →
    let w := orbitWitness a b
    let f := mapOf 10 w.2
    Mono (n:=10) w.2 ∧ ∀ i j x y, cell w.1 i j=cell w.1 x y ↔
      orbitTable a b (f i) (f j)=orbitTable a b (f x) (f y) := by native_decide

private theorem thinCatalog (m : Matrix 10) (h : Laws m) (thin : ∀ i, Function.Injective (m i)) :
    ∃ a, RowCensus.Iso (cell a) m := by
  obtain ⟨a,b,inj,keep,e,iso⟩ := thin_ten_form h thin
  obtain ⟨mono,check⟩ := thinCheck a b (fun _ _ eq => inj eq) keep
  let f := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp mono)
  exact ⟨(orbitWitness a b).1,f.trans e,fun i j x y => (check _ _ _ _).trans (iso (f i) (f j) (f x) (f y))⟩

private def firstRow (rs : List Nat) := List.ofFn fun j : V => entry 10 rs 0 j.val
private def cut (rs : List Nat) := rs.length == 1 &&
  (!(decide (thinCount (firstRow rs) ∣ 10)) || decide (∀ i j : V, entry 10 rs 0 i.val=entry 10 rs 0 j.val → i=j))

private theorem cut_sound (rs : List Nat) (m : Matrix 10) (cutoff : cut rs=true) (f : Fits m rs)
    (h : Laws m) : ∃ a, RowCensus.Iso (cell a) m := by
  simp only [cut,Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,
    decide_eq_true_eq] at cutoff
  have first (j : V) : entry 10 rs 0 j.val=(m 0 j).val := f 0 j (by simp [cutoff.1])
  rcases cutoff.2 with count|inj
  · exact (count (by simpa only [firstRow,first] using thinCount_dvd h)).elim
  · have m0 : Function.Injective (m 0) := fun i j eq => inj i j (by simp only [first,eq])
    apply thinCatalog m h
    intro i
    exact List.nodup_ofFn.mp ((h.row_perm i).nodup_iff.mpr (List.nodup_ofFn.mpr m0))

private def certificates := decode raw10

private def options (rs : List Nat) := if rs.isEmpty then blockRoots 10 else supportedRows 10 rs

set_option maxRecDepth 100000 in
private theorem verifiedRows : ∀ i : Fin certificates.size,
    cut (certificates[i.val]?.getD default).rows || verifiedBy cell options certificates i.val := by native_decide

theorem catalog (c : Table 10 Nat) (h : Laws c) : ∃ a, RowCensus.Iso (cell a) c :=
  by
    obtain ⟨m,p,_,hm,root,_,names⟩ := normalize_blocks c h
    obtain ⟨a,e,he⟩ := census_from cell certificates (by native_decide) (by native_decide) options
      (fun mat law rs f pos k hk => by
        have nz := List.length_pos_iff.mp pos
        simpa [options,nz] using supported_complete mat law rs f pos k hk)
      cut verifiedRows cut_sound m hm (by simpa [options] using root)
    exact ⟨a,e.trans p,fun i j x y => (he i j x y).trans (names _ _ _ _)⟩

end QGI.TenPointCross

namespace QGI.Literature
open TenPointCross Coherent.SmallShore

/-- Ziv-Av, Enumeration of coherent configurations of order at most 15,
section 2.1 and its GAP archive ccs1_15n, homogeneous entries of order ten.
https://actamath.savbb.sk/pdf/aumb2605.pdf -/
theorem zivAv_ten_homogeneous_catalog {v : Nat} (c : Table 10) (h : Local c v) :
  ∃ a : Key, ∃ e : Equiv.Perm V, ∀ i j x y : V,
    c (e i) (e j)=c (e x) (e y) ↔ cell a i j=cell a x y := by
  have diag := (h.diag 0 0).mpr rfl
  obtain ⟨a,e,eq⟩ := catalog c (RowCensus.of_intersections c (fun i j => by simpa only [diag] using h.diag i j)
    h.reverse h.products)
  exact ⟨a,e,fun i j x y => (eq i j x y).symm⟩

end QGI.Literature
