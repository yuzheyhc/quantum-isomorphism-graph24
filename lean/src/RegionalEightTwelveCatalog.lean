import data.ZivAvEightTwelve
import SmallShoreLocal
import DoubleEightShoreCensus
import TwelveCatalog

namespace QGI.EightTwelveCatalog
abbrev Point := Fin 12
abbrev Label := Fin 4

def digit (word i : Nat) := (word >>> (4*i)) % 16

def row (k : Nat) (a : Nat) := (if k=8 then rows8 else rows12)[a]?.getD default

def cell {k : Nat} (r : Row) (i j : Fin k) := digit r.cells (k*i.val+j.val)
def tag (s : System) (i : Point) : Label := Fin.ofNat' 4 (digit s.tag i.val)
def mapPoint (word : Nat) (i : Point) : Point := Fin.ofNat' 12 (digit word i.val)
def mapLabel (word : Nat) (i : Label) : Label := Fin.ofNat' 4 (digit word i.val)

def Thin (c : Point → Point → Nat) := ∀ i, Function.Injective (c i)
def Closed (c : Point → Point → Nat) (q : Point → Label) := ∀ p : Equiv.Perm Label,
  (∀ i j, ∃ x y, q x=p (q i) ∧ q y=p (q j) ∧ c i j=c x y) →
  ∃ h : Equiv.Perm Point, (∀ i, q (h i)=p (q i)) ∧ ∀ i j, c i j=c (h i) (h j)

def relation (r : Row) (seed : Finset Point) (i j : Point) : Bool :=
  decide ((seed.filter fun k => cell r 0 k=cell r i j).Nonempty)

private def full (r : Row) (u : Finset Point) : Bool := decide
  ((∀ i, relation r u i i=true) ∧ (∀ i, (Finset.univ.filter (fun j => relation r u i j=true)).card=3) ∧
   ∀ i j k, relation r u i j=true → relation r u i k=relation r u j k)

private def fits (r : Row) (u : Finset Point) (s : System) : Bool :=
  decide ((∀ i j, relation r u i j=decide (tag s i=tag s j)) ∧ Function.Surjective (tag s))

private def uncovered (r : Row) (u : Finset Point) : Bool :=
  decide ((0 : Point)∈u) && full r u && !(r.systems.any (fits r u))

private def lift (r : Row) (s : System) (p : Equiv.Perm Label) (d : Nat × Nat) : Bool := decide
  ((∀ i, mapLabel d.1 i=p i) ∧ Function.Injective (mapPoint d.2) ∧
    (∀ i, tag s (mapPoint d.2 i)=mapLabel d.1 (tag s i)) ∧
    ∀ i j, cell r i j=cell r (mapPoint d.2 i) (mapPoint d.2 j))

private instance (r : Row) : Decidable (Thin (cell r)) := by unfold Thin Function.Injective; infer_instance

private def checkedSystem (r : Row) (s : System) : Bool :=
  decide (Thin (cell r)) || decide (∀ p : Equiv.Perm Label,
    (∀ i j, ∃ x y, tag s x=p (tag s i) ∧ tag s y=p (tag s j) ∧ cell r i j=cell r x y) →
    s.lifts.any (lift r s p)=true)

private def checkedRow (r : Row) : Bool :=
  decide (((Finset.univ.powersetCard 3).filter (fun u => uncovered r u=true)).card=0) &&
  r.systems.all (checkedSystem r) && decide (∀ i j : Point, ∃ k : Point, cell r i j=cell r 0 k)

attribute [local irreducible] row rows12 rows8

set_option maxRecDepth 20000 in
private theorem checked : ∀ a : Fin 59, checkedRow (row 12 a.val)=true := by native_decide

private theorem checkedFacts (a : Fin 59) :
    ((Finset.univ.powersetCard 3).filter (fun u => uncovered (row 12 a.val) u=true)).card=0 ∧
    (∀ s∈(row 12 a.val).systems, checkedSystem (row 12 a.val) s=true) ∧
    ∀ i j : Point, ∃ k : Point, cell (row 12 a.val) i j=cell (row 12 a.val) 0 k := by
  have h := checked a
  simpa only [checkedRow,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc] using h

private theorem forSystem (r : Row) (s : System) (ok : checkedSystem r s=true) : Thin (cell r) ∨ Closed (cell r) (tag s) := by
  simp only [checkedSystem,Bool.or_eq_true,decide_eq_true_eq] at ok
  rcases ok with yes|all
  · exact Or.inl yes
  right; intro p agree
  obtain ⟨d,_,h⟩ := List.any_eq_true.mp (all p agree)
  obtain ⟨label,mono,cls,entry⟩ := of_decide_eq_true h
  exact ⟨Equiv.ofBijective (mapPoint d.2) (Finite.injective_iff_bijective.mp mono),fun i => (cls i).trans (label _),entry⟩

/-- The four labels of two surjective partitions with the same classes differ by a permutation. -/
theorem label_equiv {I : Type} (a b : I → Label) (onto : Function.Surjective a) (full : Function.Surjective b)
    (same : ∀ i j, a i=a j ↔ b i=b j) : ∃ h : Equiv.Perm Label, ∀ i, h (a i)=b i := by
  classical
  choose x hx using onto
  let f := fun i => b (x i)
  have step (i) : f (a i)=b i := (same _ _).mp (hx _)
  have surj : Function.Surjective f := by
    intro v; obtain ⟨i,rfl⟩ := full v; exact ⟨a i,step i⟩
  exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.mp surj),step⟩

end QGI.EightTwelveCatalog

namespace QGI.Literature
open Coherent.SmallShore EightTwelveCatalog

/-- Completeness of all 59 twelve-point models from the independently checked row and group classifications. -/
theorem zivAv_twelve_homogeneous_catalog {d : Nat} (c : Table 12) (hc : Local c d) :
    ∃ a : Fin 59, ∃ e : Equiv.Perm (Fin 12), ∀ i j x y,
      c (e i) (e j)=c (e x) (e y) ↔ cell (row 12 a.val) i j=cell (row 12 a.val) x y := by
  have diag := (hc.diag 0 0).mpr rfl
  have h := RowCensus.of_intersections c (fun i j => by simpa only [diag] using hc.diag i j) hc.reverse hc.products
  obtain ⟨a,e,iso⟩ := TwelveCatalog.complete c h
  exact ⟨a,e,fun i j x y => (iso i j x y).symm⟩

private def eightMaps : Array (Fin 21 × Nat) := #[
  (0,16434824),(1,9350264),(2,9248680),(3,6954360),(6,9248680),(7,9248680),
  (4,9909368),(5,11744376),(9,13965560),(11,14038136),(8,14038136),(10,14038136),
  (12,9248680),(14,9248680),(13,9248680),(15,9248680),(20,16431240),(18,14021392),
  (17,15655584),(19,16114448),(16,13562528)]

private def eightIndex (a : Fin 21) := (eightMaps.getD a.val default).1
private def eightPerm (a : Fin 21) := RowCensus.mapOf 8 (eightMaps.getD a.val default).2

private theorem eightMatch : ∀ a : Fin 21, (∀ i j, eightPerm a i=eightPerm a j → i=j) ∧
    ∀ i j x y, DoubleEight.ShoreCensus.seed a (eightPerm a i) (eightPerm a j)=
      DoubleEight.ShoreCensus.seed a (eightPerm a x) (eightPerm a y) ↔
      cell (row 8 (eightIndex a).val) i j=cell (row 8 (eightIndex a).val) x y := by native_decide

theorem eight_homogeneous_catalog {d : Nat} (c : Table 8) (hc : Local c d) :
    ∃ a : Fin 21, ∃ e : Equiv.Perm (Fin 8), ∀ i j x y,
      c (e i) (e j)=c (e x) (e y) ↔ cell (row 8 a.val) i j=cell (row 8 a.val) x y := by
  have diag := (hc.diag 0 0).mpr rfl
  obtain ⟨a,e,iso⟩ := DoubleEight.ShoreCensus.every_shore c
    ⟨fun i j => by simpa only [diag] using hc.diag i j,hc.reverse,fun i j x y eq u v => hc.products u v i j x y eq⟩
  obtain ⟨inj,matchEq⟩ := eightMatch a
  let p := Equiv.ofBijective (eightPerm a) (Finite.injective_iff_bijective.mp inj)
  exact ⟨eightIndex a,p.trans e,fun i j x y => (iso (p i) (p j) (p x) (p y)).symm.trans (matchEq i j x y)⟩

theorem zivAv_eight_twelve_homogeneous_catalog {k d : Nat} (order : k=8 ∨ k=12)
    (c : Table k) (hc : Local c d) : ∃ a : Fin (if k=8 then 21 else 59),
    ∃ e : Equiv.Perm (Fin k), ∀ i j x y : Fin k,
      c (e i) (e j)=c (e x) (e y) ↔ cell (row k a.val) i j=cell (row k a.val) x y := by
  rcases order with rfl|rfl
  · exact eight_homogeneous_catalog c hc
  · exact zivAv_twelve_homogeneous_catalog c hc

end QGI.Literature

namespace QGI.EightTwelveCatalog
open Coherent.SmallShore

private theorem on_model (a : Fin 59) (q : Point → Label) (classes : ∀ t, (Finset.univ.filter (fun i => q i=t)).card=3)
    (equitable : ∀ i j x y : Point, cell (row 12 a.val) i j=cell (row 12 a.val) x y → (q i=q j ↔ q x=q y)) :
    Thin (cell (row 12 a.val)) ∨ Closed (cell (row 12 a.val)) q := by
  classical
  let r := row 12 a.val
  let u := Finset.univ.filter (fun i => q i=q 0)
  obtain ⟨coverage,verified,occur⟩ := checkedFacts a
  have read (i j) : relation r u i j=true ↔ q i=q j := by
    change decide ((u.filter (fun k => cell r 0 k=cell r i j)).Nonempty)=true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨k,hk⟩
      obtain ⟨inside,hit⟩ := Finset.mem_filter.mp hk
      exact (equitable 0 k i j hit).mp (Finset.mem_filter.mp inside).2.symm
    · intro eq
      obtain ⟨k,hit⟩ := occur i j
      exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,((equitable i j 0 k hit).mp eq).symm⟩,hit.symm⟩⟩
  have interpreted (i j) : relation r u i j=decide (q i=q j) := Bool.eq_iff_iff.mpr (by simp only [read,decide_eq_true_eq])
  have all : full r u=true := by
    apply decide_eq_true
    refine ⟨fun i => (read i i).mpr rfl,?_,?_⟩
    · intro i
      have eq : Finset.univ.filter (fun j => relation r u i j=true)=Finset.univ.filter (fun j => q j=q i) := by
        ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and,read,eq_comm]
      rw [eq]; exact classes _
    · intro i j k same; rw [interpreted,interpreted,(read i j).mp same]
  obtain ⟨s,mem,same⟩ : ∃ s∈r.systems, fits r u s=true := by
    by_contra missed
    have bad : uncovered r u=true := by
      have zero : (0 : Point)∈u := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
      have none : r.systems.any (fits r u)=false := Bool.eq_false_of_not_eq_true (fun z => missed (List.any_eq_true.mp z))
      simp [uncovered,zero,none,all]
    have incl : u∈Finset.univ.powersetCard 3 := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,classes _⟩
    exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨u,Finset.mem_filter.mpr ⟨incl,bad⟩⟩)) coverage
  obtain ⟨fit,sonto⟩ := of_decide_eq_true same
  have qonto : Function.Surjective q := by
    intro t
    obtain ⟨i,hi⟩ := Finset.card_pos.mp ((by decide : 0<3).trans_eq (classes t).symm)
    exact ⟨i,(Finset.mem_filter.mp hi).2⟩
  obtain ⟨d,hd⟩ := label_equiv q (tag s) qonto sonto (fun i j => by
    rw [←read,fit]; simp only [decide_eq_true_eq])
  rcases forSystem r s (verified s mem) with thin | closed
  · exact Or.inl thin
  right; intro p agree
  let b := d.symm.trans (p.trans d)
  have value (i) : b (tag s i)=d (p (q i)) := by rw [←hd]; simp only [b,Equiv.trans_apply,Equiv.symm_apply_apply]
  obtain ⟨f,shape,names⟩ := closed b (by
    intro i j
    obtain ⟨x,y,hx,hy,eq⟩ := agree i j
    exact ⟨x,y,(hd x).symm.trans ((congrArg d hx).trans (value i).symm),
      (hd y).symm.trans ((congrArg d hy).trans (value j).symm),eq⟩)
  exact ⟨f,fun i => d.injective ((hd (f i)).trans ((shape i).trans (value i))),names⟩

/-- For a named twelve-point homogeneous scheme, every invariant partition
into four triples is either on a thin scheme or has a two-closed action on its labels. -/
theorem thin_or_closed {d : Nat} (c : Table 12) (localData : Local c d) (q : Point → Label)
    (classes : ∀ t, (Finset.univ.filter (fun i => q i=t)).card=3)
    (equitable : ∀ i j x y : Point, c i j=c x y → (q i=q j ↔ q x=q y)) : Thin c ∨ Closed c q := by
  obtain ⟨a,e,ec⟩ := Literature.zivAv_eight_twelve_homogeneous_catalog (Or.inr rfl) c localData
  let t := q ∘ e
  have cl (z) : (Finset.univ.filter (fun i => t i=z)).card=3 := by
    have move : (Finset.univ.filter (fun i => t i=z)).map e.toEmbedding=Finset.univ.filter (fun i => q i=z) := by
      ext i
      obtain ⟨x,rfl⟩ := e.surjective i
      simp [t]
    exact (Finset.card_map _).symm.trans ((congrArg Finset.card move).trans (classes z))
  rcases on_model a t cl (fun i j x y h => equitable _ _ _ _ ((ec i j x y).mpr h)) with thin|closed
  · left; intro i j k eq
    obtain ⟨x,rfl⟩ := e.surjective i
    obtain ⟨y,rfl⟩ := e.surjective j
    obtain ⟨z,rfl⟩ := e.surjective k
    exact congrArg e (thin x ((ec x y x z).mp eq))
  right; intro p agree
  obtain ⟨f,parts,names⟩ := closed p (by
    intro i j
    obtain ⟨x,y,hx,hy,h⟩ := agree (e i) (e j)
    obtain ⟨u,rfl⟩ := e.surjective x
    obtain ⟨v,rfl⟩ := e.surjective y
    exact ⟨u,v,hx,hy,(ec i j u v).mp h⟩)
  let g := e.symm.trans (f.trans e)
  refine ⟨g,?_,?_⟩
  · intro i
    obtain ⟨x,rfl⟩ := e.surjective i
    simpa only [g,t,Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply] using parts x
  · intro i j
    obtain ⟨x,rfl⟩ := e.surjective i
    obtain ⟨y,rfl⟩ := e.surjective j
    simpa only [g,Equiv.trans_apply,Equiv.symm_apply_apply] using (ec x y (f x) (f y)).mpr (names x y)

end QGI.EightTwelveCatalog

