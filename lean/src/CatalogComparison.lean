import FifteenChainSound
import StrategyColorLaws
import SmallConfiguration

namespace QGI.CatalogComparison
open Coherent.SmallUnion Coherent.StrategyColorLaws
open private perm_of_equiv sorted_eq get_ofFn from DoubleEightPrepared

structure Frame (n r : Nat) where
  name : Fin n → Fin n → Fin r
  spot : Fin r → Fin n × Fin n

variable {n r t : Nat}
abbrev Coord (r : Nat) := Fin r × Fin r
local instance {r : Nat} : BEq (Fin r × Fin r) := instBEqOfDecidableEq
private def hash := Fifteen.System.hash
private def sorted := Fifteen.System.sorted
private def path (F : Frame n r) (k : Fin r) (z : Fin n) : Coord r :=
  (F.name (F.spot k).1 z,F.name z (F.spot k).2)
private def rev (F : Frame n r) (k : Fin r) := F.name (F.spot k).2 (F.spot k).1
private def diag (F : Frame n r) (k : Fin r) := decide ((F.spot k).1=(F.spot k).2)
private def features (F : Frame n r) := Vector.ofFn fun k =>
  let ps := List.ofFn (path F k)
  ps.map fun p => (p.1,p.2,ps.count p)
private def start (F : Frame n r) (mark : Option (Fin r)) :=
  Vector.ofFn fun k => hash [(diag F k).toNat,(decide (rev F k=k)).toNat,(decide (mark=some k)).toNat]
private def step (F : Frame n r) (fs : Vector (List (Fin r × Fin r × Nat)) r) (v : Vector Nat r) :=
  Vector.ofFn fun k => hash (v.get k :: v.get (rev F k) ::
    sorted ((fs.get k).map fun p => hash [v.get p.1,v.get p.2.1,p.2.2]))
def signature (F : Frame n r) (mark : Option (Fin r)) :=
  let fs := features F
  let v := start F mark
  let w := step F fs (step F fs (step F fs v))
  hash (sorted (List.ofFn w.get))
def marked (F : Frame n r) := hash (sorted (List.ofFn fun k => signature F (some k)))

structure Respects (F : Frame n r) (T : Frame n t) (e : Fin r ≃ Fin t) : Prop where
  diagonal : ∀ k, diag F k=diag T (e k)
  transpose : ∀ k, e (rev F k)=rev T (e k)
  middle : ∀ k, ∃ h : Equiv.Perm (Fin n), ∀ z, (e.prodCongr e) (path F k z)=path T (e k) (h z)

private theorem step_eq {F : Frame n r} {T : Frame n t} {e : Fin r ≃ Fin t} (law : Respects F T e)
    (v : Vector Nat r) (w : Vector Nat t) (h : ∀ k, v.get k=w.get (e k)) (k : Fin r) :
    (step F (features F) v).get k=(step T (features T) w).get (e k) := by
  obtain ⟨p,hp⟩ := law.middle k
  let f := e.prodCongr e
  have perm : ((List.ofFn (path F k)).map f).Perm (List.ofFn (path T (e k))) := by
    rw [List.map_ofFn]
    exact perm_of_equiv p _ _ hp
  have cnt (z) : (List.ofFn (path F k)).count (path F k z) =
      (List.ofFn (path T (e k))).count (path T (e k) (p z)) := by
    rw [←hp]
    exact (List.count_map_of_injective _ f f.injective _).symm.trans (perm.count_eq _)
  let term {s : Nat} (v : Vector Nat s) (P : Fin n → Coord s) (z : Fin n) :=
    hash [v.get (P z).1,v.get (P z).2,(List.ofFn P).count (P z)]
  have pieces := perm_of_equiv p (term v (path F k)) (term w (path T (e k))) (fun z => by
    have a := congrArg Prod.fst (hp z)
    have b := congrArg Prod.snd (hp z)
    change e (path F k z).1 = (path T (e k) (p z)).1 at a
    change e (path F k z).2 = (path T (e k) (p z)).2 at b
    simp only [term,h,a,b,cnt])
  have ex {s} (P : Frame n s) (v : Vector Nat s) (k : Fin s) :
      (step P (features P) v).get k =
        hash (v.get k :: v.get (rev P k) :: sorted (List.ofFn (term v (path P k)))) := by
    simp only [step,features,get_ofFn,List.map_map,List.map_ofFn,Function.comp_def,term]
  rw [ex,ex,h,h,law.transpose,show sorted _=sorted _ from sorted_eq pieces]

theorem invariant {F : Frame n r} {T : Frame n t} {e : Fin r ≃ Fin t} (law : Respects F T e)
    (mark : Option (Fin r)) : signature F mark=signature T (mark.map e) := by
  have h (k) : (start F mark).get k=(start T (mark.map e)).get (e k) := by
    have revIff : (rev F k=k) ↔ rev T (e k)=e k := by rw [←law.transpose,e.injective.eq_iff]
    have marks : (mark=some k) ↔ mark.map e=some (e k) := by cases mark <;> simp [e.injective.eq_iff]
    simp only [start,get_ofFn,law.diagonal,decide_eq_decide.mpr revIff,decide_eq_decide.mpr marks]
  exact congrArg hash (sorted_eq (perm_of_equiv e _ _ (step_eq law _ _ (step_eq law _ _ (step_eq law _ _ h)))))

theorem invariant_marked {F : Frame n r} {T : Frame n t} {e : Fin r ≃ Fin t} (law : Respects F T e) :
    marked F=marked T :=
  congrArg hash (sorted_eq (perm_of_equiv e _ _ (fun k => invariant law (some k))))

/-- Individualize a color only on rows which refinement did not already
distinguish. Hash collisions merely demand more checking. -/
def ids {N n : Nat} {r : Fin N → Nat} (F : ∀ i, Frame n (r i)) :=
  let first := Vector.ofFn fun i => signature (F i) none
  Vector.ofFn fun i =>
    let x := first.get i
    let conflict := (List.finRange N).any fun j => j != i && first.get j == x
    (x, if conflict then marked (F i) else 0)

theorem ids_eq {N n} {r : Fin N → Nat} (F : ∀ i, Frame n (r i)) {a b}
    {e : Fin (r a) ≃ Fin (r b)} (h : Respects (F a) (F b) e) : (ids F).get a=(ids F).get b := by
  classical
  have eq : signature (F a) none=signature (F b) none := invariant h none
  by_cases same : a=b
  · rw [same]
  have collision (i j : Fin N) (diff : j≠i) (hit : signature (F j) none=signature (F i) none) :
      (List.finRange N).any (fun k => k != i && signature (F k) none == signature (F i) none) = true :=
    List.any_eq_true.mpr ⟨j,List.mem_finRange _,by simp [diff,hit]⟩
  simp only [ids,get_ofFn]
  rw [collision a b (Ne.symm same) eq.symm,collision b a same eq]
  simp only [if_true,eq,invariant_marked h,reduceCtorEq]

/-- Matching intersection numbers give a bijection of the intermediate vertices
for each matched pair, even when diagonal classes have different sizes. -/
structure Common (c d : Table n) : Prop where
  used : ∀ s, (∃ i j,c i j=s) ↔ ∃ x y,d x y=s
  numbers : ∀ s t i j x y, c i j=d x y → count c s t i j=count d s t x y

theorem intermediate {c d : Table n} (C : Common c d) {i j x y} (h : c i j=d x y) :
    ∃ p : Equiv.Perm (Fin n), ∀ z, c i z=d x (p z) ∧ c z j=d (p z) y :=
  by
    classical
    let f := fun z => (c i z,c z j)
    let g := fun z => (d x z,d z y)
    have card (k : Nat × Nat) : Fintype.card {z // f z=k} = Fintype.card {z // g z=k} := by
      rcases k with ⟨a,b⟩
      simpa [f,g,Fintype.card_subtype,Prod.mk.injEq,count] using C.numbers a b _ _ _ _ h
    let family := fun k => Fintype.equivOfCardEq (card k)
    exact ⟨Equiv.ofFiberEquiv family,fun z => Prod.mk.inj (Equiv.ofFiberEquiv_map family z).symm⟩

theorem ends {c d : Table n} (hc : Configuration c) (hd : Configuration d) (C : Common c d)
    {i j x y} (hit : c i j=d x y) : c i i=d x x ∧ c j j=d y y := by
  obtain ⟨p,h⟩ := intermediate C hit
  have D : Common d c := ⟨fun s => (C.used s).symm,fun s t x y i j eq => (C.numbers s t i j x y eq.symm).symm⟩
  have diagMatch (z : Fin n) : ∃ a, c z z=d a a := by
    obtain ⟨u,v,eq⟩ := (C.used _).mp ⟨z,z,rfl⟩
    obtain ⟨q,hq⟩ := intermediate D eq
    have hv := hc.diagonal _ _ _ ((hq u).2.symm.trans eq)
    exact ⟨u,by simpa only [hv] using (hq u).1.symm⟩
  obtain ⟨a,ha⟩ := diagMatch i
  obtain ⟨b,hb⟩ := diagMatch j
  have ix := hd.diagonal _ _ _ ((h i).1.symm.trans ha)
  have jy := hd.diagonal _ _ _ ((h j).2.symm.trans hb)
  exact ⟨by simpa only [←ix] using (h i).1,by simpa only [jy] using (h j).2⟩

theorem large_target {c d : Table n} (hc : Configuration c) (hd : Configuration d) (C : Common c d)
    {m : Nat} (large : ∀ i, m≤(Finset.univ.filter (fun j => c j j=c i i)).card) :
    ∀ x, m≤(Finset.univ.filter (fun y => d y y=d x x)).card := by
  intro x
  obtain ⟨i,j,h⟩ := (C.used _).mpr ⟨x,x,rfl⟩
  have diag := (ends hc hd C h).1
  obtain ⟨p,hp⟩ := intermediate C diag
  have eq := Finset.card_equiv p (s:=Finset.univ.filter (fun z => c z z=c i i))
    (t:=Finset.univ.filter (fun z => d z z=d x x)) (fun z => by simp only [Finset.mem_filter,Finset.mem_univ,true_and,
      (ends hc hd C (hp z).1).2,diag])
  exact (large i).trans_eq eq

structure Placement {n r : Nat} (F : Frame n r) (c : Table n) where
  points : Equiv.Perm (Fin n)
  labels : Fin r ↪ Nat
  cell : ∀ i j, c (points i) (points j)=labels (F.name i j)

theorem palette {F : Frame n r} {T : Frame n t} {c d : Table n} (C : Common c d) (A : Placement F c) (B : Placement T d)
    (sf : ∀ k, F.name (F.spot k).1 (F.spot k).2=k)
    (st : ∀ k, T.name (T.spot k).1 (T.spot k).2=k) :
    ∃ e : Fin r ≃ Fin t, ∀ k, A.labels k=B.labels (e k) := by
  classical
  have hit {r t} {F : Frame n r} {T : Frame n t} {c d : Table n} (A : Placement F c) (B : Placement T d)
      (used : ∀ s, (∃ i j,c i j=s) ↔ ∃ x y,d x y=s) (sf : ∀ k, F.name (F.spot k).1 (F.spot k).2=k)
      (k : Fin r) : ∃ l, A.labels k=B.labels l := by
    obtain ⟨x,y,eq⟩ := (used _).mp ⟨_,_,(A.cell _ _).trans (congrArg A.labels (sf k))⟩
    exact ⟨_,eq.symm.trans (by simpa using B.cell (B.points.symm x) (B.points.symm y))⟩
  choose f hf using hit A B C.used sf
  have inj : Function.Injective f := fun i j h => A.labels.injective ((hf i).trans ((congrArg B.labels h).trans (hf j).symm))
  have surj : Function.Surjective f := fun y => by
    obtain ⟨x,hx⟩ := hit B A (fun s => (C.used s).symm) st y
    exact ⟨x,B.labels.injective ((hf x).symm.trans hx.symm)⟩
  exact ⟨Equiv.ofBijective f ⟨inj,surj⟩,hf⟩

/-- The supplied row numbers may differ. The prescribed common names determine
a bijection of both palettes and transport every two-step path multiset. -/
theorem compatible {F : Frame n r} {T : Frame n t} {c d : Table n} (hc : Configuration c)
    (hd : Configuration d) (C : Common c d) (A : Placement F c) (B : Placement T d)
    (sf : ∀ k, F.name (F.spot k).1 (F.spot k).2=k)
    (st : ∀ k, T.name (T.spot k).1 (T.spot k).2=k) :
    ∃ e : Fin r ≃ Fin t, Respects F T e := by
  obtain ⟨e,hf⟩ := palette C A B sf st
  have same (i j x y) : e (F.name i j)=T.name x y ↔ c (A.points i) (A.points j)=d (B.points x) (B.points y) := by
    rw [A.cell,B.cell,hf,B.labels.injective.eq_iff]
  refine ⟨e,?_,?_,?_⟩
  · intro k
    have eq := (same _ _ _ _).mp ((congrArg e (sf k)).trans (st (e k)).symm)
    obtain ⟨left,_⟩ := ends hc hd C eq
    apply decide_eq_decide.mpr
    constructor
    · intro h; rw [h] at eq left
      exact B.points.injective (hd.diagonal _ _ _ (eq.symm.trans left))
    · intro h; rw [h] at eq left
      exact A.points.injective (hc.diagonal _ _ _ (eq.trans left.symm))
  · intro k
    have eq := (same _ _ _ _).mp ((congrArg e (sf k)).trans (st (e k)).symm)
    obtain ⟨left,_⟩ := ends hc hd C eq
    obtain ⟨p,hp⟩ := intermediate C left
    have v := hp (A.points (F.spot k).2)
    exact (same _ _ _ _).mpr (v.2.trans (hd.reverse _ _ _ _ (v.1.symm.trans eq)))
  · intro k
    have eq := (same _ _ _ _).mp ((congrArg e (sf k)).trans (st (e k)).symm)
    obtain ⟨p,hp⟩ := intermediate C eq
    refine ⟨A.points.trans (p.trans B.points.symm),fun z => Prod.ext ((same _ _ _ _).mpr ?_) ((same _ _ _ _).mpr ?_)⟩
    · simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using (hp (A.points z)).1
    · simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using (hp (A.points z)).2

end QGI.CatalogComparison

