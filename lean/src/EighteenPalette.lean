import ZivAvIntrinsic
import HomogeneousUnions

namespace QGI.EighteenPalette
open SixteenMapSearch
open Homogeneous.Unions (rawTables colorAt)
open private Table Table.trans tab stages stage_congr sorted_eq perm_of_equiv coefficients histogram histogram_at get_ofFn from DoubleEightPrepared
open private nextChoice sorted atN from SixteenMapSearch

abbrev V := Fin 18
abbrev Index := Fin 90
private def tables := (rawTables 18).toArray
def row (a : Index) := tables[a.val]?.getD #[]
theorem in_archive {t} (mem : t ∈ rawTables 18) : ∃ a : Index, row a=t := by
  have all : (List.finRange 90).map row=rawTables 18 := by native_decide
  rw [←all] at mem
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
  exact ⟨i,rfl⟩

/-- Read one representative ordered pair of each color from the first row.
The complete tensor on all ordered pairs is checked separately below. -/
private def prepare (a : Index) : Scheme := Id.run do
  let t := row a
  let r := 1+(t[0]?.getD #[]).foldl max 0
  let mut tr := #[]
  let mut mul := Array.replicate (r*r*r) 0
  for k in [:r] do
    let y := ((List.range 18).find? (fun y => colorAt t 0 y == k)).getD 0
    tr := tr.push (colorAt t y 0)
    for z in [:18] do
      let atIndex := (k*r+colorAt t 0 z)*r+colorAt t z y
      mul := mul.set! atIndex (mul[atIndex]!+1)
  return {id:=a.val,colors:=#[],rank:=r,trans:=tr,tensor:=mul,keys:=#[],profile:=[]}

private def indexed := Vector.ofFn fun a : Index =>
  let s := prepare a
  let keys := (stages (tab s) 2).toArray
  {s with keys:=keys,profile:=sorted keys.toList}

def scheme (a : Index) := indexed.get a
private theorem bounds : ∀ a : Index, ∀ i j : V, colorAt (row a) i.val j.val < (scheme a).rank := by native_decide
def name (a : Index) (i j : V) : Fin (scheme a).rank := ⟨_,bounds a i j⟩
theorem table_color (a : Index) (i j : V) : colorAt (row a) i.val j.val=(name a i j).val := rfl

attribute [local irreducible] scheme row

private theorem facts : ∀ a : Index,
    (∀ k : Fin (scheme a).rank, ∃ x : V, name a 0 x=k) ∧
    (∀ x y : V, transposeName (scheme a) (name a x y).val=(name a y x).val) ∧
    (∀ i : Fin (scheme a).rank, refinedKey (scheme a) i.val=(stages (tab (scheme a)) 2).get i) ∧
    (scheme a).profile=sorted (List.ofFn fun i : Fin (scheme a).rank => refinedKey (scheme a) i.val) := by native_decide

theorem onto (a : Index) (k : Fin (scheme a).rank) : ∃ x y, name a x y=k := by
  obtain ⟨y,h⟩ := (facts a).1 k
  exact ⟨0,y,h⟩

private def histAt (a : Index) (x y : V) :=
  histogram (List.ofFn fun z : V => finProdFinEquiv (name a x z,name a z y))
private theorem counts : ∀ a : Index, ∀ x y : V,
    coefficients (scheme a) (name a x y)=histAt a x y := by native_decide
private theorem coeff_at (a : Index) (x y : V) (i j : Fin (scheme a).rank) :
    coefficient (scheme a) (name a x y).val i.val j.val =
      ∑ z : V, if name a x z=i ∧ name a z y=j then 1 else 0 := by
  have h := congrArg (fun v => Vector.get v (finProdFinEquiv (i,j))) (counts a x y)
  simpa only [coefficients,get_ofFn,Equiv.symm_apply_apply,histAt,histogram_at,List.map_ofFn,
    Function.comp_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq,List.sum_ofFn] using h

theorem eligible (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (tr : ∀ x y u v, e (name a x y)=name b u v → e (name a y x)=name b v u)
    (numbers : ∀ x y u v, e (name a x y)=name b u v → ∀ i j : Fin (scheme a).rank,
      (∑ z : V, if name a x z=i ∧ name a z y=j then 1 else 0 : Nat) =
      ∑ z : V, if name b u z=e i ∧ name b z v=e j then 1 else 0) :
    (scheme a).profile=(scheme b).profile ∧
      List.ofFn (fun i => (e i).val) ∈ enumeratedMaps (scheme a) (scheme b) := by
  have transpose (a : Index) (x y : V) : Table.trans (tab (scheme a)) (name a x y)=name a y x := by
    have h := (facts a).2.1 x y
    apply Fin.ext
    simp only [tab,dif_pos (show transposeName (scheme a) (name a x y).val < (scheme a).rank by omega)]
    exact h
  have rev (i : Fin (scheme a).rank) :
      e (Table.trans (tab (scheme a)) i)=Table.trans (tab (scheme b)) (e i) := by
    obtain ⟨x,y,h⟩ := onto a i
    obtain ⟨u,v,t⟩ := onto b (e i)
    have ht := tr x y u v ((congrArg e h).trans t.symm)
    rw [←h,transpose,h,←t,transpose]
    exact ht
  have mul (k i j : Fin (scheme a).rank) : coefficient (scheme a) k.val i.val j.val =
      coefficient (scheme b) (e k).val (e i).val (e j).val := by
    obtain ⟨x,y,h⟩ := onto a k
    obtain ⟨u,v,t⟩ := onto b (e k)
    rw [←h,coeff_at,h,←t,coeff_at]
    exact numbers _ _ _ _ ((congrArg e h).trans t.symm) _ _
  have keys (i : Fin (scheme a).rank) : refinedKey (scheme a) i.val=refinedKey (scheme b) (e i).val :=
    ((facts a).2.2.1 i).trans ((stage_congr _ _ e rev mul 2 i).trans ((facts b).2.2.1 (e i)).symm)
  refine ⟨(facts a).2.2.2.trans ((sorted_eq (perm_of_equiv _ _ _ keys)).trans (facts b).2.2.2.symm),
    mem_of_palette_equiv _ _ e keys ?_ mul⟩
  intro i j
  obtain ⟨x,y,h⟩ := onto a i
  obtain ⟨u,v,t⟩ := onto b (e i)
  have eq := tr _ _ _ _ ((congrArg e h).trans t.symm)
  rw [←h,(facts a).2.1,h,←t,(facts b).2.1,←eq]
  exact Fin.val_inj.trans (e.injective.eq_iff.symm.trans Fin.val_inj.symm)

private def search (t : Homogeneous.Unions.Table) (pi : Array Nat) :
    Nat → List Nat → List Nat → List (Nat × Nat) → Option (List (Nat × Nat))
  | 0, _, _, assigned => some assigned
  | fuel+1, pending, free, assigned => do
    let fits (x y : Nat) := ((x,y)::assigned).all fun (u,v) =>
      pi[colorAt t x u]?.getD pi.size == colorAt t y v &&
      pi[colorAt t u x]?.getD pi.size == colorAt t v y
    let (x,ys) ← nextChoice pending (fun x => free.filter (fits x))
    ys.findSome? fun y => search t pi fuel (pending.erase x) (free.erase y) ((x,y)::assigned)

private def placement (a : Index) (pi : List Nat) : Vector V 18 :=
  let vs := List.range 18
  let pairs := (search (row a) pi.toArray 18 vs vs []).getD []
  Vector.ofFn fun x : V =>
    Fin.ofNat' 18 (((pairs.find? fun p => p.1 == x.val).map Prod.snd).getD 0)

private def verified (a : Index) (pi : List Nat) : Bool :=
  let f := placement a pi
  decide ((∀ i j, f.get i=f.get j → i=j) ∧ ∀ i j, pi[(name a i j).val]?.getD pi.length=(name a (f.get i) (f.get j)).val)

/-- Inspect all ordered pairs of rows with equal intrinsic profiles and every
admissible palette map. A point witness is checked on all 324 entries. -/
private def checkPair (a b : Index) : Bool :=
  if (scheme a).profile ≠ (scheme b).profile then true else
  (enumeratedMaps (scheme a) (scheme b)).all fun pi =>
    decide (a=b) && (decide (a.val=59) || verified a pi)

set_option maxRecDepth 20000 in
private theorem census : ∀ a b : Index, checkPair a b=true := by native_decide

attribute [local irreducible] placement name in
theorem classify (a b : Index) (e : Fin (scheme a).rank ≃ Fin (scheme b).rank)
    (profile : (scheme a).profile=(scheme b).profile)
    (maps : List.ofFn (fun k => (e k).val) ∈ enumeratedMaps (scheme a) (scheme b)) :
    (∃ f : Equiv.Perm V, ∀ i j, e (name a i j)=name b (f i) (f j)) ∨ (a.val=59 ∧ b.val=59) := by
  have checked := census a b
  simp only [checkPair,profile,ne_self_iff_false,if_false,List.all_eq_true] at checked
  have ok := checked _ maps
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at ok
  obtain ⟨rfl,exception|witness⟩ := ok
  · exact Or.inr ⟨exception,exception⟩
  · let pi := List.ofFn fun i => (e i).val
    let f := (placement a pi).get
    change verified a pi=true at witness
    unfold verified at witness
    rw [decide_eq_true_eq] at witness
    obtain ⟨inj,entries⟩ := witness
    change Function.Injective f at inj
    change ∀ i j, pi[(name a i j).val]?.getD pi.length=(name a (f i) (f j)).val at entries
    have pt (i j : V) : e (name a i j)=name a (f i) (f j) := by
      apply Fin.ext
      simpa only [pi,List.getElem?_ofFn,dif_pos (name a i j).isLt,Option.getD_some] using entries i j
    exact Or.inl ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),pt⟩

end QGI.EighteenPalette
