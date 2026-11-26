import GroupTwelveCoordinates
import data.TwelveGroupWitnesses
import data.ZivAvEightTwelve

namespace QGI.RowCensus

private abbrev V := Fin 12
private def flat : FourThree ≃ V := finProdFinEquiv

private def four (t a b : Fin 4) : Fin 4 :=
  Fin.ofNat' 4 (digit 4 (fourOps.getD t.val 0) (4*a.val+b.val))

private def actions (p q r : Equiv.Perm (Fin 4)) (a : Fin 4) : Equiv.Perm (Fin 4) :=
  match a.val with
  | 0 => 1
  | 1 => p
  | 2 => q
  | _ => r

private theorem small : ∀ p q r : Equiv.Perm (Fin 4), (∀ a, actions p q r a 0=a) →
    (∀ a b c, actions p q r (actions p q r a b) c=actions p q r a (actions p q r b c)) →
    ∃ t : Fin 4, ∀ a b, actions p q r a b=four t a b := by native_decide

private theorem four_form {K : Type} [Group K] (f : Fin 4 ≃ K) (f0 : f 0=1) :
    ∃ t : Fin 4, ∀ a b, f (four t a b)=f a*f b := by
  let l (a : Fin 4) := f.trans ((Equiv.mulLeft (f a)).trans f.symm)
  let op := actions (l 1) (l 2) (l 3)
  have prod (a b : Fin 4) : f (op a b)=f a*f b := by
    fin_cases a <;> simp [op,actions,l,f0]
  obtain ⟨t,eq⟩ := small (l 1) (l 2) (l 3)
    (fun a => f.injective (by rw [prod,f0,mul_one]))
    (fun a b c => f.injective (by change f (op (op a b) c)=f (op a (op b c)); simp only [prod,mul_assoc]))
  exact ⟨t,fun a b => (congrArg f (eq a b)).symm.trans (prod a b)⟩

private def moves (x y z : V) (a : Fin 4) : FourThree :=
  match a.val with
  | 0 => (0,1)
  | 1 => flat.symm x
  | 2 => flat.symm y
  | _ => flat.symm z

private def jump (x y z : V) (w : FourThree) : FourThree :=
  let u := moves x y z w.1
  (u.1,u.2+w.2)

private def operation (t : Fin 4) (x y z : V) (i j : FourThree) : FourThree :=
  let r := (jump x y z)^[i.2.val] j
  (four t i.1 r.1,r.2)

private def witness (t : Fin 4) (x y z : V) : Fin 59 × Nat :=
  ((groupWitnesses.find? fun w => w.1==((t.val*12+x.val)*12+y.val)*12+z.val).getD default).2

def twelveCell (a : Fin 59) : Table 12 Nat := fun i j =>
  ((EightTwelveCatalog.rows12[a.val]?.getD default).cells >>> (4*(12*i.val+j.val)))%16

set_option maxRecDepth 50000 in
private theorem groupModels : ∀ (t : Fin 4) (x y z : V),
    (∀ i, (jump x y z)^[3] i=i) →
    (∀ i j k, operation t x y z (operation t x y z i j) k=operation t x y z i (operation t x y z j k)) →
    let w := witness t x y z
    let f := fun i => flat.symm (mapOf 12 w.2 i)
    Mono (n:=12) w.2 ∧ ∀ i j a b, twelveCell w.1 i j=twelveCell w.1 a b ↔
      ∀ u, (operation t x y z (f i) u=f j ↔ operation t x y z (f a) u=f b) := by native_decide

theorem twelve_thin {c : Table 12 V} (h : Laws c) (thin : ∀ i, Function.Injective (c i)) :
    ∃ a, Iso (twelveCell a) c := by
  classical
  obtain ⟨e,color⟩ := thin_quotients h thin
  obtain ⟨K,f,u,rep,f0,hu,coord⟩ := four_three (G:=colorGroup c) (colorGroup_card h thin)
  obtain ⟨t,table⟩ := four_form f f0
  let pos (a : Fin 4) := flat (rep.symm (u*(f a).val))
  let x := pos 1
  let y := pos 2
  let z := pos 3
  have head (a : Fin 4) : rep (moves x y z a)=u*(f a).val := by
    fin_cases a
    · simp [moves,coord,f0]
    all_goals simp [moves,x,y,z,pos]
  have modpow (v : Nat) : u^(v%3)=u^v := by simpa [hu] using pow_mod_orderOf u v
  have step (w : FourThree) : rep (jump x y z w)=u*rep w := by
    rcases w with ⟨b,k⟩
    let r := moves x y z b
    change rep (r.1,r.2+k)=_
    calc
      _ = ((f r.1).val*u^r.2.val)*u^k.val := by rw [coord,Fin.val_add,modpow,pow_add,mul_assoc]
      _ = rep r*u^k.val := by rw [← coord]
      _ = _ := by rw [show rep r=u*(f b).val from head _,coord,mul_assoc]
  have iter (k : Nat) (w : FourThree) : rep ((jump x y z)^[k] w)=u^k*rep w := by
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply',step,ih,pow_succ',mul_assoc]
  have multiply (a b : FourThree) : rep (operation t x y z a b)=rep a*rep b := by
    obtain ⟨i,j⟩ := a
    let s := (jump x y z)^[j.val] b
    change rep (four t i s.1,s.2)=_
    calc
      _ = (f i).val*rep s := by rw [coord,table,Subgroup.coe_mul,mul_assoc,← coord]
      _ = _ := by rw [show rep s=_ from iter j.val b,coord i j,mul_assoc]
  have cycle (i : FourThree) : (jump x y z)^[3] i=i := rep.injective (by rw [iter,← hu,pow_orderOf_eq_one,one_mul])
  obtain ⟨inj,ok⟩ := groupModels t x y z cycle (fun a b d => rep.injective (by simp only [multiply,mul_assoc]))
  let w := witness t x y z
  let p := Equiv.ofBijective (mapOf 12 w.2) (Finite.injective_iff_bijective.mp inj)
  let v := p.trans (flat.symm.trans rep)
  refine ⟨w.1,v.trans e,fun i j a b => (ok i j a b).trans (Iff.trans ?_ (color _ _ _ _))⟩
  change (∀ l, operation t x y z (flat.symm (p i)) l=flat.symm (p j) ↔
    operation t x y z (flat.symm (p a)) l=flat.symm (p b)) ↔ (v i)⁻¹*v j=(v a)⁻¹*v b
  have iff (i j : V) (l : FourThree) :
      operation t x y z (flat.symm (p i)) l=flat.symm (p j) ↔ rep l=(v i)⁻¹*v j := by
    rw [← rep.injective.eq_iff,multiply]
    exact eq_inv_mul_iff_mul_eq.symm
  simp only [iff]
  constructor
  · intro eq
    obtain ⟨l,hl⟩ := rep.surjective ((v i)⁻¹*v j)
    exact hl.symm.trans ((eq l).mp hl)
  · intro eq l
    rw [eq]

end QGI.RowCensus
