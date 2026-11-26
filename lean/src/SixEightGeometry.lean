import SixEightModel
import RepeatedTetra

noncomputable section
namespace QGI.Coherent.SixEightGeometry
open Relations SixTenCoordinates StrategyColorLaws
open FourTwelveFunctional (source)
open SixEightCatalog (Six Eight)

abbrev rect {n l r} {c : Fin n → Fin n → Nat} {I J : Type} (S : Shore c l I) (Y : Shore c r J) (i : I) (j : J) :=
  c (atPoint S i) (atPoint Y j)

open Classical in
theorem count_equiv {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) (P : I → Prop) (Q : J → Prop)
    [DecidablePred P] [DecidablePred Q] (eq : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card=(Finset.univ.filter Q).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(eq i).mp (Finset.mem_filter.mp hi).2⟩
  · exact fun _ _ _ _ h => e.injective h
  · intro j hj
    obtain ⟨i,rfl⟩ := e.surjective j
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(eq i).mpr (Finset.mem_filter.mp hj).2⟩,rfl⟩

structure Cube {n l r} {c : Fin n → Fin n → Nat} (S : Shore c l Six) (Y : Shore c r Eight) : Prop where
  small : ∀ i j, (Finset.univ.filter (fun b => rect Y Y i b=rect Y Y i j)).card≤3
  lift : ∀ e : Equiv.Perm Six, (∀ i j, rect S S (e i) (e j)=rect S S i j) →
    ∃ g : Equiv.Perm Eight, (∀ i j, rect S Y (e i) (g j)=rect S Y i j) ∧ ∀ i j, rect Y Y (g i) (g j)=rect Y Y i j

theorem classify {n l r} {G : Graph n} (diff : l≠r) (S : Shore (source G) l Six) (Y : Shore (source G) r Eight) :
    ((∀ i j, rect S Y i j=rect S Y 0 0) ∨ ∀ j i, (Finset.univ.filter (fun b => rect S Y b j=rect S Y i j)).card≤3) ∧
    (SplitRectangle.Twins (rect S Y) ∨ (∃ v w, v≠w ∧ Nonempty (RepeatedTetra.Repeated 2 S Y v w)) ∨ Cube S Y) := by
  classical
  obtain ⟨a,u,w,N,ls,rs,cross,internal,shore⟩ := SixEightModel.represent diff S Y
  have cp (i j) : rect S Y (u i) (w j)=N (SixEightCatalog.M a i j) := cross i j
  have si (i j) : rect S S (u i) (u j)=N (SixEightCatalog.A a i j) := internal i j
  have sy (i j) : rect Y Y (w i) (w j)=N (SixEightCatalog.B a i j) := shore i j
  constructor
  · rcases SixEightCatalog.nonuniform_columns a ls rs with flat|few
    · apply Or.inl; intro i j
      obtain ⟨i,rfl⟩ := u.surjective i
      obtain ⟨j,rfl⟩ := w.surjective j
      obtain ⟨i₀,hi₀⟩ := u.surjective 0
      obtain ⟨j₀,hj₀⟩ := w.surjective 0
      rw [←hi₀,←hj₀,cp,cp,flat,flat i₀ j₀]
    · apply Or.inr; intro j i
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨i,rfl⟩ := u.surjective i
      apply LE.le.trans (le_of_eq (count_equiv u.symm _ _ ?_)) (few j i)
      intro b; obtain ⟨b,rfl⟩ := u.surjective b
      simp only [Equiv.symm_apply_apply,cp,N.injective.eq_iff]
  rcases SixEightCatalog.geometry a ls rs with twin|tet|cube
  · apply Or.inl
    constructor
    · intro i b j eq t
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨b,rfl⟩ := u.surjective b
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨t,rfl⟩ := w.surjective t
      rw [cp,cp,N.injective.eq_iff] at eq ⊢
      exact Fin.ext (twin.1 i b j (congrArg Fin.val eq) t)
    · intro i j t eq b
      obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨b,rfl⟩ := u.surjective b
      obtain ⟨j,rfl⟩ := w.surjective j; obtain ⟨t,rfl⟩ := w.surjective t
      rw [cp,cp,N.injective.eq_iff] at eq ⊢
      exact Fin.ext (twin.2 i j t (congrArg Fin.val eq) b)
  · apply Or.inr; apply Or.inl
    let E := (Equiv.ofBijective _ SixEightCatalog.edge_perm).trans u
    let L := (Equiv.ofBijective _ (SixEightCatalog.slot_perm a)).trans w
    let v := rect Y S (w 0) (u 0)
    let z := rect Y S (w 0) (u 1)
    have ne : v≠z := fun eq => tet.1 (N.injective ((cp 0 0).symm.trans ((Relations.transpose _ eq).trans (cp 1 0))))
    refine ⟨v,z,ne,⟨⟨E,L,?_⟩⟩⟩
    intro q k e
    have h := (cp _ _).trans (congrArg N (tet.2 e q k))
    by_cases mem : q∈FourTwelveCycle.edge e
    · rw [if_pos mem] at h ⊢
      exact Relations.transpose _ (h.trans (cp 0 0).symm)
    · rw [if_neg mem] at h ⊢
      exact Relations.transpose _ (h.trans (cp 1 0).symm)
  · apply Or.inr; apply Or.inr
    constructor
    · intro i j; obtain ⟨i,rfl⟩ := w.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
      apply LE.le.trans (le_of_eq (count_equiv w.symm _ _ ?_)) (SixEightCatalog.cube_shore a cube i j)
      intro b; obtain ⟨b,rfl⟩ := w.surjective b
      simp only [Equiv.symm_apply_apply,sy,N.injective.eq_iff]
    · intro e he
      let f := u.trans (e.trans u.symm)
      have back (i) : u (f i)=e (u i) := by simp [f]
      have auto (i j) : SixEightCatalog.A a (f i) (f j)=SixEightCatalog.A a i j := by
        apply N.injective; rw [←si,←si,back,back]; exact he _ _
      obtain ⟨g,hg,hh⟩ := SixEightCatalog.cube_extend a cube f auto
      let z := w.symm.trans (g.trans w)
      have val (j) : z (w j)=w (g j) := by simp [z]
      refine ⟨z,?_,?_⟩
      · intro i j; obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
        rw [←back,val,cp,cp,hg]
      · intro i j; obtain ⟨i,rfl⟩ := w.surjective i; obtain ⟨j,rfl⟩ := w.surjective j
        rw [val,val,sy,sy,hh]

end QGI.Coherent.SixEightGeometry
