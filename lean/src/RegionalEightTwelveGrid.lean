import RegionalEightTwelveQuotient
import RegionalEightTwelvePartitions

noncomputable section
namespace QGI.Coherent.RegionalEightTwelveGrid
open Intertwiner Synchrony StrategyColorLaws SixTenCoordinates RegionalEightTwelveGeometry RegionalEightTwelveStats
open RegionalEightTwelvePartitions (Split Label)
open SmallUnion SmallFiberExtension
open FourTwelveFunctional (source)
open private range from RegionalSixTwelveDispatch
open private linked from RegionalEightTwelveThin

private theorem missing (a b : Index → Label) (size : ∀ i, (Finset.univ.filter fun j => a j=i).card=3)
    (inj : ∀ x y, a x=a y → b x=b y → x=y) (i : Label) : ∃! j, ¬∃ k, a k=i ∧ b k=j := by
  let s := Finset.univ.filter fun j => a j=i
  let im := s.image b
  have count : im.card=3 := (Finset.card_image_iff.mpr (fun x hx y hy eq =>
    inj x y ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) eq)).trans (size i)
  have complement : imᶜ.card=1 := by rw [Finset.card_compl,count,Fintype.card_fin]
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp complement
  have read (x) : (¬∃ k, a k=i ∧ b k=x) ↔ x∈imᶜ := by simp [im,s]
  refine ⟨z,(read z).mpr (by rw [hz]; simp),fun y hy => ?_⟩
  have atY := (read y).mp hy; rwa [hz,Finset.mem_singleton] at atY

theorem labels (a b : Index → Label) (sa : ∀ i, (Finset.univ.filter fun j => a j=i).card=3)
    (sb : ∀ i, (Finset.univ.filter fun j => b j=i).card=3)
    (inj : ∀ x y, a x=a y → b x=b y → x=y) :
    ∃ d : Equiv.Perm Label, ∀ i j, i≠j ↔ ∃ k, a k=i ∧ d (b k)=j := by
  classical
  choose m hm unique using fun i => missing a b sa inj i
  have mono : Function.Injective m := by
    intro i j eq
    obtain ⟨v,_,hv⟩ := missing b a sb (fun i j h k => inj i j k h) (m i)
    have first : ¬∃ k, b k=m i ∧ a k=i := fun ⟨k,h,t⟩ => hm i ⟨k,t,h⟩
    have second : ¬∃ k, b k=m i ∧ a k=j := fun ⟨k,h,t⟩ => hm j ⟨k,t,h.trans eq⟩
    exact (hv i first).trans (hv j second).symm
  let e := Equiv.ofBijective m (Finite.injective_iff_bijective.mp mono)
  refine ⟨e.symm,fun i j => ⟨fun ne => ?_,fun ⟨k,hx,hy⟩ eq => ?_⟩⟩
  · by_contra missed
    have out : ¬∃ k, a k=i ∧ b k=e j := fun ⟨k,x,y⟩ => missed ⟨k,x,by rw [y,e.symm_apply_apply]⟩
    exact ne (e.injective (unique i (e j) out).symm)
  · apply hm i; refine ⟨k,hx,?_⟩
    change b k=e i
    rw [eq,←hy,e.apply_symm_apply]

theorem commonClasses {n r : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c) (Y : Shore c r Index)
    (a b : Index → Label) (size : ∀ i, (Finset.univ.filter fun j => a j=i).card=3)
    (first : ∀ i j x y, c (atPoint Y i) (atPoint Y j)=c (atPoint Y x) (atPoint Y y) → (a i=a j ↔ a x=a y))
    (second : ∀ i j x y, c (atPoint Y i) (atPoint Y j)=c (atPoint Y x) (atPoint Y y) → (b i=b j ↔ b x=b y))
    (diff : ∃ i j, a i=a j ∧ b i≠b j) : ∀ x y, a x=a y → b x=b y → x=y := by
  let u := fun i j => decide (a i=a j ∧ b i=b j)
  let cl (i) := Finset.univ.filter fun j => a i=a j ∧ b i=b j
  have rect : Block Y Y Y Y u u := fun i j x y h => by simp only [u,first i j x y h,second i j x y h]
  have count (i x) : (cl i).card=(cl x).card := by simpa only [cl,u,decide_eq_true_eq] using Block.degree_eq law rect i x
  obtain ⟨i,j,eq,ne⟩ := diff
  have dj : Disjoint (cl i) (cl j) := Finset.disjoint_left.mpr fun _ hu hv =>
    ne ((Finset.mem_filter.mp hu).2.2.trans (Finset.mem_filter.mp hv).2.2.symm)
  have incl (k) : cl k ⊆ Finset.univ.filter (fun t => a t=a k) := fun _ ht =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ht).2.1.symm⟩
  have cj : cl j ⊆ Finset.univ.filter (fun t => a t=a i) := by rw [eq]; exact incl j
  have bound := Finset.card_le_card (Finset.union_subset (incl i) cj)
  rw [Finset.card_union_of_disjoint dj,count j i,size] at bound
  intro x y ex ey
  have one : (cl x).card≤1 := by rw [count x i]; omega
  exact Finset.card_le_one.mp one x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩) y
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ex,ey⟩)

private theorem sameTag {n l r v : Nat} {c : Fin n → Fin n → Nat} (law : Laws c c)
    (F : Shore c l Point) (Y : Shore c r Index) (split : Split (family F Y v))
    (i j x y) (hit : c (atPoint Y i) (atPoint Y j)=c (atPoint Y x) (atPoint Y y)) :
    split.column i=split.column j ↔ split.column x=split.column y := by
  have gram := mixed_counts law F Y F Y v v hit
  have eq (i j) : 0 < (family F Y v i∩family F Y v j).card ↔ split.column i=split.column j := by
    rw [Finset.card_pos]
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨a,b⟩ := Finset.mem_inter.mp hu
      exact ((split.pair i u).mp a).symm.trans ((split.pair j u).mp b)
    · intro e
      obtain ⟨z,hz⟩ := Finset.card_pos.mp ((by decide : 0<2).trans_eq (split.two (split.column i)).symm)
      have h := (Finset.mem_filter.mp hz).2
      exact ⟨z,Finset.mem_inter.mpr ⟨(split.pair i z).mpr h,(split.pair j z).mpr (h.trans e)⟩⟩
  rw [←eq,←eq,gram]

variable {n : Nat} {G H : Graph n} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (p : PerfectStrategy G H K)

theorem realize {l r v w : Nat} (F : Shore (source G) l Point) (Y : Shore (source G) r Index) (reg : Nat → Prop)
    (cover : ∀ i, reg (source G i i) → source G i i=l ∨ source G i i=r)
    (S : Split (family F Y v)) (D : Split (family F Y w)) (diff : ∃ i j, S.column i=S.column j ∧ D.column i≠D.column j) :
    Realizes p reg := by
  classical
  let laws := sourceLaws (closure G)
  obtain ⟨m,diag⟩ := diagonal_names p
  let T : Shore (targetName p) l Point := F.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  let W : Shore (targetName p) r Index := Y.trans (Equiv.subtypeEquiv m (fun i => by rw [←diag]))
  obtain ⟨e,_,names⟩ := SmallShore.realize_at p (by decide : 0<12) (by decide) (atPoint Y) (atPoint W) r
    (Subtype.val_injective.comp Y.injective) (Subtype.val_injective.comp W.injective) (range Y) (range W) 0 0
  let Z := e.trans W
  have f := sameTag laws F Y S
  have g := sameTag laws F Y D
  have inj := commonClasses laws Y S.column D.column S.three f g diff
  obtain ⟨d,dense⟩ := labels S.column D.column S.three D.three inj
  let t := d ∘ D.column
  have first : Block Y Y Y Y (fun i j => decide (S.column i=S.column j)) (fun i j => decide (S.column i=S.column j)) :=
    fun i j x y eq => by simp only [f i j x y eq]
  have second : Block Y Y Y Y (fun i j => decide (t i=t j)) (fun i j => decide (t i=t j)) :=
    fun i j x y eq => by simp only [t,Function.comp_apply,d.injective.eq_iff,g i j x y eq]
  have mixed {i j x y} (eq : source G (atPoint Y i) (atPoint Y j)=source G (atPoint Y x) (atPoint Y y)) :
      S.column i=t j ↔ S.column x=t y := by
    have count := Block.fold laws first second (fun u v => if u=true ∧ v=true then 1 else 0) eq
    simp only [decide_eq_true_eq,Finset.sum_boole] at count
    have neither (i j) : 0<(Finset.univ.filter (fun k => S.column i=S.column k ∧ t k=t j)).card ↔ S.column i≠t j := by
      rw [Finset.card_pos,dense]
      constructor
      · rintro ⟨k,h⟩; obtain ⟨u,v⟩ := (Finset.mem_filter.mp h).2; exact ⟨k,u.symm,v⟩
      · rintro ⟨k,u,v⟩; exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.symm,v⟩⟩
    have cc : (Finset.univ.filter (fun k => S.column i=S.column k ∧ t k=t j)).card=
        (Finset.univ.filter (fun k => S.column x=S.column k ∧ t k=t y)).card := by exact_mod_cast count
    exact not_iff_not.mp ((neither i j).symm.trans ((Iff.of_eq (congrArg (0<·) cc)).trans (neither x y)))
  obtain ⟨ξ,h,nz,pins⟩ := RegionalEightTwelveQuotient.pins p Y Z S.column t (fun a b ne => (dense a b).mp ne)
    (fun i j hi hj => inj i j hi (d.injective hj)) (fun i j x y h => f i j x y (h.trans (names x y).symm))
    (fun i j x y h => mixed (h.trans (names x y).symm))
  have tgt (j) : (family T Z v j).card=2 := by
    have gram := mixed_counts (commonLaws p) F Y T Z v v (names j j)
    simp only [Finset.inter_self] at gram
    have eq : family F Y v j=Finset.univ.filter (fun i => S.point i=S.column j) := by ext i; simp [S.pair]
    exact gram.symm.trans ((congrArg Finset.card eq).trans (S.two _))
  apply RegionalEightTwelveThin.two_candidates p reg ξ nz
  intro x
  rcases cover x.val ((mem_vertices _ _ _).mp x.property) with c|c
  · obtain ⟨i,hi⟩ := (range F x.val).mpr c
    obtain ⟨j,hj⟩ := Finset.card_pos.mp ((by decide : 0<3).trans_eq (S.three (S.point i)).symm)
    have part := (Finset.mem_filter.mp hj).2
    obtain ⟨a,b,_,pair⟩ := Finset.card_eq_two.mp (tgt (h j))
    refine ⟨atPoint T a,atPoint T b,fun z act => ?_⟩
    rw [←hi] at act
    obtain ⟨y,rfl⟩ := (range T z).mpr ((DoubledEdges.diag_of_nonzero p act).symm.trans (F i).property)
    have name := common_transpose p (linked p act (pins j))
    have member : y∈family T Z v (h j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,name.symm.trans
      (Finset.mem_filter.mp ((S.pair j i).mpr part.symm)).2⟩
    rw [pair] at member
    exact (Finset.mem_insert.mp member).elim (fun h => Or.inl (congrArg (atPoint T) h))
      (fun h => Or.inr (congrArg (atPoint T) (Finset.mem_singleton.mp h)))
  · obtain ⟨j,hj⟩ := (range Y x.val).mpr c
    refine ⟨atPoint Z (h j),atPoint Z (h j),fun z act => Or.inl ?_⟩
    rw [←hj] at act
    by_cases ne : z=atPoint Z (h j)
    · exact ne
    exact False.elim (act (calc
      _ = U p (atPoint Y j) z (U p (atPoint Y j) (atPoint Z (h j)) ξ) := congrArg (U p _ z) (pins j).symm
      _ = 0 := congrArg (fun m : Module.End ℂ (cyclic p) => m ξ) (magic_orthogonal p (atPoint Y j) z _ ne).1))

end QGI.Coherent.RegionalEightTwelveGrid

