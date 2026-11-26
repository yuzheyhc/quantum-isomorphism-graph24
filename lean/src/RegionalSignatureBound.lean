import RegionalTernaryChoice

noncomputable section
namespace QGI.Coherent.RegionalSignatureBound
open Classical

theorem bound_set {A B X : Type*} (f : A → X) (fi : Function.Injective f) (g : B → X)
    (U : Finset A) (V : Finset B) (hits : ∀ a∈U, ∃ b∈V, g b=f a) : U.card≤V.card := by
  have ex (a : U) : ∃ b : V, g b.val=f a.val := by
    obtain ⟨b,hb,eq⟩ := hits a.val a.property
    exact ⟨⟨b,hb⟩,eq⟩
  choose z hz using ex
  have inj : Function.Injective z := by
    intro a b eq
    apply Subtype.ext; apply fi
    exact (hz a).symm.trans ((congrArg (fun v : V => g v.val) eq).trans (hz b))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective z inj

end QGI.Coherent.RegionalSignatureBound
