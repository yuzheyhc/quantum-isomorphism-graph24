import ZivAvCoreFacts

namespace QGI.ZivAv
open SixteenMapSearch
open private histogram histogram_at coefficients get_ofFn from DoubleEightPrepared

private theorem entry_from_hist (s : Scheme) (k i j : Fin s.rank)
    (f g : Vertex → Fin s.rank)
    (consistent : coefficients s k = histogram (List.ofFn fun z => finProdFinEquiv (f z,g z))) :
    coefficient s k.val i.val j.val = ∑ z : Vertex, if f z=i ∧ g z=j then 1 else 0 := by
  have h := congrArg (fun v => Vector.get v (finProdFinEquiv (i,j))) consistent
  simpa only [coefficients,get_ofFn,Equiv.symm_apply_apply,histogram_at,List.map_ofFn,
    Function.comp_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq,List.sum_ofFn] using h

attribute [local irreducible] raw keyed color cores14

theorem mult_at (a : Index) (k i j : Fin (raw a).rank) :
    coefficient (raw a) k.val i.val j.val = ∑ z : Vertex,
      if name a (atName a k).1 z = i ∧ name a z (atName a k).2 = j then 1 else 0 :=
  entry_from_hist (raw a) k i j _ _ (tables a k)

end QGI.ZivAv
