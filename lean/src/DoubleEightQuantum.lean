import CatalogPalette
import ColoredPlanarWitness
import DoubleEightCensusMaps
import DoubleEightQuantumMatching
import QuantumIsoSymmetry

noncomputable section
namespace QGI.Coherent.DoubleEightGraphs

open QGI.DoubleEight
open QGI.DoubleEight.Prepared
open QGI.Coherent.CatalogPalette
open QGI.Certificate
set_option maxRecDepth 12000

private theorem bank_size : Layers.matrices.size = 636 := by native_decide
private theorem row_size : ∀ a : Index, (row a).size = 256 := by native_decide

private theorem models (G : Graph 16) (sizes : ∀ i, (fiber G i).card = 8) :
    HasCrossMatching G ∨ ∃ a : Index, Nonempty (Model G (name a)) := by
  rcases matching_or_partition G sizes with h | ⟨t,w,e,inside,h⟩
  · exact Or.inl h
  have ht : t < Layers.matrices.size := by
    by_contra! no
    rw [getElem?_neg Layers.matrices t (Nat.not_lt.mpr no)] at inside
    contradiction
  let a : Index := ⟨t,bank_size ▸ ht⟩
  have eq : w = row a := Option.some.inj (inside.symm.trans (row_lookup a))
  subst w
  refine Or.inr ⟨a,⟨of_partition G (name a) e.symm (name_surjective a) ?_⟩⟩
  intro i j x y
  rw [← Fin.val_inj, name_val,name_val]
  simpa only [Equiv.apply_symm_apply] using (h (e.symm i) (e.symm j) (e.symm x) (e.symm y)).symm

private theorem witness_bound : Attachment.rows.all (fun r => r.colors.all (fun k => k < r.perm.length)) = true := by
  native_decide

private theorem read_indicator {a : Index} {m : ColorMatrix} (order : m.order = 16)
    (same : m.entries = row a) (k : Fin (scheme a).rank) (u : Equiv.Perm (Fin 16)) :
    inGraphLabels u (binaryMatrix m k.val) = graphMatrix (name a) k u := by
  have cell (i j : Fin 16) : m.get i.val j.val = (name a i j).val := by
    have small : 16*i.val+j.val < (row a).size := by rw [row_size]; omega
    simp only [ColorMatrix.get,order,same,Nat.mul_comm i.val 16,name_val,Placements.color,
      Array.getD_eq_getD_getElem?,getElem?_pos (row a) (16*i.val+j.val) small,Option.getD_some]
  apply Matrix.ext
  intro i j
  simp only [inGraphLabels,binaryMatrix,binary,graphMatrix,cell,Fin.val_inj]
  split <;> simp

private theorem lookup_entries {a : Index} {m : ColorMatrix}
    (h : Input.matrices[a.val]? = some m.entries) : m.entries = row a := by
  apply Option.some.inj
  exact h.symm.trans (by simpa only [Layers.matrices,List.getElem?_toArray] using row_lookup a)

private theorem key_fields (r : Attachment.Row) (i j : Nat) (perm : List Nat)
    (h : r.key = (i,j,perm)) : r.srcId = i ∧ r.dstId = j ∧ r.perm = perm := by
  simpa only [Attachment.Row.key,Prod.mk.injEq] using h

/-- A strategy on graphs with either choice of catalog representatives
produces its own color permutation. A positive vertex search realizes it;
every other outcome contradicts the attached planar witness. -/
theorem of_models {G H : Graph 16} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (p : PerfectStrategy G H K) (a b : Index)
    (S : Model G (name a)) (T : Model H (name b)) : QGI.Isomorphic G H := by
  let f := mapping p S T
  let pi := List.ofFn fun k => (f k).val
  have get (k : Fin (scheme a).rank) (fallback : Nat) : (pi[k.val]?).getD fallback = (f k).val := by
    simp only [pi,List.getElem?_ofFn,dif_pos k.isLt,Option.getD_some]
  obtain ⟨rank,profile,listed⟩ := eligible_of_cells a b f
    (fun _ _ _ _ h => transpose_preserved p S T h)
    (fun _ _ _ _ h => product_preserved p S T h)
  rcases CensusMaps.dichotomy a b pi rank profile listed with ⟨e,point⟩ | ⟨C,hC,key⟩
  · apply graph_iso p S T e
    intro i j
    apply Fin.ext
    change (f (name a i j)).val = (name b (e i) (e j)).val
    rw [←get (name a i j) 0,name_val,name_val]
    exact point i j
  · obtain ⟨r,hr,hkey,bound,excluded⟩ := Attachment.exceptional_key_excluded_reindexed
      C hC (a.val+1,b.val+1,pi) key p S.points T.points
    obtain ⟨_,_,os,ot,src,dst⟩ := bound
    obtain ⟨sid,tid,perm⟩ := key_fields r (a.val+1) (b.val+1) pi hkey
    have hs : r.src.entries = row a := lookup_entries (by simpa only [sid,Nat.add_sub_cancel] using src)
    have ht : r.dst.entries = row b := lookup_entries (by simpa only [tid,Nat.add_sub_cancel] using dst)
    exfalso
    apply excluded
    intro c hc
    have len := List.all_eq_true.mp (List.all_eq_true.mp witness_bound r hr) c hc
    have lt : c < (scheme a).rank := by simpa only [decide_eq_true_eq,perm,pi,List.length_ofFn] using len
    let k : Fin (scheme a).rank := ⟨c,lt⟩
    have rename : (r.perm[c]?).getD r.src.rank = (f k).val := by rw [perm]; exact get k _
    change Intertwiner.Intertwines p (inGraphLabels S.points (binaryMatrix r.src k.val)) _
    rw [rename,read_indicator os hs k S.points,read_indicator ot ht (f k) T.points]
    exact named_intertwines p S T k

/-- A perfect commuting-operator graph-isomorphism strategy on sixteen
vertices is classical whenever every source coherent fiber has eight points. -/
theorem isomorphic_of_two_eights {G H : Graph 16}
    (sizes : ∀ i, (fiber G i).card = 8) (q : QuantumIso G H) : QGI.Isomorphic G H := by
  obtain ⟨K,g,ip,complete,⟨p⟩⟩ := q
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  letI : CompleteSpace K := complete
  have target (a : Fin 16) : (fiber H a).card = 8 := by
    obtain ⟨i,eq⟩ := StrategyColorLaws.fiber_size p a
    exact eq.symm.trans (sizes i)
  rcases models G sizes with ⟨u,c,k,sides,matchColor⟩ | ⟨a,⟨S⟩⟩
  · exact matching_iso p target u sides c k matchColor
  rcases models H target with ⟨v,c,k,sides,matchColor⟩ | ⟨b,⟨T⟩⟩
  · exact (matching_iso p.symm sizes v sides c k matchColor).symm
  · exact of_models p a b S T

end QGI.Coherent.DoubleEightGraphs
