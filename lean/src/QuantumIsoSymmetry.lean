import QuantumGraph

namespace QGI

private def otherShore {n : Nat} (q : Question n) : Question n := (!q.1, q.2)

private theorem loses_on_other_shore {n : Nat} {G H : Graph n} {q r : Question n}
    {a b : Fin n} (h : Loses H G q r a b) : Loses G H (otherShore q) (otherShore r) a b := by
  obtain ⟨s,x⟩ := q
  obtain ⟨t,y⟩ := r
  cases s <;> cases t <;> exact Ne.symm h

/-- Exchange the two graphs by flipping the shore flag in both questions. -/
def PerfectStrategy.symm {n : Nat} {G H : Graph n} {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (p : PerfectStrategy G H K) :
    PerfectStrategy H G K where
  psi := p.psi
  norm_psi := p.norm_psi
  alice q := p.alice (otherShore q)
  bob r := p.bob (otherShore r)
  alicePVM q := p.alicePVM (otherShore q)
  bobPVM r := p.bobPVM (otherShore r)
  commute q r := p.commute (otherShore q) (otherShore r)
  perfect q r a b h := p.perfect (otherShore q) (otherShore r) a b (loses_on_other_shore h)

theorem QuantumIso.symm {n : Nat} {G H : Graph n} (h : QuantumIso G H) : QuantumIso H G := by
  obtain ⟨K, g, ip, hc, ⟨p⟩⟩ := h
  letI : NormedAddCommGroup K := g
  letI : InnerProductSpace ℂ K := ip
  exact ⟨K, g, ip, hc, ⟨p.symm⟩⟩

theorem Isomorphic.symm {n : Nat} {G H : Graph n} (h : Isomorphic G H) : Isomorphic H G := by
  obtain ⟨f⟩ := h
  exact ⟨f.symm⟩

end QGI
