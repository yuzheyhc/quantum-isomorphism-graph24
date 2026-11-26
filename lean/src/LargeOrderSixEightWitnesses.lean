import SixEightModel

namespace QGI.Coherent.LargeOrderSixEightWitnesses
open SixEightCatalog
open QGI.ZivAv

/-- Each word encodes a six-point and an eight-point permutation in base eight. -/
private def codes (a : Index) : Array Nat :=
  match a.val with
  | 130 => #[0x3eb1a22c688,0x1afac208b1a,0x2c6be21a22c,0x3795306c688,0x13de5048b1a,0x254f705a22c,0x2cf886a54c8,0x3e22c693225,0x8b3e688953,0x25dc14e54c8,0x370654d3225,0x19774c8953,0x3e688b0195a,0x8f9ab1a065,0x1a23eb25681,0x374c194195a,0x1dd395a065,0x13077965681,0x1ab08f9306c,0x2c21af81b13,0x86acfac4c1,0x13941dd306c,0x25053dc1b13,0x14e5dec4c1]
  | 138 => #[0x3eb1a22c688,0x35ea3208b1a,0x2fcd421a22c,0x1c5bd06c688,0x139ee05a22c,0x22777048b1a,0x270f1aa54c8,0x4f8ba93225,0x3885ea88953,0x16129ec195a,0x2d4cee5681,0x30465eda065,0x1d0b9d1306c,0x3bcad01b13,0x28657d2c4c1,0x333e05654c8,0x19c3c548953,0xe707553225,0x3a35899306c,0x11e2b9ac4c1,0xf4c5981b13,0x2c3907c195a,0x21a327da065,0xd8867e5681]
  | 167 => #[0x3eb1a22c688,0x2fca3208b1a,0x35ed421a22c,0x235f506c688,0x1477e048b1a,0x1a9af05a22c,0x372e0aa54c8,0x39d03a93225,0xee1ca88953,0x3d310cc195a,0xfa22cda065,0x29e84ce5681,0x2e298f1306c,0x31ac2f01b13,0xdc13f2c4c1,0x1c1b95654c8,0x207ce553225,0x3877548953,0x221e978195a,0x447d79a065,0x1094f7a5681,0x131719d306c,0x1858d9c1b13,0x266e9ec4c1]
  | 168 => #[0x3eb1a22c688,0x2fca3208b1a,0x35ed421a22c,0x235f50654c1,0x1477e041953,0x1a9af053065,0x372e0aa54c8,0x39d03a93225,0xee1ca88953,0x3d310cc195a,0xfa22cda065,0x29e84ce5681,0x2e298f1306c,0x31ac2f01b13,0xdc13f2c4c1,0x1c1b956c681,0x207ce55a06c,0x3877541b1a,0x221e9788b13,0x447d79322c,0x1094f7ac4c8,0x131719da225,0x1858d9c895a,0x266e9e5688]
  | 170 => #[0x3eb1a22c688,0x35ea3208b1a,0x2fcd421a22c,0x1c5bd06c688,0x139ee05a22c,0x22777048b1a,0x270f1aa54c8,0x4f8ba93225,0x3885ea88953,0x16129ec195a,0x2d4cee5681,0x30465eda065,0x1d0b9d1306c,0x3bcad01b13,0x28657d2c4c1,0x333e05654c8,0x19c3c548953,0xe707553225,0x3a35899306c,0x11e2b9ac4c1,0xf4c5981b13,0x2c3907c195a,0x21a327da065,0xd8867e5681]
  | 311 => #[0x3eb1a22c688,0x1afac208b1a,0x2c6be21a22c,0x3795306c688,0x13de5048b1a,0x254f705a22c,0x2cf886a54c8,0x3e22c693225,0x8b3e688953,0x25dc14e54c8,0x370654d3225,0x19774c8953,0x3e688b0195a,0x8f9ab1a065,0x1a23eb25681,0x374c194195a,0x1dd395a065,0x13077965681,0x1ab08f9306c,0x2c21af81b13,0x86acfac4c1,0x13941dd306c,0x25053dc1b13,0x14e5dec4c1]
  | 315 => #[0x3eb1a22c688,0x2fca3208b1a,0x35ed421a22c,0x235f506c688,0x1477e048b1a,0x1a9af05a22c,0x372e0aa54c8,0x39d03a93225,0xee1ca88953,0x3d310cc195a,0xfa22cda065,0x29e84ce5681,0x2e298f1306c,0x31ac2f01b13,0xdc13f2c4c1,0x1c1b95654c8,0x207ce553225,0x3877548953,0x221e978195a,0x447d79a065,0x1094f7a5681,0x131719d306c,0x1858d9c1b13,0x266e9ec4c1]
  | 316 => #[0x3eb1a22c688,0x2fca3208b1a,0x35ed421a22c,0x235f50654c1,0x1477e041953,0x1a9af053065,0x372e0aa54c8,0x39d03a93225,0xee1ca88953,0x3d310cc195a,0xfa22cda065,0x29e84ce5681,0x2e298f1306c,0x31ac2f01b13,0xdc13f2c4c1,0x1c1b956c681,0x207ce55a06c,0x3877541b1a,0x221e9788b13,0x447d79322c,0x1094f7ac4c8,0x131719da225,0x1858d9c895a,0x266e9e5688]
  | _ => #[]

private def bit (c j : Nat) := (c >>> (3*j)) % 8
private def s (c : Nat) (i : Six) : Six := ⟨bit c i.val % 6,Nat.mod_lt _ (by decide)⟩
private def y (c : Nat) (i : Eight) : Eight := ⟨bit c (6+i.val),Nat.mod_lt _ (by decide)⟩

private instance (a : Index) : Decidable (SplitRectangle.Twins (fun i j => (M a i j).val)) := by
  unfold SplitRectangle.Twins
  infer_instance

private theorem range_check : ∀ a : Index, diagSize a (left 0)=6 → diagSize a (right 0)=8 →
    SplitRectangle.Twins (fun i j => (M a i j).val) ∨ 0<(codes a).size := by native_decide

attribute [local irreducible] raw color cores14
private theorem valid : ∀ (a : Index) (q : Fin (codes a).size),
    let c := (codes a)[q.val]
    Function.Injective (s c) ∧ Function.Injective (y c) ∧
      (∀ i j, A a (s c i) (s c j)=A a i j) ∧ (∀ i j, M a (s c i) (y c j)=M a i j) ∧
      ∀ i j, B a (y c i) (y c j)=B a i j := by native_decide

private theorem all_pairs : ∀ (a : Index), 0<(codes a).size → ∀ i j u v, M a i j=M a u v →
    ∃ q : Fin (codes a).size, s (codes a)[q.val] i=u ∧ y (codes a)[q.val] j=v := by native_decide

theorem transport (a : Index) (sizes : diagSize a (left 0)=6) (sizey : diagSize a (right 0)=8)
    (mixed : ¬SplitRectangle.Twins (fun i j => (M a i j).val)) (i u : Six) (j v : Eight) (eq : M a i j=M a u v) :
    ∃ (f : Equiv.Perm Six) (g : Equiv.Perm Eight), f i=u ∧ g j=v ∧
      (∀ b d, A a (f b) (f d)=A a b d) ∧ (∀ b d, M a (f b) (g d)=M a b d) ∧
      ∀ b d, B a (g b) (g d)=B a b d := by
  obtain ⟨q,hit⟩ := all_pairs a ((range_check a sizes sizey).resolve_left mixed) i j u v eq
  obtain ⟨si,yi,other⟩ := valid a q
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp si),
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp yi),hit.1,hit.2,other⟩

/-- On a repeated tetrahedron, every thin named relation on the eight-point
shore stays inside the repeated column. -/
theorem same_columns : ∀ a : Index, Tetra a → ∀ j k : Eight,
    (∀ b, B a j b=B a j k → b=k) → ∀ i : Six, M a i j=M a i k := by native_decide

private def count (a : Index) (v : Fin (raw a).rank) (i : Six) (row : Eight → Bool) :=
  ∑ j, if M a i j=v ∧ row j=true then 1 else 0

/-- A row constant on every column pair cannot have constant intersection
with all six edge neighborhoods unless the row itself is constant. -/
theorem detect_rows : ∀ a : Index, Tetra a → ∀ row : Eight → Bool,
    (∀ j, ∃ k, k≠j ∧ (∀ i, M a i k=M a i j) ∧ row k=row j) →
    (∀ i, count a (flag a) i row=count a (flag a) 0 row) → ∀ j, row j=row 0 := by native_decide

end QGI.Coherent.LargeOrderSixEightWitnesses
