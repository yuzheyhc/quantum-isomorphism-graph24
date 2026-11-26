import CatalogRigidity

namespace QGI.CatalogRigidity
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem checked17 : Valid 17 36 := by native_decide

theorem represented17 {G H : QGI.Graph 17} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked17 g h q

private theorem checked18 : Valid 18 380 := by native_decide

theorem represented18 {G H : QGI.Graph 18} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked18 g h q

private theorem checked19 : Valid 19 60 := by native_decide

theorem represented19 {G H : QGI.Graph 19} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked19 g h q

private theorem checked20 : Valid 20 1214 := by native_decide

theorem represented20 {G H : QGI.Graph 20} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked20 g h q

private theorem checked21 : Valid 21 240 := by native_decide

theorem represented21 {G H : QGI.Graph 21} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked21 g h q

private theorem checked22 : Valid 22 816 := by native_decide

theorem represented22 {G H : QGI.Graph 22} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked22 g h q

private theorem checked23 : Valid 23 188 := by native_decide

theorem represented23 {G H : QGI.Graph 23} (g : Represented G) (h : Represented H)
    (q : QuantumIso G H) : Isomorphic G H := catalog_iso checked23 g h q

end QGI.CatalogRigidity
