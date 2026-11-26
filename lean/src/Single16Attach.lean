import Single16Check
import certificates.Witnesses

/- Attach the outputs of the upstream census to the very matrices and
renamed-edge counts appearing in the independently supplied witness file.
For every exceptional key returned by the census, the attached row gives
two unequal colored homomorphism counts on the corresponding catalog entries. -/
namespace QGI.Single16.Attachment
open QGI.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Row where
  srcId : Nat
  dstId : Nat
  src : ColorMatrix
  dst : ColorMatrix
  pattern : Pattern
  perm : List Nat
  colors : List Nat
  left : Nat
  right : Nat
  passed : check src dst pattern perm colors left right = true

def Row.key (r : Row) : Key := (r.srcId, r.dstId, r.perm)

def OnCatalog (r : Row) : Prop :=
  0 < r.srcId ∧ 0 < r.dstId ∧ r.src.order = 16 ∧ r.dst.order = 16 ∧
  Input.matrices[r.srcId-1]? = some r.src.entries ∧
  Input.matrices[r.dstId-1]? = some r.dst.entries

instance (r : Row) : Decidable (OnCatalog r) := by unfold OnCatalog; infer_instance

private def chunk0 : List Row := [
  ⟨5,6,m_single_5,m_single_6,.tetra,[0,1,2],[1,1,1,1,1,1],192,0,cert_single_001⟩,
  ⟨6,5,m_single_6,m_single_5,.tetra,[0,1,2],[1,1,1,1,1,2],192,0,cert_single_002⟩,
  ⟨14,15,m_single_14,m_single_15,.tetra,[0,1,2,3],[2,2,2,2,2,2],192,0,cert_single_003⟩,
  ⟨14,15,m_single_14,m_single_15,.tetra,[0,1,3,2],[2,2,2,2,2,2],192,0,cert_single_004⟩,
  ⟨14,16,m_single_14,m_single_16,.tetra,[0,1,2,3],[1,2,2,2,2,1],96,32,cert_single_005⟩,
  ⟨14,16,m_single_14,m_single_16,.tetra,[0,1,3,2],[1,2,2,2,2,1],96,32,cert_single_006⟩,
  ⟨14,17,m_single_14,m_single_17,.tetra,[0,1,2,3],[1,2,2,2,2,1],96,32,cert_single_007⟩,
  ⟨14,17,m_single_14,m_single_17,.tetra,[0,1,3,2],[1,2,2,2,2,1],96,32,cert_single_008⟩,
  ⟨15,14,m_single_15,m_single_14,.tetra,[0,1,2,3],[2,2,2,2,2,3],192,0,cert_single_009⟩,
  ⟨15,14,m_single_15,m_single_14,.tetra,[0,1,3,2],[2,2,2,2,2,3],192,0,cert_single_010⟩,
  ⟨15,16,m_single_15,m_single_16,.tetra,[0,1,2,3],[1,2,2,2,2,1],96,32,cert_single_011⟩,
  ⟨15,16,m_single_15,m_single_16,.tetra,[0,1,3,2],[1,2,2,2,2,1],96,32,cert_single_012⟩,
  ⟨15,17,m_single_15,m_single_17,.tetra,[0,1,2,3],[1,2,2,2,2,1],96,32,cert_single_013⟩,
  ⟨15,17,m_single_15,m_single_17,.tetra,[0,1,3,2],[1,2,2,2,2,1],96,32,cert_single_014⟩,
  ⟨16,14,m_single_16,m_single_14,.tetra,[0,1,2,3],[1,2,2,2,2,1],32,96,cert_single_015⟩,
  ⟨16,14,m_single_16,m_single_14,.tetra,[0,1,3,2],[1,2,2,2,2,1],32,96,cert_single_016⟩,
  ⟨16,15,m_single_16,m_single_15,.tetra,[0,1,2,3],[1,2,2,2,2,1],32,96,cert_single_017⟩,
  ⟨16,15,m_single_16,m_single_15,.tetra,[0,1,3,2],[1,2,2,2,2,1],32,96,cert_single_018⟩,
  ⟨16,16,m_single_16,m_single_16,.tetra,[0,1,3,2],[1,2,2,2,2,2],64,0,cert_single_019⟩,
  ⟨16,17,m_single_16,m_single_17,.tetra,[0,1,2,3],[1,2,2,2,2,2],64,32,cert_single_020⟩,
  ⟨16,17,m_single_16,m_single_17,.tetra,[0,1,3,2],[1,2,2,2,2,2],64,32,cert_single_021⟩,
  ⟨17,14,m_single_17,m_single_14,.tetra,[0,1,2,3],[1,2,2,2,2,1],32,96,cert_single_022⟩,
  ⟨17,14,m_single_17,m_single_14,.tetra,[0,1,3,2],[1,2,2,2,2,1],32,96,cert_single_023⟩,
  ⟨17,15,m_single_17,m_single_15,.tetra,[0,1,2,3],[1,2,2,2,2,1],32,96,cert_single_024⟩]

private def chunk1 : List Row := [
  ⟨17,15,m_single_17,m_single_15,.tetra,[0,1,3,2],[1,2,2,2,2,1],32,96,cert_single_025⟩,
  ⟨17,16,m_single_17,m_single_16,.tetra,[0,1,2,3],[1,2,2,2,2,2],32,64,cert_single_026⟩,
  ⟨17,16,m_single_17,m_single_16,.tetra,[0,1,3,2],[1,2,2,2,2,2],32,0,cert_single_027⟩,
  ⟨18,19,m_single_18,m_single_19,.tetra,[0,1,2,3],[1,2,2,2,2,1],96,32,cert_single_028⟩,
  ⟨18,19,m_single_18,m_single_19,.tetra,[0,1,3,2],[1,2,2,2,2,1],96,32,cert_single_029⟩,
  ⟨19,18,m_single_19,m_single_18,.tetra,[0,1,2,3],[1,2,2,2,2,1],32,96,cert_single_030⟩,
  ⟨19,18,m_single_19,m_single_18,.tetra,[0,1,3,2],[1,2,2,2,2,1],32,96,cert_single_031⟩,
  ⟨20,21,m_single_20,m_single_21,.tetra,[0,1,2,3],[1,1,2,2,1,1],160,96,cert_single_032⟩,
  ⟨20,21,m_single_20,m_single_21,.tetra,[0,1,3,2],[1,1,2,2,1,1],160,96,cert_single_033⟩,
  ⟨20,21,m_single_20,m_single_21,.tetra,[0,2,1,3],[1,1,2,2,1,1],160,96,cert_single_034⟩,
  ⟨20,21,m_single_20,m_single_21,.tetra,[0,2,3,1],[1,1,2,2,1,1],160,96,cert_single_035⟩,
  ⟨20,21,m_single_20,m_single_21,.tetra,[0,3,1,2],[1,1,2,2,1,1],160,96,cert_single_036⟩,
  ⟨20,21,m_single_20,m_single_21,.tetra,[0,3,2,1],[1,1,2,2,1,1],160,96,cert_single_037⟩,
  ⟨21,20,m_single_21,m_single_20,.tetra,[0,1,2,3],[1,1,2,2,1,1],96,160,cert_single_038⟩,
  ⟨21,20,m_single_21,m_single_20,.tetra,[0,1,3,2],[1,1,2,2,1,1],96,160,cert_single_039⟩,
  ⟨21,20,m_single_21,m_single_20,.tetra,[0,2,1,3],[1,1,2,2,1,1],96,160,cert_single_040⟩,
  ⟨21,20,m_single_21,m_single_20,.tetra,[0,2,3,1],[1,1,2,2,1,1],96,160,cert_single_041⟩,
  ⟨21,20,m_single_21,m_single_20,.tetra,[0,3,1,2],[1,1,2,2,1,1],96,160,cert_single_042⟩,
  ⟨21,20,m_single_21,m_single_20,.tetra,[0,3,2,1],[1,1,2,2,1,1],96,160,cert_single_043⟩,
  ⟨32,33,m_single_32,m_single_33,.tetra,[0,1,2,3,4],[1,2,3,3,2,1],48,16,cert_single_044⟩,
  ⟨32,33,m_single_32,m_single_33,.tetra,[0,1,3,2,4],[1,2,3,3,2,1],48,16,cert_single_045⟩,
  ⟨32,33,m_single_32,m_single_33,.tetra,[0,2,1,3,4],[1,2,3,3,2,1],48,16,cert_single_046⟩,
  ⟨32,33,m_single_32,m_single_33,.tetra,[0,2,3,1,4],[1,2,3,3,2,1],48,16,cert_single_047⟩,
  ⟨32,33,m_single_32,m_single_33,.tetra,[0,3,1,2,4],[1,2,3,3,2,1],48,16,cert_single_048⟩]

private def chunk2 : List Row := [
  ⟨32,33,m_single_32,m_single_33,.tetra,[0,3,2,1,4],[1,2,3,3,2,1],48,16,cert_single_049⟩,
  ⟨33,32,m_single_33,m_single_32,.tetra,[0,1,2,3,4],[1,2,3,3,2,1],16,48,cert_single_050⟩,
  ⟨33,32,m_single_33,m_single_32,.tetra,[0,1,3,2,4],[1,2,3,3,2,1],16,48,cert_single_051⟩,
  ⟨33,32,m_single_33,m_single_32,.tetra,[0,2,1,3,4],[1,2,3,3,2,1],16,48,cert_single_052⟩,
  ⟨33,32,m_single_33,m_single_32,.tetra,[0,2,3,1,4],[1,2,3,3,2,1],16,48,cert_single_053⟩,
  ⟨33,32,m_single_33,m_single_32,.tetra,[0,3,1,2,4],[1,2,3,3,2,1],16,48,cert_single_054⟩,
  ⟨33,32,m_single_33,m_single_32,.tetra,[0,3,2,1,4],[1,2,3,3,2,1],16,48,cert_single_055⟩,
  ⟨49,50,m_single_49,m_single_50,.prismCyclic,[0,1,2,3,4,5],[3,3,3,3,3,3,2,2,2],96,0,cert_single_056⟩,
  ⟨49,50,m_single_49,m_single_50,.prismCyclic,[0,1,2,4,3,5],[3,3,3,3,3,3,2,2,2],96,0,cert_single_057⟩,
  ⟨50,49,m_single_50,m_single_49,.prismCyclic,[0,1,2,3,4,5],[3,3,3,3,3,3,2,2,2],0,96,cert_single_058⟩,
  ⟨50,49,m_single_50,m_single_49,.prismCyclic,[0,1,2,4,3,5],[3,3,3,3,3,3,2,2,2],0,96,cert_single_059⟩,
  ⟨54,55,m_single_54,m_single_55,.tetra,[0,1,2,3,4,5],[2,4,4,4,4,2],64,0,cert_single_060⟩,
  ⟨54,55,m_single_54,m_single_55,.tetra,[0,1,2,3,5,4],[2,4,4,4,4,2],64,0,cert_single_061⟩,
  ⟨55,54,m_single_55,m_single_54,.tetra,[0,1,2,3,4,5],[2,4,4,4,4,3],64,0,cert_single_062⟩,
  ⟨55,54,m_single_55,m_single_54,.tetra,[0,1,2,3,5,4],[2,4,4,4,4,3],64,0,cert_single_063⟩,
  ⟨58,59,m_single_58,m_single_59,.tetra,[0,1,2,3,4,5],[2,4,4,4,4,2],64,0,cert_single_064⟩,
  ⟨58,59,m_single_58,m_single_59,.tetra,[0,1,2,3,5,4],[2,4,4,4,4,2],64,0,cert_single_065⟩,
  ⟨59,58,m_single_59,m_single_58,.tetra,[0,1,2,3,4,5],[2,4,4,4,4,3],64,0,cert_single_066⟩,
  ⟨59,58,m_single_59,m_single_58,.tetra,[0,1,2,3,5,4],[2,4,4,4,4,3],64,0,cert_single_067⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,2,3,4,5,6],[3,5,5,5,5,3],64,0,cert_single_068⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,2,3,4,6,5],[3,5,5,5,5,3],64,0,cert_single_069⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,2,4,3,5,6],[3,5,5,5,5,3],64,0,cert_single_070⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,2,4,3,6,5],[3,5,5,5,5,3],64,0,cert_single_071⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_072⟩]

private def chunk3 : List Row := [
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_073⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_074⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_075⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_076⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_077⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_078⟩,
  ⟨77,78,m_single_77,m_single_78,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_079⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,2],64,0,cert_single_080⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,2],64,0,cert_single_081⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,2],64,0,cert_single_082⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,2],64,0,cert_single_083⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_084⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_085⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_086⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_087⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_088⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_089⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_090⟩,
  ⟨77,79,m_single_77,m_single_79,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_091⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,2,3,4,5,6],[3,5,5,5,5,4],64,0,cert_single_092⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,2,3,4,6,5],[3,5,5,5,5,4],64,0,cert_single_093⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,2,4,3,5,6],[3,5,5,5,5,4],64,0,cert_single_094⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,2,4,3,6,5],[3,5,5,5,5,4],64,0,cert_single_095⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,3,2,4,5,6],[3,5,5,5,5,4],64,0,cert_single_096⟩]

private def chunk4 : List Row := [
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,3,2,4,6,5],[3,5,5,5,5,4],64,0,cert_single_097⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,3,4,2,5,6],[3,5,5,5,5,4],64,0,cert_single_098⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,3,4,2,6,5],[3,5,5,5,5,4],64,0,cert_single_099⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,4,2,3,5,6],[3,5,5,5,5,4],64,0,cert_single_100⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,4,2,3,6,5],[3,5,5,5,5,4],64,0,cert_single_101⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,4,3,2,5,6],[3,5,5,5,5,4],64,0,cert_single_102⟩,
  ⟨78,77,m_single_78,m_single_77,.tetra,[0,1,4,3,2,6,5],[3,5,5,5,5,4],64,0,cert_single_103⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_104⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_105⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_106⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_107⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_108⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_109⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_110⟩,
  ⟨78,78,m_single_78,m_single_78,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_111⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,2],64,0,cert_single_112⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,2],64,0,cert_single_113⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,2],64,0,cert_single_114⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,2],64,0,cert_single_115⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_116⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_117⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_118⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_119⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_120⟩]

private def chunk5 : List Row := [
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_121⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_122⟩,
  ⟨78,79,m_single_78,m_single_79,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_123⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,3],32,0,cert_single_124⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,3],32,0,cert_single_125⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,3],32,0,cert_single_126⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,3],32,0,cert_single_127⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,3],32,0,cert_single_128⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,3],32,0,cert_single_129⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,3],32,0,cert_single_130⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,3],32,0,cert_single_131⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,3],32,0,cert_single_132⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,3],32,0,cert_single_133⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,3],32,0,cert_single_134⟩,
  ⟨79,77,m_single_79,m_single_77,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,3],32,0,cert_single_135⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,3],32,0,cert_single_136⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,3],32,0,cert_single_137⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,3],32,0,cert_single_138⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,3],32,0,cert_single_139⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,3],32,0,cert_single_140⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,3],32,0,cert_single_141⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,3],32,64,cert_single_142⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,3],32,64,cert_single_143⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,3],32,0,cert_single_144⟩]

private def chunk6 : List Row := [
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,3],32,0,cert_single_145⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,3],32,64,cert_single_146⟩,
  ⟨79,78,m_single_79,m_single_78,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,3],32,64,cert_single_147⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,2,3,4,5,6],[3,5,5,5,5,3],64,0,cert_single_148⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,2,3,4,6,5],[3,5,5,5,5,3],64,0,cert_single_149⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,2,4,3,5,6],[3,5,5,5,5,3],64,0,cert_single_150⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,2,4,3,6,5],[3,5,5,5,5,3],64,0,cert_single_151⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_152⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_153⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_154⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_155⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_156⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_157⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_158⟩,
  ⟨83,84,m_single_83,m_single_84,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_159⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,2],64,0,cert_single_160⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,2],64,0,cert_single_161⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,2],64,0,cert_single_162⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,2],64,0,cert_single_163⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_164⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_165⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_166⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_167⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_168⟩]

private def chunk7 : List Row := [
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_169⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_170⟩,
  ⟨83,85,m_single_83,m_single_85,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_171⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,2,3,4,5,6],[3,5,5,5,5,4],64,0,cert_single_172⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,2,3,4,6,5],[3,5,5,5,5,4],64,0,cert_single_173⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,2,4,3,5,6],[3,5,5,5,5,4],64,0,cert_single_174⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,2,4,3,6,5],[3,5,5,5,5,4],64,0,cert_single_175⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,3,2,4,5,6],[3,5,5,5,5,4],64,0,cert_single_176⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,3,2,4,6,5],[3,5,5,5,5,4],64,0,cert_single_177⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,3,4,2,5,6],[3,5,5,5,5,4],64,0,cert_single_178⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,3,4,2,6,5],[3,5,5,5,5,4],64,0,cert_single_179⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,4,2,3,5,6],[3,5,5,5,5,4],64,0,cert_single_180⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,4,2,3,6,5],[3,5,5,5,5,4],64,0,cert_single_181⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,4,3,2,5,6],[3,5,5,5,5,4],64,0,cert_single_182⟩,
  ⟨84,83,m_single_84,m_single_83,.tetra,[0,1,4,3,2,6,5],[3,5,5,5,5,4],64,0,cert_single_183⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_184⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_185⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_186⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_187⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_188⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_189⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_190⟩,
  ⟨84,84,m_single_84,m_single_84,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_191⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,2],64,0,cert_single_192⟩]

private def chunk8 : List Row := [
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,2],64,0,cert_single_193⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,2],64,0,cert_single_194⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,2],64,0,cert_single_195⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,2],64,0,cert_single_196⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,2],64,0,cert_single_197⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,2],64,0,cert_single_198⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,2],64,0,cert_single_199⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,2],64,0,cert_single_200⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,2],64,0,cert_single_201⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,2],64,0,cert_single_202⟩,
  ⟨84,85,m_single_84,m_single_85,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,2],64,0,cert_single_203⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,3],32,0,cert_single_204⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,3],32,0,cert_single_205⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,3],32,0,cert_single_206⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,3],32,0,cert_single_207⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,3],32,0,cert_single_208⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,3],32,0,cert_single_209⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,3],32,0,cert_single_210⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,3],32,0,cert_single_211⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,3],32,0,cert_single_212⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,3],32,0,cert_single_213⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,3],32,0,cert_single_214⟩,
  ⟨85,83,m_single_85,m_single_83,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,3],32,0,cert_single_215⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,3],32,0,cert_single_216⟩]

private def chunk9 : List Row := [
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,3],32,0,cert_single_217⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,3],32,0,cert_single_218⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,3],32,0,cert_single_219⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,3,2,4,5,6],[2,5,5,5,5,3],32,0,cert_single_220⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,3,2,4,6,5],[2,5,5,5,5,3],32,0,cert_single_221⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,3,4,2,5,6],[2,5,5,5,5,3],32,64,cert_single_222⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,3,4,2,6,5],[2,5,5,5,5,3],32,64,cert_single_223⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,4,2,3,5,6],[2,5,5,5,5,3],32,0,cert_single_224⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,4,2,3,6,5],[2,5,5,5,5,3],32,0,cert_single_225⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,4,3,2,5,6],[2,5,5,5,5,3],32,64,cert_single_226⟩,
  ⟨85,84,m_single_85,m_single_84,.tetra,[0,1,4,3,2,6,5],[2,5,5,5,5,3],32,64,cert_single_227⟩,
  ⟨89,90,m_single_89,m_single_90,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,2],64,0,cert_single_228⟩,
  ⟨89,90,m_single_89,m_single_90,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,2],64,0,cert_single_229⟩,
  ⟨89,90,m_single_89,m_single_90,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,2],64,0,cert_single_230⟩,
  ⟨89,90,m_single_89,m_single_90,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,2],64,0,cert_single_231⟩,
  ⟨90,89,m_single_90,m_single_89,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,3],32,0,cert_single_232⟩,
  ⟨90,89,m_single_90,m_single_89,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,3],32,0,cert_single_233⟩,
  ⟨90,89,m_single_90,m_single_89,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,3],32,0,cert_single_234⟩,
  ⟨90,89,m_single_90,m_single_89,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,3],32,0,cert_single_235⟩,
  ⟨94,95,m_single_94,m_single_95,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,2],64,0,cert_single_236⟩,
  ⟨94,95,m_single_94,m_single_95,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,2],64,0,cert_single_237⟩,
  ⟨94,95,m_single_94,m_single_95,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,2],64,0,cert_single_238⟩,
  ⟨94,95,m_single_94,m_single_95,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,2],64,0,cert_single_239⟩,
  ⟨95,94,m_single_95,m_single_94,.tetra,[0,1,2,3,4,5,6],[2,5,5,5,5,3],32,0,cert_single_240⟩]

private def chunk10 : List Row := [
  ⟨95,94,m_single_95,m_single_94,.tetra,[0,1,2,3,4,6,5],[2,5,5,5,5,3],32,0,cert_single_241⟩,
  ⟨95,94,m_single_95,m_single_94,.tetra,[0,1,2,4,3,5,6],[2,5,5,5,5,3],32,0,cert_single_242⟩,
  ⟨95,94,m_single_95,m_single_94,.tetra,[0,1,2,4,3,6,5],[2,5,5,5,5,3],32,0,cert_single_243⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,4,5,6,7,8,9],[4,6,8,8,6,4],32,0,cert_single_244⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,4,5,6,7,9,8],[4,6,8,8,6,4],32,0,cert_single_245⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,4,5,7,6,8,9],[4,6,8,8,6,4],32,0,cert_single_246⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,4,5,7,6,9,8],[4,6,8,8,6,4],32,0,cert_single_247⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,5,4,6,7,8,9],[4,6,8,8,6,4],32,0,cert_single_248⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,5,4,6,7,9,8],[4,6,8,8,6,4],32,0,cert_single_249⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,5,4,7,6,8,9],[4,6,8,8,6,4],32,0,cert_single_250⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,2,3,5,4,7,6,9,8],[4,6,8,8,6,4],32,0,cert_single_251⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,4,5,8,9,6,7],[4,6,8,8,6,4],32,0,cert_single_252⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,4,5,8,9,7,6],[4,6,8,8,6,4],32,0,cert_single_253⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,4,5,9,8,6,7],[4,6,8,8,6,4],32,0,cert_single_254⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,8,8,6,4],32,0,cert_single_255⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,5,4,8,9,6,7],[4,6,8,8,6,4],32,0,cert_single_256⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,5,4,8,9,7,6],[4,6,8,8,6,4],32,0,cert_single_257⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,5,4,9,8,6,7],[4,6,8,8,6,4],32,0,cert_single_258⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,8,8,6,4],32,0,cert_single_259⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,6,7,4,5,8,9],[4,6,8,8,6,4],32,0,cert_single_260⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,6,7,4,5,9,8],[4,6,8,8,6,4],32,0,cert_single_261⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,6,7,5,4,8,9],[4,6,8,8,6,4],32,0,cert_single_262⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,6,7,5,4,9,8],[4,6,8,8,6,4],32,0,cert_single_263⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,7,6,4,5,8,9],[4,6,8,8,6,4],32,0,cert_single_264⟩]

private def chunk11 : List Row := [
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,7,6,4,5,9,8],[4,6,8,8,6,4],32,0,cert_single_265⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,7,6,5,4,8,9],[4,6,8,8,6,4],32,0,cert_single_266⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,1,3,7,6,5,4,9,8],[4,6,8,8,6,4],32,0,cert_single_267⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,6,7,8,9,4,5],[4,6,8,8,6,4],32,0,cert_single_268⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,6,7,8,9,5,4],[4,6,8,8,6,4],32,0,cert_single_269⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,6,7,9,8,4,5],[4,6,8,8,6,4],32,0,cert_single_270⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,6,7,9,8,5,4],[4,6,8,8,6,4],32,0,cert_single_271⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,7,6,8,9,4,5],[4,6,8,8,6,4],32,0,cert_single_272⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,7,6,8,9,5,4],[4,6,8,8,6,4],32,0,cert_single_273⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,7,6,9,8,4,5],[4,6,8,8,6,4],32,0,cert_single_274⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,2,3,1,7,6,9,8,5,4],[4,6,8,8,6,4],32,0,cert_single_275⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,8,9,4,5,6,7],[4,6,8,8,6,4],32,0,cert_single_276⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,8,9,4,5,7,6],[4,6,8,8,6,4],32,0,cert_single_277⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,8,9,5,4,6,7],[4,6,8,8,6,4],32,0,cert_single_278⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,8,9,5,4,7,6],[4,6,8,8,6,4],32,0,cert_single_279⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,9,8,4,5,6,7],[4,6,8,8,6,4],32,0,cert_single_280⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,9,8,4,5,7,6],[4,6,8,8,6,4],32,0,cert_single_281⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,9,8,5,4,6,7],[4,6,8,8,6,4],32,0,cert_single_282⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,1,2,9,8,5,4,7,6],[4,6,8,8,6,4],32,0,cert_single_283⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,8,9,6,7,4,5],[4,6,8,8,6,4],32,0,cert_single_284⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,8,9,6,7,5,4],[4,6,8,8,6,4],32,0,cert_single_285⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,8,9,7,6,4,5],[4,6,8,8,6,4],32,0,cert_single_286⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,8,9,7,6,5,4],[4,6,8,8,6,4],32,0,cert_single_287⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,9,8,6,7,4,5],[4,6,8,8,6,4],32,0,cert_single_288⟩]

private def chunk12 : List Row := [
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,9,8,6,7,5,4],[4,6,8,8,6,4],32,0,cert_single_289⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,9,8,7,6,4,5],[4,6,8,8,6,4],32,0,cert_single_290⟩,
  ⟨155,156,m_single_155,m_single_156,.tetra,[0,3,2,1,9,8,7,6,5,4],[4,6,8,8,6,4],32,0,cert_single_291⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,4,5,6,7,8,9],[4,6,8,8,6,5],32,0,cert_single_292⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,4,5,6,7,9,8],[4,6,8,8,6,5],32,0,cert_single_293⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,4,5,7,6,8,9],[4,6,8,8,6,5],32,0,cert_single_294⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,4,5,7,6,9,8],[4,6,8,8,6,5],32,0,cert_single_295⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,5,4,6,7,8,9],[4,6,8,8,6,5],32,0,cert_single_296⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,5,4,6,7,9,8],[4,6,8,8,6,5],32,0,cert_single_297⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,5,4,7,6,8,9],[4,6,8,8,6,5],32,0,cert_single_298⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,2,3,5,4,7,6,9,8],[4,6,8,8,6,5],32,0,cert_single_299⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,4,5,8,9,6,7],[4,6,8,8,6,5],32,0,cert_single_300⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,4,5,8,9,7,6],[4,6,8,8,6,5],32,0,cert_single_301⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,4,5,9,8,6,7],[4,6,8,8,6,5],32,0,cert_single_302⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,8,8,6,5],32,0,cert_single_303⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,5,4,8,9,6,7],[4,6,8,8,6,5],32,0,cert_single_304⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,5,4,8,9,7,6],[4,6,8,8,6,5],32,0,cert_single_305⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,5,4,9,8,6,7],[4,6,8,8,6,5],32,0,cert_single_306⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,8,8,6,5],32,0,cert_single_307⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,6,7,4,5,8,9],[4,6,8,8,6,5],32,0,cert_single_308⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,6,7,4,5,9,8],[4,6,8,8,6,5],32,0,cert_single_309⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,6,7,5,4,8,9],[4,6,8,8,6,5],32,0,cert_single_310⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,6,7,5,4,9,8],[4,6,8,8,6,5],32,0,cert_single_311⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,7,6,4,5,8,9],[4,6,8,8,6,5],32,0,cert_single_312⟩]

private def chunk13 : List Row := [
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,7,6,4,5,9,8],[4,6,8,8,6,5],32,0,cert_single_313⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,7,6,5,4,8,9],[4,6,8,8,6,5],32,0,cert_single_314⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,1,3,7,6,5,4,9,8],[4,6,8,8,6,5],32,0,cert_single_315⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,6,7,8,9,4,5],[4,6,8,8,6,5],32,0,cert_single_316⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,6,7,8,9,5,4],[4,6,8,8,6,5],32,0,cert_single_317⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,6,7,9,8,4,5],[4,6,8,8,6,5],32,0,cert_single_318⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,6,7,9,8,5,4],[4,6,8,8,6,5],32,0,cert_single_319⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,7,6,8,9,4,5],[4,6,8,8,6,5],32,0,cert_single_320⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,7,6,8,9,5,4],[4,6,8,8,6,5],32,0,cert_single_321⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,7,6,9,8,4,5],[4,6,8,8,6,5],32,0,cert_single_322⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,2,3,1,7,6,9,8,5,4],[4,6,8,8,6,5],32,0,cert_single_323⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,8,9,4,5,6,7],[4,6,8,8,6,5],32,0,cert_single_324⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,8,9,4,5,7,6],[4,6,8,8,6,5],32,0,cert_single_325⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,8,9,5,4,6,7],[4,6,8,8,6,5],32,0,cert_single_326⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,8,9,5,4,7,6],[4,6,8,8,6,5],32,0,cert_single_327⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,9,8,4,5,6,7],[4,6,8,8,6,5],32,0,cert_single_328⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,9,8,4,5,7,6],[4,6,8,8,6,5],32,0,cert_single_329⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,9,8,5,4,6,7],[4,6,8,8,6,5],32,0,cert_single_330⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,1,2,9,8,5,4,7,6],[4,6,8,8,6,5],32,0,cert_single_331⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,8,9,6,7,4,5],[4,6,8,8,6,5],32,0,cert_single_332⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,8,9,6,7,5,4],[4,6,8,8,6,5],32,0,cert_single_333⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,8,9,7,6,4,5],[4,6,8,8,6,5],32,0,cert_single_334⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,8,9,7,6,5,4],[4,6,8,8,6,5],32,0,cert_single_335⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,9,8,6,7,4,5],[4,6,8,8,6,5],32,0,cert_single_336⟩]

private def chunk14 : List Row := [
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,9,8,6,7,5,4],[4,6,8,8,6,5],32,0,cert_single_337⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,9,8,7,6,4,5],[4,6,8,8,6,5],32,0,cert_single_338⟩,
  ⟨156,155,m_single_156,m_single_155,.tetra,[0,3,2,1,9,8,7,6,5,4],[4,6,8,8,6,5],32,0,cert_single_339⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,6,7,4,5,8,9],[4,6,8,8,6,4],32,0,cert_single_340⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,6,7,4,5,9,8],[4,6,8,8,6,4],32,0,cert_single_341⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,6,7,5,4,8,9],[4,6,8,8,6,4],32,0,cert_single_342⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,6,7,5,4,9,8],[4,6,8,8,6,4],32,0,cert_single_343⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,7,6,4,5,8,9],[4,6,8,8,6,4],32,0,cert_single_344⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,7,6,4,5,9,8],[4,6,8,8,6,4],32,0,cert_single_345⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,7,6,5,4,8,9],[4,6,8,8,6,4],32,0,cert_single_346⟩,
  ⟨160,160,m_single_160,m_single_160,.tetra,[0,2,1,3,7,6,5,4,9,8],[4,6,8,8,6,4],32,0,cert_single_347⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,4,5,6,7,8,9],[4,6,8,8,6,4],32,0,cert_single_348⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,4,5,6,7,9,8],[4,6,8,8,6,4],32,0,cert_single_349⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,4,5,7,6,8,9],[4,6,8,8,6,4],32,0,cert_single_350⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,4,5,7,6,9,8],[4,6,8,8,6,4],32,0,cert_single_351⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,5,4,6,7,8,9],[4,6,8,8,6,4],32,0,cert_single_352⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,5,4,6,7,9,8],[4,6,8,8,6,4],32,0,cert_single_353⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,5,4,7,6,8,9],[4,6,8,8,6,4],32,0,cert_single_354⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,2,3,5,4,7,6,9,8],[4,6,8,8,6,4],32,0,cert_single_355⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,4,5,8,9,6,7],[4,6,8,8,6,4],32,0,cert_single_356⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,4,5,8,9,7,6],[4,6,8,8,6,4],32,0,cert_single_357⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,4,5,9,8,6,7],[4,6,8,8,6,4],32,0,cert_single_358⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,8,8,6,4],32,0,cert_single_359⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,5,4,8,9,6,7],[4,6,8,8,6,4],32,0,cert_single_360⟩]

private def chunk15 : List Row := [
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,5,4,8,9,7,6],[4,6,8,8,6,4],32,0,cert_single_361⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,5,4,9,8,6,7],[4,6,8,8,6,4],32,0,cert_single_362⟩,
  ⟨164,165,m_single_164,m_single_165,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,8,8,6,4],32,0,cert_single_363⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,4,5,6,7,8,9],[4,6,8,8,6,5],32,0,cert_single_364⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,4,5,6,7,9,8],[4,6,8,8,6,5],32,0,cert_single_365⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,4,5,7,6,8,9],[4,6,8,8,6,5],32,0,cert_single_366⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,4,5,7,6,9,8],[4,6,8,8,6,5],32,0,cert_single_367⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,5,4,6,7,8,9],[4,6,8,8,6,5],32,0,cert_single_368⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,5,4,6,7,9,8],[4,6,8,8,6,5],32,0,cert_single_369⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,5,4,7,6,8,9],[4,6,8,8,6,5],32,0,cert_single_370⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,2,3,5,4,7,6,9,8],[4,6,8,8,6,5],32,0,cert_single_371⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,4,5,8,9,6,7],[4,6,8,8,6,5],32,0,cert_single_372⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,4,5,8,9,7,6],[4,6,8,8,6,5],32,0,cert_single_373⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,4,5,9,8,6,7],[4,6,8,8,6,5],32,0,cert_single_374⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,8,8,6,5],32,0,cert_single_375⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,5,4,8,9,6,7],[4,6,8,8,6,5],32,0,cert_single_376⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,5,4,8,9,7,6],[4,6,8,8,6,5],32,0,cert_single_377⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,5,4,9,8,6,7],[4,6,8,8,6,5],32,0,cert_single_378⟩,
  ⟨165,164,m_single_165,m_single_164,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,8,8,6,5],32,0,cert_single_379⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,2,3,4,5,6,7,8,9],[4,6,7,7,6,4],32,0,cert_single_380⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,2,3,4,5,8,9,6,7],[4,6,7,7,6,4],32,0,cert_single_381⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,2,3,5,4,6,7,8,9],[4,6,7,7,6,4],32,0,cert_single_382⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,2,3,5,4,8,9,6,7],[4,6,7,7,6,4],32,0,cert_single_383⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,3,2,4,5,7,6,9,8],[4,6,7,7,6,4],32,0,cert_single_384⟩]

private def chunk16 : List Row := [
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,7,7,6,4],32,0,cert_single_385⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,3,2,5,4,7,6,9,8],[4,6,7,7,6,4],32,0,cert_single_386⟩,
  ⟨167,168,m_single_167,m_single_168,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,7,7,6,4],32,0,cert_single_387⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,2,3,4,5,6,7,8,9],[4,6,7,7,6,5],32,0,cert_single_388⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,2,3,4,5,8,9,6,7],[4,6,7,7,6,5],32,0,cert_single_389⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,2,3,5,4,6,7,8,9],[4,6,7,7,6,5],32,0,cert_single_390⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,2,3,5,4,8,9,6,7],[4,6,7,7,6,5],32,0,cert_single_391⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,3,2,4,5,7,6,9,8],[4,6,7,7,6,5],32,0,cert_single_392⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,7,7,6,5],32,0,cert_single_393⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,3,2,5,4,7,6,9,8],[4,6,7,7,6,5],32,0,cert_single_394⟩,
  ⟨168,167,m_single_168,m_single_167,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,7,7,6,5],32,0,cert_single_395⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,4,5,8,9,6,7],[4,6,8,8,6,4],32,0,cert_single_396⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,4,5,8,9,7,6],[4,6,8,8,6,4],32,0,cert_single_397⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,4,5,9,8,6,7],[4,6,8,8,6,4],32,0,cert_single_398⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,4,5,9,8,7,6],[4,6,8,8,6,4],32,0,cert_single_399⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,5,4,8,9,6,7],[4,6,8,8,6,4],32,0,cert_single_400⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,5,4,8,9,7,6],[4,6,8,8,6,4],32,0,cert_single_401⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,5,4,9,8,6,7],[4,6,8,8,6,4],32,0,cert_single_402⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,1,3,2,5,4,9,8,7,6],[4,6,8,8,6,4],32,0,cert_single_403⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,6,7,4,5,8,9],[4,6,8,8,6,4],32,0,cert_single_404⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,6,7,4,5,9,8],[4,6,8,8,6,4],32,0,cert_single_405⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,6,7,5,4,8,9],[4,6,8,8,6,4],32,0,cert_single_406⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,6,7,5,4,9,8],[4,6,8,8,6,4],32,0,cert_single_407⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,7,6,4,5,8,9],[4,6,8,8,6,4],32,0,cert_single_408⟩]

private def chunk17 : List Row := [
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,7,6,4,5,9,8],[4,6,8,8,6,4],32,0,cert_single_409⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,7,6,5,4,8,9],[4,6,8,8,6,4],32,0,cert_single_410⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,2,1,3,7,6,5,4,9,8],[4,6,8,8,6,4],32,0,cert_single_411⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,8,9,6,7,4,5],[4,6,8,8,6,4],32,0,cert_single_412⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,8,9,6,7,5,4],[4,6,8,8,6,4],32,0,cert_single_413⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,8,9,7,6,4,5],[4,6,8,8,6,4],32,0,cert_single_414⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,8,9,7,6,5,4],[4,6,8,8,6,4],32,0,cert_single_415⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,9,8,6,7,4,5],[4,6,8,8,6,4],32,0,cert_single_416⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,9,8,6,7,5,4],[4,6,8,8,6,4],32,0,cert_single_417⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,9,8,7,6,4,5],[4,6,8,8,6,4],32,0,cert_single_418⟩,
  ⟨172,172,m_single_172,m_single_172,.tetra,[0,3,2,1,9,8,7,6,5,4],[4,6,8,8,6,4],32,0,cert_single_419⟩]

def rows : List Row := chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 ++ chunk17

theorem attachedMatrices :
    rows.all (fun r => decide (OnCatalog r)) = true := by native_decide

theorem attachedKeys : rows.map Row.key = Input.expected := by decide

theorem actual_key_has_checked_witness
    (c : QGI.SixteenMapSearch.Counts) (hc : census = some c)
    (k : Key) (hk : k ∈ c.exceptions) :
    ∃ r ∈ rows, r.key = k ∧ OnCatalog r ∧
      homCount r.src r.pattern r.colors ≠
      homCount r.dst r.pattern (renamed r.src r.perm r.colors) := by
  have certified := catalogueCheck
  unfold checked at certified
  rw [hc] at certified
  change agrees c = true at certified
  unfold agrees at certified
  have keysMatch : expectedKeysMatch c.exceptions = true :=
    (Bool.and_eq_true_iff.mp certified).2
  unfold expectedKeysMatch at keysMatch
  have hall : c.exceptions.all (fun j => Input.expected.contains j) = true :=
    (Bool.and_eq_true_iff.mp keysMatch).2
  have hlisted : k ∈ Input.expected := by
    simpa using (List.all_eq_true.mp hall k hk)
  rw [← attachedKeys] at hlisted
  obtain ⟨r, hr, hkey⟩ := List.mem_map.mp hlisted
  have bound : OnCatalog r :=
    of_decide_eq_true (List.all_eq_true.mp attachedMatrices r hr)
  exact ⟨r, hr, hkey, bound, counts_differ_of_checked r.passed⟩

end QGI.Single16.Attachment
