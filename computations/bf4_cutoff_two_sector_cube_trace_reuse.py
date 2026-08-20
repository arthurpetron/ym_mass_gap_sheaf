"""Emit the remaining Lean shards for the cube/cube generic-sector trace.

The existing 24 sparse tables were independently checked against the folded
cube graph.  These generated shards replay the same untrusted data against the
new 140-factor graph containing genuine production lower-link factors.
"""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean" / "YMGap" / "Continuum"
ORDER = (38, 22, 14, 5, 31, 32, 56, 58, 23, 40, 47, 50,
         13, 4, 41, 2, 11, 20, 65, 29, 59, 49, 68, 67)
LETTERS = "BCDEF"


def shard_source(letter: str, start: int) -> str:
    previous = (
        "BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0"
        if letter == "B"
        else f"BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShard{chr(ord(letter) - 1)}"
    )
    namespace = f"BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShard{letter}"
    pieces = [f'''/- Generated generic-sector cube trace shard {letter}. -/
import YMGap.Continuum.{previous}

namespace YMGap.Continuum.{namespace}

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.{previous}
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv
''']
    for index in range(start, start + 4):
        pieces.append(f'''
def sectorCubeStep{index} : CheckedScopedEliminationStep 2 {ORDER[index]}
    (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
    sectorCubeFactors{index} where
  bucketResult :=
    {{ result := (cutoffTwoCubeInterfaceEliminationDatum {index}).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }}
  result_scope_remaining_checked := by decide

def sectorCubeFactors{index + 1} : List ScopedQFactor :=
  sectorCubeStep{index}.afterFactors
''')
    end = start + 4
    chain = "\n".join(
        f'''    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {index + 1})
        sectorCubeFactors{index + 1} := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sectorCubeStep{index}.partitionSum_eqv_after'''
        for index in range(start, end)
    )
    pieces.append(f'''
theorem sectorCubeShard{letter}_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {start})
        sectorCubeFactors{start} ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop {end})
        sectorCubeFactors{end} := by
  calc
{chain}

end YMGap.Continuum.{namespace}

#print axioms
  YMGap.Continuum.{namespace}.sectorCubeShard{letter}_partitionSum_eqv
''')
    return "".join(pieces)


def root_source() -> str:
    return '''/- Complete cube/cube replay on the genuine 140-factor graph. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardB
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardC
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardD
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardE
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShardF
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem sectorCubeTerminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        sectorCubeFactors24 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  decide

theorem sectorCubeInterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        sectorCubeFactors0 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  exact Q'.eqv_trans _ _ _ sectorCubeShardA_partitionSum_eqv
    (Q'.eqv_trans _ _ _ sectorCubeShardB_partitionSum_eqv
      (Q'.eqv_trans _ _ _ sectorCubeShardC_partitionSum_eqv
        (Q'.eqv_trans _ _ _ sectorCubeShardD_partitionSum_eqv
          (Q'.eqv_trans _ _ _ sectorCubeShardE_partitionSum_eqv
            (Q'.eqv_trans _ _ _ sectorCubeShardF_partitionSum_eqv
              sectorCubeTerminal_partitionSum_eqv_expected)))))

theorem sectorCubeInterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        sectorCubeFactors0 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct sectorCubeFactors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    sectorCubeInterfacePartitionSum_ordered_eqv

theorem centralPhysicalReflectedKernel_cutoffTwo_cube_cube_eqv :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState centralLowerCubeState ≈
      ((Q'.mkPos 1 4096 (by decide) : Q') *
        (Q'.mkPos 1 4096 (by decide) : Q')) *
          cutoffTwoCubeExpectedInterfaceSum := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      centralLowerCubeState centralLowerCubeState
      (by simp [cutoffTwoCubeSectorStates])
      (by simp [cutoffTwoCubeSectorStates])) ?_
  exact q_mul_congr
    (q_mul_congr cutoffTwoLowerFaceScalar_cube_eqv
      cutoffTwoLowerFaceScalar_cube_eqv)
    sectorCubeInterfacePartitionSum_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate.sectorCubeInterfacePartitionSum_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate.centralPhysicalReflectedKernel_cutoffTwo_cube_cube_eqv
'''


def write_if_changed(path: Path, source: str) -> None:
    if not path.exists() or path.read_text() != source:
        path.write_text(source)


def main() -> None:
    for offset, letter in enumerate(LETTERS, start=1):
        start = 4 * offset
        write_if_changed(
            LEAN / f"BF4PhysicalBoundaryCutoffTwoSectorCubeTraceShard{letter}.lean",
            shard_source(letter, start),
        )
    write_if_changed(
        LEAN / "BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate.lean",
        root_source(),
    )


if __name__ == "__main__":
    main()
