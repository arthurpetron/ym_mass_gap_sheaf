"""Emit memory-bounded physical-to-canonical factor transports.

Each six-factor local check lives in its own Lean module.  Root modules compose
only already checked `FactorListTransport` constants, so physical definition
reduction never accumulates across a 44- or 48-factor list.
"""

from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean" / "YMGap" / "Continuum"
COMMON_CHUNK_SIZE = 3
SOURCE_CHUNK_SIZE = 6


def _write_if_changed(path: Path, source: str) -> None:
    if path.exists() and path.read_text() == source:
        return
    path.write_text(source)


def _rest_defs(
    prefix: str, source: str, target: str, count: int, chunk_size: int
) -> str:
    pieces = [
        f"def {prefix}SourceRest0 : List ScopedQFactor :=\n  {source}",
        f"def {prefix}TargetRest0 : List ScopedQFactor :=\n  {target}",
    ]
    for index in range(count - 1):
        pieces.extend([
            f"def {prefix}SourceChunk{index:02d} : List ScopedQFactor :=\n"
            f"  {prefix}SourceRest{index}.take {chunk_size}",
            f"def {prefix}TargetChunk{index:02d} : List ScopedQFactor :=\n"
            f"  {prefix}TargetRest{index}.take {chunk_size}",
            f"def {prefix}SourceRest{index + 1} : List ScopedQFactor :=\n"
            f"  {prefix}SourceRest{index}.drop {chunk_size}",
            f"def {prefix}TargetRest{index + 1} : List ScopedQFactor :=\n"
            f"  {prefix}TargetRest{index}.drop {chunk_size}",
        ])
    pieces.extend([
        f"def {prefix}SourceChunk{count - 1:02d} : List ScopedQFactor :=\n"
        f"  {prefix}SourceRest{count - 1}",
        f"def {prefix}TargetChunk{count - 1:02d} : List ScopedQFactor :=\n"
        f"  {prefix}TargetRest{count - 1}",
    ])
    return "\n\n".join(pieces)


def render_common_data() -> str:
    return f'''/- Six-factor views of the genuine and canonical common lists. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorTableCertificate

def cutoffTwoCanonicalTransportIdentity (id : Nat) : Nat := id

{_rest_defs(
    "cutoffTwoCanonicalCommon",
    "cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors",
    "cutoffTwoCanonicalCommonFactors",
    15,
    COMMON_CHUNK_SIZE,
)}

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
'''


def render_common_chunk(index: int) -> str:
    prefix = "cutoffTwoCanonicalCommon"
    return f'''/- Checked common-factor transport chunk {index}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def {prefix}Chunk{index:02d}Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    {prefix}SourceChunk{index:02d} {prefix}TargetChunk{index:02d}

theorem {prefix}Chunk{index:02d}Check_checked :
    {prefix}Chunk{index:02d}Check = true := by
  decide

theorem {prefix}Chunk{index:02d}Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      {prefix}SourceChunk{index:02d} {prefix}TargetChunk{index:02d} :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    {prefix}SourceChunk{index:02d} {prefix}TargetChunk{index:02d}
    {prefix}Chunk{index:02d}Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.{prefix}Chunk{index:02d}Transport
'''


def _render_root(
    *, prefix: str, count: int, imports: str, namespace: str,
    source: str, target: str, extra_opens: str,
) -> str:
    names = [f"{prefix}Chunk{index:02d}Transport" for index in range(count)]
    proof = f"  have h{count - 1} := {names[-1]}\n"
    for index in reversed(range(count - 1)):
        proof += f'''  have h{index} :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        {prefix}SourceRest{index} {prefix}TargetRest{index} := by
    simpa only [{prefix}SourceChunk{index:02d},
      {prefix}TargetChunk{index:02d},
      {prefix}SourceRest{index + 1}, {prefix}TargetRest{index + 1},
      List.take_append_drop] using
        FactorListTransport.append {names[index]} h{index + 1}
'''
    proof += f'''  simpa only [{prefix}SourceRest0,
    {prefix}TargetRest0] using h0'''
    return f'''/- Complete sharded transport for {prefix}. -/
{imports}

namespace YMGap.Continuum.{namespace}

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
{extra_opens}

theorem {prefix}Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      ({source}) ({target}) := by
{proof}

end YMGap.Continuum.{namespace}

#print axioms
  YMGap.Continuum.{namespace}.{prefix}Transport
'''


def render_common_root() -> str:
    imports = "\n".join(
        "import YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk{i:02d}"
        for i in range(15)
    )
    return _render_root(
        prefix="cutoffTwoCanonicalCommon",
        count=15,
        imports=imports,
        namespace="BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded",
        source="cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors",
        target="cutoffTwoCanonicalCommonFactors",
        extra_opens=(
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks\n"
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool\n"
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction\n"
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph"
        ),
    )


def render_state_data(index: int) -> str:
    prefix = f"cutoffTwoCanonicalSource{index:02d}"
    return f'''/- Six-factor views for source state {index}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{index:02d}Data

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate

{_rest_defs(
    prefix,
    f"cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt {index})",
    f"cutoffTwoCanonicalSourceFactorsAt {index}",
    8,
    SOURCE_CHUNK_SIZE,
)}

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{index:02d}Data
'''


def render_state_chunk(state: int, chunk: int) -> str:
    prefix = f"cutoffTwoCanonicalSource{state:02d}"
    namespace = f"BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{state:02d}Chunks"
    return f'''/- Checked source-state {state} transport chunk {chunk}. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{state:02d}Data

namespace YMGap.Continuum.{namespace}

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{state:02d}Data
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def {prefix}Chunk{chunk:02d}Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    {prefix}SourceChunk{chunk:02d} {prefix}TargetChunk{chunk:02d}

theorem {prefix}Chunk{chunk:02d}Check_checked :
    {prefix}Chunk{chunk:02d}Check = true := by
  decide

theorem {prefix}Chunk{chunk:02d}Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      {prefix}SourceChunk{chunk:02d} {prefix}TargetChunk{chunk:02d} :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    {prefix}SourceChunk{chunk:02d} {prefix}TargetChunk{chunk:02d}
    {prefix}Chunk{chunk:02d}Check_checked

end YMGap.Continuum.{namespace}

#print axioms
  YMGap.Continuum.{namespace}.{prefix}Chunk{chunk:02d}Transport
'''


def render_state_root(index: int) -> str:
    prefix = f"cutoffTwoCanonicalSource{index:02d}"
    imports = "\n".join(
        "import YMGap.Continuum."
        f"BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{index:02d}Chunks.Chunk{i:02d}"
        for i in range(8)
    )
    return _render_root(
        prefix=prefix,
        count=8,
        imports=imports,
        namespace=f"BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{index:02d}Sharded",
        source=f"cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt {index})",
        target=f"cutoffTwoCanonicalSourceFactorsAt {index}",
        extra_opens=(
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool\n"
            f"open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{index:02d}Data\n"
            f"open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{index:02d}Chunks\n"
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph\n"
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate"
        ),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--state", type=int, default=1)
    arguments = parser.parse_args()
    if not 0 <= arguments.state < 65:
        raise ValueError("state must lie in 0..64")

    _write_if_changed(
        LEAN / "BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData.lean",
        render_common_data(),
    )
    common_dir = LEAN / "BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks"
    common_dir.mkdir(parents=True, exist_ok=True)
    for chunk in range(15):
        _write_if_changed(
            common_dir / f"Chunk{chunk:02d}.lean",
            render_common_chunk(chunk),
        )
    _write_if_changed(
        LEAN / "BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded.lean",
        render_common_root(),
    )

    state = arguments.state
    _write_if_changed(
        LEAN / f"BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{state:02d}Data.lean",
        render_state_data(state),
    )
    state_dir = LEAN / f"BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{state:02d}Chunks"
    state_dir.mkdir(parents=True, exist_ok=True)
    for chunk in range(8):
        _write_if_changed(
            state_dir / f"Chunk{chunk:02d}.lean",
            render_state_chunk(state, chunk),
        )
    _write_if_changed(
        LEAN / f"BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport{state:02d}Sharded.lean",
        render_state_root(state),
    )
    print("generated 15 common and 8 state transport shards")


if __name__ == "__main__":
    main()
