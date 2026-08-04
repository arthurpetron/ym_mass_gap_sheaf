/-
# Maximal-forest gauge target for the cutoff-one BF4 surfaces

This module turns the checked primal forests into the concrete chord-only
surface networks used by maximal-tree gauge fixing.  The 24 displayed face
words are independently checked against the literal corrected-slab
plaquettes and the exact 32-block active-carrier order.  For each mask, tree
edges are deleted and the remaining physical edges are compactly renumbered
in its checked chord order.

Two named propositions now separate the last mathematical seam:

* Haar-preserving transport from the selected active carrier to these
  forest-gauge words;
* evaluation of the resulting chord network as `2^(V-E)`.

Neither proposition is inhabited here.  The six-face sphere is evaluated as
a kernel-checked regression on the new generic forest-gauge evaluator.

## Axiom gate

Finite lists, exact rational polynomials, and existing constructive Haar
machinery only.  No Classical.*, native_decide, sorry, custom axiom, choice,
or noncomputable declaration.
-/

import YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate
import YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionBivalentHaarContraction
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

abbrev SurfaceWord := List (Nat × Bool)

/-- The 24 positively oriented unit-four-cube plaquette boundaries in the
compact face order.  Edge ids use the checked 32-edge primal order. -/
def hypercubeFaceWords : List SurfaceWord :=
  [[(0, false), (20, false), (12, true), (1, true)],
   [(0, false), (21, false), (7, true), (2, true)],
   [(0, false), (22, false), (4, true), (3, true)],
   [(1, false), (13, false), (8, true), (2, true)],
   [(1, false), (14, false), (5, true), (3, true)],
   [(2, false), (9, false), (6, true), (3, true)],
   [(4, false), (23, false), (15, true), (5, true)],
   [(4, false), (24, false), (10, true), (6, true)],
   [(5, false), (16, false), (11, true), (6, true)],
   [(7, false), (25, false), (17, true), (8, true)],
   [(7, false), (26, false), (10, true), (9, true)],
   [(8, false), (18, false), (11, true), (9, true)],
   [(10, false), (27, false), (19, true), (11, true)],
   [(12, false), (28, false), (17, true), (13, true)],
   [(12, false), (29, false), (15, true), (14, true)],
   [(13, false), (18, false), (16, true), (14, true)],
   [(15, false), (30, false), (19, true), (16, true)],
   [(17, false), (31, false), (19, true), (18, true)],
   [(20, false), (28, false), (25, true), (21, true)],
   [(20, false), (29, false), (23, true), (22, true)],
   [(21, false), (26, false), (24, true), (22, true)],
   [(23, false), (30, false), (27, true), (24, true)],
   [(25, false), (31, false), (27, true), (26, true)],
   [(28, false), (31, false), (30, true), (29, true)]]

private def fallbackSlabFace :
    YMGap.Continuum.ClusterCount4DProgress.Z4Plaq :=
  ((0, 0, 0, 0), .p01)

/-- Map the active-carrier block order to the compact primal-edge order used
by `edgeIncidenceMasks` and `hypercubeEdgeEndpoints`. -/
def activeCarrierToCompactEdgeIds : List Nat :=
  [0, 20, 12, 1, 21, 7, 2, 22,
   4, 3, 13, 8, 14, 5, 9, 6,
   23, 15, 24, 10, 16, 11, 25, 17,
   26, 18, 27, 19, 28, 29, 30, 31]

/-- Read a compact face directly from the literal slab and express its four
raw links in active-carrier edge ids. -/
def literalActiveHypercubeFaceWord (compactFaceId : Nat) : SurfaceWord :=
  let slabFaceId := activeHypercubeSlabFaceIds.getD compactFaceId 0
  let face := (boundaryCompleteSlabPlaquettes 1).getD slabFaceId
    fallbackSlabFace
  (orientedPlaquetteBoundary face).map fun entry =>
    (activeCarrierToCompactEdgeIds.getD
        (bf4SurfaceActiveRawBlocks.idxOf
          ((boundaryCompleteSlabLinks 1).idxOf entry.link)) 0,
      entry.reverse)

def hypercubeFaceWordsLiteralCheck : Bool :=
  decide
    ((List.range 24).map literalActiveHypercubeFaceWord =
      hypercubeFaceWords)

/-- The compact word table is exactly the literal corrected-slab geometry
after the already-proved 116-to-32 active-block permutation. -/
theorem hypercubeFaceWordsLiteralCheck_true :
    hypercubeFaceWordsLiteralCheck = true := by
  decide

def surfaceSelectedCompactFaceIds (mask : Nat) : List Nat :=
  (List.range 24).filter fun faceId => mask.testBit faceId

/-- A deterministic chord-coordinate order for exact contraction.  The
unique 16-face toroidal representative uses a lower-width elimination order;
all other masks retain the canonical increasing physical-edge order. -/
def surfaceForestGaugeChordEdgeIds (mask : Nat) : List Nat :=
  if mask = 7302558 then
    [13, 14, 16, 9, 18, 21, 28, 22, 29, 20, 24, 30, 23, 25, 27, 26, 31]
  else surfacePrimalChordEdgeIds mask

def surfaceForestGaugeChordOrderCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    decide
      ((surfaceForestGaugeChordEdgeIds mask).length =
          (surfacePrimalChordEdgeIds mask).length) &&
    decide (surfaceForestGaugeChordEdgeIds mask).Nodup &&
    (List.range 32).all fun edgeId =>
      decide
        (edgeId ∈ surfaceForestGaugeChordEdgeIds mask ↔
          edgeId ∈ surfacePrimalChordEdgeIds mask)

/-- Every exact-contraction order is merely a permutation of the checked
post-forest chord set. -/
theorem surfaceForestGaugeChordOrderCheck_true :
    surfaceForestGaugeChordOrderCheck = true := by
  decide

/-- Delete the checked forest incidences and compactly renumber each chord. -/
def pruneSurfacePrimalForest (mask : Nat) : SurfaceWord → SurfaceWord
  | [] => []
  | entry :: rest =>
      if entry.1 ∈ surfaceForestGaugeChordEdgeIds mask then
        ((surfaceForestGaugeChordEdgeIds mask).idxOf entry.1, entry.2) ::
          pruneSurfacePrimalForest mask rest
      else pruneSurfacePrimalForest mask rest

/-- Selected face words in the concrete maximal-forest gauge. -/
def surfaceForestGaugeWords (mask : Nat) : List SurfaceWord :=
  (surfaceSelectedCompactFaceIds mask).map fun faceId =>
    pruneSurfacePrimalForest mask
      (hypercubeFaceWords.getD faceId [])

def surfaceForestGaugeFactors (mask : Nat) :=
  (surfaceForestGaugeWords mask).map compactFundamentalWordFactor

/-- The actual chord-only exact evaluator produced by the checked primal
forest. -/
def surfaceForestGaugeHaar (mask : Nat) : Q' :=
  compactBivalentFactorizedHaar
    (surfaceForestGaugeChordEdgeIds mask).length
    (surfaceForestGaugeFactors mask)

/-- Maximal-forest change of variables on the concrete selected-face
carrier.  This is the remaining Haar-invariance/word-semantics theorem. -/
def CutoffOneSurfaceForestGaugeTransport : Prop :=
  ∀ mask : Nat, mask ∈ binarySurfaceMasks → mask ≠ 0 →
    embeddedSurfaceSelectedActiveBivalentHaar mask ≈
      surfaceForestGaugeHaar mask

/-- Exact evaluation of every concrete chord-only surface network. -/
def CutoffOneSurfaceForestGaugeEvaluation : Prop :=
  ∀ mask : Nat, mask ∈ binarySurfaceMasks → mask ≠ 0 →
    surfaceForestGaugeHaar mask ≈
      surfaceTopologicalHaarAmplitude mask

/-- The two explicit forest-gauge obligations close the selected active
campaign, hence the original literal BF4 surface bridge. -/
theorem cutoffOneClosedSurfaceTopologicalAmplitude_of_forestGauge
    (transport : CutoffOneSurfaceForestGaugeTransport)
    (evaluation : CutoffOneSurfaceForestGaugeEvaluation) :
    CutoffOneClosedSurfaceTopologicalAmplitude := by
  apply cutoffOneClosedSurfaceTopologicalAmplitude_of_selectedActiveBivalent
  intro mask hmask hnonzero
  exact Q'.eqv_trans _ _ _
    (transport mask hmask hnonzero)
    (evaluation mask hmask hnonzero)

/-! ## Generic-evaluator regression -/

/-- The checked forest chosen for the vacuum-row six-face sphere leaves five
chords, as expected. -/
theorem sixFaceSphereForestChordCount :
    (surfacePrimalChordEdgeIds 2167232).length = 5 := by
  decide

/-- The generic forest-gauge evaluator reproduces the exact `1/16`
six-face-sphere value. -/
theorem sixFaceSphereForestGaugeHaar_exact :
    surfaceForestGaugeHaar 2167232 ≈
      surfaceTopologicalHaarAmplitude 2167232 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge.hypercubeFaceWordsLiteralCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge.surfaceForestGaugeChordOrderCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge.cutoffOneClosedSurfaceTopologicalAmplitude_of_forestGauge
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge.sixFaceSphereForestGaugeHaar_exact
