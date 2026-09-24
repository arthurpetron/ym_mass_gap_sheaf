/-
# Local regularity of the COMPLETE original projected endpoint source

Every original spatial factor and the full terminal history are retained.
At one active physical link, the spatial derivative costs at most six
one-face bounds and the positive-depth message costs one output-heat bound.
Haar integration over the inactive fringe preserves the resulting relative
bound, rather than substituting a different source or a conditional heat.

The explicit cap and sufficiently-late cutoff depend only on the nome.
Width, terminal depth and the chosen active link remain quantified. This
supplies local angular control for spectral tail estimates. It does not
control the SAME centered variance or justify a changing-spacing limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.SU2QuaternionHaarFamilyRelativeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyRelativeBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight activeBlocks

/-- Computed local cap: six possible spatial faces plus one terminal output.
No cutoff, width, depth or selected-link parameter is hidden in this value. -/
def endpointRelativeCap (w : Q') : Q' :=
  6 * relativeCap w 4096 + relativeCap w 32

/-- One explicit cutoff suffices for both distinct relative heat estimates. -/
def endpointRelativeCutoff (w : Q') : Nat :=
  max (relativeCutoff w 4096) (relativeCutoff w 32)

private def terminalAllDepths {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) (4*s+i) (4*s+j)
      (terminalMessage w K width n) (relativeCap w 32) := by
  cases n with
  | zero =>
      exact (RelativeBound.ofZeroDerivative (Certificate.one (N width))
        (angularDerivative_one (4*s+i) (4*s+j))).weaken
        (Q'.le_of_lt (relativeCap_positive hw0 (by decide : (0 : Q') ≤ 32)))
  | succ n => exact terminalMessageRelativeBound hw0 hw1 K width hK n s hs hi hj

/-- The complete unprojected source V*g_n, including at terminal depth zero. -/
def endpointSourceRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) (4*(baseLinks width).idxOf selected+i)
      (4*(baseLinks width).idxOf selected+j)
      (endpointSource w K width (terminalMessage w K width n)) (endpointRelativeCap w) :=
  (spatialWeightRelativeBound hw0 hw1 K width
    (Nat.le_trans (Nat.le_max_left _ _) hK) selected hl hi hj).mul
    (terminalAllDepths hw0 hw1 K width (Nat.le_trans (Nat.le_max_right _ _) hK)
      n _ hs hi hj)

/-- The same local cap survives integration of the original inactive fringe.
There is no source-independence assumption and no new positivity input. -/
def projectedEndpointRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) (4*(baseLinks width).idxOf selected+i)
      (4*(baseLinks width).idxOf selected+j)
      (projectedEndpointSource w K width (terminalMessage w K width n))
      (endpointRelativeCap w) :=
  familyProjectRelativeBound (N width) (fringeBlocks width) (fringeBlocks_lt width)
    _ (List.idxOf_lt_length_of_mem hl) hi hj
    (fun hf => ((fringeBlocks_mem_iff width _).mp hf).2 hs)
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
    (endpointSourceRelativeBound hw0 hw1 K width hK n selected hl hs hi hj)

/-- Each actual projected-source derivative square, with any certified
positive background retained on the SAME carrier. -/
theorem projectedEndpointRelativeWeightedSquare {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4)
    {R : RatPoly} (HR : Certificate (N width) R) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    let d := blockAngularDerivative ((baseLinks width).idxOf selected) i j q
    weightedPair (N width) R d d ≤
      (endpointRelativeCap w * endpointRelativeCap w) * weightedPair (N width) R q q :=
  relativeWeightedSquare
    (projectedEndpointRelativeBound hw0 hw1 K width hK n selected hl hs hi hj) HR

/-- The full six-plane Casimir energy at the selected original active link.
The factor six counts rotations of ONE link, not lattice volume. -/
theorem projectedEndpointAngularSquare_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {R : RatPoly} (HR : Certificate (N width) R) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    quaternionHaar (N width)
      (polyMul (blockAngularSquare ((baseLinks width).idxOf selected) q) R) ≤
      6 * (endpointRelativeCap w * endpointRelativeCap w) * weightedPair (N width) R q q := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let s := (baseLinks width).idxOf selected
  let c := endpointRelativeCap w * endpointRelativeCap w
  let a := weightedPair (N width) R q q
  have he : quaternionHaar (N width) (polyMul (blockAngularSquare s q) R) ≈
      sixValue (fun i j => weightedPair (N width) R
        (blockAngularDerivative s i j q) (blockAngularDerivative s i j q)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (haar_six (N width) R _)
        (sixValue_congr _ _ (fun _ _ _ _ => haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))
  have hsum := sixValue_mono
    (fun i j => weightedPair (N width) R
      (blockAngularDerivative s i j q) (blockAngularDerivative s i j q))
    (fun _ _ => c*a) (fun i j hi hj =>
      projectedEndpointRelativeWeightedSquare hw0 hw1 K width hK n selected hl hs hi hj HR)
  have hc : sixValue (fun _ _ => c*a) ≈ 6*c*a :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 0) (.var 1))
          (.add (.mul (.var 0) (.var 1))
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))))
      (.mul (.mul (.const 6) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => c | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hc))

#print axioms endpointRelativeCap
#print axioms endpointRelativeCutoff
#print axioms endpointSourceRelativeBound
#print axioms projectedEndpointRelativeBound
#print axioms projectedEndpointRelativeWeightedSquare
#print axioms projectedEndpointAngularSquare_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
