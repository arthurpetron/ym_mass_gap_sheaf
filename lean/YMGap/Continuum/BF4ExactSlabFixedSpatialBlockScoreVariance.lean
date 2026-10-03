/-
Last-output angular control of the ORIGINAL half-open window.  The derivative
acts on one kinetic factor at the final transition, not on all t transitions.
Every input/intermediate spatial factor and the original terminal input remain.
The subsequent conditional score estimate retains the conditional noise; it
does not compare that noise with the surviving filtered norm or prove a
changing-family response bound.
-/
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound
import YMGap.Continuum.SU2QuaternionAngularLift
import YMGap.Continuum.SU2QuaternionMultiHeadSignedDualSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_supported_at)
open YMGap.Continuum.SU2QuaternionAngularLift
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.SU2QuaternionMultiHeadSignedDualSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add middleRatio)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4DyadicWilsonSquare (paddedSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks kineticWeight spatialWeight activeBlocks terminalMessage

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private def certificate_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large)
    (P : Certificate small p) : Certificate large p := by
  have he : small+(large-small) = large := by omega
  exact he ▸ certificate_extend (large-small) hp P

private theorem zero_after {small block i j : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hb : small ≤ block)
    (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv (angularDerivative (4*block+i) (4*block+j) p) polyZero := by
  have he : small+(block-small) = block := by omega
  have hind := supported_upper_independent hp (block-small)
  rw [he] at hind
  exact angularDerivative_blockIndependent_zero hi hj hind

private def relative_lift {blocks i j : Nat} {p : RatPoly} {c : Q'}
    (shift : Nat) (P : RelativeBound blocks i j p c) :
    RelativeBound (blocks+shift) (4*shift+i) (4*shift+j)
      (liftBoundary shift p) c where
  positive := lift_certificate shift P.positive
  nonnegative := P.nonnegative
  upper := by
    have hp : RatPolyCoeffEqv
        (polyMul (cap c) (liftBoundary shift p))
        (liftBoundary shift (polyMul (cap c) p)) := by
      have h := lift_coeff shift (cap_mul_left c p)
      rw [lift_smul] at h
      exact (cap_mul_left c (liftBoundary shift p)).trans h.symm
    have hd := angularDerivative_liftBoundary shift i j p
    exact Certificate.ofCoeff (hp.add (RatPolyCoeffEqv.neg hd))
      (by simpa only [lift_add, lift_neg] using lift_certificate shift P.upper)
  lower := by
    have hp : RatPolyCoeffEqv
        (polyMul (cap c) (liftBoundary shift p))
        (liftBoundary shift (polyMul (cap c) p)) := by
      have h := lift_coeff shift (cap_mul_left c p)
      rw [lift_smul] at h
      exact (cap_mul_left c (liftBoundary shift p)).trans h.symm
    have hd := angularDerivative_liftBoundary shift i j p
    exact Certificate.ofCoeff (hp.add hd)
      (by simpa only [lift_add] using lift_certificate shift P.lower)

private def kinetic_relative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width+N width) (4*(N width+s)+i) (4*(N width+s)+j)
      (kineticWeight w K width) (relativeCap w 32) := by
  let ids := eraseIndex s (activeBlocks width)
  have hsn := activeBlocks_lt width s hs
  have hids : ∀ k, k ∈ ids → k < N width :=
    fun k hk => activeBlocks_lt width k (mem_of_mem_erase s hk)
  have hz := angularDerivative_blockIndependent_zero hi hj
    (productHeat_independent_upper (N width) w K ids hids s hsn
      (not_mem_erase s (activeBlocks_nodup width)))
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let P := heatRelativeBound (show s < N width+N width by omega)
    (show N width+s < N width+N width by omega)
    (show 4*(N width+s)+i < 4*(N width+N width) by omega)
    (show 4*(N width+s)+j < 4*(N width+N width) by omega) hw0 hw1 K hK
  let Q := RelativeBound.ofZeroDerivative
    (productHeatCertificate (N width) hw0 hw1 K hhead ids hids) hz
  have hp : RatPolyCoeffEqv (kineticWeight w K width)
      (polyMul (heatAt s (N width+s) w K) (productHeat (N width) w K ids)) := by
    rw [kineticWeight_eq_indexedProduct]
    exact polynomialProduct_perm _ (select_perm s hs)
  exact RelativeBound.ofCoeff hp ((P.mul Q).changeCap (QPoly.q_add_zero_eqv _))

/-- Actual full half-open action at its final output plane.  The constant
is that of ONE last-link heat factor, with no time-horizon multiplier. -/
def halfOpenAction_outputRelative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    (r : Nat) → RelativeBound ((r+2)*(N width))
      (4*((r+1)*(N width)+s)+i) (4*((r+1)*(N width)+s)+j)
      (halfOpenAction (N width) (kineticWeight w K width)
        (spatialWeight w K width) (r+1)) (relativeCap w 32)
  | 0 => by
      have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
      let P := kinetic_relative hw0 hw1 K width hK s hs hi hj
      have hone : SupportedQuaternionBlocks (N width) (liftBoundary (N width) polyOne) := by
        simpa only [Nat.zero_add] using lift_supported (supported_one 0) (N width)
      have Cone : Certificate (N width) (liftBoundary (N width) polyOne) := by
        simpa only [Nat.zero_add] using lift_certificate (N width) (Certificate.one 0)
      have hr := supported_polyMul (spatialWeight_supported w K width) hone
      let Q := RelativeBound.ofZeroDerivative
        ((spatialCertificate hw0 hw1 K width (N width+N width) (by omega) hhead).mul
          (certificate_mono hone (by omega) Cone))
        (zero_after (small := N width) (block := N width+s) hr (by omega) hi hj)
      simpa only [Nat.zero_add, Nat.one_mul, Nat.two_mul, halfOpenAction] using
        (P.mul Q).changeCap (QPoly.q_add_zero_eqv _)
  | r+1 => by
      let B := halfOpenAction_outputRelative hw0 hw1 K width hK s hs hi hj r
      let L := relative_lift (N width) B
      have hsize : (r+2)*(N width)+N width = (r+1+2)*(N width) := by
        simp only [Nat.succ_mul] <;> omega
      have hcoord : 4*(N width)+(4*((r+1)*(N width)+s)+i) =
          4*((r+1+1)*(N width)+s)+i := by simp only [Nat.succ_mul] <;> omega
      have hcoordj : 4*(N width)+(4*((r+1)*(N width)+s)+j) =
          4*((r+1+1)*(N width)+s)+j := by simp only [Nat.succ_mul] <;> omega
      rw [hsize, hcoord, hcoordj] at L
      have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
      have hp := supported_polyMul (kineticWeight_supported w K width)
        (support_mono (spatialWeight_supported w K width) (by omega))
      let P := RelativeBound.ofZeroDerivative
        (certificate_mono (large := (r+1+2)*(N width)) hp
          (by simp only [Nat.succ_mul] <;> omega)
          (stepWeightCertificate hw0 hw1 K width hhead))
        (zero_after (block := (r+1+1)*(N width)+s) hp
          (by simp only [Nat.succ_mul] <;> omega) hi hj)
      change RelativeBound _ _ _
        (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width)
          (liftBoundary (N width) (halfOpenAction (N width)
            (kineticWeight w K width) (spatialWeight w K width) (r+1))))) _
      exact RelativeBound.ofCoeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm
        ((P.mul L).changeCap (QPoly.q_zero_add_eqv _))

/-- Full original terminal-weighted window, retaining every spatial factor.
Its output derivative costs exactly one selected last kinetic link. -/
def blockWindowWeight_outputRelative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound ((r+2)*(N width))
      (4*((r+1)*(N width)+s)+i) (4*((r+1)*(N width)+s)+j)
      (blockWindowWeight w K width n (r+1)) (relativeCap w 32) := by
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let G := RelativeBound.ofZeroDerivative
    (certificate_mono (large := (r+2)*(N width)) (terminalMessage_supported w K width n)
      (by simp only [Nat.succ_mul] <;> omega)
      (terminalMessage_certificate hw0 hw1 K width hhead n))
    (zero_after (block := (r+1)*(N width)+s) (terminalMessage_supported w K width n)
      (by simp only [Nat.succ_mul] <;> omega) hi hj)
  exact (G.mul (halfOpenAction_outputRelative hw0 hw1 K width hK s hs hi hj r)).changeCap
    (QPoly.q_zero_add_eqv _)

private theorem integral_pin (w : Q') (K width n t : Nat) (f : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)) (polyMul (blockWindowWeight w K width n t) f))
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) f)) := by
  unfold blockWindowWeight
  refine (partialHaarHeads_congr (t*(N width))
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun
        | 0 => terminalMessage w K width n
        | 1 => halfOpenAction (N width) (kineticWeight w K width)
            (spatialWeight w K width) t
        | _ => f))).trans ?_
  exact windowMessage_iterate (N width) (kineticWeight w K width)
    (spatialWeight w K width) t (terminalMessage w K width n) f

private theorem mass_pin (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))
      (originalBlockTransfer w K width t (terminalMessage w K width n)) :=
  (partialHaarHeads_congr (t*(N width))
    ((RatPolyCoeffEqv.mul_one (terminalMessage w K width n)).symm.mul_right
      (halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t))).trans
    (windowMessage_one (N width) (kineticWeight w K width)
      (spatialWeight w K width) t (terminalMessage w K width n))

private theorem terminal_block (w : Q') (K width n t : Nat) :
    originalBlockTransfer w K width t (terminalMessage w K width n) =
      terminalMessage w K width (n+t) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) n t polyOne).symm

/-- Constructed division-free covariance bound for the ACTUAL original
terminal block and its original-depth rational center.  The conditional
noise is retained literally, not replaced by a surviving response norm. -/
def original_block_scoreVariance_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (f : RatPoly) (c : Q') (hf : SupportedQuaternionBlocks (N width) f) :
    let A := terminalMessage w K width (n+(r+1))
    let psi := shifted f c
    let b := originalBlockTransfer w K width (r+1)
      (polyMul (terminalMessage w K width n) psi)
    let S := polyAdd (polyMul A (angularDerivative (4*s+i) (4*s+j) b))
      (polyNeg (polyMul b (angularDerivative (4*s+i) (4*s+j) A)))
    Certificate (N width) (polyAdd
      (polyMul (cap (relativeCap w 32*relativeCap w 32))
        (polyMul (polyMul A A)
          (blockNoise w K width (r+1) (terminalMessage w K width n) psi)))
      (polyNeg (polyMul S S))) := by
  dsimp only
  let heads := (r+1)*(N width)
  let W := blockWindowWeight w K width n (r+1)
  let psi := shifted f c
  let d := angularDerivative (4*heads+(4*s+i)) (4*heads+(4*s+j)) W
  have hsn := activeBlocks_lt width s hs
  have hsize : (r+2)*(N width) = N width+heads := by
    dsimp only [heads]
    simp only [Nat.succ_mul] <;> omega
  have hsmall : N width ≤ heads := by
    dsimp only [heads]
    simp only [Nat.succ_mul] <;> omega
  have hW : SupportedQuaternionBlocks (N width+heads) W := by
    have ha := halfOpenAction_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) (r+1)
    exact hsize ▸ supported_polyMul
      (support_mono (terminalMessage_supported w K width n)
        (by simp only [Nat.succ_mul] <;> omega)) ha
  have hd : SupportedQuaternionBlocks (N width+heads) d :=
    angularDerivative_supported_at (by omega) (by omega) hW
  have hpsi := shifted_supported hf c
  have hpsiHead : SupportedQuaternionBlocks heads psi := support_mono hpsi hsmall
  have hpsiAll : SupportedQuaternionBlocks (N width+heads) psi :=
    support_mono hpsi (by omega)
  let P := blockWindowWeight_outputRelative hw0 hw1 K width hK n r s hs hi hj
  have hci : 4*((r+1)*(N width)+s)+i = 4*heads+(4*s+i) := by
    dsimp only [heads]
    omega
  have hcj : 4*((r+1)*(N width)+s)+j = 4*heads+(4*s+j) := by
    dsimp only [heads]
    omega
  rw [hsize, hci, hcj] at P
  have C := conditionalCovarianceSquare_certificate (N width) heads W d psi
    (relativeCap w 32) hW hd hpsiAll P.lower P.upper
  have hA0 := mass_pin w K width n (r+1)
  have hA : RatPolyCoeffEqv (partialHaarHeads heads W)
      (terminalMessage w K width (n+(r+1))) := by
    rw [terminal_block w K width n (r+1)] at hA0
    exact hA0
  have hb := integral_pin w K width n (r+1) psi
  have hH := integral_pin w K width n (r+1) (polyMul psi psi)
  have hnoise : RatPolyCoeffEqv (determinant heads W psi)
      (blockNoise w K width (r+1) (terminalMessage w K width n) psi) :=
    ((mass_pin w K width n (r+1)).mul hH).add
      (RatPolyCoeffEqv.neg (hb.mul hb))
  have hz : RatPolyCoeffEqv
      (angularDerivative (4*heads+(4*s+i)) (4*heads+(4*s+j)) psi) polyZero := by
    have hh := zero_after (block := heads+s) hpsiHead (by omega) hi hj
    simpa only [Nat.mul_add, Nat.add_assoc] using hh
  have hdpsi : RatPolyCoeffEqv
      (angularDerivative (4*heads+(4*s+i)) (4*heads+(4*s+j)) (polyMul W psi))
      (polyMul d psi) :=
    (angularDerivative_mul _ _ W psi).trans
      (((RatPolyCoeffEqv.refl _).add
        ((hz.mul_left W).trans (RatPolyCoeffEqv.mul_zero_right W))).trans
          (RatPolyCoeffEqv.add_zero _))
  have hdb : RatPolyCoeffEqv (partialHaarHeads heads (polyMul d psi))
      (angularDerivative (4*s+i) (4*s+j)
        (originalBlockTransfer w K width (r+1)
          (polyMul (terminalMessage w K width n) psi))) :=
    ((angularDerivative_partialHaarHeads heads (4*s+i) (4*s+j) (polyMul W psi)).trans
      (partialHaarHeads_congr heads hdpsi)).symm.trans
        (angularDerivative_congr _ _ hb)
  have hda : RatPolyCoeffEqv (partialHaarHeads heads d)
      (angularDerivative (4*s+i) (4*s+j) (terminalMessage w K width (n+(r+1)))) :=
    (angularDerivative_partialHaarHeads heads (4*s+i) (4*s+j) W).symm.trans
      (angularDerivative_congr _ _ hA)
  have hscore := (hA.mul hdb).add (RatPolyCoeffEqv.neg (hb.mul hda))
  exact Certificate.ofCoeff
    ((((hA.mul hA).mul hnoise).mul_left _).add
      (RatPolyCoeffEqv.neg (hscore.mul hscore))).symm C

/-- The literal padded square retains its chronological OWN center at n;
neither this center nor the full window action is changed at the output. -/
def paddedSquare_own_block_scoreVariance_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r scale s : Nat)
    (hwidth : 2^scale < width) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let c := middleRatio hw0 hw1 K width
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) (n+1) n f
    let A := terminalMessage w K width (n+(r+1))
    let psi := shifted f c
    let b := originalBlockTransfer w K width (r+1)
      (polyMul (terminalMessage w K width n) psi)
    let S := polyAdd (polyMul A (angularDerivative (4*s+i) (4*s+j) b))
      (polyNeg (polyMul b (angularDerivative (4*s+i) (4*s+j) A)))
    Certificate (N width) (polyAdd
      (polyMul (cap (relativeCap w 32*relativeCap w 32))
        (polyMul (polyMul A A)
          (blockNoise w K width (r+1) (terminalMessage w K width n) psi)))
      (polyNeg (polyMul S S))) :=
  original_block_scoreVariance_certificate hw0 hw1 K width hK n r s hs hi hj _ _
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)

#print axioms halfOpenAction_outputRelative
#print axioms blockWindowWeight_outputRelative
#print axioms original_block_scoreVariance_certificate
#print axioms paddedSquare_own_block_scoreVariance_certificate

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreVariance
