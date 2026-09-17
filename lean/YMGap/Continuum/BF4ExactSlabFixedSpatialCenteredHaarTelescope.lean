/-
# Explicit Haar pieces of the original centered temporal source

The density is exactly nu=V*(T^n1)*(T^(n+1)1). With its own partition
Z=H[nu], the polynomial Phi=Z*f-H[nu*f] has H[nu*Phi]=0 without any
centering assumption on f. Ordinary conditional Haar projections construct
explicit pieces of this source, with their exact conditional zeros.

Their sum equals the full source under supported Haar testing. The raw
coefficient telescope retains its full-projection endpoint and its harmless
zero-padding aliases. No weighted inverse, approximation modulus, signed
cost estimate, or uniform spectral bound is asserted here.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockTelescope
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive oddMass_compactPartition)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit (compactPartition)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarBlockTelescope
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks weightedMass

/-- The mass of the same original odd-edge marginal used by the dual energy. -/
def mass (w : Q') (K width n : Nat) : Q' :=
  quaternionHaar (N width) (marginalWeight w K width n)

/-- Partition-cleared centering is a polynomial, not a rational observable. -/
def centeredObservable (w : Q') (K width n : Nat) (f : RatPoly) : RatPoly :=
  polyAdd (polySmul (mass w K width n) f)
    (polyNeg (cap (quaternionHaar (N width) (polyMul (marginalWeight w K width n) f))))

/-- Every original action and terminal factor remains in the source. -/
def source (w : Q') (K width n : Nat) (f : RatPoly) : RatPoly :=
  polyMul (marginalWeight w K width n) (centeredObservable w K width n f)

/-- Directly indexed conditional-Haar pieces of the constructed source. -/
def piece (w : Q') (K width n i : Nat) (f : RatPoly) : RatPoly :=
  term i (source w K width n f)

def pieceSum (w : Q') (K width n : Nat) (f : RatPoly) : RatPoly :=
  polySum ((List.range (N width)).map (fun i => piece w K width n i f))

theorem mass_oddMass (w : Q') (K width n : Nat) :
    mass w K width n ≈ oddMass w K width n := by
  unfold mass marginalWeight oddMass weightedMass
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
    (fun | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
         | _ => terminalMessage w K width (n+1)))

/-- The exact original partition has 2*n+1 temporal transitions. -/
theorem mass_compactPartition (w : Q') (K width n : Nat) :
    mass w K width n ≈ compactPartition w K width (2*n+1) :=
  Q'.eqv_trans _ _ _ (mass_oddMass w K width n) (oddMass_compactPartition w K width n)

theorem mass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    (0 : Q') < mass w K width n :=
  HeatKernelRGStep.lt_of_lt_of_le (oddMass_positive hw0 hw1 K width hK n)
    (Q'.ge_of_eqv (mass_oddMass w K width n))

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1)) * weight [] + 0 ≈ ((-c)*1) * weight [] + 0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

/-- Centering is proved for every input polynomial, not supplied as a hypothesis. -/
theorem source_mean_zero (w : Q') (K width n : Nat) (f : RatPoly) :
    quaternionHaar (N width) (source w K width n f) ≈ 0 := by
  let nu := marginalWeight w K width n
  let Z := mass w K width n
  let B := quaternionHaar (N width) (polyMul nu f)
  have he : RatPolyCoeffEqv (source w K width n f)
      (polyAdd (polySmul Z (polyMul nu f)) (polySmul (-B) nu)) :=
    (RatPolyCoeffEqv.mul_add_right nu _ _).trans
      ((RatPolyCoeffEqv.polyMul_smul_right Z nu f).add
        (((RatPolyCoeffEqv.refl nu).mul (cap_neg B)).trans
          ((RatPolyCoeffEqv.mul_comm nu _).trans (cap_mul_left (-B) nu))))
  have hlinear : quaternionHaar (N width) (source w K width n f) ≈ Z*B + (-B)*Z :=
    Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
        (Q'.add_eqv_congr' (quaternionHaar_polySmul (N width) Z _)
          (quaternionHaar_polySmul (N width) (-B) nu)))
  exact Q'.eqv_trans _ _ _ hlinear
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 1)) (.var 0)))
      (.const 0) (by decide) (fun | 0 => Z | _ => B))

private theorem smul_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem centeredObservable_supported (w : Q') (K width n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (centeredObservable w K width n f) := by
  apply supported_add (smul_supported hf _)
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact smul_supported (supported_one (N width)) _ s hs

theorem source_supported (w : Q') (K width n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (source w K width n f) :=
  supported_polyMul (marginalWeight_supported w K width n)
    (centeredObservable_supported w K width n hf)

theorem piece_supported (w : Q') (K width n i : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (piece w K width n i f) :=
  term_supported i (source_supported w K width n hf)

/-- Each piece is exactly centered in its own original coordinate. -/
theorem piece_centered (w : Q') (K width n i : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (project i (piece w K width n i f)) polyZero :=
  project_term_zero i (source w K width n f)

theorem pieceSum_supported (w : Q') (K width n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (pieceSum w K width n f) :=
  telescope_supported (N width) (source_supported w K width n hf)

/-- Raw coefficient telescoping keeps the full-projection endpoint explicit. -/
theorem pieceSum_coeff (w : Q') (K width n : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (pieceSum w K width n f)
      (polyAdd (source w K width n f)
        (polyNeg (partialProjection (N width) (source w K width n f)))) :=
  telescope_coeff (N width) (source w K width n f)

/-- The actual centered source is the sum under every supported Haar insertion. -/
theorem pieceSum_source (w : Q') (K width n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedHaarEqv (N width) (pieceSum w K width n f) (source w K width n f) :=
  centered_telescope (N width) (source w K width n f)
    (source_supported w K width n hf) (source_mean_zero w K width n f)

#print axioms mass_oddMass
#print axioms mass_compactPartition
#print axioms mass_positive
#print axioms source_mean_zero
#print axioms centeredObservable_supported
#print axioms source_supported
#print axioms piece_supported
#print axioms piece_centered
#print axioms pieceSum_supported
#print axioms pieceSum_coeff
#print axioms pieceSum_source

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
