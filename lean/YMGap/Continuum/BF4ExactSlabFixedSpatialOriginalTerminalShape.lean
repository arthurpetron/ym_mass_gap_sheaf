/-
# Quantitative terminal shape on the ORIGINAL source

Return the retained cube estimate through the checked all-insertion original
terminal pin. Both the original Haar mass and the original centered Haar
square are preserved. At fixed nome 1/16 and width two, every guarded finite
cutoff and every terminal depth has relative centered-square cap (1/80000)^2.

The normalization here is explicitly the bare Haar mass H(g_n), not the
weighted mass ell(g_n), odd partition, completed vacuum or OS norm. No such
quantities are identified with each other. The useful tested-source and OWN
mean comparisons still have to be made with their actual weights.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage cubeTerminal

/-- Bare Haar amplitudes agree; neither is declared an interacting partition. -/
theorem original_haar_mass_pin (K n : Nat) :
    H (terminalMessage smallNome K 2 n) ≈ H (cubeTerminal K n) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (blocks := N)
    (RatPolyCoeffEqv.one_mul (terminalMessage smallNome K 2 n))))
    (Q'.eqv_trans _ _ _ (terminalMessage_cubeTerminal K n polyOne (supported_one N))
      (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul (cubeTerminal K n))))

theorem original_haar_mass_positive (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (0 : Q') < H (terminalMessage smallNome K 2 n) :=
  HeatKernelRGStep.lt_of_lt_of_le (cubeTerminal_mass_positive K hK hhead n)
    (Q'.ge_of_eqv (original_haar_mass_pin K n))

private theorem centered_source_pin (K n : Nat) :
    SupportedHaarEqv N
      (polyAdd (terminalMessage smallNome K 2 n)
        (polyNeg (cap (H (terminalMessage smallNome K 2 n)))))
      (polyAdd (cubeTerminal K n) (polyNeg (cap (H (cubeTerminal K n))))) := by
  exact (terminalMessage_cubeTerminal K n).add
    (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.smul_coefficient
        (original_haar_mass_pin K n) polyOne))))

private theorem centered_supported {p : RatPoly}
    (hp : SupportedQuaternionBlocks N p) (a : Q') :
    SupportedQuaternionBlocks N (polyAdd p (polyNeg (cap a))) := by
  apply supported_add hp
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact (SquareBound.constant N a).support s hs

/-- The actual original relative centered Haar square is uniformly small
in BOTH terminal depth and guarded finite representation cutoff. -/
theorem original_terminal_variance_bound (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    H (polyMul
      (polyAdd (terminalMessage smallNome K 2 n)
        (polyNeg (cap (H (terminalMessage smallNome K 2 n)))))
      (polyAdd (terminalMessage smallNome K 2 n)
        (polyNeg (cap (H (terminalMessage smallNome K 2 n)))))) ≤
      (terminalRadius*terminalRadius)*
        (H (terminalMessage smallNome K 2 n)*H (terminalMessage smallNome K 2 n)) := by
  have ho := centered_supported (terminalMessage_supported smallNome K 2 n)
    (H (terminalMessage smallNome K 2 n))
  have hc := centered_supported (cubeTerminal_supported K n) (H (cubeTerminal K n))
  have hp := (centered_source_pin K n).mul (centered_source_pin K n) ho hc
  have he := haar_of_carrier (carrier_of_supported
    (supported_polyMul ho ho) (supported_polyMul hc hc) hp)
  have hm := original_haar_mass_pin K n
  have hs := Q'.mul_eqv_congr_left (terminalRadius*terminalRadius) _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
      (Q'.mul_eqv_congr_left _ _ _ hm))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (cubeTerminal_variance_bound K hK hhead n) (Q'.ge_of_eqv hs))

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape.original_haar_mass_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape.original_haar_mass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape.original_terminal_variance_bound
