/-
# Computed relative comparison of actual positive terminal messages

The original transfer sandwich a*ell(v) <= T v <= b*ell(v) constructs a
bracket between T v and T z, with exact endpoints (a/b)*R and (b/a)*R,
where R=ell(v)/ell(z). Both masses are the actual V-weighted masses.
The reverse relative-floor certificate supplies the upper endpoint after
positive scaling; the reciprocal cancellations are proved explicitly.

For terminal messages, support, certificates and strict mass positivity
are all supplied by existing theorems. After s further actual steps, the
bracket compares u_(s+1+r) with u_(s+1+t), keeps a positive lower endpoint,
and has relative width at most comparisonKappa*q^s. The computed kappa is
the deliberately coarser (b/a)^2, not the sharper (b/a)^2-1. It depends on
nome and spatial width, but not on late cutoff or either terminal length.
No division by q, growing-partition floor, stationary vector or physical
OS identification is used. This supplies left-window boundary comparison.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- The actual cap/floor ratio b/a, with its proved positive denominator. -/
def comparisonStretch {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : Q' :=
  kineticCap w width * Q'.recipPos (kineticFloor w width) (kineticFloor_positive hw0 hw1 width)

theorem comparisonStretch_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < comparisonStretch hw0 hw1 width :=
  Q'.mul_pos (kineticCap_positive hw0 hw1 width)
    (Q'.recipPos_pos _ (kineticFloor_positive hw0 hw1 width))

/-- Exact cancellation against the original floor/cap mixing fraction. -/
theorem comparisonStretch_fraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : comparisonStretch hw0 hw1 width * mixFraction hw0 hw1 width ≈ 1 := by
  let ra := Q'.recipPos (kineticFloor w width) (kineticFloor_positive hw0 hw1 width)
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
    (fun | 0 => kineticCap w width | 1 => ra | _ => mixFraction hw0 hw1 width)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ ra (mixFraction_mul_cap hw0 hw1 width))
    (Q'.mul_recipPos_eqv _ (kineticFloor_positive hw0 hw1 width))

/-- A coarse but cutoff-independent relative-width coefficient (b/a)^2. -/
def comparisonKappa {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : Q' :=
  comparisonStretch hw0 hw1 width * comparisonStretch hw0 hw1 width

theorem comparisonKappa_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < comparisonKappa hw0 hw1 width :=
  Q'.mul_pos (comparisonStretch_positive hw0 hw1 width) (comparisonStretch_positive hw0 hw1 width)

theorem comparisonKappa_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') ≤ comparisonKappa hw0 hw1 width :=
  Q'.le_of_lt (comparisonKappa_positive hw0 hw1 width)

/-- The explicit relative-error budget after s common transfer steps. -/
def comparisonEta {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width s : Nat) : Q' := comparisonKappa hw0 hw1 width * mixRate hw0 hw1 width ^ s

theorem comparisonEta_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width s : Nat) : (0 : Q') ≤ comparisonEta hw0 hw1 width s :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (comparisonKappa_positive hw0 hw1 width))
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) s)

private theorem mass_ratio_positive (w : Q') (K width : Nat) (v z : RatPoly)
    (hv : (0 : Q') < weightedMass w K width v) (hz : (0 : Q') < weightedMass w K width z) :
    (0 : Q') < massRatio w K width v z hz := Q'.mul_pos hv (Q'.recipPos_pos _ hz)

private theorem reverse_gain_cancel {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (v z : RatPoly)
    (hv : (0 : Q') < weightedMass w K width v) (hz : (0 : Q') < weightedMass w K width z) :
    (comparisonStretch hw0 hw1 width * massRatio w K width v z hz) *
      gain hw0 hw1 K width v z hv ≈ 1 := by
  let rv := Q'.recipPos (weightedMass w K width v) hv
  let rz := Q'.recipPos (weightedMass w K width z) hz
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 2) (.var 5)))
      (.mul (.var 1) (.mul (.var 3) (.var 4))))
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5)))) (by decide)
    (fun
      | 0 => comparisonStretch hw0 hw1 width
      | 1 => mixFraction hw0 hw1 width
      | 2 => weightedMass w K width v
      | 3 => weightedMass w K width z
      | 4 => rv
      | _ => rz)) ?_
  exact Q'.eqv_trans _ _ _
    (mul_congr (comparisonStretch_fraction hw0 hw1 width)
      (mul_congr (Q'.mul_recipPos_eqv _ hv) (Q'.mul_recipPos_eqv _ hz)))
    (by decide : (1 : Q') * (1 * 1) ≈ 1)

private def reciprocal_upper {blocks : Nat} {f g : RatPoly} {u c : Q'}
    (hu : (0 : Q') ≤ u) (he : u*c ≈ 1)
    (H : Certificate blocks (polyAdd g (polySmul (-c) f))) :
    Certificate blocks (polyAdd (polySmul u g) (polySmul (-1) f)) := by
  have hn : u * (-c) ≈ -1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv u c) (Q'.neg_eqv_congr _ _ he)
  have hc : RatPolyCoeffEqv (polySmul u (polyAdd g (polySmul (-c) f)))
      (polyAdd (polySmul u g) (polySmul (-1) f)) :=
    (RatPolyCoeffEqv.smul_add u g _).trans
      ((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.smul_assoc u (-c) f).trans
        (RatPolyCoeffEqv.smul_coefficient hn f)))
  exact Certificate.ofCoeff hc.symm (Certificate.smul u hu H)

section Initial

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) {v z : RatPoly}
  (hv : SupportedQuaternionBlocks (N width) v) (hz : SupportedQuaternionBlocks (N width) z)
  (V : Certificate (N width) v) (Z : Certificate (N width) z)
  (hvmass : (0 : Q') < weightedMass w K width v)
  (hzmass : (0 : Q') < weightedMass w K width z)

/-- The exact sandwich comparison, constructed from both original messages. -/
def initialComparison : Bracket width (transferStep w K width v) (transferStep w K width z) where
  lower := gain hw0 hw1 K width z v hzmass
  upper := comparisonStretch hw0 hw1 width * massRatio w K width v z hzmass
  lowerCertificate := relativeFloorCertificate hw0 hw1 K width hK hz hv Z V hzmass
  upperCertificate := reciprocal_upper
    (Q'.le_of_lt (Q'.mul_pos (comparisonStretch_positive hw0 hw1 width)
      (mass_ratio_positive w K width v z hvmass hzmass)))
    (reverse_gain_cancel hw0 hw1 K width v z hvmass hzmass)
    (relativeFloorCertificate hw0 hw1 K width hK hv hz V Z hvmass)

theorem initialComparison_lower :
    (initialComparison hw0 hw1 K width hK hv hz V Z hvmass hzmass).lower =
      mixFraction hw0 hw1 width * massRatio w K width v z hzmass := rfl

theorem initialComparison_lower_positive :
    (0 : Q') < (initialComparison hw0 hw1 K width hK hv hz V Z hvmass hzmass).lower :=
  Q'.mul_pos (mixFraction_positive hw0 hw1 width) (mass_ratio_positive w K width v z hvmass hzmass)

/-- The initial upper endpoint is exactly kappa times its positive lower. -/
theorem initialComparison_upper_pin :
    (initialComparison hw0 hw1 K width hK hv hz V Z hvmass hzmass).upper ≈
      comparisonKappa hw0 hw1 width *
        (initialComparison hw0 hw1 K width hK hv hz V Z hvmass hzmass).lower := by
  apply Q'.eqv_symm
  let b := comparisonStretch hw0 hw1 width
  let e := mixFraction hw0 hw1 width
  let R := massRatio w K width v z hzmass
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
    (.mul (.var 0) (.mul (.mul (.var 0) (.var 1)) (.var 2))) (by decide)
    (fun | 0 => b | 1 => e | _ => R)) ?_
  exact Q'.mul_eqv_congr_left b _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ R (comparisonStretch_fraction hw0 hw1 width))
      (Q'.one_mul_eqv R))

end Initial

/-- Initial comparison for two actual terminal messages; every mass premise
of the generic producer is discharged, including zero terminal length. -/
def terminalInitialComparison {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (r t : Nat) :
    Bracket width (transferStep w K width (terminalMessage w K width r))
      (transferStep w K width (terminalMessage w K width t)) :=
  initialComparison hw0 hw1 K width hK
    (terminalMessage_supported w K width r) (terminalMessage_supported w K width t)
    (terminalMessage_certificate hw0 hw1 K width hK r)
    (terminalMessage_certificate hw0 hw1 K width hK t)
    (terminalMessage_mass_positive hw0 hw1 K width hK r)
    (terminalMessage_mass_positive hw0 hw1 K width hK t)

private def terminalIteration {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) :
    Bracket width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) s
        (transferStep w K width (terminalMessage w K width r)))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) s
        (transferStep w K width (terminalMessage w K width t))) :=
  iterateBracket hw0 hw1 K width hK s
    (transferStep_supported w K width (terminalMessage_supported w K width r))
    (transferStep_supported w K width (terminalMessage_supported w K width t))
    (transferStep_certificate hw0 hw1 K width hK (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK t))
    (weightedMass_transfer_positive hw0 hw1 K width hK (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK t)
      (terminalMessage_mass_positive hw0 hw1 K width hK t))
    (terminalInitialComparison hw0 hw1 K width hK r t)

private theorem terminal_iteration_pin (w : Q') (K width s r : Nat) :
    iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) s
      (transferStep w K width (terminalMessage w K width r)) =
        terminalMessage w K width (s+1+r) := by
  have h := iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) r (s+1) polyOne
  rw [Nat.add_comm r (s+1)] at h
  exact h.symm

/-- The computed bracket on the actual two late terminal messages. Explicit
fields keep its scalar endpoints unchanged by the exact index rewrites. -/
def terminalComparison {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) :
    Bracket width (terminalMessage w K width (s+1+r)) (terminalMessage w K width (s+1+t)) where
  lower := (terminalIteration hw0 hw1 K width hK s r t).lower
  upper := (terminalIteration hw0 hw1 K width hK s r t).upper
  lowerCertificate := by
    rw [← terminal_iteration_pin w K width s r, ← terminal_iteration_pin w K width s t]
    exact (terminalIteration hw0 hw1 K width hK s r t).lowerCertificate
  upperCertificate := by
    rw [← terminal_iteration_pin w K width s r, ← terminal_iteration_pin w K width s t]
    exact (terminalIteration hw0 hw1 K width hK s r t).upperCertificate

theorem terminalComparison_lower_ge_initial {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) :
    (terminalInitialComparison hw0 hw1 K width hK r t).lower ≤
      (terminalComparison hw0 hw1 K width hK s r t).lower := by
  exact (iterateBracket_nested hw0 hw1 K width hK 0 s (Nat.zero_le s)
    (transferStep_supported w K width (terminalMessage_supported w K width r))
    (transferStep_supported w K width (terminalMessage_supported w K width t))
    (transferStep_certificate hw0 hw1 K width hK (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK t))
    (weightedMass_transfer_positive hw0 hw1 K width hK (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK t)
      (terminalMessage_mass_positive hw0 hw1 K width hK t))
    (terminalInitialComparison hw0 hw1 K width hK r t)).1

theorem terminalComparison_lower_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) :
    (0 : Q') < (terminalComparison hw0 hw1 K width hK s r t).lower :=
  Q'.pos_of_lt_of_le
    (initialComparison_lower_positive hw0 hw1 K width hK
      (terminalMessage_supported w K width r) (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK r)
      (terminalMessage_certificate hw0 hw1 K width hK t)
      (terminalMessage_mass_positive hw0 hw1 K width hK r)
      (terminalMessage_mass_positive hw0 hw1 K width hK t))
    (terminalComparison_lower_ge_initial hw0 hw1 K width hK s r t)

/-- Exact absolute bracket width before the positive lower is compared. -/
theorem terminalComparison_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) :
    (terminalComparison hw0 hw1 K width hK s r t).upper +
      -(terminalComparison hw0 hw1 K width hK s r t).lower ≈
        mixRate hw0 hw1 width ^ s *
          ((terminalInitialComparison hw0 hw1 K width hK r t).upper +
            -(terminalInitialComparison hw0 hw1 K width hK r t).lower) :=
  iterateBracket_width hw0 hw1 K width hK s
    (transferStep_supported w K width (terminalMessage_supported w K width r))
    (transferStep_supported w K width (terminalMessage_supported w K width t))
    (transferStep_certificate hw0 hw1 K width hK (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK t))
    (weightedMass_transfer_positive hw0 hw1 K width hK (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK t)
      (terminalMessage_mass_positive hw0 hw1 K width hK t))
    (terminalInitialComparison hw0 hw1 K width hK r t)

private theorem relative_width (l u L d k q : Q')
    (hl : (0 : Q') ≤ l) (hk : (0 : Q') ≤ k) (hq : (0 : Q') ≤ q)
    (hL : l ≤ L) (hu : u ≈ k*l) (hd : d ≈ q*(u + -l)) : d ≤ (k*q)*L := by
  have hsub : u + -l ≤ u :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left u _ _ (show -l ≤ (0 : Q') by simpa only using Q'.neg_le_neg hl))
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv u))
  have he : q*u ≈ (k*q)*l :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ hu)
      (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
        (fun | 0 => q | 1 => k | _ => l))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hd)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ q hsub hq)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.mul_le_mul_of_nonneg_left _ _ (k*q) hL (Q'.mul_nonneg _ _ hk hq))))

/-- Relative width with a computed cutoff-independent coefficient. The
terminal mass ratio cancels from the coefficient; no reciprocal floor for
that mass, or division by the final lower endpoint or q, is used. -/
theorem terminalComparison_relative_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s r t : Nat) :
    (terminalComparison hw0 hw1 K width hK s r t).upper +
      -(terminalComparison hw0 hw1 K width hK s r t).lower ≤
        comparisonEta hw0 hw1 width s * (terminalComparison hw0 hw1 K width hK s r t).lower :=
  relative_width _ _ _ _ _ _
    (Q'.le_of_lt (initialComparison_lower_positive hw0 hw1 K width hK
      (terminalMessage_supported w K width r) (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK r)
      (terminalMessage_certificate hw0 hw1 K width hK t)
      (terminalMessage_mass_positive hw0 hw1 K width hK r)
      (terminalMessage_mass_positive hw0 hw1 K width hK t)))
    (Q'.le_of_lt (comparisonKappa_positive hw0 hw1 width))
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) s)
    (terminalComparison_lower_ge_initial hw0 hw1 K width hK s r t)
    (initialComparison_upper_pin hw0 hw1 K width hK
      (terminalMessage_supported w K width r) (terminalMessage_supported w K width t)
      (terminalMessage_certificate hw0 hw1 K width hK r)
      (terminalMessage_certificate hw0 hw1 K width hK t)
      (terminalMessage_mass_positive hw0 hw1 K width hK r)
      (terminalMessage_mass_positive hw0 hw1 K width hK t))
    (terminalComparison_width hw0 hw1 K width hK s r t)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonStretch
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonStretch_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonStretch_fraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonKappa
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonKappa_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonKappa_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonEta
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.comparisonEta_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.initialComparison
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.initialComparison_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.initialComparison_lower_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.initialComparison_upper_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.terminalInitialComparison
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.terminalComparison
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.terminalComparison_lower_ge_initial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.terminalComparison_lower_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.terminalComparison_width
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison.terminalComparison_relative_width
