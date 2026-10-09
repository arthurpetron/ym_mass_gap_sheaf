/-
# Exclusive and outside slots of a mixed angular gradient

An angular derivative at s preserves every raw monomial's degree at b != s,
including zero-coefficient derivative terms. Thus Gamma_s(p,q) has degree
pd+qd at b. A supported exclusive degree-one slot has Casimir three on the
SAME arbitrary-insertion quaternion Haar carrier; a degree-zero outside slot
has Casimir zero already coefficientwise. Shared, signed spectator factors
are unrestricted. The existing degree-one Casimir supplies its head-swap
transport; no further coordinate wrapper or analytic hypothesis is added.

The full physical overlapping-face join and its signed weighted payment
remain separate. These local identities are not MAIN retention or a gap.
-/

import YMGap.Continuum.QuaternionHaarMixedAngularDerivative
import YMGap.Continuum.SU2QuaternionBlockLinearCasimir
import YMGap.Continuum.SU2QuaternionActiveCasimirProduct
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionBlockLinearCasimir
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.QuaternionHaarMixedAngularDerivative (blockAngularDerivative_supported)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

private theorem exponentAt_lower_other
    (coordinate target : Nat) (hne : coordinate ≠ target) :
    ∀ monomial : List Nat,
      exponentAt (lowerExponentAt coordinate monomial) target =
        exponentAt monomial target
  | [] => by cases coordinate <;> cases target <;> rfl
  | _ :: rest => by
      cases coordinate with
      | zero =>
          cases target with
          | zero => exact False.elim (hne rfl)
          | succ _ => rfl
      | succ coordinate =>
          cases target with
          | zero => rfl
          | succ target =>
              simp only [lowerExponentAt, exponentAt]
              exact exponentAt_lower_other coordinate target
                (fun h => hne (congrArg Nat.succ h)) rest

private theorem lower_preserves_degree (b coordinate : Nat)
    (houtside : ∀ k, k < 4 → coordinate ≠ 4*b+k) (m : List Nat) :
    quaternionBlockDegree (lowerExponentAt coordinate m) b = quaternionBlockDegree m b := by
  have h0 : coordinate ≠ 4*b := by simpa only [Nat.add_zero] using houtside 0 (by decide)
  simp only [quaternionBlockDegree,
    exponentAt_lower_other coordinate (4*b) h0,
    exponentAt_lower_other coordinate (4*b+1) (houtside 1 (by decide)),
    exponentAt_lower_other coordinate (4*b+2) (houtside 2 (by decide)),
    exponentAt_lower_other coordinate (4*b+3) (houtside 3 (by decide))]

private theorem derivative_degree_other {b coordinate degree : Nat}
    (houtside : ∀ k, k < 4 → coordinate ≠ 4*b+k) {p : RatPoly}
    (hp : HasQuaternionBlockDegree b degree p) :
    HasQuaternionBlockDegree b degree (ratDerivative coordinate p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact (lower_preserves_degree b coordinate houtside source.1).trans (hp source hs)

private theorem angular_degree_other {b s degree : Nat} (hne : b ≠ s)
    (i j : Nat) (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : HasQuaternionBlockDegree b degree p) :
    HasQuaternionBlockDegree b degree (blockAngularDerivative s i j p) := by
  have hout_i : ∀ k, k < 4 → 4*s+i ≠ 4*b+k := by
    intro k hk he
    exact hne (by omega)
  have hout_j : ∀ k, k < 4 → 4*s+j ≠ 4*b+k := by
    intro k hk he
    exact hne (by omega)
  have hvar_i : HasQuaternionBlockDegree b 0 (polyVar (4*s+i)) := by
    simpa only [if_neg hne] using hasQuaternionBlockDegree_coordinate s i b hi
  have hvar_j : HasQuaternionBlockDegree b 0 (polyVar (4*s+j)) := by
    simpa only [if_neg hne] using hasQuaternionBlockDegree_coordinate s j b hj
  have hl := hvar_i.mul (derivative_degree_other hout_j hp)
  have hr := hvar_j.mul (derivative_degree_other hout_i hp)
  have hl' : HasQuaternionBlockDegree b degree
      (polyMul (polyVar (4*s+i)) (ratDerivative (4*s+j) p)) := by
    simpa only [Nat.zero_add] using hl
  have hr' : HasQuaternionBlockDegree b degree
      (polyMul (polyVar (4*s+j)) (ratDerivative (4*s+i) p)) := by
    simpa only [Nat.zero_add] using hr
  exact hl'.add (hr'.smul (-1))

/-- Literal mixed six-plane gradients add the two degrees at any distinct
slot. This includes zero coefficients and needs no Haar or support premise. -/
theorem blockGamma_degree_of_ne {b s pd qd : Nat} (hne : b ≠ s)
    (p q : RatPoly) (hp : HasQuaternionBlockDegree b pd p)
    (hq : HasQuaternionBlockDegree b qd q) :
    HasQuaternionBlockDegree b (pd+qd) (blockGamma s p q) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) :
      HasQuaternionBlockDegree b (pd+qd)
        (polyMul (blockAngularDerivative s i j p) (blockAngularDerivative s i j q)) :=
    (angular_degree_other hne i j hi hj hp).mul (angular_degree_other hne i j hi hj hq)
  exact (h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add (h 2 3 (by decide) (by decide))))))

/-- The actual mixed gradient remains in the same finite quaternion carrier. -/
theorem blockGamma_supported {blocks s : Nat} (hs : s < blocks)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (blockGamma s p q) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) :
      SupportedQuaternionBlocks blocks
        (polyMul (blockAngularDerivative s i j p) (blockAngularDerivative s i j q)) :=
    supported_polyMul (blockAngularDerivative_supported hs i j hi hj hp)
      (blockAngularDerivative_supported hs i j hi hj hq)
  exact polyAdd_supported (h 0 1 (by decide) (by decide))
    (polyAdd_supported (h 0 2 (by decide) (by decide))
      (polyAdd_supported (h 0 3 (by decide) (by decide))
        (polyAdd_supported (h 1 2 (by decide) (by decide))
          (polyAdd_supported (h 1 3 (by decide) (by decide)) (h 2 3 (by decide) (by decide))))))

private theorem singletonC (b : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial [b] p) (polyNeg (blockAngularLaplacian b p)) := by
  change RatPolyCoeffEqv (polyAdd (polyNeg (blockAngularLaplacian b p)) polyZero) _
  exact RatPolyCoeffEqv.add_zero _

/-- An exclusive degree-one slot contributes exactly three to the mixed
gradient Casimir, retaining every original Haar insertion. -/
theorem blockGamma_exclusive_linear_casimir {blocks b s : Nat}
    (hb : b < blocks) (hs : s < blocks) (hne : b ≠ s)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hdp : HasQuaternionBlockDegree b 1 p) (hdq : HasQuaternionBlockDegree b 0 q) :
    HaarCarrierEqv blocks (activeCasimirPolynomial [b] (blockGamma s p q))
      (polySmul 3 (blockGamma s p q)) := by
  have hd : HasQuaternionBlockDegree b 1 (blockGamma s p q) := by
    simpa only [Nat.add_zero] using blockGamma_degree_of_ne hne p q hdp hdq
  have hc := blockCasimir_linear hb (blockGamma s p q) (blockGamma_supported hs p q hp hq) hd
  exact (RatPolyCoeffEqv.haarCarrier (singletonC b _)).trans
    ((HaarCarrierEqv.neg hc).trans (RatPolyCoeffEqv.haarCarrier
      ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) (-3) _).trans
        (RatPolyCoeffEqv.smul_coefficient
          (by decide : Q'.eqv ((-1 : Q')*(-3)) 3) _)))))

/-- An outside degree-zero slot contributes zero already coefficientwise.
Hence the result applies on every Haar carrier, without an in-range premise. -/
theorem blockGamma_outside_casimir_zero {b s : Nat} (hne : b ≠ s)
    (p q : RatPoly) (hdp : HasQuaternionBlockDegree b 0 p)
    (hdq : HasQuaternionBlockDegree b 0 q) :
    RatPolyCoeffEqv (activeCasimirPolynomial [b] (blockGamma s p q)) polyZero := by
  have hd : HasQuaternionBlockDegree b 0 (blockGamma s p q) :=
    blockGamma_degree_of_ne hne p q hdp hdq
  exact (singletonC b _).trans
    (RatPolyCoeffEqv.neg (blockAngularLaplacian_independent_zero b _ (degree_zero_independent hd)))

end YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir

#print axioms YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir.blockGamma_degree_of_ne
#print axioms YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir.blockGamma_supported
#print axioms YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir.blockGamma_exclusive_linear_casimir
#print axioms YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir.blockGamma_outside_casimir_zero
