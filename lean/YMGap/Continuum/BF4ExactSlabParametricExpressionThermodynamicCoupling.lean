/-
# Guarded two-nome comparison of ORIGINAL thermodynamic expression limits

The existing finite-volume localized coupling estimate compares two original
Wilson laws at distinct guarded nomes, uniformly in all outer padding.  The
parametric thermodynamic-limit producer therefore transports that same bound
to the two infinite-volume expectation limits.

This is an actual cross-nome statement for the same finite plaquette
expression and the same original action family.  Both nomes still lie in the
strong-coupling window; no AF trajectory, continuum modulus, block-spin
identity, or Hamiltonian mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit
import YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound

namespace YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabLocalizedCouplingBound
open YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v)
  (hvW : v ≤ W) (hW1 : W < (1 : Q'))

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1

/-- The volume-uniform finite coupling estimate survives both independently
constructed thermodynamic limits.  The localization margin remains explicit,
so later scale work can balance its two decaying boundary terms against the
finite inner-window coupling cost. -/
theorem meanLimit_coupling_bound
    (hsmallu : heatRatio u ≤ HalfPow.half)
    (hsmallv : heatRatio v ≤ HalfPow.half)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1)
    (hsu : entropyRate 625 (adjustedCoreRate u hdu) < 1)
    (hsv : entropyRate 625 (adjustedCoreRate v hdv) < 1)
    (hrateu : entropyRate 625 (adjustedCoreRate u hdu) ≤ HalfPow.half)
    (hratev : entropyRate 625 (adjustedCoreRate v hdv) ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    leEv
      (CReal.abs
        (CReal.sub
          (meanLimit hv0 hv1 hsmallv hdv hsv hratev e)
          (meanLimit hu0 hu1 hsmallu hdu hsu hrateu e)))
      (ofQ' (localizedCap W u v hdu hdv hsu hsv e margin)) := by
  have hvConverges :
      ConvergesTo
        (fun padding => meanSequence hv0 hv1 e (margin + padding))
        (meanLimit hv0 hv1 hsmallv hdv hsv hratev e) := by
    intro epsilon he
    obtain ⟨N, hN⟩ :=
      meanLimit_converges hv0 hv1 hsmallv hdv hsv hratev e epsilon he
    exact ⟨N, fun padding hpadding =>
      hN (margin + padding) (Nat.le_trans hpadding (Nat.le_add_left _ _))⟩
  have huConverges :
      ConvergesTo
        (fun padding => meanSequence hu0 hu1 e (margin + padding))
        (meanLimit hu0 hu1 hsmallu hdu hsu hrateu e) := by
    intro epsilon he
    obtain ⟨N, hN⟩ :=
      meanLimit_converges hu0 hu1 hsmallu hdu hsu hrateu e epsilon he
    exact ⟨N, fun padding hpadding =>
      hN (margin + padding) (Nat.le_trans hpadding (Nat.le_add_left _ _))⟩
  have hsub := convergesTo_add hvConverges
    (TrigAddCReal.convergesTo_neg huConverges)
  exact leEv_of_convergesTo_le (convergesTo_abs hsub) (convergesTo_const _)
    (fun padding => localized_coupling_bound hu0 huv hvW hW1
      hsmallu hsmallv hdu hdv hsu hsv e margin padding)

/-- A common localization margin obtained by taking the larger of the two
explicit thermodynamic volume moduli. -/
def couplingMargin {u v : Q'}
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1)
    (hsu : entropyRate 625 (adjustedCoreRate u hdu) < 1)
    (hsv : entropyRate 625 (adjustedCoreRate v hdv) < 1)
    {base : Nat} (e : PlaquetteExpression base) (epsilon : Q') : Nat :=
  max (volumeModulus hdu hsu e epsilon) (volumeModulus hdv hsv e epsilon)

/-- At any margin paying both explicit volume moduli, the two thermodynamic
boundary errors cost at most `epsilon` each.  The only remaining middle term
is the literal finite inner-window coupling cost. -/
theorem meanLimit_coupling_bound_of_moduli
    (hsmallu : heatRatio u ≤ HalfPow.half)
    (hsmallv : heatRatio v ≤ HalfPow.half)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1)
    (hsu : entropyRate 625 (adjustedCoreRate u hdu) < 1)
    (hsv : entropyRate 625 (adjustedCoreRate v hdv) < 1)
    (hrateu : entropyRate 625 (adjustedCoreRate u hdu) ≤ HalfPow.half)
    (hratev : entropyRate 625 (adjustedCoreRate v hdv) ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hmu : volumeModulus hdu hsu e epsilon ≤ margin)
    (hmv : volumeModulus hdv hsv e epsilon ≤ margin) :
    leEv
      (CReal.abs
        (CReal.sub
          (meanLimit hv0 hv1 hsmallv hdv hsv hratev e)
          (meanLimit hu0 hu1 hsmallu hdu hsu hrateu e)))
      (ofQ' ((epsilon + windowCouplingCap W u v e margin) + epsilon)) := by
  apply leEv_trans
    (meanLimit_coupling_bound hu0 huv hvW hW1 hsmallu hsmallv hdu hdv
      hsu hsv hrateu hratev e margin)
  apply leEv_le_ofQ'_of_approx_le
  intro _
  unfold localizedCap boundaryCap
  exact Q'.add_le_add
    (Q'.add_le_add
      (coefficient_small hv0 hdv hsv hratev e epsilon he margin hmv)
      (Q'.le_refl' _))
    (coefficient_small hu0 hdu hsu hrateu e epsilon he margin hmu)

/-- Fully explicit guarded two-nome thermodynamic comparison.  The selected
margin is computed from the two volume moduli; later scale work only has to
control the displayed finite-window coupling term. -/
theorem meanLimit_coupling_bound_explicit
    (hsmallu : heatRatio u ≤ HalfPow.half)
    (hsmallv : heatRatio v ≤ HalfPow.half)
    (hdu : heatRemainderBound u < 1) (hdv : heatRemainderBound v < 1)
    (hsu : entropyRate 625 (adjustedCoreRate u hdu) < 1)
    (hsv : entropyRate 625 (adjustedCoreRate v hdv) < 1)
    (hrateu : entropyRate 625 (adjustedCoreRate u hdu) ≤ HalfPow.half)
    (hratev : entropyRate 625 (adjustedCoreRate v hdv) ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    leEv
      (CReal.abs
        (CReal.sub
          (meanLimit hv0 hv1 hsmallv hdv hsv hratev e)
          (meanLimit hu0 hu1 hsmallu hdu hsu hrateu e)))
      (ofQ' ((epsilon + windowCouplingCap W u v e
        (couplingMargin hdu hdv hsu hsv e epsilon)) + epsilon)) :=
  meanLimit_coupling_bound_of_moduli hu0 huv hvW hW1 hsmallu hsmallv
    hdu hdv hsu hsv hrateu hratev e epsilon he
    (couplingMargin hdu hdv hsu hsv e epsilon)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling

#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling.meanLimit_coupling_bound
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling.couplingMargin
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling.meanLimit_coupling_bound_of_moduli
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicCoupling.meanLimit_coupling_bound_explicit
