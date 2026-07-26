/-
# A concrete BF4 bare heat / asymptotic-freedom instantiation

This module performs two exact constructions that were previously only
described in the BF4 notes.

1. It puts the normalized reciprocal AF trajectory

       tau_k = 1 / (k+2)

   on the genuine constructive heat and transmutation exponentials

       w_k = exp(-tau_k),        a_k = exp(-1/tau_k).

   The cubic AF remainder is inherited from the kernel-checked
   `AFCertificateModel.O4Model`, and the exact exponential spacing is proved
   to obey `a_k <= tau_k`.

2. It constructs an actual `BareAFDiagnostic.AFEnvelope` through the reduced
   Padé constructor with

       t(g) = 4 g^2,             a_envelope(g) = g^2,

   so the BF4 heat argument is exactly `t/4 = g^2`.  It then applies
   `BareAFImpliesLinearFloor` and exposes its positive constant and bound.

The rational `a_envelope` is a collapsed upper envelope for the exact
transmutation exponential, not an assertion that a four-dimensional
same-action block transform preserves a one-parameter heat-kernel action.
The latter operator-identification theorem is separate.

All proofs are constructive and axiom-gated.
-/

import YMGap.Continuum.AFCertificateModel
import YMGap.Continuum.BF4AFHeatSpacing

namespace YMGap.Continuum.BF4AFInstantiation

open YMGap.Constructive
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFCertificateModel
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4AFHeatSpacing

/-! ## 1. Exact exponential BF4 bare trajectory -/

/-- Normalized BF4 heat argument along the reciprocal AF trajectory. -/
def blockTau (k : Nat) : Q' := tauModel k

/-- The exact constructive BF4 heat weight `exp(-tau_k)`. -/
def blockHeatWeight (k : Nat) : CReal :=
  ExpNeg.expNeg (blockTau k) (Q'.le_of_lt (O4Model.τ_pos k))

/-- The inverse heat argument controlling dimensional transmutation. -/
def blockInverseTau (k : Nat) : Q' :=
  recip (blockTau k) (O4Model.τ_pos k)

/-- The exact constructive transmutation spacing `exp(-1/tau_k)`. -/
def blockExactSpacing (k : Nat) : CReal :=
  ExpNeg.expNeg (blockInverseTau k)
    (recip_nonneg (blockTau k) (O4Model.τ_pos k))

/-- A positive rational is represented exactly by the custom reciprocal's
denominator cast. -/
private theorem recip_den_cast {x : Q'} (hx : (0 : Q') < x) :
    ((recip x hx).den : Int) = x.num := by
  have hnum : (0 : Int) ≤ x.num :=
    Int.le_of_lt (num_pos_of_pos hx)
  have hdenNat : (recip x hx).den = x.num.toNat :=
    Q'.mkPos_den (x.den : Int) x.num.toNat (recip_den_pos x hx)
  rw [hdenNat]
  exact Int.toNat_of_nonneg hnum

/-- The reciprocal's positive numerator has the expected `toNat` cast. -/
private theorem recip_num_toNat_cast {x : Q'} (hx : (0 : Q') < x) :
    ((recip x hx).num.toNat : Int) = (x.den : Int) := by
  have hden : (0 : Int) ≤ (x.den : Int) := by
    exact Int.le_of_lt (by exact_mod_cast x.den_pos)
  show (((x.den : Int).toNat : Nat) : Int) = (x.den : Int)
  exact Int.toNat_of_nonneg hden

/-- The Padé upper bound at the reciprocal is itself bounded by the original
positive rational:

`1/(1+1/x) = x/(1+x) <= x`.
-/
theorem oneOver1p_recip_le_self (x : Q') (hx : (0 : Q') < x) :
    ExpUBInstance.oneOver1p (recip x hx) ≤ x := by
  show (ExpUBInstance.oneOver1p (recip x hx)).num * (x.den : Int)
      ≤ x.num * ((ExpUBInstance.oneOver1p (recip x hx)).den : Int)
  rw [ExpUBInstance.oneOver1p_num, ExpUBInstance.oneOver1p_den]
  rw [recip_den_cast hx]
  have hden :
      (((recip x hx).num.toNat + (recip x hx).den : Nat) : Int)
        = (x.den : Int) + x.num := by
    rw [Int.natCast_add, recip_num_toNat_cast hx, recip_den_cast hx]
  rw [hden]
  have hnum : (0 : Int) ≤ x.num := Int.le_of_lt (num_pos_of_pos hx)
  have hsq : (0 : Int) ≤ x.num * x.num := Int.mul_nonneg hnum hnum
  calc
    x.num * (x.den : Int)
        ≤ x.num * (x.den : Int) + x.num * x.num :=
      Int.le_add_of_nonneg_right hsq
    _ = x.num * ((x.den : Int) + x.num) := by
      rw [Int.mul_add]

/-- **Exact transmutation spacing bound.**
`exp(-1/x) <= x` for every positive rational `x`. -/
theorem expNeg_recip_le_self (x : Q') (hx : (0 : Q') < x) :
    CReal.leRat
      (ExpNeg.expNeg (recip x hx) (recip_nonneg x hx)) x :=
  CReal.leRat_mono
    (expNeg_le_oneOver1p (recip x hx) (recip_nonneg x hx))
    (oneOver1p_recip_le_self x hx)

/-- Along the exact BF4 bare trajectory, the exponential lattice spacing is
bounded by the heat argument at every block. -/
theorem blockExactSpacing_le_tau (k : Nat) :
    CReal.leRat (blockExactSpacing k) (blockTau k) :=
  expNeg_recip_le_self (blockTau k) (O4Model.τ_pos k)

/-- **Cubic AF remainder on the BF4 heat trajectory.**
The exact reciprocal trajectory satisfies

`|tau_(k+1) - (tau_k - tau_k^2)| <= tau_k^3`.
-/
theorem blockTau_cubic_remainder (k : Nat) :
    Q'.abs
      (blockTau (k + 1) -
        (blockTau k - 1 * (blockTau k * blockTau k)))
      ≤ 1 * (blockTau k * (blockTau k * blockTau k)) :=
  O4Model.recurrence k (Nat.zero_le k)

/-! ## 2. A concrete Padé `AFEnvelope` and the linear floor -/

/-- Exact rational heat time used by the BF4 envelope: `t(g)=4g^2`. -/
def envelopeTime (g : Q') : Q' := Q'.ofNat 4 * (g * g)

/-- Collapsed rational spacing upper envelope. -/
def envelopeSpacing (g : Q') : Q' := g * g

/-- Concrete reduced AF data.  Its heat argument is `t/4=g^2`; all scalar
fields are proved from the definitions. -/
def bf4PadeData : PadeEnvelopeData where
  α := Q'.ofNat 4
  ᾱ := Q'.ofNat 4
  C := 1
  Λ := 1
  g₁ := 1
  t := envelopeTime
  a := envelopeSpacing
  α_pos := by decide
  ᾱ_pos := by decide
  C_pos := by decide
  Λ_pos := by decide
  g₁_pos := by decide
  t_lower := by
    intro g _ _
    exact Q'.le_refl' _
  t_upper := by
    intro g _ _
    exact Q'.le_refl' _
  heat_window := by
    unfold quarter
    decide
  spacing_quad := by
    intro g _ _
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_one_eqv (g * g))
        (Q'.eqv_symm (Q'.one_mul_eqv (g * g))))

/-- The fully constructed rational AF envelope for the BF4 heat argument. -/
def bf4AFEnvelope : AFEnvelope :=
  padeAFEnvelope bf4PadeData

/-- Positivity of the squared coupling. -/
theorem couplingSquare_pos {g : Q'} (hg : (0 : Q') < g) :
    (0 : Q') < g * g :=
  Q'.mul_pos hg hg

/-- Exact one-loop transmutation spacing attached to a positive coupling:
`exp(-1/g^2)`. -/
def exactTransmutationSpacing (g : Q') (hg : (0 : Q') < g) : CReal :=
  ExpNeg.expNeg (recip (g * g) (couplingSquare_pos hg))
    (recip_nonneg (g * g) (couplingSquare_pos hg))

/-- The exact exponential spacing is below the rational spacing envelope
used by `bf4AFEnvelope`. -/
theorem exactTransmutationSpacing_le_envelope
    (g : Q') (hg : (0 : Q') < g) :
    CReal.leRat (exactTransmutationSpacing g hg)
      (bf4AFEnvelope.a g) := by
  exact expNeg_recip_le_self (g * g) (couplingSquare_pos hg)

/-- Exact BF4 heat weight attached to the envelope's heat argument. -/
def exactBF4HeatWeight
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ bf4AFEnvelope.g₁) : CReal :=
  ExpNeg.expNeg (heatArgument bf4PadeData g)
    (heatArgument_nonneg bf4PadeData g hg hgle)

/-- The rational weight in `bf4AFEnvelope` is a proved upper envelope for the
exact constructive BF4 heat weight. -/
theorem exactBF4HeatWeight_le_envelopeWeight
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ bf4AFEnvelope.g₁) :
    CReal.leRat (exactBF4HeatWeight g hg hgle)
      (bf4AFEnvelope.w g) :=
  physical_exp_le_padeWeight bf4PadeData g hg hgle

/-- The BF4 heat-time/spacing rate is positive for the concrete envelope. -/
theorem bf4_heatSpacingRate_pos :
    (0 : Q') < heatSpacingRate bf4AFEnvelope :=
  heatSpacingRate_pos bf4AFEnvelope

/-- The concrete BF4 envelope satisfies the required heat-time/spacing
comparison. -/
theorem bf4_heat_time_ge_rate_mul_spacing
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ bf4AFEnvelope.g₁) :
    heatSpacingRate bf4AFEnvelope * bf4AFEnvelope.a g
      ≤ quarter * bf4AFEnvelope.t g :=
  heat_time_ge_rate_mul_spacing bf4AFEnvelope g hg hgle

/-- **Application of the pre-existing theorem requested by BF4.**
This is the `Type`-level positive linear-floor witness obtained by applying
`BareAFImpliesLinearFloor` to the constructed envelope. -/
def bf4BareLinearFloor :
    Σ' c₀ : Q', (0 : Q') < c₀ ∧
      ∀ g : Q', (0 : Q') < g → g ≤ bf4AFEnvelope.g₁ →
        c₀ * (bf4AFEnvelope.a g * bf4AFEnvelope.Λ)
          ≤ 1 + (-(bf4AFEnvelope.w g)) :=
  BareAFImpliesLinearFloor bf4AFEnvelope

/-- The instantiated linear-floor constant is strictly positive. -/
theorem bf4BareLinearFloor_constant_pos :
    (0 : Q') < bf4BareLinearFloor.1 :=
  bf4BareLinearFloor.2.1

/-- The instantiated linear-floor inequality. -/
theorem bf4BareLinearFloor_bound
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ bf4AFEnvelope.g₁) :
    bf4BareLinearFloor.1 * (bf4AFEnvelope.a g * bf4AFEnvelope.Λ)
      ≤ 1 + (-(bf4AFEnvelope.w g)) :=
  bf4BareLinearFloor.2.2 g hg hgle

end YMGap.Continuum.BF4AFInstantiation

#print axioms YMGap.Continuum.BF4AFInstantiation.oneOver1p_recip_le_self
#print axioms YMGap.Continuum.BF4AFInstantiation.expNeg_recip_le_self
#print axioms YMGap.Continuum.BF4AFInstantiation.blockExactSpacing_le_tau
#print axioms YMGap.Continuum.BF4AFInstantiation.blockTau_cubic_remainder
#print axioms YMGap.Continuum.BF4AFInstantiation.bf4PadeData
#print axioms YMGap.Continuum.BF4AFInstantiation.bf4AFEnvelope
#print axioms YMGap.Continuum.BF4AFInstantiation.exactTransmutationSpacing_le_envelope
#print axioms YMGap.Continuum.BF4AFInstantiation.exactBF4HeatWeight_le_envelopeWeight
#print axioms YMGap.Continuum.BF4AFInstantiation.bf4_heat_time_ge_rate_mul_spacing
#print axioms YMGap.Continuum.BF4AFInstantiation.bf4BareLinearFloor
#print axioms YMGap.Continuum.BF4AFInstantiation.bf4BareLinearFloor_bound
