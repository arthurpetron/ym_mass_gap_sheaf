/-
# Exporting a finite refresh packet to the stable RG interface

This module connects the intuitionistic BF4 finite-kernel theorem to the
existing RG-I7 structural consumer.  For a square finite refresh kernel,
admissible states are explicit nonnegative normalized weights.  The
pushforward preserves those witnesses and contracts their exact `l¹`
distance by `1 - epsilon`, so it supplies a literal
`UniformContractionCertificate`.

No Yang--Mills refresh packet is constructed here.  The result only proves
that such a packet, once obtained from the grouped physical Haar map, has
the exact type required by the stable-dynamics layer.
-/

import YMGap.Continuum.ConstructiveRefreshContraction
import YMGap.RG.StableDynamics

namespace YMGap.RG.ConstructiveRefreshStableDynamics

open YMGap.Constructive
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.ConstructiveRefreshContraction.FiniteRefreshCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.RG.StableDynamics

local infix:50 " ≈ " => Q'.eqv

/-- Proof-relevant membership in the finite probability simplex. -/
structure AdmissibleFiniteWeight
    {State : Type} (states : List State) (weight : State → Q') : Type where
  nonnegative :
    ∀ state, state ∈ states → (0 : Q') ≤ weight state
  mass_one :
    finiteMass states weight ≈ 1

private theorem refreshPushforward_nonnegative
    {State : Type} {states : List State}
    (certificate : FiniteRefreshCertificate states states)
    (weight : State → Q')
    (hweight : AdmissibleFiniteWeight states weight)
    (target : State) (htarget : target ∈ states) :
    (0 : Q') ≤
      finiteKernelPushforward
        states weight certificate.kernel target := by
  unfold finiteKernelPushforward
  apply listQSum_nonnegative_on
  intro source hsource
  exact Q'.mul_nonneg _ _
    (hweight.nonnegative source hsource)
    (certificate.kernel_nonnegative
      source hsource target htarget)

/-- A square finite refresh certificate is already a stable-interface
uniform contraction certificate.  The scale index is ignored because this
constructor packages one fixed grouped physical step. -/
def toUniformContractionCertificate
    {State : Type} {states : List State}
    (certificate : FiniteRefreshCertificate states states) :
    UniformContractionCertificate (State → Q') where
  distance := finiteL1Distance states
  Admissible := AdmissibleFiniteWeight states
  step := fun _ weight =>
    finiteKernelPushforward states weight certificate.kernel
  q := certificate.rate
  qNonnegative := certificate.rate_nonnegative
  qBelowOne := certificate.rate_lt_one
  distanceNonnegative := finiteL1Distance_nonnegative states
  stepAdmissible := by
    intro _ weight hweight
    exact
      { nonnegative := fun target htarget =>
          refreshPushforward_nonnegative
            certificate weight hweight target htarget
        mass_one := Q'.eqv_trans _ _ _
          (finiteKernelPushforward_total
            states states weight certificate.kernel
            certificate.kernel_row_normalized)
          hweight.mass_one }
  contracts := by
    intro _ left right hleft hright
    exact certificate.l1_contraction left right
      (Q'.eqv_trans _ _ _
        hleft.mass_one (Q'.eqv_symm hright.mass_one))

theorem exported_rate_eq
    {State : Type} {states : List State}
    (certificate : FiniteRefreshCertificate states states) :
    (toUniformContractionCertificate certificate).q =
      certificate.rate :=
  rfl

theorem exported_step_eq
    {State : Type} {states : List State}
    (certificate : FiniteRefreshCertificate states states)
    (scale : Nat) (weight : State → Q') :
    (toUniformContractionCertificate certificate).step scale weight =
      finiteKernelPushforward
        states weight certificate.kernel :=
  rfl

#print axioms toUniformContractionCertificate
#print axioms exported_rate_eq
#print axioms exported_step_eq

end YMGap.RG.ConstructiveRefreshStableDynamics
