/-
# Conditional bridge from the current Wilson carrier to canonical OS/GNS data

The current spatial-union completion has a genuine `RC`-valued form, a
completed physical-time map, and the checked normalized-excitation resolvent
floor.  The canonical `WilsonTimeTranslationPin` instead lives on a
`GNSData` completion.  These carriers are not definitionally the same, so the
missing passage must be named rather than silently coerced.

This file supplies the smallest backward-facing bridge datum that consumes the
current result: a map preserving the completed form and zero, intertwining the
two-step current time map with the selected canonical transfer, and recording
vacuum orthogonality of the transported probe.  From it we construct a
canonical probe package whose squared norm has the same explicit `1/4` floor.
No bridge inhabitant is fabricated here; the structure is the exact remaining
OS/GNS carrier obligation for this route.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
import YMGap.Continuum.WilsonGNSTransferUnderdetermination

namespace YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner_symm)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
  (mixed_correlator_sq_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (completed_twoStep_form_gap)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
  (center_fixed_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonGNS

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "R" => resolvent nome_pos nome_lt_one hsmall hd hs

/-! ## The exact conditional carrier handoff -/

/-- The static part of the carrier handoff: a map from the completed current
carrier to the selected canonical completion, preserving zero and the full
completed pairing.  This certificate contains no dynamics. -/
structure CurrentCarrierFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  map : V → GNSCompletionSpace W.toGNSData
  map_zero : map Z = embedV W.toGNSData W.toGNSData.zero
  form_preserving : ∀ x y,
    W.toGNSData.cinnerCompl (map x) (map y) = B x y

/-- The dynamic part of the carrier handoff.  It is deliberately separate from
the static form certificate so a producer can establish time intertwining
without silently supplying a form identification. -/
structure CurrentCarrierTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentCarrierFormCertificate P) : Type 2 where
  twoStep_intertwines : ∀ x,
    F.map (T 2 x) = P.op.T (P.op.T (F.map x))

/-- The probe-specific vacuum-complement certificate.  It is the smallest
nontriviality-side input needed by the current resolvent consumer and is kept
independent of the all-vector dynamic estimate. -/
structure CurrentCarrierProbeCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentCarrierFormCertificate P) : Type 2 where
  probe_vacuum_orthogonal :
    W.toGNSData.cinnerCompl (F.map (R unitExcitation)) P.op.vacuum = RCzero

/-- The named OS/GNS carrier bridge still required by the current Wilson route.

`map` is not assumed to be an identification: it is supplied together with
the form equation that makes the current `RC`-valued estimate usable on the
canonical completion.  `twoStep_intertwines` is the dynamic part needed before
the current same-object estimate can feed a canonical transfer argument. -/
structure CurrentCarrierBridge
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  /-- Map from the current spatial-union completion to the canonical completion. -/
  map : V → GNSCompletionSpace W.toGNSData
  /-- The current zero is sent to the canonical GNS zero. -/
  map_zero : map Z = embedV W.toGNSData W.toGNSData.zero
  /-- The completed pairings are preserved exactly in `RC`. -/
  form_preserving : ∀ x y,
    W.toGNSData.cinnerCompl (map x) (map y) = B x y
  /-- The current physical two-step map intertwines with the selected transfer. -/
  twoStep_intertwines : ∀ x,
    map (T 2 x) = P.op.T (P.op.T (map x))
  /-- The transported normalized resolvent probe is in the canonical vacuum complement. -/
  probe_vacuum_orthogonal :
    W.toGNSData.cinnerCompl (map (R unitExcitation)) P.op.vacuum = RCzero

/-- Reassemble the full bridge from its three independently producible
certificates.  This is a structural constructor only: it does not create any
of the certificates or weaken their carrier, form, or dynamics fields. -/
def CurrentCarrierBridge.ofCertificates
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (F : CurrentCarrierFormCertificate P)
    (D : CurrentCarrierTwoStepCertificate P F)
    (O : CurrentCarrierProbeCertificate P F) : CurrentCarrierBridge P where
  map := F.map
  map_zero := F.map_zero
  form_preserving := F.form_preserving
  twoStep_intertwines := D.twoStep_intertwines
  probe_vacuum_orthogonal := O.probe_vacuum_orthogonal

/-- The canonical probe data produced by a supplied carrier bridge. -/
structure CanonicalProbeData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (J : CurrentCarrierBridge P) : Type 2 where
  vector : GNSCompletionSpace W.toGNSData
  vacuum_orthogonal :
    W.toGNSData.cinnerCompl vector P.op.vacuum = RCzero
  norm_floor :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (W.toGNSData.cinnerCompl vector vector)
  twoStep_intertwines :
    J.map (T 2 (R unitExcitation)) = P.op.T (P.op.T vector)

namespace CurrentCarrierBridge

variable
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}

/-- The checked current-carrier floor transported to the canonical completion. -/
theorem canonical_resolvent_norm_floor (J : CurrentCarrierBridge P) :
  RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (W.toGNSData.cinnerCompl (J.map (R unitExcitation))
        (J.map (R unitExcitation))) := by
  rw [J.form_preserving]
  exact
    YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_norm_floor

/-- The bridge exposes a canonical non-vacuum-complement probe package. -/
def canonicalProbe (J : CurrentCarrierBridge P) : CanonicalProbeData P J where
  vector := J.map (R unitExcitation)
  vacuum_orthogonal := J.probe_vacuum_orthogonal
  norm_floor := J.canonical_resolvent_norm_floor
  twoStep_intertwines := J.twoStep_intertwines (R unitExcitation)

theorem canonicalProbe_vector (J : CurrentCarrierBridge P) :
    (J.canonicalProbe).vector = J.map (R unitExcitation) := rfl

theorem canonicalProbe_vacuum_orthogonal (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl (J.canonicalProbe).vector P.op.vacuum = RCzero :=
  J.canonicalProbe.vacuum_orthogonal

theorem canonicalProbe_norm_floor (J : CurrentCarrierBridge P) :
    RCle (Quotient.mk crealSetoid
      (ofQ' (Q'.mkPos 1 4 (by decide))))
      (W.toGNSData.cinnerCompl (J.canonicalProbe).vector
        (J.canonicalProbe).vector) :=
  J.canonicalProbe.norm_floor

private theorem positive_constant_not_le_zero_local (q : Q')
    (hq : (0 : Q') < q) :
    ¬ RCle (Quotient.mk crealSetoid (ofQ' q)) RCzero := by
  intro h
  obtain ⟨N, hN⟩ := h (HalfPow.half * q) (ExpNeg.half_mul_pos q hq)
  have hbad := hN N (Nat.le_refl N)
  change q ≤ 0 + HalfPow.half * q at hbad
  rw [Q'.zero_add'] at hbad
  have hprod : q * 1 ≤ q * HalfPow.half := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hbad (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact (by decide : ¬ (1 : Q') ≤ HalfPow.half)
    (Q'.le_of_mul_le_mul_left hprod hq)

/-- The checked current-carrier floor makes the transported canonical probe
genuinely nonzero.  This is a consequence of the supplied bridge, not a new
OS/GNS identification or a replacement observable. -/
theorem canonicalProbe_ne_zero (J : CurrentCarrierBridge P) :
    (J.canonicalProbe).vector ≠
      embedV W.toGNSData W.toGNSData.zero := by
  intro hzero
  have hfloor := J.canonicalProbe_norm_floor
  rw [hzero, W.toGNSData.cinnerCompl_embedZero_left] at hfloor
  exact positive_constant_not_le_zero_local
    (Q'.mkPos 1 4 (by decide)) (by decide) hfloor

/-! ## The first canonical same-object moment consumer -/

/-- The canonical two-step matrix coefficient of the transported resolvent
probe is exactly the current-carrier coefficient.  The equality uses only
the bridge's form preservation and its explicit two-step intertwining field.
-/
theorem canonicalProbe_twoStepCorrelation_eq_current
    (J : CurrentCarrierBridge P) :
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.canonicalProbe.vector)))
        (J.canonicalProbe.vector) =
      B (T 2 (R unitExcitation)) (R unitExcitation) := by
  change W.toGNSData.cinnerCompl
      (P.op.T (P.op.T (J.map (R unitExcitation))))
      (J.map (R unitExcitation)) =
    B (T 2 (R unitExcitation)) (R unitExcitation)
  rw [← J.twoStep_intertwines (R unitExcitation)]
  exact J.form_preserving (T 2 (R unitExcitation)) (R unitExcitation)

/-- The transported canonical probe inherits the fixed-spacing current
same-object squared decay at the two-step lag.  This is conditional only on
the named carrier bridge; it does not construct the OS/GNS bridge or change
the observable. -/
theorem canonicalProbe_twoStep_sq_decay
    (J : CurrentCarrierBridge P) :
    CReal.RCle
      (CReal.RCmul
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (J.canonicalProbe.vector)))
          (J.canonicalProbe.vector))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (J.canonicalProbe.vector)))
          (J.canonicalProbe.vector)))
      (CReal.RCmul
        (W.toGNSData.cinnerCompl
          (J.canonicalProbe.vector) (J.canonicalProbe.vector))
        (CReal.RCscale
          (twoStepRate nome hd ^ 2)
          (W.toGNSData.cinnerCompl
            (J.canonicalProbe.vector) (J.canonicalProbe.vector)))) := by
  have hcurrent := mixed_correlator_sq_decay
    nome_pos nome_lt_one hsmall hd hs
    (R unitExcitation) (R unitExcitation)
    ((center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mp
      (unitExcitation_resolvent_centered)) 2
  rw [canonicalProbe_twoStepCorrelation_eq_current J]
  rw [canonicalProbe_vector J]
  rw [J.form_preserving (R unitExcitation) (R unitExcitation)]
  have hcorr :
      B (T 2 (R unitExcitation)) (R unitExcitation) =
        B (R unitExcitation) (T 2 (R unitExcitation)) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 (R unitExcitation)) (R unitExcitation)
  have hsq :
      CReal.RCmul
          (B (T 2 (R unitExcitation)) (R unitExcitation))
          (B (T 2 (R unitExcitation)) (R unitExcitation)) =
        CReal.RCmul
          (B (R unitExcitation) (T 2 (R unitExcitation)))
          (B (R unitExcitation) (T 2 (R unitExcitation))) :=
    congrArg (fun z : CReal.RC => CReal.RCmul z z) hcorr
  rw [hsq]
  exact hcurrent

/-! ## The strict form-gap consumer -/

/-- The transported canonical resolvent probe inherits the current carrier's
strict two-step form bound.  The orientation change is only the completed
pairing symmetry; the rate is still the literal fixed-spacing `twoStepRate`.
-/
theorem canonicalProbe_twoStep_form_bound
    (J : CurrentCarrierBridge P) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.canonicalProbe.vector)))
        (J.canonicalProbe.vector))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl
          (J.canonicalProbe.vector) (J.canonicalProbe.vector))) := by
  have horth : B (R unitExcitation) U = RCzero :=
    (center_fixed_iff nome_pos nome_lt_one hsmall hd hs _).mp
      unitExcitation_resolvent_centered
  have hgap := completed_twoStep_form_gap
    nome_pos nome_lt_one hsmall hd hs (R unitExcitation) horth
  have hsym :
      B (T 2 (R unitExcitation)) (R unitExcitation) =
        B (R unitExcitation) (T 2 (R unitExcitation)) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 (R unitExcitation)) (R unitExcitation)
  rw [canonicalProbe_twoStepCorrelation_eq_current J]
  rw [canonicalProbe_vector J]
  rw [J.form_preserving (R unitExcitation) (R unitExcitation)]
  rw [hsym]
  exact hgap

end CurrentCarrierBridge

end YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.ofCertificates
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonical_resolvent_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStepCorrelation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStep_sq_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStep_form_bound
