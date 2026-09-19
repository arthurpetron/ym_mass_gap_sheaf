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
  (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonGNS

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "R" => resolvent nome_pos nome_lt_one hsmall hd hs

/-! ## The exact conditional carrier handoff -/

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

end CurrentCarrierBridge

end YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonical_resolvent_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_norm_floor
