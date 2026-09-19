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
import YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
import YMGap.Continuum.WilsonGNSTransferUnderdetermination

namespace YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnion (zeroStage unitStage)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner_symm)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero fixed_orthogonal_eq_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
  (mixed_correlator_sq_decay)
open YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
  (evenOrbitResidual evenOrbitResidual_strict_form_bound)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
  (completed_eq_of_pairings completedInner_sub_right)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (completed_twoStep_form_gap)
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
  (center_fixed_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
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
local notation "S" => unionSeminorm nome_pos nome_lt_one hsmall hd hs

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
  /-- The current vacuum is sent to the selected canonical vacuum. -/
  vacuum_preserving : map U = P.op.vacuum
  form_preserving : ∀ x y,
    W.toGNSData.cinnerCompl (map x) (map y) = B x y

/-! A producer-facing refinement of the static certificate. The current
completion is presented by explicit CReal-Cauchy streams, so a genuine source
must first map those streams into canonical GNS Cauchy streams and prove both
null descent and the completed Gram identity. -/

structure CurrentCarrierCauchyFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  mapCauchy : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy →
    CauchyGNS W.toGNSData
  mapCauchy_null : ∀ {X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy},
    (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Close X Y →
    CauchyNull W.toGNSData (mapCauchy X) (mapCauchy Y)
  mapCauchy_pairing : ∀
    (X Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy),
    W.toGNSData.cinnerCompl
      (Quotient.mk (cauchySetoid W.toGNSData) (mapCauchy X))
      (Quotient.mk (cauchySetoid W.toGNSData) (mapCauchy Y)) =
      B (Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid X)
        (Quotient.mk
          (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid Y)
  mapCauchy_zero :
    Quotient.mk (cauchySetoid W.toGNSData)
        (mapCauchy ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) =
      embedV W.toGNSData W.toGNSData.zero
  mapCauchy_unit :
    Quotient.mk (cauchySetoid W.toGNSData)
        (mapCauchy ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum

def CurrentCarrierCauchyFormCertificate.toFormCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (C : CurrentCarrierCauchyFormCertificate P) :
    CurrentCarrierFormCertificate P where
  map := Quotient.lift
    (fun X => Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy X))
    (fun X Y h => by
      rcases h with ⟨hclose⟩
      exact Quotient.sound (C.mapCauchy_null (X := X) (Y := Y) hclose))
  map_zero := by
    change Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant zeroStage)) =
      embedV W.toGNSData W.toGNSData.zero
    exact C.mapCauchy_zero
  vacuum_preserving := by
    change Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((unionSeminorm nome_pos nome_lt_one hsmall hd hs).constant unitStage)) =
      P.op.vacuum
    exact C.mapCauchy_unit
  form_preserving := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro X Y
    exact C.mapCauchy_pairing X Y

/-! The dynamic stream-level obligation is separated from the static Gram
identity. It asks only for transport of the explicit current two-step stream
through the already supplied canonical stream map. -/

structure CurrentCarrierCauchyTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (C : CurrentCarrierCauchyFormCertificate P) : Type 2 where
  mapCauchy_twoStep : ∀ X : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy,
    Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((timeNonexpansive nome_pos nome_lt_one hsmall hd hs 2).mapCauchy X)) =
      P.op.T (P.op.T
        (Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy X)))

/-! The probe stream certificate keeps quotient representative choice explicit.
The completed resolvent is not destructed to obtain a representative; a
producer must supply the Cauchy stream and its class equation. -/

structure CurrentCarrierCauchyProbeCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (C : CurrentCarrierCauchyFormCertificate P) : Type 2 where
  probeCauchy : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy
  probeCauchy_class :
    Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
        probeCauchy = R unitExcitation
  probe_vacuum_orthogonal :
    W.toGNSData.cinnerCompl
      (Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy probeCauchy))
      P.op.vacuum = RCzero

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

def CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (C : CurrentCarrierCauchyFormCertificate P)
    (D : CurrentCarrierCauchyTwoStepCertificate P C) :
    CurrentCarrierTwoStepCertificate P C.toFormCertificate where
  twoStep_intertwines := by
    intro x
    refine Quotient.inductionOn x ?_
    intro X
    change Quotient.mk (cauchySetoid W.toGNSData)
        (C.mapCauchy
          ((timeNonexpansive nome_pos nome_lt_one hsmall hd hs 2).mapCauchy X)) =
      P.op.T (P.op.T
        (Quotient.mk (cauchySetoid W.toGNSData) (C.mapCauchy X)))
    exact D.mapCauchy_twoStep X

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

def CurrentCarrierCauchyProbeCertificate.toProbeCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (C : CurrentCarrierCauchyFormCertificate P)
    (O : CurrentCarrierCauchyProbeCertificate P C) :
    CurrentCarrierProbeCertificate P C.toFormCertificate where
  probe_vacuum_orthogonal := by
    rw [← O.probeCauchy_class]
    exact O.probe_vacuum_orthogonal

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
  /-- The current vacuum is sent to the selected canonical vacuum. -/
  vacuum_preserving : map U = P.op.vacuum
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
  vacuum_preserving := F.vacuum_preserving
  form_preserving := F.form_preserving
  twoStep_intertwines := D.twoStep_intertwines
  probe_vacuum_orthogonal := O.probe_vacuum_orthogonal

/-- Contract the three stream-level producer certificates into the named
completed-space bridge. This is only composition of checked quotient descents;
it does not construct any producer certificate. -/
def CurrentCarrierCauchyFormCertificate.toBridge
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (C : CurrentCarrierCauchyFormCertificate P)
    (D : CurrentCarrierCauchyTwoStepCertificate P C)
    (O : CurrentCarrierCauchyProbeCertificate P C) :
    CurrentCarrierBridge P :=
  CurrentCarrierBridge.ofCertificates P C.toFormCertificate
    (CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate C D)
    (CurrentCarrierCauchyProbeCertificate.toProbeCertificate C O)

/-- Exact form preservation makes the bridge map injective.  The proof uses the
separating completed current pairing, so injectivity is not an extra field and
does not require a representative choice or classical quotient reasoning. -/
theorem CurrentCarrierBridge.map_injective
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    (J : CurrentCarrierBridge P) {x y : V}
    (h : J.map x = J.map y) : x = y := by
  apply completed_eq_of_pairings nome_pos nome_lt_one hsmall hd hs x y
  intro z
  rw [← J.form_preserving x z, ← J.form_preserving y z]
  exact congrArg (fun u => W.toGNSData.cinnerCompl u (J.map z)) h

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

/-! ## The all-image vacuum-complement consumer -/

/-- A current vacuum-complement vector remains in the canonical vacuum
complement under a supplied bridge.  This is the first all-vector consequence
of the static vacuum identification; it is still restricted to the bridge
image and therefore does not assert canonical density. -/
theorem image_vacuum_orthogonal
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero) :
    W.toGNSData.cinnerCompl (J.map x) P.op.vacuum = RCzero := by
  rw [← J.vacuum_preserving, J.form_preserving x U]
  exact hx

/-- The canonical two-step same-object coefficient agrees exactly with the
current completed coefficient for every vector in the bridge image. -/
theorem image_twoStep_correlation_eq_current
    (J : CurrentCarrierBridge P) (x : V) :
    W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map x))) (J.map x) =
      B (T 2 x) x := by
  rw [← J.twoStep_intertwines x]
  exact J.form_preserving (T 2 x) x

/-- The current strict two-step form bound transports to every vector in the
image of a supplied bridge, once that vector is known to be orthogonal to the
current vacuum.  The remaining dense-range and completed-space steps are not
assumed here. -/
theorem image_twoStep_form_bound
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (J.map x))) (J.map x))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl (J.map x) (J.map x))) := by
  have hgap := completed_twoStep_form_gap
    nome_pos nome_lt_one hsmall hd hs x hx
  have hsym :
      B (T 2 x) x = B x (T 2 x) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs
      (T 2 x) x
  rw [← J.twoStep_intertwines x]
  rw [J.form_preserving (T 2 x) x]
  rw [J.form_preserving x x]
  rw [hsym]
  exact hgap

/-! The stronger same-carrier residual margin also transports through the
conditional bridge. This is still image-level: no density or canonical
completed-space coercivity is inferred. -/

theorem image_twoStep_defect_form_bound
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero) :
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl (J.map x) (J.map x)))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl (J.map x) (J.map x))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (J.map x))) (J.map x))) := by
  have hcurrent := evenOrbitResidual_strict_form_bound
    nome_pos nome_lt_one hsmall hd hs x hx
  unfold evenOrbitResidual at hcurrent
  rw [completedInner_sub_right] at hcurrent
  have hsym :
      B (T 2 x) x = B x (T 2 x) :=
    completedInner_symm nome_pos nome_lt_one hsmall hd hs (T 2 x) x
  rw [← J.twoStep_intertwines x]
  rw [J.form_preserving x x, J.form_preserving (T 2 x) x]
  rw [hsym]
  exact hcurrent

/-- A canonical two-step fixed vector cannot be a nonzero vector in the
bridge image.  Intertwining and the already-proved bridge injectivity pull the
fixed-point equation back to the current carrier, where the current strict
form gap kills every vacuum-complement fixed vector. -/
theorem image_twoStep_fixed_eq_zero
    (J : CurrentCarrierBridge P) {x : V}
    (hx : B x U = RCzero)
    (hfixed : P.op.T (P.op.T (J.map x)) = J.map x) :
    J.map x = embedV W.toGNSData W.toGNSData.zero := by
  have hmap : J.map (T 2 x) = J.map x := by
    rw [J.twoStep_intertwines x, hfixed]
  have hsource : T 2 x = x := J.map_injective hmap
  have hzero : x = Z :=
    fixed_orthogonal_eq_zero nome_pos nome_lt_one hsmall hd hs x hx hsource
  rw [hzero, J.map_zero]

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

/-! ## The completed canonical-range consumer

The image estimates above are conditional on a vector already known to come
from the current carrier. The next backward-facing obligation is therefore a
constructive section of the canonical completion through the current carrier.
The section is stated at the supplied Cauchy-stream level, so a future
producer must return representatives and a kernel-checked class equation
rather than invoking choice. When supplied, that class equation is itself an
exact surjectivity witness for the bridge map; no section inhabitant is
constructed here.
-/

/-- A constructive section of the canonical completion through a supplied
current-carrier bridge. This is an explicit producer interface, not an
inhabited assertion: no canonical preimage is selected here. -/
structure CanonicalRangeSectionCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    (J : CurrentCarrierBridge P) : Type 2 where
  preimage : CauchyGNS W.toGNSData ->
    (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy
  class_eq : ∀ X : CauchyGNS W.toGNSData,
    Quotient.mk (cauchySetoid W.toGNSData) X =
      J.map (Quotient.mk
        (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid
        (preimage X))

namespace CanonicalRangeSectionCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {J : CurrentCarrierBridge P}

def canonicalClass (X : CauchyGNS W.toGNSData) :
    GNSCompletionSpace W.toGNSData :=
  Quotient.mk (cauchySetoid W.toGNSData) X

def currentClass
    (Y : (unionSeminorm nome_pos nome_lt_one hsmall hd hs).Cauchy) : V :=
  Quotient.mk
    (unionSeminorm nome_pos nome_lt_one hsmall hd hs).completionSetoid Y

/-! A supplied section is stronger than a dense-range statement: because every
canonical completion point is represented by a `CauchyGNS`, its class equation
is an exact surjectivity witness for the bridge map.  We expose this only as a
conditional consumer; no section inhabitant is constructed here. -/

theorem map_surjective
    (D : CanonicalRangeSectionCertificate P J) :
    Function.Surjective J.map := by
  intro z
  refine Quotient.inductionOn z ?_
  intro X
  exact ⟨currentClass (D.preimage X), (D.class_eq X).symm⟩

theorem preimage_class_unique
    (D : CanonicalRangeSectionCertificate P J)
    {X Y : CauchyGNS W.toGNSData}
    (hXY : canonicalClass X = canonicalClass Y) :
    currentClass (D.preimage X) = currentClass (D.preimage Y) := by
  apply J.map_injective
  exact (D.class_eq X).symm.trans (hXY.trans (D.class_eq Y))

/-- Every canonical vector orthogonal to the selected vacuum inherits the
strict two-step form bound once the explicit range section is supplied. The
proof is an image rewrite: the section supplies the current preimage, while
`CurrentCarrierBridge.image_twoStep_form_bound` supplies the estimate. No
density, limit interchange, or spectral theorem is hidden in this consumer. -/
theorem twoStep_form_bound
    (D : CanonicalRangeSectionCertificate P J)
    (X : CauchyGNS W.toGNSData)
    (hx : W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum = RCzero) :
    RCle
      (W.toGNSData.cinnerCompl
        (P.op.T (P.op.T (canonicalClass X))) (canonicalClass X))
      (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl (canonicalClass X) (canonicalClass X))) := by
  let Y := D.preimage X
  let y := currentClass Y
  have hyclass : canonicalClass X = J.map y := by
    simpa only [canonicalClass, y, currentClass, Y] using (D.class_eq X)
  have hyorth : B y U = RCzero := by
    calc
      B y U = W.toGNSData.cinnerCompl (J.map y) (J.map U) :=
        (J.form_preserving y U).symm
      _ = W.toGNSData.cinnerCompl (J.map y) P.op.vacuum := by
        rw [J.vacuum_preserving]
      _ = W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum := by
        rw [hyclass]
      _ = RCzero := hx
  have himage := J.image_twoStep_form_bound hyorth
  rw [← hyclass] at himage
  exact himage

/-! The residual version is kept alongside the strict form version because it
is the form used by the current resolvent and by later inverse/range consumers.
-/

/-- The same explicit range section transports the `(1-q)` residual margin to
every canonical vacuum-complement vector. -/
theorem twoStep_defect_form_bound
    (D : CanonicalRangeSectionCertificate P J)
    (X : CauchyGNS W.toGNSData)
    (hx : W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum = RCzero) :
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl (canonicalClass X) (canonicalClass X)))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl (canonicalClass X) (canonicalClass X))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (canonicalClass X))) (canonicalClass X))) := by
  let Y := D.preimage X
  let y := currentClass Y
  have hyclass : canonicalClass X = J.map y := by
    simpa only [canonicalClass, y, currentClass, Y] using (D.class_eq X)
  have hyorth : B y U = RCzero := by
    calc
      B y U = W.toGNSData.cinnerCompl (J.map y) (J.map U) :=
        (J.form_preserving y U).symm
      _ = W.toGNSData.cinnerCompl (J.map y) P.op.vacuum := by
        rw [J.vacuum_preserving]
      _ = W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum := by
        rw [hyclass]
      _ = RCzero := hx
  have himage := J.image_twoStep_defect_form_bound hyorth
  rw [← hyclass] at himage
  exact himage

/-- A supplied canonical range section upgrades the image-level fixed-point
exclusion to the whole canonical completion: a vacuum-orthogonal canonical
two-step fixed vector is the canonical zero. -/
theorem twoStep_fixed_eq_zero
    (D : CanonicalRangeSectionCertificate P J)
    (X : CauchyGNS W.toGNSData)
    (hx : W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum = RCzero)
    (hfixed : P.op.T (P.op.T (canonicalClass X)) = canonicalClass X) :
    canonicalClass X = embedV W.toGNSData W.toGNSData.zero := by
  let Y := D.preimage X
  let y := currentClass Y
  have hyclass : canonicalClass X = J.map y := by
    simpa only [canonicalClass, y, currentClass, Y] using (D.class_eq X)
  have hyorth : B y U = RCzero := by
    calc
      B y U = W.toGNSData.cinnerCompl (J.map y) (J.map U) :=
        (J.form_preserving y U).symm
      _ = W.toGNSData.cinnerCompl (J.map y) P.op.vacuum := by
        rw [J.vacuum_preserving]
      _ = W.toGNSData.cinnerCompl (canonicalClass X) P.op.vacuum := by
        rw [hyclass]
      _ = RCzero := hx
  have hfixed_image : P.op.T (P.op.T (J.map y)) = J.map y := by
    rw [← hyclass]
    exact hfixed
  have hzero := J.image_twoStep_fixed_eq_zero hyorth hfixed_image
  rw [hyclass]
  exact hzero

end CanonicalRangeSectionCertificate

/-! ## Contracted conditional canonical gap datum -/

/-- The exact canonical completed-gap package produced by a supplied range
section. Its rate and all three operator consequences remain fixed-spacing
SU(2) data; the structure is a downstream interface, not an assertion that a
range section or a continuum limit has been constructed. -/
structure CanonicalCompletedGapCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) : Type 2 where
  rate_pos : (0 : Q') < twoStepRate nome hd
  rate_lt_one : twoStepRate nome hd < (1 : Q')
  form_bound : ∀ (X : CauchyGNS W.toGNSData),
    W.toGNSData.cinnerCompl
        (CanonicalRangeSectionCertificate.canonicalClass X) P.op.vacuum = RCzero →
    RCle
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (CanonicalRangeSectionCertificate.canonicalClass X)))
          (CanonicalRangeSectionCertificate.canonicalClass X))
        (CReal.RCmul
        (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (W.toGNSData.cinnerCompl
          (CanonicalRangeSectionCertificate.canonicalClass X)
          (CanonicalRangeSectionCertificate.canonicalClass X)))
  defect_form_bound : ∀ (X : CauchyGNS W.toGNSData),
    W.toGNSData.cinnerCompl
        (CanonicalRangeSectionCertificate.canonicalClass X) P.op.vacuum = RCzero →
    RCle
      (CReal.RCscale (1 - twoStepRate nome hd)
        (W.toGNSData.cinnerCompl
          (CanonicalRangeSectionCertificate.canonicalClass X)
          (CanonicalRangeSectionCertificate.canonicalClass X)))
      (CReal.RCsub
        (W.toGNSData.cinnerCompl
          (CanonicalRangeSectionCertificate.canonicalClass X)
          (CanonicalRangeSectionCertificate.canonicalClass X))
        (W.toGNSData.cinnerCompl
          (P.op.T (P.op.T (CanonicalRangeSectionCertificate.canonicalClass X)))
          (CanonicalRangeSectionCertificate.canonicalClass X)))
  fixed_eq_zero : ∀ (X : CauchyGNS W.toGNSData),
    W.toGNSData.cinnerCompl
        (CanonicalRangeSectionCertificate.canonicalClass X) P.op.vacuum = RCzero →
    P.op.T (P.op.T (CanonicalRangeSectionCertificate.canonicalClass X)) =
      CanonicalRangeSectionCertificate.canonicalClass X →
    CanonicalRangeSectionCertificate.canonicalClass X =
      embedV W.toGNSData W.toGNSData.zero

namespace CanonicalCompletedGapCertificate

variable
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {J : CurrentCarrierBridge P}

/-- Contract a supplied canonical range section into the complete conditional
gap datum. Every field is obtained from a previously checked consumer. -/
def ofRangeSection
    (D : CanonicalRangeSectionCertificate P J) :
    CanonicalCompletedGapCertificate P where
  rate_pos := twoStepRate_positive nome_pos hd
  rate_lt_one := twoStepRate_lt_one nome_pos hd hs
  form_bound := fun X hx => D.twoStep_form_bound X hx
  defect_form_bound := fun X hx => D.twoStep_defect_form_bound X hx
  fixed_eq_zero := fun X hx hfixed => D.twoStep_fixed_eq_zero X hx hfixed

end CanonicalCompletedGapCertificate

end YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.map_surjective
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.preimage_class_unique
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.twoStep_defect_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalRangeSectionCertificate.twoStep_fixed_eq_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalCompletedGapCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CanonicalCompletedGapCertificate.ofRangeSection
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyFormCertificate.toFormCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyTwoStepCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyTwoStepCertificate.toTwoStepCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyProbeCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyProbeCertificate.toProbeCertificate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.ofCertificates
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierCauchyFormCertificate.toBridge
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.map_injective
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_vacuum_orthogonal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_correlation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_defect_form_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.image_twoStep_fixed_eq_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonical_resolvent_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStepCorrelation_eq_current
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStep_sq_decay
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionCanonicalGNSBridge.CurrentCarrierBridge.canonicalProbe_twoStep_form_bound
