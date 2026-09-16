/-
# Fixed support neighborhood of the actual conditional approximation

Integrating the selected physical link removes its quaternion block. The
actual numerator involves only the input and incident faces; the actual
normalizer involves only those faces. Polynomial division never enlarges
this neighborhood, even as its iteration index tends to infinity.

The final witness is the EXISTING original full-action Cauchy representative
of the conditional projection, with its existing modulus and the proved
support bound at EVERY index. No new completion or representative choice
is introduced. This is locality, not commutation of neighboring updates,
quantitative spatial mixing, an OS estimate or a physical gap.
-/

import YMGap.Continuum.SU2QuaternionHeadBlockLocality
import YMGap.Continuum.BF4ExactSlabStarConditionalProjection
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabStarConditionalLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- A finite explicit neighborhood, independent of cutoff and iteration. -/
def updateLinks (extent : Nat) (link : Z4Link) (support : List Z4Link) : List Z4Link :=
  (support ++ faceLinks extent (incidentIds extent link)).filter (fun j => decide (j ≠ link))

private theorem integrate_local (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (support : List Z4Link) {p : RatPoly}
    (hp : LinkLocal extent support p) :
    BlockLocal (blocks extent-1)
      (fun b => correctedSlabLinkAt extent ((linkHeadSwap extent link hl).map (b+1)) ∈ support)
      (partialHaarHead (reindexQuaternionPolynomial (linkHeadSwap extent link hl) p)) :=
  (hp.reindex (linkHeadSwap extent link hl) (fun _ _ h => h)).partialHaarHead

private theorem probe_local (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (support : List Z4Link) {r : RatPoly}
    (hr : BlockLocal (blocks extent-1)
      (fun b => correctedSlabLinkAt extent ((linkHeadSwap extent link hl).map (b+1)) ∈ support) r) :
    LinkLocal extent (support.filter (fun j => decide (j ≠ link)))
      (headProbe (linkHeadSwap extent link hl) r) := by
  let swap := linkHeadSwap extent link hl
  apply (BlockLocal.liftHead (blocks := blocks extent) hr).reindex swap
  intro b hb h
  have hplus : swap.map b - 1 + 1 = swap.map b := by omega
  have hmem := h.2
  rw [hplus, swap.involutive b hb] at hmem
  apply List.mem_filter.mpr
  refine ⟨hmem, ?_⟩
  apply decide_eq_true
  intro he
  have hk := List.idxOf_lt_length_of_mem hl
  have hbk : b = (boundaryCompleteSlabLinks extent).idxOf link :=
    correctedSlabLinkAt_injective_on_physical (List.mem_range.mpr hb) (List.mem_range.mpr hk)
      (he.trans (correctedSlabLinkAt_idxOf hl).symm)
  have hz : swap.map b = 0 := by
    rw [hbk]
    exact headSwapBlockInvolution_map_selected _ _ hk
  omega

theorem normalizer_local (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    BlockLocal (blocks extent-1)
      (fun b => correctedSlabLinkAt extent ((linkHeadSwap extent link hl).map (b+1)) ∈
        faceLinks extent (incidentIds extent link))
      (normalizer w K extent link hl) :=
  integrate_local extent link hl _ (heatProduct_local w K extent (incidentIds extent link))

theorem insertedNormalizer_local (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (support : List Z4Link) (p : RatPoly)
    (hp : LinkLocal extent support p) :
    BlockLocal (blocks extent-1)
      (fun b => correctedSlabLinkAt extent ((linkHeadSwap extent link hl).map (b+1)) ∈
        support ++ faceLinks extent (incidentIds extent link))
      (insertedNormalizer w K extent link hl p) :=
  integrate_local extent link hl _
    ((hp.mono (fun _ h => List.mem_append.mpr (Or.inl h))).mul
      ((heatProduct_local w K extent (incidentIds extent link)).mono
        (fun _ h => List.mem_append.mpr (Or.inr h))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "F" => fullData hw0 hw1 K extent hK
local notation "A" => approximateInverse hw0 hw1 K extent hK link hl

private theorem inverse_local (allowed : Nat → Prop)
    (hD : BlockLocal (blocks extent-1) allowed (normalizer w K extent link hl))
    (r : (G).V) (hr : BlockLocal (blocks extent-1) allowed r.val) :
    ∀ n, BlockLocal (blocks extent-1) allowed (A r n).val
  | 0 => (BlockLocal.one _ _).smul 0
  | n+1 =>
    (inverse_local allowed hD r hr n).add
      ((hr.add (((inverse_local allowed hD r hr n).mul hD).smul (-1))).smul _)

/-- Every finite conditional approximant depends only on the original input
and the selected link's incident faces, with that link removed. -/
theorem conditionalApproximation_local (support : List Z4Link) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (hlocal : LinkLocal extent support p) (n : Nat) :
    LinkLocal extent (updateLinks extent link support)
      (headProbe (linkHeadSwap extent link hl)
        (conditionalApproximation hw0 hw1 K extent hK link hl p hp n).val) := by
  apply probe_local
  apply inverse_local
  · intro t ht b hb hn
    exact normalizer_local w K extent link hl t ht b hb
      (fun h => hn (List.mem_append.mpr (Or.inr h)))
  · exact insertedNormalizer_local w K extent link hl support p hlocal

/-- Explicit localized representative of the ACTUAL original conditional
projection. Its Cauchy modulus is the already constructed division/lift
modulus; locality holds at every index without an extra tolerance cutoff. -/
def conditionalProjection_localRepresentative (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) :
    { X : CauchyGNS F //
      (∀ n, LinkLocal extent (updateLinks extent link support) (X.seq n).val) ∧
      Quotient.mk (cauchySetoid F) X =
        conditionalProjection hw0 hw1 K extent hK link hl (embedV F p) } := by
  refine ⟨probeCauchy hw0 hw1 K extent hK link hl
    (inverseCauchy hw0 hw1 K extent hK link hl (numeratorMap hw0 hw1 K extent hK link hl p)), ?_, ?_⟩
  · intro n
    exact conditionalApproximation_local hw0 hw1 K extent hK link hl support p.val p.property hp n
  · exact (conditionalProjection_embed hw0 hw1 K extent hK link hl p).symm

end YMGap.Continuum.BF4ExactSlabStarConditionalLocality

#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalLocality.updateLinks
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalLocality.normalizer_local
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalLocality.insertedNormalizer_local
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalLocality.conditionalApproximation_local
#print axioms YMGap.Continuum.BF4ExactSlabStarConditionalLocality.conditionalProjection_localRepresentative
