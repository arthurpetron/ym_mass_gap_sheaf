/-
# Original normalized covariance through the actual Chebyshev state

The existing centered original polynomials and reciprocal partition are
retained. The normalized first component of the actual balanced-sweep
recurrence has exactly the SAME covariance pairing until its 16*n cone
reaches the test. Literal coordinate separation supplies that premise.

No physical-time identification, strict operator decay, or continuum
construction follows from this exact finite identity alone.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevPairing
import YMGap.Continuum.BF4ExactSlabConeCoordinateDistance

namespace YMGap.Continuum.BF4ExactSlabChebyshevCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConeCoordinateDistance
open YMGap.Continuum.BF4ExactSlabChebyshevPairing
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe (fullData)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- The SAME normalized finite covariance, with its original partition,
is the normalized Chebyshev pairing before literal cone/test contact. -/
theorem covariance_as_chebyshev_pairing (c : Q') (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val) (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    Quotient.mk crealSetoid
      (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)) =
      RCscale (inversePartition hw0 hw1 extent stage)
        ((F).cinnerCompl
          (normalizedFirst hw0 hw1 K extent hK c n ht
            (embedV F (centered hw0 hw1 extent stage p)))
          (embedV F (centered hw0 hw1 extent stage q))) := by
  rw [normalizedFirst_pairing hw0 hw1 K extent hK c n ht support testSupport
    (embedV F (centered hw0 hw1 extent stage p))
    (embedV F (centered hw0 hw1 extent stage q))
    (localized_embed hw0 hw1 K extent hK support _
      (centered_local hw0 hw1 extent stage support p hp))
    (localized_embed hw0 hw1 K extent hK testSupport _
      (centered_local hw0 hw1 extent stage testSupport q hq)) hsep]
  exact completed_covariance hw0 hw1 extent stage p q

/-- The existing rooted support geometry discharges the Chebyshev cone
premise at the explicit degree-dependent coordinate separation. -/
theorem covariance_as_chebyshev_pairing_of_root_far (c : Q') (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (p q : (F).V) (hp : LinkLocal extent left p.val) (hq : LinkLocal extent right q.val)
    (hfar : 16*n + P.animal.support.length + Q.animal.support.length <
      linfDist P.animal.root Q.animal.root) :
    Quotient.mk crealSetoid
      (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)) =
      RCscale (inversePartition hw0 hw1 extent stage)
        ((F).cinnerCompl
          (normalizedFirst hw0 hw1 K extent hK c n ht
            (embedV F (centered hw0 hw1 extent stage p)))
          (embedV F (centered hw0 hw1 extent stage q))) := by
  apply covariance_as_chebyshev_pairing hw0 hw1 extent stage c n ht left right p q hp hq
  intro j hj hjq
  have h := contact_root_bound P Q extent (16*n) j hj hjq
  omega

#print axioms covariance_as_chebyshev_pairing
#print axioms covariance_as_chebyshev_pairing_of_root_far

end YMGap.Continuum.BF4ExactSlabChebyshevCovariance
