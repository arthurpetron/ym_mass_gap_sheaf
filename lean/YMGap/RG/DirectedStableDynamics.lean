/-
Forward-only composition of stable-interface RG dynamics.

Physical block-spin maps are generally non-invertible.  This module therefore
uses `DirectedStableTailCertificate` as the default stable-tail input and pins
the stable-interface trajectory to the forward-normalized physical states:

    orbit n = stableTail.stableStateAt sourceOrbit n.

The contraction, landing, and separated distortion structures are reused from
`StableDynamics.lean`; none of them requires an inverse interface transport.
The resulting certificate exposes the same absolute landing scale,
post-landing geometric contraction, and separately-accounted distortion
consequences as the exact-transport composition.

No state recovery, injectivity, inverse transport, interface equivalence, or
round-trip law is asserted.  In particular, the source state remains available
as physical input data, while only its directed forward image participates in
the stable-interface contraction estimate.

This module does NOT construct the Yang--Mills contraction, landing state, or
summability estimates.  Those remain explicit named analytic inputs.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.DirectedStableTailPresentation
import YMGap.RG.StableDynamics

namespace YMGap.RG.DirectedStableDynamics

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.PolynomialTree
open YMGap.RG.StableDynamics
open YMGap.RG.DirectedStableTailPresentation

universe u v

/-! ## Directed composition certificate -/

/-- The constructive RG-I7--I9 input surface over a forward-only stable tail.

`sourceOrbit` lives on the changing physical interfaces.  `orbit` lives on the
single stable interface used by contraction, and `forwardOrbit` pins it exactly
to `DirectedStableTailCertificate.stableStateAt`.  This is a one-way law: no
field asks for recovery of `sourceOrbit` from `orbit`. -/
structure DirectedStableDynamicsCertificate (p : RGProgram.{u}) where
  stableTail : DirectedStableTailCertificate.{u, v} p
  contraction : UniformContractionCertificate.{u, v}
    (RGState stableTail.stableInterface)
  /-- Physical states along the changing-interface selected ray. -/
  sourceOrbit : DirectedStableTailCertificate.SourceStateFamily stableTail
  /-- Their forward-normalized trajectory on the common stable interface. -/
  orbit : Nat -> RGState stableTail.stableInterface
  /-- Exact pinning to directed pushforward, with no inverse or recovery law. -/
  forwardOrbit : forall n,
    orbit n = stableTail.stableStateAt sourceOrbit n
  landing : ConstructiveLandingCertificate contraction orbit
  dynamicError : QSeq
  interfaceError : QSeq
  distortion : SeparatedDistortionBudget dynamicError interfaceError

/-- Extracted directed physical landing data.

Both the node-indexed physical source state and its stable forward image remain
visible as data.  The only relation between them is the directed pushforward
law `state_is_forward`; no reverse image is requested. -/
structure DirectedPhysicalLandingWitness
    {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) where
  scale : Nat
  sourceState :
    RGState (p.interface (dynamics.stableTail.nodeAt dynamics.landing.offset))
  state : RGState dynamics.stableTail.stableInterface
  scale_eq :
    scale = dynamics.stableTail.kStar + dynamics.landing.offset
  sourceState_eq :
    sourceState = dynamics.sourceOrbit dynamics.landing.offset
  state_is_forward :
    state = dynamics.stableTail.stableStateAt
      dynamics.sourceOrbit dynamics.landing.offset
  admissible : dynamics.contraction.Admissible state

namespace DirectedStableDynamicsCertificate

/-- The absolute physical scale where the forward-normalized trajectory enters
the preserved contraction domain. -/
def absoluteLandingScale {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) : Nat :=
  dynamics.stableTail.physicalScale dynamics.landing.offset

/-- Return the physical source state, its stable forward image, the absolute
landing scale, and an admissibility certificate as Type-level data. -/
def physicalLanding {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    DirectedPhysicalLandingWitness dynamics where
  scale := dynamics.absoluteLandingScale
  sourceState := dynamics.sourceOrbit dynamics.landing.offset
  state := dynamics.orbit dynamics.landing.offset
  scale_eq := rfl
  sourceState_eq := rfl
  state_is_forward := dynamics.forwardOrbit dynamics.landing.offset
  admissible := dynamics.landing.landed

/-- The extracted landing state is exactly the one-way pushforward of the
physical node-indexed state. -/
theorem physicalLanding_state_is_forward_image {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    dynamics.physicalLanding.state =
      dynamics.stableTail.stableStateAt
        dynamics.sourceOrbit dynamics.landing.offset :=
  dynamics.forwardOrbit dynamics.landing.offset

/-- The extracted physical source state remains the selected source-orbit
state; this theorem does not assert it can be recovered from the stable state. -/
theorem physicalLanding_sourceState_eq {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    dynamics.physicalLanding.sourceState =
      dynamics.sourceOrbit dynamics.landing.offset :=
  rfl

/-- The absolute landing scale lies at or after the stabilization scale. -/
theorem kStar_le_absoluteLandingScale {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    dynamics.stableTail.kStar <= dynamics.absoluteLandingScale :=
  dynamics.stableTail.kStar_le_physicalScale dynamics.landing.offset

/-- The forward-normalized physical trajectory contracts geometrically after
landing, relative to every admitted comparison state on the same stable
interface. -/
theorem postLanding_contracts {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p)
    {y : RGState dynamics.stableTail.stableInterface}
    (hy : dynamics.contraction.Admissible y) :
    forall n,
      dynamics.contraction.distance
          (dynamics.orbit (dynamics.landing.offset + n))
          (dynamics.contraction.evolveFrom dynamics.landing.offset y n) <=
        dynamics.contraction.q ^ n *
          dynamics.contraction.distance
            (dynamics.orbit dynamics.landing.offset) y :=
  dynamics.landing.orbit_pair_contracts hy

/-- Dynamic distortion remains bounded under its independently supplied cap. -/
theorem dynamic_partial_sum_bound {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    forall N,
      finSum dynamics.dynamicError N <= dynamics.distortion.dynamicBudget.cap :=
  dynamics.distortion.dynamicBudget.partialSumBound

/-- Directed interface-transport distortion remains bounded under its own cap. -/
theorem interface_partial_sum_bound {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    forall N,
      finSum dynamics.interfaceError N <=
        dynamics.distortion.interfaceBudget.cap :=
  dynamics.distortion.interfaceBudget.partialSumBound

/-- Total accumulated distortion is formed only at this named composition
point, with the two component caps still visible. -/
theorem total_partial_sum_bound {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) :
    forall N,
      finSum dynamics.distortion.combinedTerm N <=
        dynamics.distortion.combinedCap :=
  dynamics.distortion.combined_partial_sum_bound

/-- The independent constructive tail moduli compose at separately requested
dynamic and interface resolutions. -/
theorem total_tail_bound {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p)
    (dynamicResolution interfaceResolution : Q')
    (hDynamic : (0 : Q') < dynamicResolution)
    (hInterface : (0 : Q') < interfaceResolution) :
    forall start,
      dynamics.distortion.jointModulus
          dynamicResolution interfaceResolution <= start ->
      forall length,
        finSum (fun j => dynamics.distortion.combinedTerm (start + j)) length <=
          dynamicResolution + interfaceResolution :=
  dynamics.distortion.combined_tail_bound
    dynamicResolution interfaceResolution hDynamic hInterface

end DirectedStableDynamicsCertificate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms DirectedStableDynamicsCertificate
#print axioms DirectedPhysicalLandingWitness
#print axioms DirectedStableDynamicsCertificate.absoluteLandingScale
#print axioms DirectedStableDynamicsCertificate.physicalLanding
#print axioms DirectedStableDynamicsCertificate.physicalLanding_state_is_forward_image
#print axioms DirectedStableDynamicsCertificate.physicalLanding_sourceState_eq
#print axioms DirectedStableDynamicsCertificate.kStar_le_absoluteLandingScale
#print axioms DirectedStableDynamicsCertificate.postLanding_contracts
#print axioms DirectedStableDynamicsCertificate.dynamic_partial_sum_bound
#print axioms DirectedStableDynamicsCertificate.interface_partial_sum_bound
#print axioms DirectedStableDynamicsCertificate.total_partial_sum_bound
#print axioms DirectedStableDynamicsCertificate.total_tail_bound

end YMGap.RG.DirectedStableDynamics
