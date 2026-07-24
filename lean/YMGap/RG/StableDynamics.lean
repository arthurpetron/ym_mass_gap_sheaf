/-
Constructive composition layer for stable-interface RG dynamics.

This module implements the STRUCTURAL content of work-plan items RG-I7,
RG-I8, and RG-I9 after an RG branch has been identified by
`StableTailCertificate`:

* `UniformContractionCertificate` carries an explicit rational rate `q < 1`,
  the stable-interface evolution maps, an admissible-ball witness family, and
  the uniform one-step contraction and invariance estimates.
* `ConstructiveLandingCertificate` carries an explicit landing offset and an
  admissibility witness.  `PhysicalLandingWitness` restores the absolute scale
  `kStar + offset` as extractable Type-level data.
* `SummableDistortion` carries a rational cap and a computable tail modulus.
  `SeparatedDistortionBudget` keeps dynamic and interface-transport errors in
  distinct certificates; they are added only by named composition theorems.
* `StableDynamicsCertificate` packages the stable tail, contraction, landing,
  and both distortion budgets.  Its derived declarations expose the physical
  landing scale, post-landing geometric contraction, and accumulated-error
  bounds without hiding any witness in a proposition-level existential.

This module does NOT construct the Yang--Mills contraction, landing state, or
summability estimates.  Those are genuine analytic inputs, represented by the
nontrivial named structures above.  In particular, no frontier bundle is
inhabited and no physical mass-gap claim is made.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.InterfaceStability
import YMGap.Constructive.GeometricTail
import YMGap.Constructive.FinSumAlg

namespace YMGap.RG.StableDynamics

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.PolynomialTree
open YMGap.RG.InterfaceStability

universe u v

/-! ## Uniform transported contraction on the stable interface -/

/-- A proof-carrying uniform contraction certificate on one stable carrier.

`Admissible x` is Type-valued so a later construction retains the actual
Gaussian-ball (or other invariant-domain) certificate.  The analytic instance
must supply a common `q < 1` and prove both ball preservation and the
one-step Lipschitz estimate uniformly in the tail offset. -/
structure UniformContractionCertificate (X : Type u) where
  /-- Constructive rational distance or norm discrepancy. -/
  distance : X -> X -> Q'
  /-- Proof-relevant membership in the preserved contraction domain. -/
  Admissible : X -> Type v
  /-- Stable-interface RG map at each offset from `kStar`. -/
  step : Nat -> X -> X
  /-- Uniform contraction rate. -/
  q : Q'
  qNonnegative : (0 : Q') <= q
  qBelowOne : q < (1 : Q')
  distanceNonnegative : forall x y, (0 : Q') <= distance x y
  stepAdmissible : forall n x, Admissible x -> Admissible (step n x)
  contracts : forall n x y, Admissible x -> Admissible y ->
    distance (step n x) (step n y) <= q * distance x y

namespace UniformContractionCertificate

/-- Evolve a stable-interface state for `n` steps, beginning at tail offset
`start`.  The definition is executable structural recursion. -/
def evolveFrom {X : Type u}
    (c : UniformContractionCertificate.{u, v} X)
    (start : Nat) (x : X) : Nat -> X
  | 0 => x
  | n + 1 => c.step (start + n) (c.evolveFrom start x n)

/-- Admissibility is preserved along every finite post-landing evolution.
The result is Type-level certificate data, not an erased existence claim. -/
def evolveAdmissible {X : Type u}
    (c : UniformContractionCertificate.{u, v} X)
    (start : Nat) {x : X} (hx : c.Admissible x) :
    (n : Nat) -> c.Admissible (c.evolveFrom start x n)
  | 0 => hx
  | n + 1 => c.stepAdmissible (start + n) _ (c.evolveAdmissible start hx n)

/-- Iterating the uniform one-step estimate gives the explicit geometric
bound `q^n * distance x y` for two admitted starting states. -/
theorem evolve_pair_contracts {X : Type u}
    (c : UniformContractionCertificate.{u, v} X)
    (start : Nat) {x y : X}
    (hx : c.Admissible x) (hy : c.Admissible y) :
    forall n,
      c.distance (c.evolveFrom start x n) (c.evolveFrom start y n) <=
        c.q ^ n * c.distance x y
  | 0 => by
      show c.distance x y <= (1 : Q') * c.distance x y
      exact Q'.ge_of_eqv (Q'.one_mul_eqv (c.distance x y))
  | n + 1 => by
      have hstep := c.contracts (start + n)
        (c.evolveFrom start x n) (c.evolveFrom start y n)
        (c.evolveAdmissible start hx n) (c.evolveAdmissible start hy n)
      have hind := c.evolve_pair_contracts start hx hy n
      have hscaled :
          c.q * c.distance (c.evolveFrom start x n) (c.evolveFrom start y n) <=
            c.q * (c.q ^ n * c.distance x y) :=
        Q'.mul_le_mul_of_nonneg_left _ _ c.q hind c.qNonnegative
      exact Q'.le_trans' _ _ _ hstep
        (Q'.le_trans' _ _ _ hscaled
          (Q'.ge_of_eqv (Q'.mul_assoc_eqv c.q (c.q ^ n) (c.distance x y))))

end UniformContractionCertificate

/-! ## Constructive landing -/

/-- An explicit trajectory landing certificate in the stable-interface
contraction domain.

The trajectory is indexed by offsets from `kStar`; `offset` is the first scale
claimed by this certificate.  Minimality is deliberately not required: RG-I8
needs a computable landing scale, not a proof that it is the least one. -/
structure ConstructiveLandingCertificate
    {X : Type u}
    (c : UniformContractionCertificate.{u, v} X)
    (orbit : Nat -> X) where
  offset : Nat
  follows : forall n, c.step n (orbit n) = orbit (n + 1)
  landed : c.Admissible (orbit offset)

namespace ConstructiveLandingCertificate

/-- The supplied orbit after landing is exactly the structurally iterated
stable dynamics. -/
theorem evolve_eq_orbit
    {X : Type u}
    {c : UniformContractionCertificate.{u, v} X}
    {orbit : Nat -> X}
    (landing : ConstructiveLandingCertificate c orbit) :
    forall n,
      c.evolveFrom landing.offset (orbit landing.offset) n =
        orbit (landing.offset + n)
  | 0 => rfl
  | n + 1 => by
      show c.step (landing.offset + n)
          (c.evolveFrom landing.offset (orbit landing.offset) n) =
        orbit (landing.offset + (n + 1))
      rw [landing.evolve_eq_orbit n]
      simpa [Nat.add_assoc] using landing.follows (landing.offset + n)

/-- Every later point on the supplied trajectory has an explicit
admissibility certificate. -/
def orbitAdmissible
    {X : Type u}
    {c : UniformContractionCertificate.{u, v} X}
    {orbit : Nat -> X}
    (landing : ConstructiveLandingCertificate c orbit)
    (n : Nat) : c.Admissible (orbit (landing.offset + n)) := by
  rw [<- landing.evolve_eq_orbit n]
  exact c.evolveAdmissible landing.offset landing.landed n

/-- Post-landing comparison with any other admitted state contracts at the
explicit geometric rate. -/
theorem orbit_pair_contracts
    {X : Type u}
    {c : UniformContractionCertificate.{u, v} X}
    {orbit : Nat -> X}
    (landing : ConstructiveLandingCertificate c orbit)
    {y : X} (hy : c.Admissible y) :
    forall n,
      c.distance (orbit (landing.offset + n))
          (c.evolveFrom landing.offset y n) <=
        c.q ^ n * c.distance (orbit landing.offset) y := by
  intro n
  rw [<- landing.evolve_eq_orbit n]
  exact c.evolve_pair_contracts landing.offset landing.landed hy n

end ConstructiveLandingCertificate

/-! ## Separate dynamic and interface-transport distortion budgets -/

/-- Constructive summability data for one nonnegative rational error stream.

`partialSumBound` controls all accumulated finite distortion.  `modulus` and
`tailBound` are the stronger constructive-Cauchy data: after the returned
index, every finite tail block is bounded by the requested positive rational
resolution. -/
structure SummableDistortion (term : QSeq) where
  cap : Q'
  capNonnegative : (0 : Q') <= cap
  termNonnegative : forall n, (0 : Q') <= term n
  partialSumBound : forall N, finSum term N <= cap
  modulus : Q' -> Nat
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    forall start, modulus epsilon <= start ->
      forall length, finSum (fun j => term (start + j)) length <= epsilon

/-- Dynamic errors and changing-interface transport errors remain separately
certified.  This prevents an interface discrepancy from being silently charged
to a contraction estimate. -/
structure SeparatedDistortionBudget (dynamic interface : QSeq) where
  dynamicBudget : SummableDistortion dynamic
  interfaceBudget : SummableDistortion interface

namespace SeparatedDistortionBudget

/-- Pointwise total error, introduced only at the explicit composition layer. -/
def combinedTerm {dynamic interface : QSeq}
    (_budget : SeparatedDistortionBudget dynamic interface) : QSeq :=
  fun n => dynamic n + interface n

/-- The joint rational cap is the visible sum of the two separate caps. -/
def combinedCap {dynamic interface : QSeq}
    (budget : SeparatedDistortionBudget dynamic interface) : Q' :=
  budget.dynamicBudget.cap + budget.interfaceBudget.cap

/-- The combined term is nonnegative because each independently-certified
error stream is nonnegative. -/
theorem combinedTerm_nonnegative {dynamic interface : QSeq}
    (budget : SeparatedDistortionBudget dynamic interface) :
    forall n, (0 : Q') <= budget.combinedTerm n := by
  intro n
  exact Q'.zero_le_add _ _
    (budget.dynamicBudget.termNonnegative n)
    (budget.interfaceBudget.termNonnegative n)

/-- The joint cap is nonnegative without weakening either component cap. -/
theorem combinedCap_nonnegative {dynamic interface : QSeq}
    (budget : SeparatedDistortionBudget dynamic interface) :
    (0 : Q') <= budget.combinedCap :=
  Q'.zero_le_add _ _ budget.dynamicBudget.capNonnegative
    budget.interfaceBudget.capNonnegative

/-- Every accumulated finite total error is bounded by the sum of the dynamic
and interface caps. -/
theorem combined_partial_sum_bound {dynamic interface : QSeq}
    (budget : SeparatedDistortionBudget dynamic interface) :
    forall N, finSum budget.combinedTerm N <= budget.combinedCap := by
  intro N
  have hsplit : finSum budget.combinedTerm N <=
      finSum dynamic N + finSum interface N :=
    Q'.le_of_eqv (finSum_add dynamic interface N)
  have hd : finSum dynamic N + finSum interface N <=
      budget.dynamicBudget.cap + finSum interface N :=
    Q'.add_le_add_right _ _ _ (budget.dynamicBudget.partialSumBound N)
  have hi : budget.dynamicBudget.cap + finSum interface N <=
      budget.dynamicBudget.cap + budget.interfaceBudget.cap :=
    Q'.add_le_add_left _ _ _ (budget.interfaceBudget.partialSumBound N)
  exact Q'.le_trans' _ _ _ hsplit (Q'.le_trans' _ _ _ hd hi)

/-- A joint tail index at independently requested dynamic and interface
resolutions. -/
def jointModulus {dynamic interface : QSeq}
    (budget : SeparatedDistortionBudget dynamic interface)
    (dynamicResolution interfaceResolution : Q') : Nat :=
  max (budget.dynamicBudget.modulus dynamicResolution)
    (budget.interfaceBudget.modulus interfaceResolution)

/-- Past the joint modulus, total tail distortion is bounded by the explicit
sum of the independently requested resolutions.  No hidden allocation of one
error source against the other occurs. -/
theorem combined_tail_bound {dynamic interface : QSeq}
    (budget : SeparatedDistortionBudget dynamic interface)
    (dynamicResolution interfaceResolution : Q')
    (hDynamic : (0 : Q') < dynamicResolution)
    (hInterface : (0 : Q') < interfaceResolution) :
    forall start, budget.jointModulus dynamicResolution interfaceResolution <= start ->
      forall length,
        finSum (fun j => budget.combinedTerm (start + j)) length <=
          dynamicResolution + interfaceResolution := by
  intro start hstart length
  have hdm : budget.dynamicBudget.modulus dynamicResolution <= start :=
    Nat.le_trans (Nat.le_max_left _ _) hstart
  have him : budget.interfaceBudget.modulus interfaceResolution <= start :=
    Nat.le_trans (Nat.le_max_right _ _) hstart
  have hsplit :
      finSum (fun j => budget.combinedTerm (start + j)) length <=
        finSum (fun j => dynamic (start + j)) length +
          finSum (fun j => interface (start + j)) length :=
    Q'.le_of_eqv
      (finSum_add (fun j => dynamic (start + j))
        (fun j => interface (start + j)) length)
  have hd :
      finSum (fun j => dynamic (start + j)) length +
          finSum (fun j => interface (start + j)) length <=
        dynamicResolution + finSum (fun j => interface (start + j)) length :=
    Q'.add_le_add_right _ _ _
      (budget.dynamicBudget.tailBound dynamicResolution hDynamic start hdm length)
  have hi :
      dynamicResolution + finSum (fun j => interface (start + j)) length <=
        dynamicResolution + interfaceResolution :=
    Q'.add_le_add_left _ _ _
      (budget.interfaceBudget.tailBound interfaceResolution hInterface start him length)
  exact Q'.le_trans' _ _ _ hsplit (Q'.le_trans' _ _ _ hd hi)

end SeparatedDistortionBudget

/-! ## Composition with interface stabilization -/

/-- The complete constructive input surface for RG-I7--I9.

An inhabitant is intentionally nontrivial: it requires the physical stable
tail, a uniform subunit contraction estimate, an actual trajectory landing
witness, and independent summability/modulus estimates for both error streams.
-/
structure StableDynamicsCertificate (p : RGProgram.{u}) where
  stableTail : StableTailCertificate.{u, v} p
  contraction : UniformContractionCertificate.{u, v}
    (RGState stableTail.stableInterface)
  /-- The physical state before transport, at each node of the certified tail. -/
  sourceOrbit : (n : Nat) -> RGState (p.interface (stableTail.nodeAt n))
  /-- The same trajectory expressed in the common stable interface. -/
  orbit : Nat -> RGState stableTail.stableInterface
  /-- The stable-interface trajectory is exactly the coherent transport of
  the node-indexed physical trajectory. -/
  transportedOrbit : forall n,
    orbit n = (stableTail.transport n).stateForward (sourceOrbit n)
  landing : ConstructiveLandingCertificate contraction orbit
  dynamicError : QSeq
  interfaceError : QSeq
  distortion : SeparatedDistortionBudget dynamicError interfaceError

/-- Extracted physical landing data, with its absolute scale and stable-tail
state tied to the originating certificate. -/
structure PhysicalLandingWitness
    {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) where
  scale : Nat
  state : RGState dynamics.stableTail.stableInterface
  scale_eq : scale = dynamics.stableTail.kStar + dynamics.landing.offset
  state_eq : state = dynamics.orbit dynamics.landing.offset
  admissible : dynamics.contraction.Admissible state

namespace StableDynamicsCertificate

/-- The absolute physical scale at which the trajectory enters the preserved
contraction domain. -/
def absoluteLandingScale {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) : Nat :=
  dynamics.stableTail.kStar + dynamics.landing.offset

/-- The landing scale, state, and admissibility witness are returned as
Type-level data. -/
def physicalLanding {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) :
    PhysicalLandingWitness dynamics where
  scale := dynamics.absoluteLandingScale
  state := dynamics.orbit dynamics.landing.offset
  scale_eq := rfl
  state_eq := rfl
  admissible := dynamics.landing.landed

/-- The extracted landing state is the coherent transport of the physical
node-indexed state at the landing offset. -/
theorem physicalLanding_state_is_transported {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) :
    dynamics.physicalLanding.state =
      (dynamics.stableTail.transport dynamics.landing.offset).stateForward
        (dynamics.sourceOrbit dynamics.landing.offset) :=
  dynamics.transportedOrbit dynamics.landing.offset

/-- The absolute landing scale is at or after the stabilization scale `kStar`. -/
theorem kStar_le_absoluteLandingScale {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) :
    dynamics.stableTail.kStar <= dynamics.absoluteLandingScale :=
  Nat.le_add_right _ _

/-- Derived geometric contraction of the physical trajectory after landing,
relative to any admitted comparison state. -/
theorem postLanding_contracts {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p)
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

/-- Dynamic distortion remains available under its own cap. -/
theorem dynamic_partial_sum_bound {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) :
    forall N,
      finSum dynamics.dynamicError N <= dynamics.distortion.dynamicBudget.cap :=
  dynamics.distortion.dynamicBudget.partialSumBound

/-- Interface-transport distortion remains available under its own cap. -/
theorem interface_partial_sum_bound {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) :
    forall N,
      finSum dynamics.interfaceError N <= dynamics.distortion.interfaceBudget.cap :=
  dynamics.distortion.interfaceBudget.partialSumBound

/-- Total accumulated distortion is bounded only at this named composition
point, by the visible sum of the separate caps. -/
theorem total_partial_sum_bound {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) :
    forall N,
      finSum dynamics.distortion.combinedTerm N <=
        dynamics.distortion.combinedCap :=
  dynamics.distortion.combined_partial_sum_bound

/-- The two constructive tail moduli compose at independently supplied
resolutions. -/
theorem total_tail_bound {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p)
    (dynamicResolution interfaceResolution : Q')
    (hDynamic : (0 : Q') < dynamicResolution)
    (hInterface : (0 : Q') < interfaceResolution) :
    forall start,
      dynamics.distortion.jointModulus dynamicResolution interfaceResolution <= start ->
      forall length,
        finSum (fun j => dynamics.distortion.combinedTerm (start + j)) length <=
          dynamicResolution + interfaceResolution :=
  dynamics.distortion.combined_tail_bound
    dynamicResolution interfaceResolution hDynamic hInterface

end StableDynamicsCertificate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms UniformContractionCertificate
#print axioms UniformContractionCertificate.evolveFrom
#print axioms UniformContractionCertificate.evolveAdmissible
#print axioms UniformContractionCertificate.evolve_pair_contracts
#print axioms ConstructiveLandingCertificate
#print axioms ConstructiveLandingCertificate.evolve_eq_orbit
#print axioms ConstructiveLandingCertificate.orbitAdmissible
#print axioms ConstructiveLandingCertificate.orbit_pair_contracts
#print axioms SummableDistortion
#print axioms SeparatedDistortionBudget
#print axioms SeparatedDistortionBudget.combined_partial_sum_bound
#print axioms SeparatedDistortionBudget.combined_tail_bound
#print axioms StableDynamicsCertificate
#print axioms StableDynamicsCertificate.physicalLanding
#print axioms StableDynamicsCertificate.physicalLanding_state_is_transported
#print axioms StableDynamicsCertificate.kStar_le_absoluteLandingScale
#print axioms StableDynamicsCertificate.postLanding_contracts
#print axioms StableDynamicsCertificate.total_partial_sum_bound
#print axioms StableDynamicsCertificate.total_tail_bound

end YMGap.RG.StableDynamics
