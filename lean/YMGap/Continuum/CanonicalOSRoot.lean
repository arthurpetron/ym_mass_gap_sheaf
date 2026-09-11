/-
Canonical functional and positive-time Osterwalder--Schrader roots.

This module records the dependency correction forced by
`PositiveIsometricTimeNoGo`.  The ordinary state form

  E(a* b)

is an AMBIENT Euclidean form.  State-preserving Euclidean time is isometric for
that form, so it cannot also be a nontrivial positive physical transfer.  The
physical datum below is instead pinned only to the reflected half-space form

  E((Theta a)* b).

In particular, the canonical interface does NOT inherit
`PositiveTimeCompression.embed_form`, its finite weighted-Gram certificate, or
its finite-rank consequences.  That older API remains useful for exact cutoff
models, but is not the generic continuum OS carrier.

The structures here are named constructive obligations, not inhabitants for
four-dimensional Yang--Mills.  A genuine realization must construct their
stage geometry, convergence moduli, support certificates, reflected form, and
transfer laws from one Wilson family.  No classical choice or nonconstructive
axiom is introduced.
-/

import YMGap.Continuum.FiniteVolume
import YMGap.Continuum.WilsonGNS
import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.GNSDynamics

namespace YMGap.Continuum.CanonicalOSRoot

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.WilsonGNS
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A single functional and its ordinary ambient Wilson form -/

/-- One observable algebra, one probability functional, and one Wilson module
datum whose expectation is definitionally that functional.

`unitFormNormalized` is explicit because the legacy `ObsAlg` does not yet
bundle the unital `*`-algebra laws needed to derive
`E(star 1 * 1) = E(1) = 1`.  This record is an ambient functional root, not the
physical OS Hilbert space. -/
structure WilsonFunctionalRoot (A : ObsAlg) (E : ProbFunctional A) : Type 1 where
  wilson : WilsonGNSData A
  expectationPinned : wilson.E = E.E
  unitFormNormalized : wilson.B A.one A.one ≈ 1

namespace WilsonFunctionalRoot

variable {A : ObsAlg} {E : ProbFunctional A}

/-- The ordinary state GNS datum, used only as the ambient Euclidean space. -/
def ambientData (R : WilsonFunctionalRoot A E) : GNSData :=
  R.wilson.toGNSData

/-- Unconditional arbitrary-modulus completeness for the ambient state GNS
space.  This is not declared to be the physical Hilbert space. -/
def ambientCompletion (R : WilsonFunctionalRoot A E) :
    CompleteGNSHilbertGeneral R.ambientData :=
  R.ambientData.gnsComplete_general

end WilsonFunctionalRoot

/-! ## 2. Two-parameter reference-weight approximants and their limit -/

/-- Finite-volume/reference-weight approximants indexed independently by
volume and lattice spacing.

This deliberately does not claim exact projective consistency: bare Wilson
plaquette measures at different spacings are not exact marginals under a block
map.  Nor does `ReferenceWeight` by itself prove interaction.  A later
group/action-pinned family must identify these weights with the genuine Wilson
action and construct the geometric positive-time certificates. -/
structure ReferenceWeightStageFamily : Type 2 where
  Obs : Nat → Nat → ObsAlg
  weight : ∀ volume cutoff, ReferenceWeight (Obs volume cutoff)
  functional : ∀ volume cutoff, ProbFunctional (Obs volume cutoff)
  functionalPinned : ∀ volume cutoff (a : (Obs volume cutoff).carrier),
    (functional volume cutoff).E a ≈ (weight volume cutoff).E_Λ a
  spacing : Nat → Q'
  spacingPositive : ∀ cutoff, (0 : Q') < spacing cutoff
  spacingModulus : Q' → Nat
  spacingTendsToZero : ∀ ε, (0 : Q') < ε → ∀ cutoff,
    spacingModulus ε ≤ cutoff → spacing cutoff ≤ ε
  volumeRadius : Nat → Nat
  volumeModulus : Nat → Nat
  volumeTendsToInfinity : ∀ r volume,
    volumeModulus r ≤ volume → r ≤ volumeRadius volume
  /-- A Type-level certificate that a stage observable is geometrically
  supported in the nonnegative Euclidean-time half-space.  Its concrete Wilson
  realization, rather than this interface, must define the actual geometry. -/
  positiveTimeCertificate : ∀ volume cutoff,
    (Obs volume cutoff).carrier → Type
  witnessVolume : Nat
  witnessCutoff : Nat
  fluctuation : (Obs witnessVolume witnessCutoff).carrier
  fluctuationCentered :
    (functional witnessVolume witnessCutoff).E fluctuation ≈ 0
  fluctuationVariancePositive :
    (0 : Q') < (functional witnessVolume witnessCutoff).E
      ((Obs witnessVolume witnessCutoff).mul
        ((Obs witnessVolume witnessCutoff).star fluctuation) fluctuation)

/-- A Schwinger functional obtained as an actual two-parameter approximation
limit, not by attaching spacing/volume metadata to an inverse-limit thread.

Every limiting algebraic observable has a stage discretization.  The same
explicit error controls both its ambient-GNS approximation and the discrepancy
of its expectation.  Separate Type-level volume and cutoff moduli make the
thermodynamic and continuum limits auditable. -/
structure CanonicalSchwingerLimit (F : ReferenceWeightStageFamily) : Type 2 where
  A : ObsAlg
  E : ProbFunctional A
  functionalRoot : WilsonFunctionalRoot A E
  stageMap : ∀ volume cutoff, ObsHom (F.Obs volume cutoff) A
  approximation : A.carrier → ∀ volume cutoff,
    (F.Obs volume cutoff).carrier
  approximationError : A.carrier → Nat → Nat → Q'
  approximationErrorNonneg : ∀ a volume cutoff,
    (0 : Q') ≤ approximationError a volume cutoff
  observableApproximation : ∀ a volume cutoff,
    functionalRoot.ambientData.B
      (functionalRoot.ambientData.sub
        ((stageMap volume cutoff).map (approximation a volume cutoff)) a)
      (functionalRoot.ambientData.sub
        ((stageMap volume cutoff).map (approximation a volume cutoff)) a) ≤
      approximationError a volume cutoff
  expectationApproximationLower : ∀ a volume cutoff,
    E.E a ≤
      (F.functional volume cutoff).E (approximation a volume cutoff) +
        approximationError a volume cutoff
  expectationApproximationUpper : ∀ a volume cutoff,
    (F.functional volume cutoff).E (approximation a volume cutoff) ≤
      E.E a + approximationError a volume cutoff
  thermodynamicModulus : A.carrier → Q' → Nat
  continuumModulus : A.carrier → Q' → Nat
  approximationConverges : ∀ a ε, (0 : Q') < ε → ∀ volume cutoff,
    thermodynamicModulus a ε ≤ volume →
    continuumModulus a ε ≤ cutoff →
    approximationError a volume cutoff ≤ ε

/-! ## 3. Observable-compatible ambient time and reflection -/

/-- A unital `*`-endomorphism which is also well defined and linear for the
selected Wilson module structure. -/
structure CompatibleWilsonHom
    {A : ObsAlg} {E : ProbFunctional A} (R : WilsonFunctionalRoot A E) where
  hom : ObsHom A A
  map_veq : ∀ {a b}, R.ambientData.veq a b →
    R.ambientData.veq (hom.map a) (hom.map b)
  map_add : ∀ a b, R.ambientData.veq
    (hom.map (R.ambientData.add a b))
    (R.ambientData.add (hom.map a) (hom.map b))
  map_neg : ∀ a, R.ambientData.veq
    (hom.map (R.ambientData.neg a)) (R.ambientData.neg (hom.map a))
  map_smul : ∀ s a, R.ambientData.veq
    (hom.map (R.ambientData.smul s a))
    (R.ambientData.smul s (hom.map a))

/-- Ambient Euclidean time and reflection on the SAME observable algebra and
Wilson functional.  Time/reflection are actual observable `*`-endomorphisms,
not free maps on an unrelated GNS carrier. -/
structure WilsonAmbientTimeReflection
    {A : ObsAlg} {E : ProbFunctional A} (R : WilsonFunctionalRoot A E) where
  tau : CompatibleWilsonHom R
  tauInv : CompatibleWilsonHom R
  theta : CompatibleWilsonHom R
  tauLeftInverse : ∀ a, R.ambientData.veq (tauInv.hom.map (tau.hom.map a)) a
  tauRightInverse : ∀ a, R.ambientData.veq (tau.hom.map (tauInv.hom.map a)) a
  thetaInvolutive : ∀ a, R.ambientData.veq
    (theta.hom.map (theta.hom.map a)) a
  thetaTimeInverse : ∀ a, R.ambientData.veq
    (theta.hom.map (tau.hom.map (theta.hom.map a))) (tauInv.hom.map a)
  tauExpectationInvariant : ∀ a,
    R.wilson.E (tau.hom.map a) ≈ R.wilson.E a
  thetaExpectationInvariant : ∀ a,
    R.wilson.E (theta.hom.map a) ≈ R.wilson.E a

namespace WilsonAmbientTimeReflection

variable {A : ObsAlg} {E : ProbFunctional A}
  {R : WilsonFunctionalRoot A E}

/-- State invariance and the `*`-homomorphism laws derive ambient isometry. -/
theorem tau_isometry (G : WilsonAmbientTimeReflection R) (a b : A.carrier) :
    R.ambientData.B (G.tau.hom.map a) (G.tau.hom.map b) ≈
      R.ambientData.B a b := by
  change
    R.wilson.E (A.mul (A.star (G.tau.hom.map a)) (G.tau.hom.map b)) ≈
      R.wilson.E (A.mul (A.star a) b)
  rw [← G.tau.hom.map_star a, ← G.tau.hom.map_mul]
  exact G.tauExpectationInvariant (A.mul (A.star a) b)

end WilsonAmbientTimeReflection

/-! ## 4. Geometric positive-time support -/

/-- Constructive half-space support inside the SAME limiting observable
algebra.  Certificates are Type-valued so a realization must retain their
computational/geometric content.

`approximationSupported` ties limiting support to the two-parameter Wilson
approximants.  This interface is still an obligation: calling a certificate
"positive time" is not a proof until the concrete stage family constructs it
from lattice support geometry. -/
structure PositiveTimeSupport
    {F : ReferenceWeightStageFamily} (L : CanonicalSchwingerLimit F)
    (G : WilsonAmbientTimeReflection L.functionalRoot) : Type 2 where
  certificate : L.A.carrier → Type
  transport : ∀ {a b}, L.functionalRoot.ambientData.veq a b →
    certificate a → certificate b
  unit : certificate L.A.one
  zero : certificate L.functionalRoot.ambientData.zero
  add : ∀ {a b}, certificate a → certificate b →
    certificate (L.functionalRoot.ambientData.add a b)
  neg : ∀ {a}, certificate a →
    certificate (L.functionalRoot.ambientData.neg a)
  smul : ∀ s {a}, certificate a →
    certificate (L.functionalRoot.ambientData.smul s a)
  tau : ∀ {a}, certificate a → certificate (G.tau.hom.map a)
  approximationSupported : ∀ a, certificate a → ∀ volume cutoff,
    F.positiveTimeCertificate volume cutoff (L.approximation a volume cutoff)

namespace PositiveTimeSupport

variable {F : ReferenceWeightStageFamily} {L : CanonicalSchwingerLimit F}
  {G : WilsonAmbientTimeReflection L.functionalRoot}

/-- An actual limiting observable together with its half-space certificate. -/
def Observable (S : PositiveTimeSupport L G) : Type :=
  Σ a : L.A.carrier, S.certificate a

/-- The underlying observable in the canonical limiting algebra. -/
def Observable.value (S : PositiveTimeSupport L G) (p : S.Observable) :
    L.A.carrier := p.1

/-- The algebra unit with its positive-time support certificate. -/
def unitObservable (S : PositiveTimeSupport L G) : S.Observable :=
  ⟨L.A.one, S.unit⟩

end PositiveTimeSupport

/-! ## 5. The standard reflected positive-time root -/

/-- The standard reflected positive-time OS prerequisite.

The physical form is pinned ONLY to
`E((Theta a)* b)`.  There is no assertion equating it with the ordinary ambient
state norm, no finite-mode factorization, and no arbitrary projection.  Every
physical representative is equivalent to a certified half-space observable,
and the representative embedding both preserves and reflects carrier
equivalence, blocking nondegenerate adjoined toy sectors.

The representative transfer laws are explicit semantic obligations.  A real
Yang--Mills inhabitant must derive self-adjointness, positivity, and contraction
from OS support/reflection/Markov estimates; storing those theorem statements
here does not claim they have been proved for the 4D theory. -/
structure PositiveTimeOSRoot
    {F : ReferenceWeightStageFamily} (L : CanonicalSchwingerLimit F)
    (G : WilsonAmbientTimeReflection L.functionalRoot) : Type 2 where
  support : PositiveTimeSupport L G
  positive : GNSData
  representative : positive.V → L.A.carrier
  representativeMapVeq : ∀ {a b}, positive.veq a b →
    L.functionalRoot.ambientData.veq (representative a) (representative b)
  representativeReflectsVeq : ∀ {a b},
    L.functionalRoot.ambientData.veq (representative a) (representative b) →
      positive.veq a b
  representativeZero : L.functionalRoot.ambientData.veq
    (representative positive.zero) L.functionalRoot.ambientData.zero
  representativeAdd : ∀ a b, L.functionalRoot.ambientData.veq
    (representative (positive.add a b))
    (L.functionalRoot.ambientData.add (representative a) (representative b))
  representativeNeg : ∀ a, L.functionalRoot.ambientData.veq
    (representative (positive.neg a))
    (L.functionalRoot.ambientData.neg (representative a))
  representativeSmul : ∀ s a, L.functionalRoot.ambientData.veq
    (representative (positive.smul s a))
    (L.functionalRoot.ambientData.smul s (representative a))
  representativeSupported : ∀ a, support.certificate (representative a)
  state : support.Observable → positive.V
  stateRepresentative : ∀ p, L.functionalRoot.ambientData.veq
    (representative (state p)) p.1
  /-- No nondegenerate adjoined summand: every representative comes from a
  certified positive-time observable in the canonical limit algebra. -/
  stateEssentiallySurjective : ∀ x : positive.V,
    Σ' p : support.Observable, positive.veq x (state p)
  reflectedForm : ∀ a b,
    L.functionalRoot.ambientData.B
      (G.theta.hom.map (representative a)) (representative b) ≈ positive.B a b
  transfer : positive.V → positive.V
  transferRepresentative : ∀ a, L.functionalRoot.ambientData.veq
    (representative (transfer a)) (G.tau.hom.map (representative a))
  transferMapVeq : ∀ {a b}, positive.veq a b →
    positive.veq (transfer a) (transfer b)
  transferMapZero : positive.veq (transfer positive.zero) positive.zero
  transferMapAdd : ∀ a b, positive.veq (transfer (positive.add a b))
    (positive.add (transfer a) (transfer b))
  transferMapNeg : ∀ a, positive.veq (transfer (positive.neg a))
    (positive.neg (transfer a))
  transferMapSmul : ∀ s a, positive.veq (transfer (positive.smul s a))
    (positive.smul s (transfer a))
  transferSelfAdjoint : ∀ a b,
    positive.B (transfer a) b ≈ positive.B a (transfer b)
  transferPositive : ∀ a, (0 : Q') ≤ positive.B (transfer a) a
  transferContraction : ∀ a,
    positive.B (transfer a) (transfer a) ≤ positive.B a a
  probeObservable : support.Observable
  probeVacuumOrthogonal :
    positive.B (state probeObservable) (state support.unitObservable) ≈ 0
  probeNormOne :
    positive.B (state probeObservable) (state probeObservable) ≈ 1
  /-- A finite nonzero transfer response.  The positive lower bound excludes
  zero transfer and the strict upper bound excludes identity, without assuming
  that the probe is an eigenvector. -/
  rayleighLower : Q'
  rayleighUpper : Q'
  rayleighLowerPositive : (0 : Q') < rayleighLower
  rayleighUpperLtOne : rayleighUpper < (1 : Q')
  probeRayleighLower : rayleighLower ≤
    positive.B (transfer (state probeObservable)) (state probeObservable)
  probeRayleighUpper :
    positive.B (transfer (state probeObservable)) (state probeObservable) ≤
      rayleighUpper

namespace PositiveTimeOSRoot

variable {F : ReferenceWeightStageFamily} {L : CanonicalSchwingerLimit F}
  {G : WilsonAmbientTimeReflection L.functionalRoot}

/-- Representative of the algebra unit in the physical positive-time space. -/
def unitRep (P : PositiveTimeOSRoot L G) : P.positive.V :=
  P.state P.support.unitObservable

/-- The normalized vacuum-orthogonal physical probe. -/
def probeRep (P : PositiveTimeOSRoot L G) : P.positive.V :=
  P.state P.probeObservable

/-- The reflected form is nonnegative on every represented half-space
observable. -/
theorem reflected_nonneg (P : PositiveTimeOSRoot L G) (a : P.positive.V) :
    (0 : Q') ≤ L.functionalRoot.ambientData.B
      (G.theta.hom.map (P.representative a)) (P.representative a) :=
  le_of_le_eqv (P.positive.self_nonneg a) (Q'.eqv_symm (P.reflectedForm a a))

/-- Unit normalization is DERIVED from the common functional, the unital
reflection, and the reflected-form pin. -/
theorem unitNormOne (P : PositiveTimeOSRoot L G) :
    P.positive.B P.unitRep P.unitRep ≈ 1 := by
  have hrep : L.functionalRoot.ambientData.veq
      (P.representative P.unitRep) L.A.one :=
    P.stateRepresentative P.support.unitObservable
  have htheta : L.functionalRoot.ambientData.veq
      (G.theta.hom.map (P.representative P.unitRep)) L.A.one := by
    refine L.functionalRoot.ambientData.veq_trans (G.theta.map_veq hrep) ?_
    rw [G.theta.hom.map_one]
    exact L.functionalRoot.ambientData.veq_refl L.A.one
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (P.reflectedForm P.unitRep P.unitRep)) ?_
  refine Q'.eqv_trans _ _ _
    (L.functionalRoot.ambientData.B_congr_left
      (P.representative P.unitRep) htheta) ?_
  refine Q'.eqv_trans _ _ _
    (L.functionalRoot.ambientData.B_congr_right L.A.one hrep) ?_
  exact L.functionalRoot.unitFormNormalized

/-- Vacuum invariance is DERIVED from the representative time pin and the
unitality of the observable time translation. -/
theorem unitFixed (P : PositiveTimeOSRoot L G) :
    P.positive.veq (P.transfer P.unitRep) P.unitRep := by
  have hrep : L.functionalRoot.ambientData.veq
      (P.representative P.unitRep) L.A.one :=
    P.stateRepresentative P.support.unitObservable
  have htau : L.functionalRoot.ambientData.veq
      (G.tau.hom.map (P.representative P.unitRep)) L.A.one := by
    refine L.functionalRoot.ambientData.veq_trans (G.tau.map_veq hrep) ?_
    rw [G.tau.hom.map_one]
    exact L.functionalRoot.ambientData.veq_refl L.A.one
  apply P.representativeReflectsVeq
  exact L.functionalRoot.ambientData.veq_trans
    (P.transferRepresentative P.unitRep)
    (L.functionalRoot.ambientData.veq_trans htau
      (L.functionalRoot.ambientData.veq_symm hrep))

theorem transfer_map_sub (P : PositiveTimeOSRoot L G) (a b : P.positive.V) :
    P.positive.veq (P.transfer (P.positive.sub a b))
      (P.positive.sub (P.transfer a) (P.transfer b)) :=
  P.positive.veq_trans (P.transferMapAdd a (P.positive.neg b))
    (P.positive.add_congr (P.positive.veq_refl _) (P.transferMapNeg b))

/-- Representative contractivity gives the exact squared-distance inequality
needed to descend transfer to the constructive completion. -/
theorem transfer_distSq_contraction (P : PositiveTimeOSRoot L G)
    (a b : P.positive.V) :
    P.positive.distSqQ (P.transfer a) (P.transfer b) ≤
      P.positive.distSqQ a b := by
  have hsub := P.transfer_map_sub a b
  exact le_of_eqv_le
    (Q'.eqv_symm (P.positive.B_diag_congr hsub))
    (P.transferContraction (P.positive.sub a b))

/-! ### Sound descent to unconditional constructive completion -/

def applyCauchy (P : PositiveTimeOSRoot L G)
    (x : CauchyGNS P.positive) : CauchyGNS P.positive where
  seq := fun n => P.transfer (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact Q'.le_trans' _ _ _
      (P.transfer_distSq_contraction (x.seq p) (x.seq q))
      (x.isCauchy ε hε p q hp hq)

theorem applyCauchy_null (P : PositiveTimeOSRoot L G)
    {x y : CauchyGNS P.positive} (h : CauchyNull P.positive x y) :
    CauchyNull P.positive (P.applyCauchy x) (P.applyCauchy y) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (P.transfer_distSq_contraction (x.seq n) (y.seq n)) (hN n hn)⟩

/-- The physical one-step transfer on the completion. -/
def completedTransfer (P : PositiveTimeOSRoot L G) :
    GNSCompletionSpace P.positive → GNSCompletionSpace P.positive :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid P.positive) (P.applyCauchy x))
    (fun _ _ h => Quotient.sound (P.applyCauchy_null h))

theorem completedTransfer_embed (P : PositiveTimeOSRoot L G)
    (a : P.positive.V) :
    P.completedTransfer (embedV P.positive a) =
      embedV P.positive (P.transfer a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

/-- Lift `Q'` equivalence to the constructive-real equivalence used by the
completed inner product. -/
theorem lifted_eqv {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro ε hε
  exact ⟨0, fun _ _ => ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a ε (Q'.le_of_lt hε))⟩⟩

theorem cinnerRep_transfer_selfAdjoint (P : PositiveTimeOSRoot L G)
    (x y : CauchyGNS P.positive) :
    CReal.Equiv
      (P.positive.cinnerRep (P.applyCauchy x) y)
      (P.positive.cinnerRep x (P.applyCauchy y)) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (P.positive.cInnerSeq (P.applyCauchy x) y n))
    (bSeq := fun n => CReal.ofQ'
      (P.positive.cInnerSeq x (P.applyCauchy y) n))
    (fun n => lifted_eqv (P.transferSelfAdjoint (x.seq n) (y.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedTransfer_selfAdjoint (P : PositiveTimeOSRoot L G)
    (x y : GNSCompletionSpace P.positive) :
    P.positive.cinnerCompl (P.completedTransfer x) y =
      P.positive.cinnerCompl x (P.completedTransfer y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact P.cinnerRep_transfer_selfAdjoint u v

theorem completedTransfer_positive (P : PositiveTimeOSRoot L G)
    (x : GNSCompletionSpace P.positive) :
    CReal.RCnonneg (P.positive.cinnerCompl (P.completedTransfer x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    (P.positive.cinnerRep (P.applyCauchy u) u)
  exact CReal.leEv_ofQ'_of_approx_ge
    (fun _ => P.transferPositive (u.seq _))

theorem cinnerRep_transfer_contraction (P : PositiveTimeOSRoot L G)
    (x : CauchyGNS P.positive) :
    CReal.leEv
      (P.positive.cinnerRep (P.applyCauchy x) (P.applyCauchy x))
      (P.positive.cinnerRep x x) := by
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (P.transferContraction (x.seq n))
    (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))⟩

theorem completedTransfer_contraction (P : PositiveTimeOSRoot L G)
    (x : GNSCompletionSpace P.positive) :
    CReal.RCle
      (P.positive.cinnerCompl (P.completedTransfer x) (P.completedTransfer x))
      (P.positive.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro u
  exact P.cinnerRep_transfer_contraction u

/-- The physical Hilbert carrier uses unconditional arbitrary-modulus
completion of the reflected positive-time form. -/
def physicalHilbert (P : PositiveTimeOSRoot L G) :
    CompleteGNSHilbertGeneral P.positive :=
  P.positive.gnsComplete_general

/-- The physical vacuum is the completed image of the algebra unit. -/
def physicalVacuum (P : PositiveTimeOSRoot L G) :
    P.physicalHilbert.hilbert.carrier :=
  embedV P.positive P.unitRep

/-- Unit normalization proves that the vacuum quotient class is nonzero. -/
theorem unit_qmk_ne_zero (P : PositiveTimeOSRoot L G) :
    P.positive.qmk P.unitRep ≠ P.positive.qmk P.positive.zero := by
  intro h
  have hr : P.positive.rad P.unitRep P.positive.zero := Quotient.exact h
  have hz : P.positive.B P.unitRep P.unitRep ≈ 0 :=
    (P.positive.rad_zero_iff P.unitRep).mp hr
  have honezero : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm P.unitNormOne) hz
  exact (by decide : ¬ ((1 : Q') ≈ 0)) honezero

/-- The completed physical vacuum is not the zero vector. -/
theorem physicalVacuum_ne_zero (P : PositiveTimeOSRoot L G) :
    P.physicalVacuum ≠ embedV P.positive P.positive.zero := by
  intro h
  apply P.unit_qmk_ne_zero
  apply embedQuot_injective P.positive
  exact h

/-- The completed physical transfer fixes the derived unit vacuum. -/
theorem completedTransfer_vacuum (P : PositiveTimeOSRoot L G) :
    P.completedTransfer P.physicalVacuum = P.physicalVacuum := by
  refine Eq.trans (P.completedTransfer_embed P.unitRep) ?_
  apply Quotient.sound
  apply embed_null_of_rad P.positive
  have hsub : P.positive.veq
      (P.positive.sub (P.transfer P.unitRep) P.unitRep)
      (P.positive.sub P.unitRep P.unitRep) :=
    P.positive.add_congr P.unitFixed (P.positive.veq_refl _)
  exact Q'.eqv_trans _ _ _ (P.positive.B_diag_congr hsub)
    (P.positive.rad_refl P.unitRep)

/-- Completed transfer FORM-LAW interface over the unconditional completion.

The current completion API has not yet constructed vector operations, so this
record intentionally does not call its map a linear operator: completed
additivity/scalar-linearity require the completion-module bridge listed in the
work plan. -/
structure GeneralTransferFormLaws (D : GNSData)
    (H : CompleteGNSHilbertGeneral D) where
  T : H.hilbert.carrier → H.hilbert.carrier
  vacuum : H.hilbert.carrier
  selfAdjoint : ∀ x y, H.hilbert.cinner (T x) y = H.hilbert.cinner x (T y)
  positive : ∀ x, CReal.RCnonneg (H.hilbert.cinner (T x) x)
  contraction : ∀ x, CReal.RCle
    (H.hilbert.cinner (T x) (T x)) (H.hilbert.cinner x x)

/-- The derived completed physical transfer form laws with nonzero unit vacuum. -/
def physicalTransferFormLaws (P : PositiveTimeOSRoot L G) :
    GeneralTransferFormLaws P.positive P.physicalHilbert where
  T := P.completedTransfer
  vacuum := P.physicalVacuum
  selfAdjoint := P.completedTransfer_selfAdjoint
  positive := P.completedTransfer_positive
  contraction := P.completedTransfer_contraction

/-- The completed transfer map fixes its derived nonzero vacuum. -/
theorem physicalTransferFormLaws_vacuum_fixed (P : PositiveTimeOSRoot L G) :
    P.physicalTransferFormLaws.T P.physicalTransferFormLaws.vacuum =
      P.physicalTransferFormLaws.vacuum :=
  P.completedTransfer_vacuum

end PositiveTimeOSRoot

end YMGap.Continuum.CanonicalOSRoot

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.CanonicalOSRoot.WilsonAmbientTimeReflection.tau_isometry
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.reflected_nonneg
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.unitNormOne
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.unitFixed
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.completedTransfer
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.completedTransfer_selfAdjoint
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.completedTransfer_positive
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.completedTransfer_contraction
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.physicalHilbert
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.unit_qmk_ne_zero
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.physicalVacuum_ne_zero
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.completedTransfer_vacuum
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.physicalTransferFormLaws
#print axioms YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot.physicalTransferFormLaws_vacuum_fixed
