/-
Concrete sufficient mechanisms for the interacting time-halfspace law.

`ReflectionPositivity.ReflectionPositiveSchwinger` proves positivity of an
external, Schur-diagonal heat-kernel form.  Its variables do not include the
interacting `ReferenceWeight`, the observable carrier, or the selected time
action.  Consequently it cannot by itself discharge
`ReferenceWeightTransferConstruction.TimeHalfspaceLaw`.

This module supplies two honest bridges.

* `InteractingMarkovSquareLaw` is the algebraic Markov-semigroup square:
  the reflected interacting form factors through one half-time map.  Its one
  mixed factorization identity implies reflected symmetry and positivity.
* `FiniteCharacterGramLaw` is a finite exact character/Haar resolution of the
  reflected interacting form as a rational Gram sum.  A constructive finite
  sum-of-squares proof then supplies positivity; termwise commutativity
  supplies symmetry.

The final plane theorem banks the precise interface obstruction.  The current
external OS2 predicate holds while the nontrivial, unit-witness, exactly
isometric interacting time action fails `TimeHalfspaceLaw`.  Thus an actual
connector such as either bridge above is mathematically necessary.

All declarations are constructive.  Closed rational facts use kernel
`decide`; axiom dependencies remain contained in `{propext, Quot.sound}`.
-/

import YMGap.Continuum.ReferenceWeightTransferConstruction
import YMGap.Continuum.ReflectionDagger

namespace YMGap.Continuum.InteractingReflectionTimeLaw

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.ReferenceWeightTransferConstruction
open YMGap.Continuum.ReflectionDagger
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-! ## The interacting Markov-semigroup square -/

/-- A concrete half-time factorization of the actual interacting reflected
form.  This is the observable-algebra version of `T = S†S`: both legs are
sent through the same half-time map before the ordinary Wilson form is
evaluated.  It is one coherent mixed-form identity, rather than separate
symmetry and positivity assumptions. -/
structure InteractingMarkovSquareLaw
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))) : Type where
  halfTime : A.carrier → A.carrier
  reflected_factor : ∀ a b,
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) b).eqv
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (halfTime a) (halfTime b))

/-- The Markov square derives both representative halfspace laws.  Symmetry
uses the ordinary Wilson-form symmetry between the two half-time legs;
positivity is the ordinary Wilson Gram positivity of the common half-time
image. -/
def InteractingMarkovSquareLaw.toTimeHalfspaceLaw
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : InteractingMarkovSquareLaw G elin_congr elin_add elin_smul hconj) :
    TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj := by
  let W := G.toWilsonGNSData elin_congr elin_add elin_smul hconj
  refine {
    reflected_symmetric := ?_
    reflected_positive := ?_
  }
  · intro a b
    exact Q'.eqv_trans _ _ _ (L.reflected_factor a b)
      (Q'.eqv_trans _ _ _
        (W.toGNSData.B_symm (L.halfTime a) (L.halfTime b))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (L.reflected_factor b a))
          (W.toGNSData.B_symm (G.action.hom.map b) a)))
  · intro a
    exact OSReconstructionProgress.le_of_le_eqv
      (W.E_self_nonneg (L.halfTime a))
      (Q'.eqv_symm (L.reflected_factor a a))

/-! ## Exact finite character/Haar Gram resolution -/

/-- The finite rational Gram sum of a coordinate map.  In the intended
application `coordinate a s` is the exact finite Haar/character amplitude of
the positive-time observable `a` in mode `s`; no measured value enters. -/
def characterGramSum {V : Type} (coordinate : V → Nat → Q')
    (a b : V) : Nat → Q'
  | 0 => 0
  | n + 1 => characterGramSum coordinate a b n + coordinate a n * coordinate b n

/-- Termwise rational commutativity makes the exact character Gram sum
symmetric. -/
theorem characterGramSum_symm {V : Type} (coordinate : V → Nat → Q')
    (a b : V) : ∀ N,
    characterGramSum coordinate a b N ≈ characterGramSum coordinate b a N
  | 0 => Q'.eqv_refl 0
  | n + 1 =>
      QPoly.q_add_congr
        (characterGramSum_symm coordinate a b n)
        (Q'.mul_comm_eqv (coordinate a n) (coordinate b n))

/-- The diagonal finite character Gram sum is a finite sum of exact rational
squares, hence is nonnegative constructively. -/
theorem characterGramSum_nonneg {V : Type} (coordinate : V → Nat → Q')
    (a : V) : ∀ N, (0 : Q') ≤ characterGramSum coordinate a a N
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _ (characterGramSum_nonneg coordinate a n)
        (SumOfSquares.q_mul_self_nonneg (coordinate a n))

/-- A concrete exact finite-volume character resolution of the *interacting*
reflected Wilson form.  The load-bearing field is a single mixed identity
identifying that form with its derived finite Haar/character Gram sum.  Once
that identity is established for an actual lattice model, positivity and
symmetry are consequences, not further premises. -/
structure FiniteCharacterGramLaw
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))) : Type where
  modeCount : Nat
  coordinate : A.carrier → Nat → Q'
  reflected_character_resolution : ∀ a b,
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) b).eqv
    (characterGramSum coordinate a b modeCount)

/-- An exact finite character/Haar Gram resolution derives the interacting
time-halfspace law. -/
def FiniteCharacterGramLaw.toTimeHalfspaceLaw
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : FiniteCharacterGramLaw G elin_congr elin_add elin_smul hconj) :
    TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj := by
  let W := G.toWilsonGNSData elin_congr elin_add elin_smul hconj
  refine {
    reflected_symmetric := ?_
    reflected_positive := ?_
  }
  · intro a b
    exact Q'.eqv_trans _ _ _ (L.reflected_character_resolution a b)
      (Q'.eqv_trans _ _ _
        (characterGramSum_symm L.coordinate a b L.modeCount)
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (L.reflected_character_resolution b a))
          (W.toGNSData.B_symm (G.action.hom.map b) a)))
  · intro a
    exact OSReconstructionProgress.le_of_le_eqv
      (characterGramSum_nonneg L.coordinate a L.modeCount)
      (Q'.eqv_symm (L.reflected_character_resolution a a))

/-! ## Exact separation of the existing external OS2 interface -/

/-- A bundled, nondegenerate separation result: the already-proved external
Schur-diagonal OS2 predicate coexists with a nonidentity, exactly isometric
interacting action whose unit-norm witness makes the time-halfspace law
impossible. -/
structure ExternalOS2TimeLawSeparation : Type where
  external_markov_square : ∀ s,
    CReal.Equiv (reflWeight 1 (by decide) s)
      (CReal.mul (sqrtReflWeight 1 (by decide) s)
        (sqrtReflWeight 1 (by decide) s))
  externalOS2 : ReflectionPositiveSchwinger 1 (by decide)
  action_nontrivial :
    planeIdentityGeometry.action.hom.map ≠ planeFlipGeometry.action.hom.map
  witness_unit :
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).B planeWitness planeWitness).eqv 1
  action_isometric : ∀ a b : Q' × Q',
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).toGNSData.distSqQ
      (planeFlipGeometry.action.hom.map a)
      (planeFlipGeometry.action.hom.map b)).eqv
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).toGNSData.distSqQ a b)
  no_interacting_time_law :
    TimeHalfspaceLaw planeFlipGeometry plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj → False

/-- The exact plane inhabitant of the separation theorem.  In particular,
`ReflectionPositiveSchwinger` alone cannot imply the interacting
`TimeHalfspaceLaw`; a model-connecting factorization/resolution is required. -/
def planeExternalOS2TimeLawSeparation : ExternalOS2TimeLawSeparation where
  external_markov_square := reflWeight_is_square 1 (by decide)
  externalOS2 := fun N c => reflSchwinger_nonneg_via_square 1 (by decide) c N
  action_nontrivial := planeIdentity_flip_action_ne
  witness_unit := planeWitness_norm_eqv_one
  action_isometric := planeFlip_distSq_isometry
  no_interacting_time_law := planeFlip_no_timeHalfspaceLaw

/-- The nondegenerate plane action also rules out an interacting Markov
square connector: such a connector would construct the forbidden halfspace
law. -/
theorem planeFlip_no_interactingMarkovSquareLaw :
    InteractingMarkovSquareLaw planeFlipGeometry plane_elin_congr
      plane_elin_add plane_elin_smul plane_hconj → False := by
  intro L
  exact planeFlip_no_timeHalfspaceLaw L.toTimeHalfspaceLaw

/-- Likewise, the current external character OS2 theorem cannot secretly be
an exact character resolution of the plane action's interacting reflected
form.  Any such resolution would contradict its unit negative witness. -/
theorem planeFlip_no_finiteCharacterGramLaw :
    FiniteCharacterGramLaw planeFlipGeometry plane_elin_congr
      plane_elin_add plane_elin_smul plane_hconj → False := by
  intro L
  exact planeFlip_no_timeHalfspaceLaw L.toTimeHalfspaceLaw

end YMGap.Continuum.InteractingReflectionTimeLaw

#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.InteractingMarkovSquareLaw.toTimeHalfspaceLaw
#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.characterGramSum_symm
#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.characterGramSum_nonneg
#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.FiniteCharacterGramLaw.toTimeHalfspaceLaw
#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.planeExternalOS2TimeLawSeparation
#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.planeFlip_no_interactingMarkovSquareLaw
#print axioms YMGap.Continuum.InteractingReflectionTimeLaw.planeFlip_no_finiteCharacterGramLaw
