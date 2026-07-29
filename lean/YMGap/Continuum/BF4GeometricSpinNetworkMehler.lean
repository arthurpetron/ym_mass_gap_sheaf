/-
# Geometric BF4 chord contraction and the coupled `(K,S)` Gaussian kernel

The earlier five-holonomy endpoint used a mixed-radix state code followed by
five independent central characters.  That construction was injective, but
it was not the BF4 boundary spin network.  This file builds the geometric
replacement.

* The 24 physical lower spatial plaquettes are read with their oriented
  boundary words.
* The fixed 25-link tree is set to the identity and the remaining 23 links
  are literal quaternion variables.
* Every twice-spin label is evaluated by the corresponding Chebyshev
  character of the noncommutative plaquette word.
* The 18 chord variables complementary to `{0,4,5,6,10}` are integrated by
  the exact normalized `S^3` monomial moment.  The result is a polynomial in
  exactly the twenty real coordinates of five retained SU(2) holonomies.

The second half replaces the uncoupled product heat kernel by the genuine
one-step Gaussian Feynman--Kac/Mehler kernel determined by the symmetric
pair `(K,S)`:

  exp[-(x-y)^T K (x-y)/4 - x^T S x/8 - y^T S y/8].

Here `K24 = 24 K`, so the kinetic coefficient is `1/96`.  Exact LDL
certificates prove both quadratic forms nonnegative.  Consequently the
kernel is a constructive `CReal`, is symmetric, and its tangent action is
coupled in the physical BF4 coordinates.  The three Lie-algebra components
give the full fifteen-dimensional kernel, and its specified imaginary-chart
pullback puts it on the same rational `SU(2)^5` carrier as the geometric
wavefunctions.  The already-proved generalized spectrum and
`BF4GaussianPerronRatio` supply its strict `q₀ < 1/5` spectral certificate.

This is the exact finite polynomial/geometric and Gaussian reference layer.
The compact pullback is not asserted to be a globally injective logarithmic
chart, nor is its fivefold-Haar partition normalization constructed here.
The nonlinear short-time Hilbert--Schmidt convergence from the physical
compact SU(2) kernel to this Gaussian reference also remains open.

## Axiom gate

Finite lists, exact `Q'` algebra, the constructive `S^3` moment, and
constructive `CReal.expNeg` only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
import YMGap.Continuum.BF4GaussianPerronRatio
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS
import YMGap.Constructive.ExpNegCongr

namespace YMGap.Continuum.BF4GeometricSpinNetworkMehler

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4FiveHolonomyGaussian
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4GaussianPerronRatio
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact 5+18 chord partition -/

/-- The eighteen tree-gauge chord coordinates not transmitted by the
temporal cylinder graph. -/
def bf4IntegratedCycleTable : List BF4SpatialCycle :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩,
   ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩,
   ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩,
   ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩,
   ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

theorem bf4IntegratedCycleTable_length :
    bf4IntegratedCycleTable.length = 18 := rfl

theorem bf4IntegratedCycleTable_nodup :
    bf4IntegratedCycleTable.Nodup := by
  decide

theorem transmitted_integrated_disjoint :
    ∀ transmitted, transmitted ∈ bf4TransmittedCycleTable →
      ∀ integrated, integrated ∈ bf4IntegratedCycleTable →
        transmitted ≠ integrated := by
  decide

/-- Every one of the 23 geometric chords is either transmitted or integrated.
This is the exact finite carrier statement behind `23 = 5 + 18`. -/
theorem transmitted_or_integrated (cycle : BF4SpatialCycle) :
    cycle ∈ bf4TransmittedCycleTable ∨
      cycle ∈ bf4IntegratedCycleTable := by
  revert cycle
  decide

/-! ## 2. Polynomial quaternions and oriented plaquette words -/

/-- A quaternion whose four real coordinates are finite rational
polynomials in the 92 coordinates of the 23 chord holonomies. -/
structure PolyQuaternion : Type where
  scalar : RatPoly
  iPart : RatPoly
  jPart : RatPoly
  kPart : RatPoly

namespace PolyQuaternion

def one : PolyQuaternion where
  scalar := polyOne
  iPart := polyZero
  jPart := polyZero
  kPart := polyZero

def coordinateVariable (cycle : Nat) : PolyQuaternion where
  scalar := polyVar (4 * cycle)
  iPart := polyVar (4 * cycle + 1)
  jPart := polyVar (4 * cycle + 2)
  kPart := polyVar (4 * cycle + 3)

def conj (q : PolyQuaternion) : PolyQuaternion where
  scalar := q.scalar
  iPart := polyNeg q.iPart
  jPart := polyNeg q.jPart
  kPart := polyNeg q.kPart

/-- Hamilton multiplication.  This is deliberately noncommutative even
though the scalar coordinate polynomials commute. -/
def mul (q r : PolyQuaternion) : PolyQuaternion where
  scalar :=
    polyAdd (polyMul q.scalar r.scalar)
      (polyNeg
        (polyAdd (polyMul q.iPart r.iPart)
          (polyAdd (polyMul q.jPart r.jPart)
            (polyMul q.kPart r.kPart))))
  iPart :=
    polyAdd (polyMul q.scalar r.iPart)
      (polyAdd (polyMul q.iPart r.scalar)
        (polyAdd (polyMul q.jPart r.kPart)
          (polyNeg (polyMul q.kPart r.jPart))))
  jPart :=
    polyAdd (polyMul q.scalar r.jPart)
      (polyAdd (polyMul q.jPart r.scalar)
        (polyAdd (polyMul q.kPart r.iPart)
          (polyNeg (polyMul q.iPart r.kPart))))
  kPart :=
    polyAdd (polyMul q.scalar r.kPart)
      (polyAdd (polyMul q.kPart r.scalar)
        (polyAdd (polyMul q.iPart r.jPart)
          (polyNeg (polyMul q.jPart r.iPart))))

end PolyQuaternion

/-- Exact rational value of a polynomial quaternion at an environment. -/
structure QuaternionValue : Type where
  scalar : Q'
  iPart : Q'
  jPart : Q'
  kPart : Q'

namespace QuaternionValue

def one : QuaternionValue := ⟨1, 0, 0, 0⟩

def conj (q : QuaternionValue) : QuaternionValue :=
  ⟨q.scalar, -q.iPart, -q.jPart, -q.kPart⟩

def mul (q r : QuaternionValue) : QuaternionValue where
  scalar :=
    q.scalar * r.scalar +
      -(q.iPart * r.iPart +
        (q.jPart * r.jPart + q.kPart * r.kPart))
  iPart :=
    q.scalar * r.iPart +
      (q.iPart * r.scalar +
        (q.jPart * r.kPart + -(q.kPart * r.jPart)))
  jPart :=
    q.scalar * r.jPart +
      (q.jPart * r.scalar +
        (q.kPart * r.iPart + -(q.iPart * r.kPart)))
  kPart :=
    q.scalar * r.kPart +
      (q.kPart * r.scalar +
        (q.iPart * r.jPart + -(q.jPart * r.iPart)))

structure Eqv (q r : QuaternionValue) : Prop where
  scalar : q.scalar ≈ r.scalar
  iPart : q.iPart ≈ r.iPart
  jPart : q.jPart ≈ r.jPart
  kPart : q.kPart ≈ r.kPart

end QuaternionValue

def evalPolyQuaternion
    (rho : Nat → Q') (q : PolyQuaternion) : QuaternionValue :=
  ⟨evalRatPoly rho q.scalar,
   evalRatPoly rho q.iPart,
   evalRatPoly rho q.jPart,
   evalRatPoly rho q.kPart⟩

theorem evalRatPoly_neg (rho : Nat → Q') :
    ∀ polynomial : RatPoly,
      evalRatPoly rho (polyNeg polynomial) ≈
        -(evalRatPoly rho polynomial)
  | [] => by
      change (0 : Q') ≈ -0
      decide
  | term :: rest => by
      unfold polyNeg List.map evalRatPoly
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.neg_mul_eqv term.2
            (evalMono rho term.1))
          (evalRatPoly_neg rho rest)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv_split
          (term.2 * evalMono rho term.1)
          (evalRatPoly rho rest))

private theorem evalRatPoly_threeProducts
    (rho : Nat → Q')
    (a b c d e f : RatPoly) :
    evalRatPoly rho
        (polyAdd (polyMul a b)
          (polyAdd (polyMul c d) (polyMul e f))) ≈
      evalRatPoly rho a * evalRatPoly rho b +
        (evalRatPoly rho c * evalRatPoly rho d +
          evalRatPoly rho e * evalRatPoly rho f) := by
  refine Q'.eqv_trans _ _ _
    (evalRatPoly_add rho _ _) ?_
  exact Q'.add_eqv_congr'
    (evalRatPoly_mul rho a b)
    (Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr'
        (evalRatPoly_mul rho c d)
        (evalRatPoly_mul rho e f)))

theorem evalPolyQuaternion_one (rho : Nat → Q') :
    QuaternionValue.Eqv
      (evalPolyQuaternion rho PolyQuaternion.one)
      QuaternionValue.one := by
  exact
    ⟨evalRatPoly_one rho,
     Q'.eqv_refl 0,
     Q'.eqv_refl 0,
     Q'.eqv_refl 0⟩

theorem evalPolyQuaternion_conj
    (rho : Nat → Q') (q : PolyQuaternion) :
    QuaternionValue.Eqv
      (evalPolyQuaternion rho (PolyQuaternion.conj q))
      (QuaternionValue.conj (evalPolyQuaternion rho q)) := by
  exact
    ⟨Q'.eqv_refl _,
     evalRatPoly_neg rho q.iPart,
     evalRatPoly_neg rho q.jPart,
     evalRatPoly_neg rho q.kPart⟩

/-- **Hamilton semantic certificate.**  Polynomial-quaternion
multiplication evaluates to literal noncommutative Hamilton multiplication
in every rational environment. -/
theorem evalPolyQuaternion_mul
    (rho : Nat → Q') (q r : PolyQuaternion) :
    QuaternionValue.Eqv
      (evalPolyQuaternion rho (PolyQuaternion.mul q r))
      (QuaternionValue.mul
        (evalPolyQuaternion rho q)
        (evalPolyQuaternion rho r)) := by
  constructor
  · refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    exact Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.scalar r.scalar)
      (Q'.eqv_trans _ _ _
        (evalRatPoly_neg rho _)
        (Q'.neg_eqv_congr _ _
          (evalRatPoly_threeProducts rho
            q.iPart r.iPart
            q.jPart r.jPart
            q.kPart r.kPart)))
  · refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    refine Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.scalar r.iPart) ?_
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    refine Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.iPart r.scalar) ?_
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    exact Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.jPart r.kPart)
      (Q'.eqv_trans _ _ _
        (evalRatPoly_neg rho _)
        (Q'.neg_eqv_congr _ _
          (evalRatPoly_mul rho q.kPart r.jPart)))
  · refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    refine Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.scalar r.jPart) ?_
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    refine Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.jPart r.scalar) ?_
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    exact Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.kPart r.iPart)
      (Q'.eqv_trans _ _ _
        (evalRatPoly_neg rho _)
        (Q'.neg_eqv_congr _ _
          (evalRatPoly_mul rho q.iPart r.kPart)))
  · refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    refine Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.scalar r.kPart) ?_
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    refine Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.kPart r.scalar) ?_
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _) ?_
    exact Q'.add_eqv_congr'
      (evalRatPoly_mul rho q.iPart r.jPart)
      (Q'.eqv_trans _ _ _
        (evalRatPoly_neg rho _)
        (Q'.neg_eqv_congr _ _
          (evalRatPoly_mul rho q.jPart r.iPart)))

/-- An oriented positive lattice link.  `reverse = true` means that the
inverse holonomy is read in the plaquette word. -/
structure OrientedBF4Link : Type where
  link : Z4Link
  reverse : Bool

/-- The positively oriented plaquette boundary
`U_a(v) U_b(v+e_a) U_a(v+e_b)⁻¹ U_b(v)⁻¹`. -/
def orientedPlaquetteBoundary (face : Z4Plaq) : List OrientedBF4Link :=
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  [{ link := (face.1, a), reverse := false },
   { link := (addE face.1 a, b), reverse := false },
   { link := (addE face.1 b, a), reverse := true },
   { link := (face.1, b), reverse := true }]

theorem orientedPlaquetteBoundary_length (face : Z4Plaq) :
    (orientedPlaquetteBoundary face).length = 4 := by
  rfl

/-- Tree-gauge value of a positive boundary link.  Tree links are identity;
chord links are the matching one of the 23 polynomial quaternions. -/
def treeGaugeLinkPolynomial (link : Z4Link) : PolyQuaternion :=
  if link ∈ bf4SpatialChordLinks then
    PolyQuaternion.coordinateVariable (bf4SpatialChordLinks.idxOf link)
  else PolyQuaternion.one

/-- Closed finite proof that the displayed chord list and `idxOf` use the
same coordinate order. -/
theorem bf4SpatialChord_idxOf
    (cycle : BF4SpatialCycle) :
    bf4SpatialChordLinks.idxOf (bf4SpatialChord cycle) =
      cycle.val := by
  revert cycle
  decide

/-- Each literal geometric chord is sent to its own quaternion-variable
block.  This closes the otherwise easy-to-miss `idxOf` indexing obligation. -/
theorem treeGaugeLinkPolynomial_chord
    (cycle : BF4SpatialCycle) :
    treeGaugeLinkPolynomial (bf4SpatialChord cycle) =
      PolyQuaternion.coordinateVariable cycle.val := by
  have hmem :
      bf4SpatialChord cycle ∈ bf4SpatialChordLinks :=
    List.get_mem bf4SpatialChordLinks
      ⟨cycle.val, by
        rw [bf4SpatialChordLinks_length]
        exact cycle.isLt⟩
  unfold treeGaugeLinkPolynomial
  rw [if_pos hmem, bf4SpatialChord_idxOf cycle]

def orientedTreeGaugeLinkPolynomial
    (entry : OrientedBF4Link) : PolyQuaternion :=
  if entry.reverse then
    PolyQuaternion.conj (treeGaugeLinkPolynomial entry.link)
  else treeGaugeLinkPolynomial entry.link

/-- The literal noncommutative tree-gauge plaquette holonomy word. -/
def treeGaugePlaquettePolynomial (face : Z4Plaq) : PolyQuaternion :=
  (orientedPlaquetteBoundary face).foldl
    (fun total entry =>
      PolyQuaternion.mul total
        (orientedTreeGaugeLinkPolynomial entry))
    PolyQuaternion.one

/-! ## 3. All-spin characters and the 24-face spin network -/

/-- The second-kind Chebyshev character applied inside the multivariate
polynomial algebra.  No spin cutoff is present. -/
def characterPolynomial (x : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | 1 => polySmul 2 x
  | n + 2 =>
      polyAdd
        (polyMul (polySmul 2 x) (characterPolynomial x (n + 1)))
        (polySmul (-1) (characterPolynomial x n))

/-- The multivariate character polynomial evaluates to the genuine SU(2)
character at the scalar part of the quaternion word. -/
theorem eval_characterPolynomial
    (rho : Nat → Q') (x : RatPoly) :
    ∀ spin,
      evalRatPoly rho (characterPolynomial x spin) ≈
        Cheb.U spin (evalRatPoly rho x)
  | 0 => by
      rw [Cheb.U_zero]
      exact evalRatPoly_one rho
  | 1 => by
      rw [Cheb.U_one]
      exact evalRatPoly_smul rho 2 x
  | spin + 2 => by
      rw [characterPolynomial, Cheb.U_succ_succ]
      refine Q'.eqv_trans _ _ _
        (evalRatPoly_add rho _ _) ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · refine Q'.eqv_trans _ _ _
          (evalRatPoly_mul rho
            (polySmul 2 x)
            (characterPolynomial x (spin + 1))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (evalRatPoly_smul rho 2 x)) ?_
        exact Q'.mul_eqv_congr_left
          (2 * evalRatPoly rho x) _ _
          (eval_characterPolynomial rho x (spin + 1))
      · refine Q'.eqv_trans _ _ _
          (evalRatPoly_smul rho (-1)
            (characterPolynomial x spin)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.neg_mul_eqv 1
            (evalRatPoly rho (characterPolynomial x spin))) ?_
        exact Q'.neg_eqv_congr _ _
          (Q'.eqv_trans _ _ _
            (Q'.one_mul_eqv
              (evalRatPoly rho (characterPolynomial x spin)))
            (eval_characterPolynomial rho x spin))

/-- Character factor of one physical BF4 spatial plaquette. -/
def plaquetteSpinFactor
    (faceLabel : Z4Plaq → Nat) (face : Z4Plaq) : RatPoly :=
  characterPolynomial
    (treeGaugePlaquettePolynomial face).scalar
    (faceLabel face)

/-- The pre-contraction spin-network integrand on all 23 chord holonomies. -/
def bf4SpatialSpinNetworkIntegrand
    (faceLabel : Z4Plaq → Nat) : RatPoly :=
  bf4SourceSpatialFaces.foldr
    (fun face total =>
      polyMul (plaquetteSpinFactor faceLabel face) total)
    polyOne

/-! ## 4. Exact Haar contraction of the eighteen forgotten chords -/

def chordMoment (monomial : List Nat)
    (cycle : BF4SpatialCycle) : Q' :=
  sphereMoment4
    (exponentAt monomial (4 * cycle.val))
    (exponentAt monomial (4 * cycle.val + 1))
    (exponentAt monomial (4 * cycle.val + 2))
    (exponentAt monomial (4 * cycle.val + 3))

def integratedChordMoment (monomial : List Nat) : Q' :=
  bf4IntegratedCycleTable.foldr
    (fun cycle total => chordMoment monomial cycle * total)
    1

/-- Reindex a 92-variable chord monomial onto the five retained quaternion
blocks, in the physical order `{0,4,5,6,10}`. -/
def retainedFiveMonomial (monomial : List Nat) : List Nat :=
  [exponentAt monomial 0, exponentAt monomial 1,
   exponentAt monomial 2, exponentAt monomial 3,
   exponentAt monomial 16, exponentAt monomial 17,
   exponentAt monomial 18, exponentAt monomial 19,
   exponentAt monomial 20, exponentAt monomial 21,
   exponentAt monomial 22, exponentAt monomial 23,
   exponentAt monomial 24, exponentAt monomial 25,
   exponentAt monomial 26, exponentAt monomial 27,
   exponentAt monomial 40, exponentAt monomial 41,
   exponentAt monomial 42, exponentAt monomial 43]

theorem retainedFiveMonomial_length (monomial : List Nat) :
    (retainedFiveMonomial monomial).length = 20 := rfl

def integrateEighteenChordTerm (term : RatTerm) : RatTerm :=
  (retainedFiveMonomial term.1,
    term.2 * integratedChordMoment term.1)

/-- Exact normalized product-Haar integration over the eighteen
non-transmitted `S^3` chord variables. -/
def integrateEighteenChords (polynomial : RatPoly) : RatPoly :=
  polynomial.map integrateEighteenChordTerm

/-- Direct semantic evaluation of a polynomial after normalized Haar
integration in the eighteen forgotten quaternion blocks.  The retained
environment has twenty coordinates, while every forgotten block is replaced
by its exact normalized `S³` monomial moment. -/
def conditionalEighteenChordHaarEval
    (retainedEnvironment : Nat → Q') : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      term.2 *
          (integratedChordMoment term.1 *
            evalMono retainedEnvironment
              (retainedFiveMonomial term.1)) +
        conditionalEighteenChordHaarEval
          retainedEnvironment rest

/-- **Exact partial-Haar semantics.**  The syntactic eighteen-chord
contraction evaluates to the direct iterated normalized-Haar functional.
Thus `integrateEighteenChords` is not a projection table: its coefficient on
every source monomial is the product of the eighteen exact `S³` moments. -/
theorem eval_integrateEighteenChords
    (retainedEnvironment : Nat → Q') :
    ∀ polynomial : RatPoly,
      evalRatPoly retainedEnvironment
          (integrateEighteenChords polynomial) ≈
        conditionalEighteenChordHaarEval
          retainedEnvironment polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      unfold integrateEighteenChords List.map evalRatPoly
        integrateEighteenChordTerm conditionalEighteenChordHaarEval
      exact Q'.add_eqv_congr'
        (Q'.mul_assoc_eqv term.2
          (integratedChordMoment term.1)
          (evalMono retainedEnvironment
            (retainedFiveMonomial term.1)))
        (eval_integrateEighteenChords retainedEnvironment rest)

/-- A polynomial is supported on the twenty real coordinates of the five
retained quaternion holonomies. -/
def SupportedOnRetainedFive (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    allZero (term.1.drop 20) = true

theorem integrateEighteenChords_supported
    (polynomial : RatPoly) :
    SupportedOnRetainedFive
      (integrateEighteenChords polynomial) := by
  intro term hterm
  simp only [integrateEighteenChords, List.mem_map] at hterm
  rcases hterm with ⟨source, _, rfl⟩
  simp [integrateEighteenChordTerm, retainedFiveMonomial, allZero]

/-- The geometric all-spin BF4 five-holonomy wavefunction.  The magnetic
and intertwiner contractions are not inserted by a table: they are the exact
result of the eighteen normalized Haar moments. -/
def geometricBF4Wavefunction
    (faceLabel : Z4Plaq → Nat) : RatPoly :=
  integrateEighteenChords
    (bf4SpatialSpinNetworkIntegrand faceLabel)

private theorem bf4SpatialSpinNetworkIntegrand_vacuum :
    bf4SpatialSpinNetworkIntegrand (fun _ => 0) = polyOne := by
  rfl

private theorem evalMono_retainedZero
    (rho : Nat → Q') :
    evalMono rho (retainedFiveMonomial []) ≈ 1 := by
  change
    evalMonoFrom rho 0
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≈ 1
  simp only [evalMonoFrom, qpow_zero]
  decide

private theorem integratedChordMoment_empty :
    integratedChordMoment [] ≈ 1 := by
  decide

private theorem conditionalEighteenChordHaarEval_one
    (rho : Nat → Q') :
    conditionalEighteenChordHaarEval rho polyOne ≈ 1 := by
  unfold conditionalEighteenChordHaarEval polyOne
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 1 _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            integratedChordMoment_empty)
          (Q'.one_mul_eqv
            (evalMono rho (retainedFiveMonomial [])))))
      (Q'.eqv_refl 0)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.one_mul_eqv
        (evalMono rho (retainedFiveMonomial [])))
      (Q'.eqv_refl 0))
    (Q'.eqv_trans _ _ _
      (QPoly.q_add_zero_eqv
        (evalMono rho (retainedFiveMonomial [])))
      (evalMono_retainedZero rho))

theorem geometricBF4Wavefunction_supported
    (faceLabel : Z4Plaq → Nat) :
    SupportedOnRetainedFive
      (geometricBF4Wavefunction faceLabel) :=
  integrateEighteenChords_supported _

/-- Evaluation of the geometric wavefunction is literally the normalized
eighteen-chord partial Haar integral of the product of the twenty-four
oriented plaquette characters. -/
theorem eval_geometricBF4Wavefunction
    (retainedEnvironment : Nat → Q')
    (faceLabel : Z4Plaq → Nat) :
    evalRatPoly retainedEnvironment
        (geometricBF4Wavefunction faceLabel) ≈
      conditionalEighteenChordHaarEval
        retainedEnvironment
        (bf4SpatialSpinNetworkIntegrand faceLabel) :=
  eval_integrateEighteenChords retainedEnvironment _

/-- The all-vacuum spin network evaluates to the normalized constant
wavefunction.  This checks both character normalization and all eighteen
zero-degree Haar moments. -/
theorem eval_geometricBF4Wavefunction_vacuum
    (rho : Nat → Q') :
    evalRatPoly rho
        (geometricBF4Wavefunction (fun _ => 0)) ≈ 1 := by
  refine Q'.eqv_trans _ _ _
    (eval_geometricBF4Wavefunction rho (fun _ => 0)) ?_
  rw [bf4SpatialSpinNetworkIntegrand_vacuum]
  exact conditionalEighteenChordHaarEval_one rho

theorem bf4SourceSpatialFace_mem_boundary
    (face : Z4Plaq)
    (hface : face ∈ bf4SourceSpatialFaces) :
    face ∈ boundaryCompleteSlabPlaquettes 1 := by
  exact (List.mem_filter.mp hface).1

/-- Pull the 24 geometric labels from a physical face labelling using the
actual corrected one-slab face enumeration.  This deliberately fixes extent
one: using an arbitrary extent here would silently send an absent face to
`idxOf = 0` and would not be the BF4 boundary transform. -/
def geometricBF4WavefunctionOfState
    (state :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    RatPoly :=
  geometricBF4Wavefunction
    (fun face =>
      state ((boundaryCompleteSlabPlaquettes 1).idxOf face))

/-- Flatten the five retained rational unit quaternions into the twenty
coordinates used by the contracted polynomial. -/
def retainedFiveEnvironment
    (configuration : BF4FiveHolonomyConfiguration)
    (index : Nat) : Q' :=
  if hindex : index < 20 then
    (configuration
      ⟨index / 4, by omega⟩).quaternion.coordinate
        ⟨index % 4, Nat.mod_lt _ (by decide)⟩
  else 0

/-- Same-carrier point value of the geometric BF4 boundary spin network on
the literal five retained `SU(2)` holonomies. -/
def geometricBF4WavefunctionValue
    (state :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (configuration : BF4FiveHolonomyConfiguration) : Q' :=
  evalRatPoly
    (retainedFiveEnvironment configuration)
    (geometricBF4WavefunctionOfState state)

/-- The same-carrier value retains the exact eighteen-chord Haar semantics. -/
theorem geometricBF4WavefunctionValue_eq_partialHaar
    (state :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (configuration : BF4FiveHolonomyConfiguration) :
    geometricBF4WavefunctionValue state configuration ≈
      conditionalEighteenChordHaarEval
        (retainedFiveEnvironment configuration)
        (bf4SpatialSpinNetworkIntegrand
          (fun face =>
            state
              ((boundaryCompleteSlabPlaquettes 1).idxOf face))) := by
  exact eval_geometricBF4Wavefunction _ _

/-! ## 5. Exact fivefold Haar pairing on the retained carrier -/

/-- Exact normalized `SU(2)^5 = (S³)^5` moment of one twenty-coordinate
monomial. -/
def fivefoldHaarMono (monomial : List Nat) : Q' :=
  if allZero (monomial.drop 20) then
    sphereMoment4
        (exponentAt monomial 0) (exponentAt monomial 1)
        (exponentAt monomial 2) (exponentAt monomial 3) *
      (sphereMoment4
          (exponentAt monomial 4) (exponentAt monomial 5)
          (exponentAt monomial 6) (exponentAt monomial 7) *
        (sphereMoment4
            (exponentAt monomial 8) (exponentAt monomial 9)
            (exponentAt monomial 10) (exponentAt monomial 11) *
          (sphereMoment4
              (exponentAt monomial 12) (exponentAt monomial 13)
              (exponentAt monomial 14) (exponentAt monomial 15) *
            sphereMoment4
              (exponentAt monomial 16) (exponentAt monomial 17)
              (exponentAt monomial 18) (exponentAt monomial 19))))
  else 0

/-- Exact fivefold normalized-Haar functional on finite rational
twenty-coordinate polynomials. -/
def fivefoldHaar : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      term.2 * fivefoldHaarMono term.1 + fivefoldHaar rest

theorem fivefoldHaar_one :
    fivefoldHaar polyOne ≈ 1 := by
  decide

/-- Real Haar pairing of two retained polynomial wavefunctions. -/
def fivefoldHaarInner
    (left right : RatPoly) : Q' :=
  fivefoldHaar (polyMul left right)

/-- The geometric vacuum has exact unit fivefold Haar norm. -/
theorem geometricBF4Wavefunction_vacuum_normalized :
    fivefoldHaarInner
        (geometricBF4Wavefunction (fun _ => 0))
        (geometricBF4Wavefunction (fun _ => 0)) ≈
      1 := by
  decide

/-! ## 6. The coupled symmetric-pair Gaussian action -/

def vectorSub (x y : Vector5) : Vector5 :=
  fun coordinate => x coordinate - y coordinate

private def sq (x : Q') : Q' := x * x

private def spatialQuadraticExpr : PolyExpr :=
  .add
    (.mul (.const 2) (.mul (.var 0) (.var 0)))
    (.add
      (.mul (.const 2) (.mul (.var 1) (.var 1)))
      (.add
        (.mul (.const 2) (.mul (.var 2) (.var 2)))
        (.add
          (.mul (.const 2) (.mul (.var 3) (.var 3)))
          (.add
            (.mul (.const 2) (.mul (.var 4) (.var 4)))
            (.add
              (.mul (.const (-2)) (.mul (.var 0) (.var 4)))
              (.add
                (.mul (.const (-2)) (.mul (.var 1) (.var 2)))
                (.add
                  (.mul (.const (-2)) (.mul (.var 1) (.var 3)))
                  (.add
                    (.mul (.const 2) (.mul (.var 1) (.var 4)))
                    (.add
                      (.mul (.const 2) (.mul (.var 2) (.var 3)))
                      (.add
                        (.mul (.const (-2)) (.mul (.var 2) (.var 4)))
                        (.mul (.const (-2))
                          (.mul (.var 3) (.var 4)))))))))))))

private def spatialLDLClearedExpr : PolyExpr :=
  let z0 := .add (.mul (.const 2) (.var 0)) (.neg (.var 4))
  let z1 := .add
    (.add (.add (.mul (.const 2) (.var 1)) (.neg (.var 2)))
      (.neg (.var 3))) (.var 4)
  let z2 := .add
    (.add (.mul (.const 3) (.var 2)) (.var 3)) (.neg (.var 4))
  let z3 := .add (.mul (.const 4) (.var 3)) (.neg (.var 4))
  .add
    (.mul (.const 24) (.mul z0 z0))
    (.add
      (.mul (.const 24) (.mul z1 z1))
      (.add
        (.mul (.const 8) (.mul z2 z2))
        (.add
          (.mul (.const 4) (.mul z3 z3))
          (.mul (.const 36) (.mul (.var 4) (.var 4))))))

private theorem spatial_ldl_normal :
    normalize (.mul (.const 48) spatialQuadraticExpr) =
      normalize spatialLDLClearedExpr := by
  decide

private def kineticQuadraticExpr : PolyExpr :=
  let x0 := .var 0; let x1 := .var 1; let x2 := .var 2
  let x3 := .var 3; let x4 := .var 4
  .add (.mul (.const 10) (.mul x0 x0))
    (.add (.mul (.const 10) (.mul x1 x1))
      (.add (.mul (.const 10) (.mul x2 x2))
        (.add (.mul (.const 10) (.mul x3 x3))
          (.add (.mul (.const 10) (.mul x4 x4))
            (.add (.mul (.const 2) (.mul x0 x1))
              (.add (.mul (.const (-4)) (.mul x0 x2))
                (.add (.mul (.const (-2)) (.mul x0 x3))
                  (.add (.mul (.const (-8)) (.mul x0 x4))
                    (.add (.mul (.const (-10)) (.mul x1 x2))
                      (.add (.mul (.const (-8)) (.mul x1 x3))
                        (.add (.mul (.const 10) (.mul x1 x4))
                          (.add (.mul (.const 10) (.mul x2 x3))
                            (.add (.mul (.const (-8)) (.mul x2 x4))
                              (.mul (.const (-10))
                                (.mul x3 x4)))))))))))))))

private def kineticLDLClearedExpr : PolyExpr :=
  let z0 := .add
    (.add
      (.add
        (.add (.mul (.const 10) (.var 0)) (.var 1))
        (.mul (.const (-2)) (.var 2)))
      (.neg (.var 3)))
    (.mul (.const (-4)) (.var 4))
  let z1 := .add
    (.add
      (.add (.mul (.const 33) (.var 1))
        (.mul (.const (-16)) (.var 2)))
      (.mul (.const (-13)) (.var 3)))
    (.mul (.const 18) (.var 4))
  let z2 := .add
    (.add (.mul (.const 10) (.var 2))
      (.mul (.const 4) (.var 3)))
    (.mul (.const (-3)) (.var 4))
  let z3 := .add (.mul (.const 3) (.var 3)) (.neg (.var 4))
  .add
    (.mul (.const 10890) (.mul z0 z0))
    (.add
          (.mul (.const 990) (.mul z1 z1))
      (.add
        (.mul (.const 7920) (.mul z2 z2))
        (.add
          (.mul (.const 87120) (.mul z3 z3))
          (.mul (.const 435600)
            (.mul (.var 4) (.var 4))))))

private theorem kinetic_ldl_normal :
    normalize (.mul (.const 108900) kineticQuadraticExpr) =
      normalize kineticLDLClearedExpr := by
  decide

/-- The rational environment of one five-vector. -/
def vectorEnvironment (x : Vector5) (index : Nat) : Q' :=
  if h : index < 5 then x ⟨index, h⟩ else 0

/-- The exact coordinate expansion of `xᵀ S x`. -/
def spatialQuadratic (x : Vector5) : Q' :=
  RingNormaliser.eval (vectorEnvironment x) spatialQuadraticExpr

/-- The exact coordinate expansion of `xᵀ K24 x`. -/
def kineticQuadratic24 (x : Vector5) : Q' :=
  RingNormaliser.eval (vectorEnvironment x) kineticQuadraticExpr

def spatialLDLClearedValue (x : Vector5) : Q' :=
  RingNormaliser.eval (vectorEnvironment x) spatialLDLClearedExpr

def kineticLDLClearedValue (x : Vector5) : Q' :=
  RingNormaliser.eval (vectorEnvironment x) kineticLDLClearedExpr

/-- Division-free exact LDL certificate `48 xᵀSx = SOS_S(x)`. -/
theorem spatialQuadratic_scaled_eq_ldl (x : Vector5) :
    (48 : Q') * spatialQuadratic x ≈
      spatialLDLClearedValue x := by
  exact poly_identity_of_normal_eq
    (.mul (.const 48) spatialQuadraticExpr)
    spatialLDLClearedExpr spatial_ldl_normal
    (vectorEnvironment x)

/-- Division-free exact LDL certificate
`108900 xᵀK24x = SOS_K(x)`. -/
theorem kineticQuadratic24_scaled_eq_ldl (x : Vector5) :
    (108900 : Q') * kineticQuadratic24 x ≈
      kineticLDLClearedValue x := by
  exact poly_identity_of_normal_eq
    (.mul (.const 108900) kineticQuadraticExpr)
    kineticLDLClearedExpr kinetic_ldl_normal
    (vectorEnvironment x)

theorem spatialLDLClearedValue_nonnegative (x : Vector5) :
    (0 : Q') ≤ spatialLDLClearedValue x := by
  unfold spatialLDLClearedValue vectorEnvironment
  simp only [spatialLDLClearedExpr, RingNormaliser.eval]
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (SumOfSquares.q_mul_self_nonneg _))
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide)
        (SumOfSquares.q_mul_self_nonneg _))
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide)
          (SumOfSquares.q_mul_self_nonneg _))
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ (by decide)
            (SumOfSquares.q_mul_self_nonneg _))
          (Q'.mul_nonneg _ _ (by decide)
            (SumOfSquares.q_mul_self_nonneg _)))))

theorem kineticLDLClearedValue_nonnegative (x : Vector5) :
    (0 : Q') ≤ kineticLDLClearedValue x := by
  unfold kineticLDLClearedValue vectorEnvironment
  simp only [kineticLDLClearedExpr, RingNormaliser.eval]
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (SumOfSquares.q_mul_self_nonneg _))
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide)
        (SumOfSquares.q_mul_self_nonneg _))
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide)
          (SumOfSquares.q_mul_self_nonneg _))
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ (by decide)
            (SumOfSquares.q_mul_self_nonneg _))
          (Q'.mul_nonneg _ _ (by decide)
            (SumOfSquares.q_mul_self_nonneg _)))))

theorem spatialQuadratic_nonnegative (x : Vector5) :
    (0 : Q') ≤ spatialQuadratic x := by
  have hscaled :
      (0 : Q') ≤ (48 : Q') * spatialQuadratic x :=
    Q'.le_trans' _ _ _
      (spatialLDLClearedValue_nonnegative x)
      (Q'.le_of_eqv
        (Q'.eqv_symm (spatialQuadratic_scaled_eq_ldl x)))
  apply Q'.le_of_mul_le_mul_left (c := (48 : Q'))
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv 48))
      hscaled
  · decide

theorem kineticQuadratic24_nonnegative (x : Vector5) :
    (0 : Q') ≤ kineticQuadratic24 x := by
  have hscaled :
      (0 : Q') ≤ (108900 : Q') * kineticQuadratic24 x :=
    Q'.le_trans' _ _ _
      (kineticLDLClearedValue_nonnegative x)
      (Q'.le_of_eqv
        (Q'.eqv_symm (kineticQuadratic24_scaled_eq_ldl x)))
  apply Q'.le_of_mul_le_mul_left (c := (108900 : Q'))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.zero_mul_eqv 108900)) hscaled
  · decide

def oneOver96 : Q' := Q'.mkPos 1 96 (by decide)
def oneOver8 : Q' := Q'.mkPos 1 8 (by decide)

/-- The exact coupled one-step BF4 Gaussian Feynman--Kac action. -/
def coupledBF4Action (source target : Vector5) : Q' :=
  oneOver96 * kineticQuadratic24 (vectorSub source target) +
    (oneOver8 * spatialQuadratic source +
      oneOver8 * spatialQuadratic target)

theorem coupledBF4Action_nonnegative
    (source target : Vector5) :
    (0 : Q') ≤ coupledBF4Action source target := by
  unfold coupledBF4Action
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (kineticQuadratic24_nonnegative _))
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide)
        (spatialQuadratic_nonnegative _))
      (Q'.mul_nonneg _ _ (by decide)
        (spatialQuadratic_nonnegative _)))

/-- The coupled `(K,S)` Feynman--Kac/Mehler kernel, up to the irrelevant
positive normalization scalar. -/
def coupledBF4MehlerKernel
    (source target : Vector5) : CReal :=
  ExpNeg.expNeg
    (coupledBF4Action source target)
    (coupledBF4Action_nonnegative source target)

private theorem vectorSub_swap_neg
    (source target : Vector5) :
    ∀ coordinate,
      vectorSub target source coordinate ≈
        -(vectorSub source target coordinate) := by
  intro coordinate
  unfold vectorSub
  exact Q'.eqv_symm
    (Q'.neg_sub_eqv (source coordinate) (target coordinate))

private def vectorNeg (x : Vector5) : Vector5 :=
  fun coordinate => -(x coordinate)

private theorem eval_eqv_congr
    (expression : PolyExpr) {rho sigma : Nat → Q'}
    (henv : ∀ index, rho index ≈ sigma index) :
    RingNormaliser.eval rho expression ≈
      RingNormaliser.eval sigma expression := by
  induction expression with
  | const _ => exact Q'.eqv_refl _
  | var index => exact henv index
  | add left right ihLeft ihRight =>
      exact Q'.add_eqv_congr' ihLeft ihRight
  | mul left right ihLeft ihRight =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ ihLeft)
        (Q'.mul_eqv_congr_left _ _ _ ihRight)
  | neg value ih =>
      exact Q'.neg_eqv_congr _ _ ih
  | pow value power ih =>
      exact RingNormaliser.qpow_eqv_congr ih power

private theorem kineticQuadratic24_congr
    {left right : Vector5}
    (h : ∀ coordinate, left coordinate ≈ right coordinate) :
    kineticQuadratic24 left ≈ kineticQuadratic24 right := by
  unfold kineticQuadratic24
  apply eval_eqv_congr
  intro index
  unfold vectorEnvironment
  split
  · exact h _
  · exact Q'.eqv_refl 0

private def negateVariables : PolyExpr → PolyExpr
  | .const coefficient => .const coefficient
  | .var index => .neg (.var index)
  | .add left right =>
      .add (negateVariables left) (negateVariables right)
  | .mul left right =>
      .mul (negateVariables left) (negateVariables right)
  | .neg value => .neg (negateVariables value)
  | .pow value power => .pow (negateVariables value) power

private theorem kinetic_even_normal :
    normalize kineticQuadraticExpr =
      normalize (negateVariables kineticQuadraticExpr) := by
  decide

private theorem kineticQuadratic24_neg (x : Vector5) :
    kineticQuadratic24 x ≈ kineticQuadratic24 (vectorNeg x) := by
  have hnormal := poly_identity_of_normal_eq
    kineticQuadraticExpr
    (negateVariables kineticQuadraticExpr)
    kinetic_even_normal
    (vectorEnvironment x)
  simpa [kineticQuadratic24, vectorEnvironment, vectorNeg,
    kineticQuadraticExpr, negateVariables, RingNormaliser.eval] using hnormal

theorem kineticQuadratic24_sub_symmetric
    (source target : Vector5) :
    kineticQuadratic24 (vectorSub source target) ≈
      kineticQuadratic24 (vectorSub target source) := by
  have hswap :
      kineticQuadratic24 (vectorSub target source) ≈
        kineticQuadratic24 (vectorNeg (vectorSub source target)) :=
    kineticQuadratic24_congr (vectorSub_swap_neg source target)
  exact Q'.eqv_trans _ _ _
    (kineticQuadratic24_neg (vectorSub source target))
    (Q'.eqv_symm hswap)

theorem coupledBF4Action_symmetric
    (source target : Vector5) :
    coupledBF4Action source target ≈
      coupledBF4Action target source := by
  unfold coupledBF4Action
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left oneOver96 _ _
      (kineticQuadratic24_sub_symmetric source target))
    (Q'.add_comm_eqv
      (oneOver8 * spatialQuadratic source)
      (oneOver8 * spatialQuadratic target))

/-- Symmetry of the genuine coupled kernel. -/
theorem coupledBF4MehlerKernel_symmetric
    (source target : Vector5) :
    CReal.Equiv
      (coupledBF4MehlerKernel source target)
      (coupledBF4MehlerKernel target source) :=
  expNeg_eqv_congr
    (coupledBF4Action_nonnegative source target)
    (coupledBF4Action_nonnegative target source)
    (coupledBF4Action_symmetric source target)

/-! ## 7. The full fifteen-dimensional `su(2)^5` tangent kernel -/

/-- Three colour components, each carrying the five transmitted BF4
holonomy coordinates. -/
abbrev BF4LieConfiguration := Fin 3 → Vector5

def lieColorIndices : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

theorem lieColorIndices_length :
    lieColorIndices.length = 3 := rfl

/-- Sum of the coupled `(K,S)` action over all three `su(2)` components. -/
def coupledBF4LieAction
    (source target : BF4LieConfiguration) : Q' :=
  lieColorIndices.foldr
    (fun color total =>
      coupledBF4Action (source color) (target color) + total)
    0

private theorem coupledBF4LieAction_fold_nonnegative
    (source target : BF4LieConfiguration) :
    ∀ colors : List (Fin 3),
      (0 : Q') ≤
        colors.foldr
          (fun color total =>
            coupledBF4Action (source color) (target color) + total)
          0
  | [] => Q'.le_refl' 0
  | color :: rest =>
      Q'.zero_le_add _ _
        (coupledBF4Action_nonnegative
          (source color) (target color))
        (coupledBF4LieAction_fold_nonnegative
          source target rest)

theorem coupledBF4LieAction_nonnegative
    (source target : BF4LieConfiguration) :
    (0 : Q') ≤ coupledBF4LieAction source target := by
  exact coupledBF4LieAction_fold_nonnegative
    source target lieColorIndices

private theorem coupledBF4LieAction_fold_symmetric
    (source target : BF4LieConfiguration) :
    ∀ colors : List (Fin 3),
      colors.foldr
          (fun color total =>
            coupledBF4Action (source color) (target color) + total)
          0 ≈
        colors.foldr
          (fun color total =>
            coupledBF4Action (target color) (source color) + total)
          0
  | [] => Q'.eqv_refl 0
  | color :: rest =>
      Q'.add_eqv_congr'
        (coupledBF4Action_symmetric
          (source color) (target color))
        (coupledBF4LieAction_fold_symmetric
          source target rest)

theorem coupledBF4LieAction_symmetric
    (source target : BF4LieConfiguration) :
    coupledBF4LieAction source target ≈
      coupledBF4LieAction target source := by
  exact coupledBF4LieAction_fold_symmetric
    source target lieColorIndices

/-- The full fifteen-dimensional constructive Feynman--Kac/Mehler kernel. -/
def coupledBF4LieMehlerKernel
    (source target : BF4LieConfiguration) : CReal :=
  ExpNeg.expNeg
    (coupledBF4LieAction source target)
    (coupledBF4LieAction_nonnegative source target)

theorem coupledBF4LieMehlerKernel_symmetric
    (source target : BF4LieConfiguration) :
    CReal.Equiv
      (coupledBF4LieMehlerKernel source target)
      (coupledBF4LieMehlerKernel target source) :=
  expNeg_eqv_congr
    (coupledBF4LieAction_nonnegative source target)
    (coupledBF4LieAction_nonnegative target source)
    (coupledBF4LieAction_symmetric source target)

/-- The constructive imaginary-coordinate chart on `SU(2)^5`.  At the
identity it is the ordinary `su(2)^5` tangent coordinate; globally it is a
specified chart pullback rather than an asserted logarithm. -/
def retainedImaginaryTangent
    (configuration : BF4FiveHolonomyConfiguration) :
    BF4LieConfiguration :=
  fun color holonomy =>
    (configuration holonomy).quaternion.coordinate
      ⟨color.val + 1, by omega⟩

/-- Pull the coupled Mehler kernel back to the exact compact
five-holonomy carrier on which the geometric spin networks are evaluated. -/
def coupledBF4FiveHolonomyMehlerKernel
    (source target : BF4FiveHolonomyConfiguration) : CReal :=
  coupledBF4LieMehlerKernel
    (retainedImaginaryTangent source)
    (retainedImaginaryTangent target)

/-- The coupled kernel and the geometric wavefunctions now have literally
the same source/target carrier. -/
theorem coupledBF4FiveHolonomyMehlerKernel_symmetric
    (source target : BF4FiveHolonomyConfiguration) :
    CReal.Equiv
      (coupledBF4FiveHolonomyMehlerKernel source target)
      (coupledBF4FiveHolonomyMehlerKernel target source) :=
  coupledBF4LieMehlerKernel_symmetric
    (retainedImaginaryTangent source)
    (retainedImaginaryTangent target)

def vectorAdd (left right : Vector5) : Vector5 :=
  fun coordinate => left coordinate + right coordinate

def tangentBasis (coordinate : Fin 5) : Vector5 :=
  fun other => if coordinate = other then 1 else 0

/-- The physical spatial quadratic is not a product of five one-coordinate
quadratics: coordinates zero and four carry the exact BF4 cross term. -/
theorem spatialQuadratic_genuinely_coupled :
    ¬ spatialQuadratic
          (vectorAdd
            (tangentBasis ⟨0, by decide⟩)
            (tangentBasis ⟨4, by decide⟩)) ≈
        spatialQuadratic (tangentBasis ⟨0, by decide⟩) +
          spatialQuadratic (tangentBasis ⟨4, by decide⟩) := by
  decide

/-- The kinetic quadratic is likewise non-product: its zero--one cross term
survives in the exact `K24` matrix. -/
theorem kineticQuadratic24_genuinely_coupled :
    ¬ kineticQuadratic24
          (vectorAdd
            (tangentBasis ⟨0, by decide⟩)
            (tangentBasis ⟨1, by decide⟩)) ≈
        kineticQuadratic24 (tangentBasis ⟨0, by decide⟩) +
          kineticQuadratic24 (tangentBasis ⟨1, by decide⟩) := by
  decide

/-- The exact generalized spectrum of this symmetric pair is the already
proved `4×3,6×2` BF4 spectrum. -/
theorem coupledBF4_pair_spectrum :
    MatrixEqv (matMul kineticK24 generalizedA) spatialS24 ∧
      MatrixEqv
        (matMul
          (matSub generalizedA (scalarMatrix 4))
          (matSub generalizedA (scalarMatrix 6)))
        (scalarMatrix 0) :=
  ⟨kinetic_mul_generalized, generalized_minimal_polynomial⟩

/-- The coupled Gaussian reference has the constructive Perron separator
`q₀ ≤ 9/50 < 1/5`. -/
theorem coupledBF4_gaussian_ratio_strict :
    gaussianPerronRatio ≤ CReal.ofQ' nineFiftieths ∧
      nineFiftieths < oneFifth :=
  ⟨gaussianPerronRatio_le_nineFiftieths,
    nineFiftieths_lt_oneFifth⟩

end YMGap.Continuum.BF4GeometricSpinNetworkMehler

#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.transmitted_or_integrated
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.bf4SpatialChord_idxOf
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.treeGaugeLinkPolynomial_chord
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.evalRatPoly_neg
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.evalPolyQuaternion_mul
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.eval_characterPolynomial
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.eval_integrateEighteenChords
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.integrateEighteenChords_supported
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.eval_geometricBF4Wavefunction
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.eval_geometricBF4Wavefunction_vacuum
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.geometricBF4Wavefunction_supported
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.geometricBF4WavefunctionValue_eq_partialHaar
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.fivefoldHaar_one
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.geometricBF4Wavefunction_vacuum_normalized
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.spatialQuadratic_scaled_eq_ldl
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.spatialQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.kineticQuadratic24_scaled_eq_ldl
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.kineticQuadratic24_nonnegative
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4Action_nonnegative
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4MehlerKernel_symmetric
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4LieAction_nonnegative
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4LieMehlerKernel_symmetric
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4FiveHolonomyMehlerKernel_symmetric
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.spatialQuadratic_genuinely_coupled
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.kineticQuadratic24_genuinely_coupled
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4_pair_spectrum
#print axioms YMGap.Continuum.BF4GeometricSpinNetworkMehler.coupledBF4_gaussian_ratio_strict
