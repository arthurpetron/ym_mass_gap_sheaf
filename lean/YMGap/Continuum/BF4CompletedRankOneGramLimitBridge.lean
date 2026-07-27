/-
# Same-path rank-one Gram channels survive cutoff removal

`BF4CompletedConditionalGramLimitBridge` accepts an already-formed
nonnegative quadratic channel as an honest premise.  This module discharges
that premise for the first canonical case: a rank-one channel obtained by
squaring a supplied amplitude on the same retained path carrier.

Given rational cutoff amplitudes `a_path(N)` and completed amplitudes `A_path`,
with:

* `ofQ'(a_path(N)) -> A_path`;
* `|a_path(N)| <= B` uniformly in the cutoff;
* `|A_path.approx(n)| <= B` uniformly in the approximation index;

the literal rational squares converge to `A_path * A_path`.  Both cutoff and
completed squares are nonnegative, and the completed square approximations
are bounded by `B * B`.  These facts instantiate the finite weighted
quadratic/Gram cutoff-limit certificate on exactly the same finite path list.

Crucial fence: this constructs diagonal/rank-one same-path squares.  It does
not identify the amplitude with the physical BF4 slab amplitude, does not
construct signed cross entries, and does not infer Loewner/CP order from
entrywise scalar convergence.

## Axiom gate

Only exact rational square positivity and constructive multiplication
continuity are used.  There is no `Classical.*`, `Real`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedConditionalGramLimitBridge

namespace YMGap.Continuum.BF4CompletedRankOneGramLimitBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompletedConditionalGramLimitBridge

/-! ## 1. Rank-one cutoff and completed channels -/

/-- Literal rational rank-one quadratic at one common cutoff. -/
def rationalRankOnePathQuadratic
    {Path : Type}
    (cutoffAmplitude : Path → Nat → Q')
    (path : Path) (cutoff : Nat) : Q' :=
  cutoffAmplitude path cutoff *
    cutoffAmplitude path cutoff

/-- Completed rank-one quadratic on the same retained path. -/
def completedRankOnePathQuadratic
    {Path : Type}
    (completedAmplitude : Path → CReal)
    (path : Path) : CReal :=
  CReal.mul
    (completedAmplitude path)
    (completedAmplitude path)

/-- Every literal rational cutoff rank-one channel is nonnegative, with no
sign restriction on its amplitude. -/
theorem rationalRankOnePathQuadratic_nonnegative
    {Path : Type}
    (cutoffAmplitude : Path → Nat → Q')
    (path : Path) (cutoff : Nat) :
    (0 : Q') ≤
      rationalRankOnePathQuadratic
        cutoffAmplitude path cutoff :=
  SumOfSquares.q_mul_self_nonneg
    (cutoffAmplitude path cutoff)

/-- Every completed rank-one channel is nonnegative in semantic
constructive-real order. -/
theorem completedRankOnePathQuadratic_nonnegative
    {Path : Type}
    (completedAmplitude : Path → CReal)
    (path : Path) :
    ExpPos.geRat
      (completedRankOnePathQuadratic
        completedAmplitude path)
      0 :=
  SumOfSquares.geRat_sq_nonneg
    (completedAmplitude path)

/-! ## 2. Square convergence and square bounds -/

/-- A common amplitude bound tensors to the corresponding bound on every
approximation of the completed square. -/
theorem completedRankOnePathQuadratic_abs_approx_le
    {Path : Type}
    (completedAmplitude : Path → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (path : Path)
    (completedAmplitudeBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude path).approx approximation) ≤
          amplitudeBound)
    (approximation : Nat) :
    Q'.abs
        ((completedRankOnePathQuadratic
          completedAmplitude path).approx approximation) ≤
      amplitudeBound * amplitudeBound := by
  unfold completedRankOnePathQuadratic
  change
    Q'.abs
        ((completedAmplitude path).approx approximation *
          (completedAmplitude path).approx approximation) ≤
      amplitudeBound * amplitudeBound
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le
      ((completedAmplitude path).approx approximation)
      ((completedAmplitude path).approx approximation)) ?_
  exact Q'.mul_le_mul_of_nonneg
    (completedAmplitudeBound approximation)
    (completedAmplitudeBound approximation)
    amplitudeBound_nonnegative
    (Q'.abs_nonneg
      ((completedAmplitude path).approx approximation))

/-- Under explicit uniform cutoff and completed-amplitude bounds, the literal
rational squares converge to the completed rank-one square. -/
theorem rationalRankOnePathQuadratic_converges
    {Path : Type}
    (cutoffAmplitude : Path → Nat → Q')
    (completedAmplitude : Path → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (path : Path)
    (cutoffAmplitudeBound :
      ∀ cutoff,
        Q'.abs (cutoffAmplitude path cutoff) ≤
          amplitudeBound)
    (completedAmplitudeBound :
      ∀ approximation,
        Q'.abs
            ((completedAmplitude path).approx approximation) ≤
          amplitudeBound)
    (amplitudeConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.ofQ' (cutoffAmplitude path cutoff))
        (completedAmplitude path)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (rationalRankOnePathQuadratic
            cutoffAmplitude path cutoff))
      (completedRankOnePathQuadratic
        completedAmplitude path) := by
  have multipliedConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.mul
            (CReal.ofQ' (cutoffAmplitude path cutoff))
            (CReal.ofQ' (cutoffAmplitude path cutoff)))
        (CReal.mul
          (completedAmplitude path)
          (completedAmplitude path)) :=
    CReal.convergesTo_mul
      amplitudeBound_nonnegative
      (fun cutoff approximation =>
        cutoffAmplitudeBound cutoff)
      completedAmplitudeBound
      amplitudeConverges
      amplitudeConverges
  unfold rationalRankOnePathQuadratic
  unfold completedRankOnePathQuadratic
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.mul
          (CReal.ofQ' (cutoffAmplitude path cutoff))
          (CReal.ofQ' (cutoffAmplitude path cutoff)))
  · intro cutoff
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul
        (cutoffAmplitude path cutoff)
        (cutoffAmplitude path cutoff))
  · exact multipliedConverges

/-! ## 3. Same-carrier weighted rank-one Gram certificate -/

/-- The finite retained-path weighted rank-one Gram limit certificate.

All premises live on the same supplied path list.  The resulting certificate
contains cutoff nonnegativity, convergence of the literal rational weighted
sum, and nonnegativity of its completed value. -/
def weightedRankOneGramLimitCertificate
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (cutoffAmplitude : Path → Nat → Q')
    (completedAmplitude : Path → CReal)
    (amplitudeBound : Q')
    (amplitudeBound_nonnegative :
      (0 : Q') ≤ amplitudeBound)
    (cutoffAmplitudeBound :
      ∀ path, path ∈ paths →
        ∀ cutoff,
          Q'.abs (cutoffAmplitude path cutoff) ≤
            amplitudeBound)
    (completedAmplitudeBound :
      ∀ path, path ∈ paths →
        ∀ approximation,
          Q'.abs
              ((completedAmplitude path).approx approximation) ≤
            amplitudeBound)
    (amplitudeConverges :
      ∀ path, path ∈ paths →
        CReal.ConvergesTo
          (fun cutoff =>
            CReal.ofQ' (cutoffAmplitude path cutoff))
          (completedAmplitude path)) :
    WeightedQuadraticGramLimitCertificate
      (rationalWeightedQuadraticPathSum
        paths pathWeight
        (rationalRankOnePathQuadratic
          cutoffAmplitude))
      (completedWeightedQuadraticPathSum
        paths pathWeight
        (completedRankOnePathQuadratic
          completedAmplitude)) :=
  weightedQuadraticGramLimitCertificate
    paths
    pathWeight pathWeight_nonnegative
    (rationalRankOnePathQuadratic
      cutoffAmplitude)
    (fun path _ cutoff =>
      rationalRankOnePathQuadratic_nonnegative
        cutoffAmplitude path cutoff)
    (completedRankOnePathQuadratic
      completedAmplitude)
    (fun path _ =>
      completedRankOnePathQuadratic_nonnegative
        completedAmplitude path)
    (amplitudeBound * amplitudeBound)
    (Q'.mul_nonneg _ _
      amplitudeBound_nonnegative
      amplitudeBound_nonnegative)
    (fun path hpath approximation =>
      completedRankOnePathQuadratic_abs_approx_le
        completedAmplitude
        amplitudeBound amplitudeBound_nonnegative
        path
        (completedAmplitudeBound path hpath)
        approximation)
    (fun path hpath =>
      rationalRankOnePathQuadratic_converges
        cutoffAmplitude completedAmplitude
        amplitudeBound amplitudeBound_nonnegative
        path
        (cutoffAmplitudeBound path hpath)
        (completedAmplitudeBound path hpath)
        (amplitudeConverges path hpath))

end YMGap.Continuum.BF4CompletedRankOneGramLimitBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedRankOneGramLimitBridge.rationalRankOnePathQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4CompletedRankOneGramLimitBridge.completedRankOnePathQuadratic_abs_approx_le
#print axioms YMGap.Continuum.BF4CompletedRankOneGramLimitBridge.rationalRankOnePathQuadratic_converges
#print axioms YMGap.Continuum.BF4CompletedRankOneGramLimitBridge.weightedRankOneGramLimitCertificate
