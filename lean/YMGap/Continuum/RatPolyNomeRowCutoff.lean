/-
# Nome-independent cutoff for a fixed finite row skeleton

Evaluating the nome coefficients changes scalar coefficients but retains each
row's monomial list, including terms whose coefficient evaluates to zero.
Consequently the computed input mode cutoff is independent of the nome for a
fixed finite row family. This is a finite-input statement, not a uniform bound
for changing source rows.
-/

import YMGap.Continuum.RatPolyNomeRows
import YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion

namespace YMGap.Continuum.RatPolyNomeRowCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
  (identityQuaternionBlockInvolution)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionAngularSupport

private theorem degreeSum_append (block : Nat) (p q : RatPoly) :
    quaternionBlockDegreeSum block (p ++ q) =
      quaternionBlockDegreeSum block p + quaternionBlockDegreeSum block q := by
  induction p with
  | nil => simp [quaternionBlockDegreeSum]
  | cons term p ih => simp [quaternionBlockDegreeSum, ih, Nat.add_assoc]

private theorem degreeSum_smul (block : Nat) (c : Q') (p : RatPoly) :
    quaternionBlockDegreeSum block (polySmul c p) =
      quaternionBlockDegreeSum block p := by
  induction p with
  | nil => rfl
  | cons term p ih =>
      change quaternionBlockDegree term.1 block + quaternionBlockDegreeSum block (polySmul c p) =
        quaternionBlockDegree term.1 block + quaternionBlockDegreeSum block p
      rw [ih]

private theorem blockZeroDegree_reindex_identity {blocks : Nat}
    (hblocks : 0 < blocks) (m : List Nat) :
    quaternionBlockDegree
        (reindexQuaternionExponents (identityQuaternionBlockInvolution blocks) m) 0 =
      quaternionBlockDegree m 0 := by
  unfold quaternionBlockDegree
  have h0 := exponentAt_reindexQuaternionExponents
    (identityQuaternionBlockInvolution blocks) m (by omega : 0 < 4 * blocks)
  have h1 := exponentAt_reindexQuaternionExponents
    (identityQuaternionBlockInvolution blocks) m (by omega : 1 < 4 * blocks)
  have h2 := exponentAt_reindexQuaternionExponents
    (identityQuaternionBlockInvolution blocks) m (by omega : 2 < 4 * blocks)
  have h3 := exponentAt_reindexQuaternionExponents
    (identityQuaternionBlockInvolution blocks) m (by omega : 3 < 4 * blocks)
  rw [h0, h1, h2, h3]
  simp [identityQuaternionBlockInvolution]

private theorem degreeSum_reindex_identity {blocks : Nat}
    (hblocks : 0 < blocks) : ∀ p : RatPoly,
    quaternionBlockDegreeSum 0
        (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) p) =
      quaternionBlockDegreeSum 0 p
  | [] => rfl
  | term :: p => by
      simp only [reindexQuaternionPolynomial, List.map_cons,
        quaternionBlockDegreeSum]
      rw [blockZeroDegree_reindex_identity hblocks term.1]
      change quaternionBlockDegree term.1 0 + quaternionBlockDegreeSum 0
        (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) p) = _
      rw [degreeSum_reindex_identity hblocks p]

private theorem paddedDegreeBound_add (blocks : Nat) (p q : RatPoly) :
    headDegreeBound (paddedInput blocks (polyAdd p q)) =
      headDegreeBound (paddedInput blocks p) +
        headDegreeBound (paddedInput blocks q) := by
  unfold headDegreeBound paddedInput
  change quaternionBlockDegreeSum 0
      (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks)
        (polyAdd p q)) = _
  rw [reindexQuaternionPolynomial, polyAdd, List.map_append]
  exact degreeSum_append 0 _ _

private theorem paddedDegreeBound_smul (blocks : Nat)
    (hblocks : 0 < blocks) (c : Q') (p : RatPoly) :
    headDegreeBound (paddedInput blocks (polySmul c p)) =
      headDegreeBound (paddedInput blocks p) := by
  unfold headDegreeBound paddedInput
  exact (degreeSum_reindex_identity hblocks (polySmul c p)).trans
    ((degreeSum_smul 0 c p).trans (degreeSum_reindex_identity hblocks p).symm)

private theorem evalRows_cons (a : Poly × RatPoly) (A : Rows) (r : Q') :
    evalRows (a :: A) r =
      polyAdd (polySmul (QPoly.eval a.1 r) a.2) (evalRows A r) := rfl

/-- A concrete cutoff for the fixed row family, computed at nome zero. -/
def rowCutoff (blocks : Nat) (A : Rows) : Nat :=
  modeCutoff blocks (evalRows A 0)

/-- The existing computed mode cutoff is exactly invariant under nome
evaluation for a fixed row skeleton. No positivity or cutoff growth bound is
assumed; zero scalar coefficients do not delete row monomials. -/
theorem modeCutoff_evalRows_eq (blocks : Nat) (hblocks : 0 < blocks)
    (A : Rows) (r s : Q') :
    modeCutoff blocks (evalRows A r) = modeCutoff blocks (evalRows A s) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
      simp only [modeCutoff, evalRows_cons]
      rw [paddedDegreeBound_add blocks,
        paddedDegreeBound_add blocks,
        paddedDegreeBound_smul blocks hblocks,
        paddedDegreeBound_smul blocks hblocks,
        show headDegreeBound (paddedInput blocks (evalRows A r)) =
          headDegreeBound (paddedInput blocks (evalRows A s)) by
            simpa only [modeCutoff] using ih]

/-- The cutoff computed once from nome zero bounds the identical row family at
every nome. -/
theorem rowCutoff_spec (blocks : Nat) (hblocks : 0 < blocks)
    (A : Rows) (r : Q') :
    modeCutoff blocks (evalRows A r) = rowCutoff blocks A :=
  modeCutoff_evalRows_eq blocks hblocks A r 0

/-- Row support is inherited from the fixed coefficient polynomials. -/
theorem evalRows_supported {blocks : Nat} (A : Rows)
    (hA : ∀ row, row ∈ A → SupportedQuaternionBlocks blocks row.2)
    (r : Q') : SupportedQuaternionBlocks blocks (evalRows A r) := by
  induction A with
  | nil =>
      intro term hterm
      simp [evalRows, polySum, polyZero] at hterm
  | cons a A ih =>
      rw [evalRows_cons]
      apply polyAdd_supported
      · exact polySmul_supported (hA a List.mem_cons_self) _
      · apply ih
        intro row hrow
        exact hA row (List.mem_cons_of_mem a hrow)

end YMGap.Continuum.RatPolyNomeRowCutoff

#print axioms YMGap.Continuum.RatPolyNomeRowCutoff.rowCutoff
#print axioms YMGap.Continuum.RatPolyNomeRowCutoff.modeCutoff_evalRows_eq
#print axioms YMGap.Continuum.RatPolyNomeRowCutoff.rowCutoff_spec
#print axioms YMGap.Continuum.RatPolyNomeRowCutoff.evalRows_supported
