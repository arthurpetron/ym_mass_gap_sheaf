/-
# Exact arithmetic check of the finite-cube normalized-pair diagnostic

STATUS: candidate for local Lean verification. Not imported by YMGap.lean.

This checks the displayed INTEGER certificate: seven weighted orthogonality
relations, positive dual norm and a positive full-weight pairing numerator.
The integers were generated using exact SU(2) Haar contractions. Their pin to
`transferStep`/the full original weighted window is NOT a theorem of this file.
In particular, a successful check is NOT a physical or continuum gap proof.
No canonical statement is edited and no analytic premise is introduced.

Consumer: reject a plaquette-span closure shortcut only after the separate
original-cube moment pin has been proved. The source-level mathematical
interpretation and exact Python checks are in the associated audit.
-/

import Init

namespace YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck
set_option autoImplicit false

def gramDenominator : Nat := 3377699720527872
def dualDenominator : Nat := 1789451725276305179088810175057724506537732805244559413711429
def sourceDenominator : Nat := 1125899906842624
def gram : List (List Int) := [
  [3378112350535716, 844915130663526, 844915130663526, 844915130663526, 844915130663526, 844915130663526, 844915130663526, 107264186211408],
  [844915130663526, 3378215573760072, 212051084540931, 212051266811312, 212051266811312, 212051266811312, 212051266811312, 422773727133512],
  [844915130663526, 212051084540931, 3378215573760072, 212051266811312, 212051266811312, 212051266811312, 212051266811312, 33011838082372],
  [844915130663526, 212051266811312, 212051266811312, 3378215573760072, 212051084540931, 212051266811312, 212051266811312, 422773727133512],
  [844915130663526, 212051266811312, 212051266811312, 212051084540931, 3378215573760072, 212051266811312, 212051266811312, 33011838082372],
  [844915130663526, 212051266811312, 212051266811312, 212051266811312, 212051266811312, 3378215573760072, 212051084540931, 33011928851200],
  [844915130663526, 212051266811312, 212051266811312, 212051266811312, 212051266811312, 212051084540931, 3378215573760072, 33011928851200],
  [107264186211408, 422773727133512, 33011838082372, 422773727133512, 33011838082372, 33011928851200, 33011928851200, 3378163981231176]]
def dual : List Int := [58459392946606363382626494437976179670067367027812415079624, -223674650147344101693935322608271891258065947351019901188780, -3389163659076961957771460218809517657961292396490877182120, -223674650147344101693935322608271891258065947351019901188780, -3389163659076961957771460218809517657961292396490877182120, -3389202278337208721561314781386145020852355891819881169808, -3389202278337208721561314781386145020852355891819881169808, 1789451725276305179088810175057724506537732805244559413711429]
def sourcePairing : List Int := [281638376887842, 70683694846977, 70441984410113, 70442037904144, 70442037904144, 70442037904144, 70442037904144, 8973526793284]

def dot : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | a::xs, b::ys => a*b + dot xs ys

def rowPairing (i : Nat) : Int := dot (gram.getD i []) dual

def normNumerator : Int := dot dual ((List.range 8).map rowPairing)
def pairingNumerator : Int := dot sourcePairing dual

-- Shape guards prevent truncated list operations from hiding missing entries.
theorem shapes : gram.length = 8 ∧ dual.length = 8 ∧
    sourcePairing.length = 8 ∧ (gram.all (fun row => row.length == 8)) = true := by decide

theorem denominators_positive : 0 < gramDenominator ∧
    0 < dualDenominator ∧ 0 < sourceDenominator := by decide

theorem weighted_orthogonality_0 : rowPairing 0 = 0 := by decide
theorem weighted_orthogonality_1 : rowPairing 1 = 0 := by decide
theorem weighted_orthogonality_2 : rowPairing 2 = 0 := by decide
theorem weighted_orthogonality_3 : rowPairing 3 = 0 := by decide
theorem weighted_orthogonality_4 : rowPairing 4 = 0 := by decide
theorem weighted_orthogonality_5 : rowPairing 5 = 0 := by decide
theorem weighted_orthogonality_6 : rowPairing 6 = 0 := by decide

theorem weighted_norm_positive : 0 < normNumerator := by decide
theorem source_pairing_positive : 0 < pairingNumerator := by decide

def partitionNumerator : Int := 281509362544643
def partitionDenominator : Int := 281474976710656
theorem normalized_norm_below_one :
    normNumerator * partitionDenominator <
      (gramDenominator : Int) * (dualDenominator : Int)^2 * partitionNumerator := by decide
theorem connected_covariance_lower :
    (sourceDenominator : Int) * (dualDenominator : Int) * partitionNumerator <
      (2500000 : Int) * partitionDenominator * pairingNumerator := by decide
theorem connected_covariance_upper :
    (2000000 : Int) * partitionDenominator * pairingNumerator <
      (sourceDenominator : Int) * (dualDenominator : Int) * partitionNumerator := by decide

end YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck

#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.shapes
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.denominators_positive
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_0
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_1
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_2
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_3
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_4
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_5
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_orthogonality_6
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.weighted_norm_positive
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.source_pairing_positive
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.normalized_norm_below_one
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.connected_covariance_lower
#print axioms YMGap.Continuum.BF4CubeNormalizedPairEscapeCheck.connected_covariance_upper
