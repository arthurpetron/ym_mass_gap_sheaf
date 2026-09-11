/-
# Singlet/triplet diagonalization of the signed four-valent Haar projector

The direct/crossed invariant pairings at a balanced fundamental SU(2) link
have Gram matrix `[[4,2],[2,4]]`.  This leaf makes the corresponding channel
change of basis explicit:

    S = (D - X) / 2,       T = (D + X) / 2.

The new pairing tensors are orthogonal with squared norms `1` and `3`.
Consequently the inverse-Gram Haar kernel is diagonal,

    K(row,column) = S(row) S(column) + (1/3) T(row) T(column).

Thus the signed mixed coefficients of the direct/crossed formula are not
discarded: they are exactly the expansion of the positive channel weights
`1` and `1/3`.  The Gram `diag(1,3)` is the same dimension-rescaled channel
Gram used by the exact rational fundamental F-move.

Only four bounded Boolean binders occur in the closed Gram and trace checks.
No global assignment family, trajectory, or lattice labelling is unfolded.

# Axiom gate

No choice principle, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
import YMGap.Continuum.SU2TrivalentThetaRecoupling

namespace YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2TrivalentThetaRecoupling

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Orthogonal singlet and triplet pairing tensors -/

/-- The antisymmetric/singlet combination `(D-X)/2`. -/
def singletOrientedPairing
    (first second firstConjugate secondConjugate : Bool) : Q' :=
  oneHalf *
    (directOrientedPairing first second firstConjugate secondConjugate +
      (-crossedOrientedPairing first second firstConjugate secondConjugate))

/-- The symmetric/triplet combination `(D+X)/2`. -/
def tripletOrientedPairing
    (first second firstConjugate secondConjugate : Bool) : Q' :=
  oneHalf *
    (directOrientedPairing first second firstConjugate secondConjugate +
      crossedOrientedPairing first second firstConjugate secondConjugate)

/-- Inverse channel change of basis: `D = S + T`, pointwise. -/
theorem directOrientedPairing_eq_singlet_add_triplet
    (first second firstConjugate secondConjugate : Bool) :
    directOrientedPairing first second firstConjugate secondConjugate ≈
      singletOrientedPairing first second firstConjugate secondConjugate +
        tripletOrientedPairing first second firstConjugate
          secondConjugate := by
  cases first <;> cases second <;> cases firstConjugate <;>
    cases secondConjugate <;>
    unfold singletOrientedPairing tripletOrientedPairing
      directOrientedPairing crossedOrientedPairing boolKronecker oneHalf <;>
    decide

/-- Inverse channel change of basis: `X = T - S`, pointwise. -/
theorem crossedOrientedPairing_eq_triplet_sub_singlet
    (first second firstConjugate secondConjugate : Bool) :
    crossedOrientedPairing first second firstConjugate secondConjugate ≈
      tripletOrientedPairing first second firstConjugate secondConjugate +
        (-singletOrientedPairing first second firstConjugate
          secondConjugate) := by
  cases first <;> cases second <;> cases firstConjugate <;>
    cases secondConjugate <;>
    unfold singletOrientedPairing tripletOrientedPairing
      directOrientedPairing crossedOrientedPairing boolKronecker oneHalf <;>
    decide

/-- The channel pairing Gram is exactly `diag(1,3)`.  Both mixed entries are
retained in the statement so that row/column orientation is certified. -/
theorem singlet_triplet_oriented_pairing_gram_exact :
    orientedPairingInner singletOrientedPairing
        singletOrientedPairing ≈ 1 ∧
    orientedPairingInner singletOrientedPairing
        tripletOrientedPairing ≈ 0 ∧
    orientedPairingInner tripletOrientedPairing
        singletOrientedPairing ≈ 0 ∧
    orientedPairingInner tripletOrientedPairing
        tripletOrientedPairing ≈ 3 := by
  unfold orientedPairingInner rationalFourBoolSum rationalBoolSum
    singletOrientedPairing tripletOrientedPairing directOrientedPairing
    crossedOrientedPairing boolKronecker oneHalf
  decide

/-- The Boolean pairing tensors and the rational recoupling carrier use the
same ordered singlet/triplet Gram convention. -/
theorem pairing_channel_gram_matches_recouple_basis :
    orientedPairingInner singletOrientedPairing
        singletOrientedPairing ≈ recoupleGram singletChannel singletChannel ∧
    orientedPairingInner singletOrientedPairing
        tripletOrientedPairing ≈ recoupleGram singletChannel tripletChannel ∧
    orientedPairingInner tripletOrientedPairing
        singletOrientedPairing ≈ recoupleGram tripletChannel singletChannel ∧
    orientedPairingInner tripletOrientedPairing
        tripletOrientedPairing ≈ recoupleGram tripletChannel tripletChannel := by
  have hss : (1 : Q') ≈ recoupleGram singletChannel singletChannel := by
    unfold recoupleGram singletChannel
    decide
  have hst : (0 : Q') ≈ recoupleGram singletChannel tripletChannel := by
    unfold recoupleGram singletChannel tripletChannel
    decide
  have hts : (0 : Q') ≈ recoupleGram tripletChannel singletChannel := by
    unfold recoupleGram singletChannel tripletChannel
    decide
  have htt : (3 : Q') ≈ recoupleGram tripletChannel tripletChannel := by
    unfold recoupleGram tripletChannel
    decide
  exact
    ⟨Q'.eqv_trans _ 1 _
        singlet_triplet_oriented_pairing_gram_exact.1 hss,
      Q'.eqv_trans _ 0 _
        singlet_triplet_oriented_pairing_gram_exact.2.1 hst,
      Q'.eqv_trans _ 0 _
        singlet_triplet_oriented_pairing_gram_exact.2.2.1 hts,
      Q'.eqv_trans _ 3 _
        singlet_triplet_oriented_pairing_gram_exact.2.2.2 htt⟩

/-! ## 2. Diagonal inverse-Gram kernel -/

/-- Pairing values in the dimension-rescaled `(singlet,triplet)` basis. -/
def orientedPairingChannelCoordinates
    (first second firstConjugate secondConjugate : Bool) : RecoupleVec :=
  (singletOrientedPairing first second firstConjugate secondConjugate,
    tripletOrientedPairing first second firstConjugate secondConjugate)

/-- The diagonal inverse of `recoupleGram = diag(1,3)`. -/
def inverseRecoupleGram (row column : RecoupleVec) : Q' :=
  row.1 * column.1 + oneThird * (row.2 * column.2)

/-- The channel-diagonal scalar kernel, with the reverse slots transposed in
exactly the same way as the signed Haar projector. -/
def orientedFourFundamentalHaarProjectorChannelScalar
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) : Q' :=
  inverseRecoupleGram
    (orientedPairingChannelCoordinates
      firstForwardRow secondForwardRow
      firstReverseColumn secondReverseColumn)
    (orientedPairingChannelCoordinates
      firstForwardColumn secondForwardColumn
      firstReverseRow secondReverseRow)

/-- Rational-complex channel form of the projector. -/
def orientedFourFundamentalHaarProjectorChannel
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) : RationalComplex :=
  (orientedFourFundamentalHaarProjectorChannelScalar
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn, 0)

/-- **Exact channel diagonalization of the signed scalar projector.** -/
theorem orientedFourFundamentalHaarProjectorScalar_eqv_channel
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    orientedFourFundamentalHaarProjectorScalar
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn ≈
    orientedFourFundamentalHaarProjectorChannelScalar
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn := by
  cases firstForwardRow <;> cases firstForwardColumn <;>
    cases secondForwardRow <;> cases secondForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    unfold orientedFourFundamentalHaarProjectorScalar
      orientedFourFundamentalHaarProjectorChannelScalar inverseRecoupleGram
      orientedPairingChannelCoordinates singletOrientedPairing
      tripletOrientedPairing directOrientedPairing crossedOrientedPairing
      boolKronecker oneHalf oneThird oneSixth <;>
    decide

/-- Rational-complex version of the exact channel diagonalization. -/
theorem orientedFourFundamentalHaarProjector_eqv_channel
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (orientedFourFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn)
      (orientedFourFundamentalHaarProjectorChannel
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn) := by
  constructor
  · exact orientedFourFundamentalHaarProjectorScalar_eqv_channel
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
  · exact Q'.eqv_refl 0

/-! ## 3. Rank-one channel trace checks -/

/-- The normalized singlet summand has closed trace one. -/
theorem singlet_channel_projector_diagonal_trace_exact :
    rationalFourBoolSum (fun first second firstConjugate secondConjugate =>
      singletOrientedPairing first second firstConjugate secondConjugate *
        singletOrientedPairing first second firstConjugate secondConjugate) ≈
      1 := by
  unfold rationalFourBoolSum rationalBoolSum singletOrientedPairing
    directOrientedPairing crossedOrientedPairing boolKronecker oneHalf
  decide

/-- The triplet summand has norm three and inverse-Gram weight `1/3`, hence
also contributes closed trace one. -/
theorem triplet_channel_projector_diagonal_trace_exact :
    rationalFourBoolSum (fun first second firstConjugate secondConjugate =>
      oneThird *
        (tripletOrientedPairing first second firstConjugate secondConjugate *
          tripletOrientedPairing first second firstConjugate
            secondConjugate)) ≈ 1 := by
  unfold rationalFourBoolSum rationalBoolSum tripletOrientedPairing
    directOrientedPairing crossedOrientedPairing boolKronecker oneHalf oneThird
  decide

/-- The signed rational F-move acts on precisely the channel carrier used
above, with columns `(-1/2,1/2)` and `(3/2,1/2)`. -/
theorem fundamentalFMove_channel_basis_exact :
    RecoupleEq (fundamentalFMove singletChannel) ((-oneHalf), oneHalf) ∧
    RecoupleEq (fundamentalFMove tripletChannel) (threeHalves, oneHalf) :=
  fundamentalFMove_basis_exact

#print axioms directOrientedPairing_eq_singlet_add_triplet
#print axioms crossedOrientedPairing_eq_triplet_sub_singlet
#print axioms singlet_triplet_oriented_pairing_gram_exact
#print axioms pairing_channel_gram_matches_recouple_basis
#print axioms orientedFourFundamentalHaarProjectorScalar_eqv_channel
#print axioms orientedFourFundamentalHaarProjector_eqv_channel
#print axioms singlet_channel_projector_diagonal_trace_exact
#print axioms triplet_channel_projector_diagonal_trace_exact
#print axioms fundamentalFMove_channel_basis_exact

end YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization
