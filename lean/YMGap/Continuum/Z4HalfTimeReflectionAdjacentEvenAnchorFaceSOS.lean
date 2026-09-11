/-
# Exact finite weighted SOS for the truncated anchor face

The adjacent-even reflection-positive route must treat the complete active
face weight at once: a fixed original character rank does not separately give
a same-half Gram kernel.  The reserve decomposition has already rewritten the
truncated anchor face as

```
  R_K + sum_{s=1}^K c_s ((s+1) + U_s(x)),
```

with `R_K >= 0` and `c_s >= 0`.  This module turns that rewrite into literal
finite weighted rational sum-of-squares data on rational unit quaternions.

For even `s = 2m`, the shifted character is the all-order Chebyshev SOS

```
  (2m+1) + U_{2m}(x) = 2 + 4 sum_{k<m} T_{k+1}(x)^2.
```

For odd `s = 2m+1`, the unit-quaternion identity supplies the four-square
half-angle certificate already proved in `SU2QuaternionOddFaceSOS`.  Finite
direct sums package the modes, nonnegative scaling absorbs `c_s` into their
weights, and a structural recursion adds the ranks.  The vacuum reserve is a
one-term SOS whose coefficient remains a weight; no square root is selected.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition
import YMGap.Continuum.ChebyshevEvenSOS
import YMGap.Continuum.SU2QuaternionOddFaceSOS
import YMGap.Continuum.FiniteWeightedRationalSOSProduct

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOddFaceSOS
open YMGap.Continuum.ChebyshevEvenSOS
open YMGap.Continuum.SU2QuaternionOddFaceSOS
open YMGap.Continuum.FiniteWeightedRationalSOSProduct
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceReserve
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Rational unit-quaternion input and elementary square packets -/

/-- The rational class coordinate together with the three remaining
quaternion coordinates and the exact unit-sphere relation. -/
structure AnchorQuaternionInput where
  x : Q'
  y1 : Q'
  y2 : Q'
  y3 : Q'
  onSphere : OnUnitQuaternionSphere x y1 y2 y3

/-- The finite weighted SOS type used throughout this face-local module. -/
abbrev AnchorFaceSOS := FiniteWeightedRationalSOS AnchorQuaternionInput

/-- A finite list of literal unit-weight squares.  Values beyond `count` are
irrelevant, as in the general finite weighted SOS interface. -/
def unitSquareSumSOS (count : Nat)
    (feature : Nat → AnchorQuaternionInput → Q') : AnchorFaceSOS where
  termCount := count
  weight := fun _ => 1
  weight_nonnegative := fun _ => by decide
  feature := feature

/-- Evaluation of `unitSquareSumSOS` is the corresponding finite square sum. -/
theorem value_unitSquareSumSOS (count : Nat)
    (feature : Nat → AnchorQuaternionInput → Q')
    (input : AnchorQuaternionInput) :
    value (unitSquareSumSOS count feature) input ≈
      finSum (fun term =>
        feature term input * feature term input) count := by
  unfold value unitSquareSumSOS
  exact finSum_eqv_congr _ _
    (fun term => Q'.one_mul_eqv
      (feature term input * feature term input)) count

/-! ## 2. Even shifted characters -/

/-- The nonconstant square modes in the even shifted-character identity. -/
def evenModeSquareSOS (m : Nat) : AnchorFaceSOS :=
  unitSquareSumSOS m (fun k input => T (k + 1) input.x)

/-- The exact even shifted-character SOS: one constant weight `2`, followed
by the first `m` first-kind modes with weight `4`. -/
def evenShiftedCharacterSOS (m : Nat) : AnchorFaceSOS :=
  add
    (constant AnchorQuaternionInput (2 : Q') (by decide))
    (scale (4 : Q') (by decide) (evenModeSquareSOS m))

/-- Evaluation of the packaged even SOS is its explicit Chebyshev square
sum. -/
theorem value_evenShiftedCharacterSOS
    (m : Nat) (input : AnchorQuaternionInput) :
    value (evenShiftedCharacterSOS m) input ≈
      (2 : Q') + (4 : Q') *
        finSum (fun k =>
          T (k + 1) input.x * T (k + 1) input.x) m := by
  calc
    value (evenShiftedCharacterSOS m) input
        ≈ value (constant AnchorQuaternionInput (2 : Q') (by decide)) input +
            value (scale (4 : Q') (by decide)
              (evenModeSquareSOS m)) input :=
          value_add _ _ input
    _ ≈ (2 : Q') +
          (4 : Q') * value (evenModeSquareSOS m) input :=
        Cheb.add_eqv_congr _ _ _ _
          (value_constant (2 : Q') (by decide) input)
          (value_scale (4 : Q') (by decide) (evenModeSquareSOS m) input)
    _ ≈ (2 : Q') + (4 : Q') *
          finSum (fun k =>
            T (k + 1) input.x * T (k + 1) input.x) m :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left (4 : Q') _ _
            (value_unitSquareSumSOS m
              (fun k input => T (k + 1) input.x) input))

/-- Every even dimension-shifted character has the displayed finite weighted
SOS presentation. -/
theorem evenShiftedCharacter_eqv_value
    (m : Nat) (input : AnchorQuaternionInput) :
    Q'.ofNat (2 * m + 1) + U (2 * m) input.x ≈
      value (evenShiftedCharacterSOS m) input := by
  exact Q'.eqv_trans _ _ _
    (ofNat_odd_add_U_even_eqv_two_add_four_Tsq_finSum m input.x)
    (Q'.eqv_symm (value_evenShiftedCharacterSOS m input))

/-! ## 3. Odd shifted characters -/

/-- One of the four quaternion features at odd half-angle level `k`. -/
def oddQuaternionFeature
    (k term : Nat) (input : AnchorQuaternionInput) : Q' :=
  match term with
  | 0 => ((1 : Q') + input.x) * C k input.x
  | 1 => input.y1 * C k input.x
  | 2 => input.y2 * C k input.x
  | _ => input.y3 * C k input.x

/-- The four literal unit-weight squares at one odd half-angle level. -/
def oddQuaternionChannelSOS (k : Nat) : AnchorFaceSOS :=
  unitSquareSumSOS 4 (oddQuaternionFeature k)

/-- The four-term presentation evaluates to the exact quaternion square
packet used by the odd-character theorem. -/
theorem value_oddQuaternionChannelSOS
    (k : Nat) (input : AnchorQuaternionInput) :
    value (oddQuaternionChannelSOS k) input ≈
      oddQuaternionSquares k input.x input.y1 input.y2 input.y3 := by
  refine Q'.eqv_trans _
    (finSum (fun term =>
      oddQuaternionFeature k term input *
        oddQuaternionFeature k term input) 4) _
    (value_unitSquareSumSOS 4 (oddQuaternionFeature k) input) ?_
  unfold oddQuaternionSquares
  simp only [finSum_succ, finSum_zero, oddQuaternionFeature]
  rw [Q'.zero_add']
  exact Q'.eqv_refl _

/-- Direct sum of the four-square packets through odd level `m`. -/
def oddShiftedCharacterSOS : Nat → AnchorFaceSOS
  | 0 => oddQuaternionChannelSOS 0
  | m + 1 => add (oddShiftedCharacterSOS m)
      (oddQuaternionChannelSOS (m + 1))

/-- Evaluation of the recursively packaged odd SOS is the finite quaternion
square sum already identified with the odd shifted character. -/
theorem value_oddShiftedCharacterSOS
    (m : Nat) (input : AnchorQuaternionInput) :
    value (oddShiftedCharacterSOS m) input ≈
      oddQuaternionSOSSum m input.x input.y1 input.y2 input.y3 := by
  induction m with
  | zero =>
      calc
        value (oddShiftedCharacterSOS 0) input
            ≈ oddQuaternionSquares 0
              input.x input.y1 input.y2 input.y3 :=
            value_oddQuaternionChannelSOS 0 input
        _ ≈ oddQuaternionSOSSum 0
              input.x input.y1 input.y2 input.y3 := by
            unfold oddQuaternionSOSSum
            simp only [finSum_succ, finSum_zero]
            rw [Q'.zero_add']
            exact Q'.eqv_refl _
  | succ m ih =>
      calc
        value (oddShiftedCharacterSOS (m + 1)) input
            ≈ value (oddShiftedCharacterSOS m) input +
                value (oddQuaternionChannelSOS (m + 1)) input :=
              value_add _ _ input
        _ ≈ oddQuaternionSOSSum m
                input.x input.y1 input.y2 input.y3 +
              oddQuaternionSquares (m + 1)
                input.x input.y1 input.y2 input.y3 :=
            Cheb.add_eqv_congr _ _ _ _ ih
              (value_oddQuaternionChannelSOS (m + 1) input)
        _ ≈ oddQuaternionSOSSum (m + 1)
              input.x input.y1 input.y2 input.y3 := by
            exact Q'.eqv_symm
              (Q'.eqv_of_eq
                (finSum_succ
                  (fun k => oddQuaternionSquares k
                    input.x input.y1 input.y2 input.y3) (m + 1)))

/-- Every odd dimension-shifted character has its finite quaternion SOS
presentation. -/
theorem oddShiftedCharacter_eqv_value
    (m : Nat) (input : AnchorQuaternionInput) :
    Q'.ofNat (2 * m + 2) + U (2 * m + 1) input.x ≈
      value (oddShiftedCharacterSOS m) input := by
  exact Q'.eqv_trans _ _ _
    (odd_face_character_eq_quaternionSOSSum
      m input.x input.y1 input.y2 input.y3 input.onSphere)
    (Q'.eqv_symm (value_oddShiftedCharacterSOS m input))

/-! ## 4. Parity-uniform shifted-character presentation -/

/-- Select the exact even or odd SOS from the decidable parity of the rank. -/
def shiftedCharacterSOS (rank : Nat) : AnchorFaceSOS :=
  if rank % 2 = 0 then evenShiftedCharacterSOS (rank / 2)
  else oddShiftedCharacterSOS (rank / 2)

theorem shiftedCharacterSOS_even (m : Nat) :
    shiftedCharacterSOS (2 * m) = evenShiftedCharacterSOS m := by
  unfold shiftedCharacterSOS
  rw [if_pos (by omega : (2 * m) % 2 = 0)]
  rw [show (2 * m) / 2 = m by omega]

theorem shiftedCharacterSOS_odd (m : Nat) :
    shiftedCharacterSOS (2 * m + 1) = oddShiftedCharacterSOS m := by
  unfold shiftedCharacterSOS
  rw [if_neg (by omega : ¬ (2 * m + 1) % 2 = 0)]
  rw [show (2 * m + 1) / 2 = m by omega]

/-- **Parity-uniform local SOS theorem.**  Every shifted SU(2) character is
presented by explicit finite weighted rational squares on the unit
quaternion sphere. -/
theorem shiftedCharacter_eqv_value
    (rank : Nat) (input : AnchorQuaternionInput) :
    dimQ rank + U rank input.x ≈
      value (shiftedCharacterSOS rank) input := by
  rcases Nat.mod_two_eq_zero_or_one rank with heven | hodd
  · have hrank : rank = 2 * (rank / 2) := by omega
    rw [hrank, shiftedCharacterSOS_even]
    unfold dimQ
    exact evenShiftedCharacter_eqv_value (rank / 2) input
  · have hrank : rank = 2 * (rank / 2) + 1 := by omega
    rw [hrank, shiftedCharacterSOS_odd]
    unfold dimQ
    exact oddShiftedCharacter_eqv_value (rank / 2) input

/-! ## 5. Anchor coefficients, finite rank sum, and vacuum reserve -/

/-- The shifted-character SOS at rank `1+index`, scaled by its nonnegative
anchor heat-kernel coefficient. -/
def anchorRankSOS (index : Nat) : AnchorFaceSOS :=
  scale (coeffW anchorCoupling (1 + index))
    (anchorReserveShiftedCharacter_coefficient_nonnegative index)
    (shiftedCharacterSOS (1 + index))

/-- One scaled rank packet evaluates to its exact summand in the reserve
rewrite. -/
theorem value_anchorRankSOS
    (index : Nat) (input : AnchorQuaternionInput) :
    value (anchorRankSOS index) input ≈
      coeffW anchorCoupling (1 + index) *
        (dimQ (1 + index) + U (1 + index) input.x) := by
  calc
    value (anchorRankSOS index) input
        ≈ coeffW anchorCoupling (1 + index) *
            value (shiftedCharacterSOS (1 + index)) input :=
          value_scale _ _ _ input
    _ ≈ coeffW anchorCoupling (1 + index) *
          (dimQ (1 + index) + U (1 + index) input.x) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (shiftedCharacter_eqv_value (1 + index) input))

/-- Structural direct sum of the first `cutoff` scaled excited-rank packets.
The empty sum is represented by the nonnegative constant zero. -/
def anchorExcitedSOS : Nat → AnchorFaceSOS
  | 0 => constant AnchorQuaternionInput (0 : Q') (by decide)
  | cutoff + 1 => add (anchorExcitedSOS cutoff) (anchorRankSOS cutoff)

/-- The excited direct sum evaluates to the exact finite shifted-character
sum in the reserve decomposition. -/
theorem value_anchorExcitedSOS
    (cutoff : Nat) (input : AnchorQuaternionInput) :
    value (anchorExcitedSOS cutoff) input ≈
      finSum (fun index =>
        coeffW anchorCoupling (1 + index) *
          (dimQ (1 + index) + U (1 + index) input.x)) cutoff := by
  induction cutoff with
  | zero =>
      exact value_constant (0 : Q') (by decide) input
  | succ cutoff ih =>
      calc
        value (anchorExcitedSOS (cutoff + 1)) input
            ≈ value (anchorExcitedSOS cutoff) input +
                value (anchorRankSOS cutoff) input :=
              value_add _ _ input
        _ ≈ finSum (fun index =>
                coeffW anchorCoupling (1 + index) *
                  (dimQ (1 + index) + U (1 + index) input.x)) cutoff +
              coeffW anchorCoupling (1 + cutoff) *
                (dimQ (1 + cutoff) + U (1 + cutoff) input.x) :=
            Cheb.add_eqv_congr _ _ _ _ ih
              (value_anchorRankSOS cutoff input)
        _ ≈ finSum (fun index =>
              coeffW anchorCoupling (1 + index) *
                (dimQ (1 + index) + U (1 + index) input.x))
              (cutoff + 1) :=
            Q'.eqv_symm
              (Q'.eqv_of_eq
                (finSum_succ
                  (fun index =>
                    coeffW anchorCoupling (1 + index) *
                      (dimQ (1 + index) + U (1 + index) input.x))
                  cutoff))

/-- The complete truncated anchor-face SOS: one reserve term followed by all
scaled excited-rank packets. -/
def anchorFaceSOS (cutoff : Nat) : AnchorFaceSOS :=
  add
    (constant AnchorQuaternionInput (anchorVacuumReserve cutoff)
      (anchorVacuumReserve_nonnegative cutoff))
    (anchorExcitedSOS cutoff)

/-- Evaluation of the complete face SOS is exactly the reserve-shifted
character expression. -/
theorem value_anchorFaceSOS_eqv_reserveShifted
    (cutoff : Nat) (input : AnchorQuaternionInput) :
    value (anchorFaceSOS cutoff) input ≈
      anchorReserveShiftedCharacterValue cutoff input.x := by
  calc
    value (anchorFaceSOS cutoff) input
        ≈ value
              (constant AnchorQuaternionInput (anchorVacuumReserve cutoff)
                (anchorVacuumReserve_nonnegative cutoff)) input +
            value (anchorExcitedSOS cutoff) input :=
          value_add _ _ input
    _ ≈ anchorVacuumReserve cutoff +
          finSum (fun index =>
            coeffW anchorCoupling (1 + index) *
              (dimQ (1 + index) + U (1 + index) input.x)) cutoff :=
        Cheb.add_eqv_congr _ _ _ _
          (value_constant (anchorVacuumReserve cutoff)
            (anchorVacuumReserve_nonnegative cutoff) input)
          (value_anchorExcitedSOS cutoff input)
    _ ≈ anchorReserveShiftedCharacterValue cutoff input.x := by
        unfold anchorReserveShiftedCharacterValue
        exact Q'.eqv_refl _

/-- **Exact finite weighted SOS presentation of the complete truncated anchor
face weight.**  This is the local rank-mixing certificate needed by the
direct active-quadratic route. -/
theorem anchorTruncatedFaceClassValue_eqv_anchorFaceSOS
    (cutoff : Nat) (input : AnchorQuaternionInput) :
    anchorTruncatedFaceClassValue cutoff input.x ≈
      value (anchorFaceSOS cutoff) input := by
  exact Q'.eqv_trans _ _ _
    (anchorTruncatedFaceClassValue_eqv_reserveShifted cutoff input.x)
    (Q'.eqv_symm
      (value_anchorFaceSOS_eqv_reserveShifted cutoff input))

/-- Every weight in the complete face presentation is constructively
nonnegative. -/
theorem anchorFaceSOS_weight_nonnegative
    (cutoff term : Nat) :
    (0 : Q') ≤ (anchorFaceSOS cutoff).weight term :=
  (anchorFaceSOS cutoff).weight_nonnegative term

/-- The complete truncated anchor face weight is pointwise nonnegative on
every rational unit quaternion.  This is a corollary of the stronger explicit
finite-SOS presentation, not a separate analytic estimate. -/
theorem anchorTruncatedFaceClassValue_nonnegative
    (cutoff : Nat) (input : AnchorQuaternionInput) :
    (0 : Q') ≤ anchorTruncatedFaceClassValue cutoff input.x := by
  exact Q'.le_trans' _ _ _
    (value_nonnegative (anchorFaceSOS cutoff) input)
    (Q'.ge_of_eqv
      (anchorTruncatedFaceClassValue_eqv_anchorFaceSOS cutoff input))

#print axioms shiftedCharacter_eqv_value
#print axioms value_anchorRankSOS
#print axioms value_anchorExcitedSOS
#print axioms anchorTruncatedFaceClassValue_eqv_anchorFaceSOS
#print axioms anchorFaceSOS_weight_nonnegative
#print axioms anchorTruncatedFaceClassValue_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceSOS
