/-
# Reflected all-spin BF4 Peter--Weyl bridge

The geometric BF4 boundary wavefunction is already an all-spin central
Peter--Weyl polynomial: it is obtained from the twenty-four oriented
plaquette characters after exact normalized Haar integration of the eighteen
non-transmitted chords.  The compact physical limit, however, was first
located only as the diagonal quadratic

  Q(P) = H₁₀(P² exp(-A)).

This file constructs the missing reflected source/target coefficient by
constructive polarization.  For a source wavefunction `P` and its reflected,
coordinate-shifted target wavefunction `R`, set

  B(P,R) = 1/4 (Q(P+R) - Q(P-R)).

Every polynomial remains on the literal ten-quaternion carrier.  A finite
Haar-algebra calculation proves that each polarized Taylor coefficient is
exactly

  H₁₀(P R (-A)^k/k!),

so the located polarized `CReal` is equivalent to the previously constructed
geometric coupled-Mehler coefficient.  This is a source/target bridge, not a
spectral or row-relative estimate.

## Axiom gate

Finite exact polynomial algebra and constructive-real arithmetic only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CompactActionPhysicalLimit
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionExponentialShift
open YMGap.Continuum.BF4CompactActionPhysicalLimit
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Literal reflected source/target carrier -/

/-- The exact source all-spin wavefunction on the first five holonomies. -/
def reflectedSourceWavefunction (state : EdgeLabelling) : RatPoly :=
  sourceGeometricWavefunction state

/-- The reflected target wavefunction on the second five holonomies.

The BF4 character wavefunctions are real and central, so inversion/conjugation
fixes their values; reflection is therefore the literal twenty-coordinate
shift already used by the coupled action.
-/
def reflectedTargetWavefunction (state : EdgeLabelling) : RatPoly :=
  targetGeometricWavefunction state

def reflectedSumWavefunction
    (left right : EdgeLabelling) : RatPoly :=
  polyAdd
    (reflectedSourceWavefunction left)
    (reflectedTargetWavefunction right)

def reflectedDifferenceWavefunction
    (left right : EdgeLabelling) : RatPoly :=
  polyAdd
    (reflectedSourceWavefunction left)
    (polySmul (-1) (reflectedTargetWavefunction right))

theorem geometricBF4WavefunctionOfState_term_length
    (state : EdgeLabelling) (term : RatTerm)
    (hterm : term ∈ geometricBF4WavefunctionOfState state) :
    term.1.length = 20 := by
  unfold geometricBF4WavefunctionOfState geometricBF4Wavefunction
    integrateEighteenChords at hterm
  simp only [List.mem_map] at hterm
  rcases hterm with ⟨source, _, rfl⟩
  exact retainedFiveMonomial_length source.1

theorem geometricBF4WavefunctionOfState_supported_ten
    (state : EdgeLabelling) :
    SupportedQuaternionBlocks 10
      (geometricBF4WavefunctionOfState state) := by
  intro term hterm
  rw [geometricBF4WavefunctionOfState_term_length
    state term hterm]
  omega

theorem reflectedSourceWavefunction_supported
    (state : EdgeLabelling) :
    SupportedQuaternionBlocks 10
      (reflectedSourceWavefunction state) := by
  exact geometricBF4WavefunctionOfState_supported_ten state

theorem reflectedTargetWavefunction_supported
    (state : EdgeLabelling) :
    SupportedQuaternionBlocks 10
      (reflectedTargetWavefunction state) := by
  intro term hterm
  unfold reflectedTargetWavefunction targetGeometricWavefunction
    shiftPolynomial at hterm
  simp only [List.mem_map] at hterm
  rcases hterm with ⟨source, hsource, rfl⟩
  simp only [List.length_append, List.length_replicate]
  have hsourceLength :
      source.1.length = 20 :=
    geometricBF4WavefunctionOfState_term_length state source hsource
  rw [hsourceLength]
  omega

private theorem supported_polyAdd_ten
    {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks 10 left)
    (hright : SupportedQuaternionBlocks 10 right) :
    SupportedQuaternionBlocks 10 (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  rcases hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polySmul_ten
    (coefficient : Q') {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks 10 polynomial) :
    SupportedQuaternionBlocks 10
      (polySmul coefficient polynomial) := by
  intro term hterm
  simp only [polySmul, List.mem_map] at hterm
  rcases hterm with ⟨source, hsource, rfl⟩
  exact hsupport source hsource

theorem reflectedSumWavefunction_supported
    (left right : EdgeLabelling) :
    SupportedQuaternionBlocks 10
      (reflectedSumWavefunction left right) := by
  exact supported_polyAdd_ten
    (reflectedSourceWavefunction_supported left)
    (reflectedTargetWavefunction_supported right)

theorem reflectedDifferenceWavefunction_supported
    (left right : EdgeLabelling) :
    SupportedQuaternionBlocks 10
      (reflectedDifferenceWavefunction left right) := by
  exact supported_polyAdd_ten
    (reflectedSourceWavefunction_supported left)
    (supported_polySmul_ten (-1)
      (reflectedTargetWavefunction_supported right))

/-! ## 2. Finite reflected Haar polarization -/

private def weightedHaar
    (left right kernel : RatPoly) : Q' :=
  tenfoldHaar (polyMul (polyMul left right) kernel)

private theorem weightedHaar_symmetric
    (left right kernel : RatPoly) :
    weightedHaar left right kernel ≈
      weightedHaar right left kernel := by
  unfold weightedHaar
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul kernel (polyMul left right))) _
    (quaternionHaar_polyMul_comm
      10 (polyMul left right) kernel) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul kernel (polyMul right left))) _
    (quaternionHaar_polyMul_middle_comm
      10 kernel left right) ?_
  exact quaternionHaar_polyMul_comm
    10 kernel (polyMul right left)

private theorem weightedHaar_add_left
    (first second right kernel : RatPoly) :
    weightedHaar (polyAdd first second) right kernel ≈
      weightedHaar first right kernel +
        weightedHaar second right kernel := by
  unfold weightedHaar
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul (polyAdd first second)
        (polyMul right kernel))) _
    (quaternionHaar_polyMul_assoc
      10 (polyAdd first second) right kernel) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul (polyMul right kernel)
        (polyAdd first second))) _
    (quaternionHaar_polyMul_comm
      10 (polyAdd first second)
        (polyMul right kernel)) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar (polyMul (polyMul right kernel) first) +
      tenfoldHaar (polyMul (polyMul right kernel) second)) _
    (quaternionHaar_polyMul_add_right
      10 (polyMul right kernel) first second) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_comm
        10 (polyMul right kernel) first)
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc
          10 first right kernel)))
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_comm
        10 (polyMul right kernel) second)
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc
          10 second right kernel)))

private theorem weightedHaar_add_right
    (left first second kernel : RatPoly) :
    weightedHaar left (polyAdd first second) kernel ≈
      weightedHaar left first kernel +
        weightedHaar left second kernel := by
  refine Q'.eqv_trans _
    (weightedHaar (polyAdd first second) left kernel) _
    (weightedHaar_symmetric
      left (polyAdd first second) kernel) ?_
  refine Q'.eqv_trans _
    (weightedHaar first left kernel +
      weightedHaar second left kernel) _
    (weightedHaar_add_left first second left kernel) ?_
  exact Q'.add_eqv_congr'
    (weightedHaar_symmetric first left kernel)
    (weightedHaar_symmetric second left kernel)

private theorem weightedHaar_smul_left
    (coefficient : Q') (left right kernel : RatPoly) :
    weightedHaar (polySmul coefficient left) right kernel ≈
      coefficient * weightedHaar left right kernel := by
  refine Q'.eqv_trans _
    (weightedHaar right
      (polySmul coefficient left) kernel) _
    (weightedHaar_symmetric
      (polySmul coefficient left) right kernel) ?_
  unfold weightedHaar
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul (polyMul kernel right)
        (polySmul coefficient left))) _
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_comm
        10 (polyMul right
          (polySmul coefficient left)) kernel)
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc
          10 kernel right
            (polySmul coefficient left)))) ?_
  refine Q'.eqv_trans _
    (coefficient *
      tenfoldHaar
        (polyMul (polyMul kernel right) left)) _
    (quaternionHaar_polyMul_smul_right
      10 coefficient (polyMul kernel right) left) ?_
  exact Q'.mul_eqv_congr_left coefficient _ _
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_comm
        10 (polyMul kernel right) left)
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_middle_comm
          10 left kernel right)
        (Q'.eqv_symm
          (quaternionHaar_polyMul_assoc
            10 left right kernel))))

private theorem weightedHaar_smul_right
    (coefficient : Q') (left right kernel : RatPoly) :
    weightedHaar left (polySmul coefficient right) kernel ≈
      coefficient * weightedHaar left right kernel := by
  refine Q'.eqv_trans _
    (weightedHaar (polySmul coefficient right) left kernel) _
    (weightedHaar_symmetric
      left (polySmul coefficient right) kernel) ?_
  refine Q'.eqv_trans _
    (coefficient * weightedHaar right left kernel) _
    (weightedHaar_smul_left coefficient right left kernel) ?_
  exact Q'.mul_eqv_congr_left coefficient _ _
    (weightedHaar_symmetric right left kernel)

private theorem negOne_mul_eqv_neg (value : Q') :
    (-1 : Q') * value ≈ -value := by
  q_ring

private theorem four_mul_eqv (value : Q') :
    (4 : Q') * value ≈
      (value + value) + (value + value) := by
  have hfour :
      (4 : Q') ≈
        (((1 : Q') + 1) + (1 + 1)) := by
    decide
  have htwo :
      ((1 : Q') + 1) * value ≈
        value + value := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv 1 1 value)
      (Q'.add_eqv_congr'
        (Q'.one_mul_eqv value)
        (Q'.one_mul_eqv value))
  refine Q'.eqv_trans _
    ((((1 : Q') + 1) + (1 + 1)) * value) _
    (Q'.mul_eqv_congr_right
      (4 : Q') (((1 : Q') + 1) + (1 + 1))
      value hfour) ?_
  refine Q'.eqv_trans _
    (((1 : Q') + 1) * value +
      ((1 : Q') + 1) * value) _
    (Q'.add_mul_eqv
      ((1 : Q') + 1) (1 + 1) value) ?_
  exact Q'.add_eqv_congr' htwo htwo

private theorem polarization_scalar
    (ll lr rr : Q') :
    Q'.mkPos 1 4 (by decide) *
        (((ll + lr) + (lr + rr)) +
          (-((ll + (-lr)) + ((-lr) + rr)))) ≈
      lr := by
  have hneg :
      (-((ll + (-lr)) + ((-lr) + rr))) ≈
        ((-ll + lr) + (lr + (-rr))) := by
    refine Q'.eqv_trans _
      ((-(ll + (-lr))) + (-((-lr) + rr))) _
      (Q'.neg_add_eqv
        (ll + (-lr)) ((-lr) + rr)) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv ll (-lr))
        (Q'.add_eqv_congr_left (-ll) _ _
          (Q'.neg_neg_eqv lr)))
      (Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv (-lr) rr)
        (Q'.add_eqv_congr'
          (Q'.neg_neg_eqv lr)
          (Q'.eqv_refl (-rr))))
  have hrearrange :
      (((ll + lr) + (lr + rr)) +
          ((-ll + lr) + (lr + (-rr)))) ≈
        ((ll + (-ll)) + (rr + (-rr))) +
          ((lr + lr) + (lr + lr)) := by
    q_ring
  have hcollapse :
      ((ll + (-ll)) + (rr + (-rr))) +
          ((lr + lr) + (lr + lr)) ≈
        (lr + lr) + (lr + lr) := by
    refine Q'.eqv_trans _
      ((0 : Q') + 0 +
        ((lr + lr) + (lr + lr))) _ ?_ ?_
    · exact Q'.add_eqv_congr_right
        ((ll + (-ll)) + (rr + (-rr))) _ _
        (Q'.add_eqv_congr'
          (Q'.add_neg_self_eqv ll)
          (Q'.add_neg_self_eqv rr))
    · refine Q'.eqv_trans _
        ((0 : Q') + ((lr + lr) + (lr + lr))) _ ?_ ?_
      · exact Q'.add_eqv_congr_right
          ((0 : Q') + 0) 0
          ((lr + lr) + (lr + lr))
          (by decide)
      · exact QPoly.q_zero_add_eqv _
  refine Q'.eqv_trans _
    (Q'.mkPos 1 4 (by decide) *
      (((ll + lr) + (lr + rr)) +
        ((-ll + lr) + (lr + (-rr))))) _
    (Q'.mul_eqv_congr_left
      (Q'.mkPos 1 4 (by decide)) _ _
      (Q'.add_eqv_congr_left
        ((ll + lr) + (lr + rr)) _ _ hneg)) ?_
  refine Q'.eqv_trans _
    (Q'.mkPos 1 4 (by decide) *
      (((ll + (-ll)) + (rr + (-rr))) +
        ((lr + lr) + (lr + lr)))) _
    (Q'.mul_eqv_congr_left
      (Q'.mkPos 1 4 (by decide)) _ _
      hrearrange) ?_
  refine Q'.eqv_trans _
    (Q'.mkPos 1 4 (by decide) *
      ((lr + lr) + (lr + lr))) _
    (Q'.mul_eqv_congr_left
      (Q'.mkPos 1 4 (by decide)) _ _
      hcollapse) ?_
  refine Q'.eqv_trans _
    (Q'.mkPos 1 4 (by decide) *
      ((4 : Q') * lr)) _
    (Q'.mul_eqv_congr_left
      (Q'.mkPos 1 4 (by decide)) _ _
      (Q'.eqv_symm (four_mul_eqv lr))) ?_
  refine Q'.eqv_trans _
    ((Q'.mkPos 1 4 (by decide) * (4 : Q')) * lr) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.mkPos 1 4 (by decide)) 4 lr)) ?_
  refine Q'.eqv_trans _
    ((1 : Q') * lr) _
    (Q'.mul_eqv_congr_right _ _ lr (by decide)) ?_
  exact Q'.one_mul_eqv lr

private theorem weightedHaar_square_add
    (left right kernel : RatPoly) :
    weightedHaar
        (polyAdd left right) (polyAdd left right) kernel ≈
      (weightedHaar left left kernel +
          weightedHaar left right kernel) +
        (weightedHaar right left kernel +
          weightedHaar right right kernel) := by
  refine Q'.eqv_trans _
    (weightedHaar left (polyAdd left right) kernel +
      weightedHaar right (polyAdd left right) kernel) _
    (weightedHaar_add_left left right
      (polyAdd left right) kernel) ?_
  exact Q'.add_eqv_congr'
    (weightedHaar_add_right left left right kernel)
    (weightedHaar_add_right right left right kernel)

private theorem weightedHaar_square_sub
    (left right kernel : RatPoly) :
    weightedHaar
        (polyAdd left (polySmul (-1) right))
        (polyAdd left (polySmul (-1) right))
        kernel ≈
      (weightedHaar left left kernel +
          -(weightedHaar left right kernel)) +
        (-(weightedHaar right left kernel) +
          weightedHaar right right kernel) := by
  let negativeRight := polySmul (-1) right
  refine Q'.eqv_trans _
    ((weightedHaar left left kernel +
        weightedHaar left negativeRight kernel) +
      (weightedHaar negativeRight left kernel +
        weightedHaar negativeRight negativeRight kernel)) _
    (weightedHaar_square_add left negativeRight kernel) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.add_eqv_congr_left
      (weightedHaar left left kernel) _ _
      (Q'.eqv_trans _ _ _
        (weightedHaar_smul_right (-1)
          left right kernel)
        (negOne_mul_eqv_neg
          (weightedHaar left right kernel)))
  · refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (weightedHaar_smul_left (-1)
          right left kernel)
        (negOne_mul_eqv_neg
          (weightedHaar right left kernel))
    · refine Q'.eqv_trans _
        ((-1) *
          weightedHaar right negativeRight kernel) _
        (weightedHaar_smul_left (-1)
          right negativeRight kernel) ?_
      refine Q'.eqv_trans _
        ((-1) * ((-1) *
          weightedHaar right right kernel)) _
        (Q'.mul_eqv_congr_left (-1) _ _
          (weightedHaar_smul_right (-1)
            right right kernel)) ?_
      q_ring

/-- Exact finite Haar polarization for an arbitrary kernel polynomial. -/
theorem weightedHaar_polarization
    (left right kernel : RatPoly) :
    (Q'.mkPos 1 4 (by decide)) *
        (weightedHaar
            (polyAdd left right)
            (polyAdd left right) kernel +
          -(weightedHaar
            (polyAdd left (polySmul (-1) right))
            (polyAdd left (polySmul (-1) right))
            kernel)) ≈
      weightedHaar left right kernel := by
  let ll := weightedHaar left left kernel
  let lr := weightedHaar left right kernel
  let rl := weightedHaar right left kernel
  let rr := weightedHaar right right kernel
  refine Q'.eqv_trans _
    (Q'.mkPos 1 4 (by decide) *
      (((ll + lr) + (rl + rr)) +
        (-((ll + (-lr)) + ((-rl) + rr))))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (Q'.mkPos 1 4 (by decide)) _ _
      (Q'.add_eqv_congr'
        (weightedHaar_square_add left right kernel)
        (Q'.neg_eqv_congr _ _
          (weightedHaar_square_sub left right kernel)))
  · have hsymm : rl ≈ lr :=
      weightedHaar_symmetric right left kernel
    change
      Q'.mkPos 1 4 (by decide) *
          (((ll + lr) + (rl + rr)) +
            (-((ll + (-lr)) + ((-rl) + rr)))) ≈
        lr
    refine Q'.eqv_trans _
      (Q'.mkPos 1 4 (by decide) *
        (((ll + lr) + (lr + rr)) +
          (-((ll + (-lr)) + ((-lr) + rr))))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        (Q'.mkPos 1 4 (by decide)) _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left (ll + lr) _ _
            (Q'.add_eqv_congr_right rl lr rr hsymm))
          (Q'.neg_eqv_congr _ _
            (Q'.add_eqv_congr_left (ll + (-lr)) _ _
              (Q'.add_eqv_congr_right (-rl) (-lr) rr
                (Q'.neg_eqv_congr _ _ hsymm)))))
    · exact polarization_scalar ll lr rr

/-! ## 3. Located reflected coefficient and exact all-spin identification -/

/-- The finite polarized physical Taylor partial. -/
def reflectedPhysicalTaylorPartial
    (left right : EdgeLabelling) (terms : Nat) : Q' :=
  Q'.mkPos 1 4 (by decide) *
    (compactPhysicalNegativeTaylorQuadraticPartial
        (reflectedSumWavefunction left right) terms +
      -(compactPhysicalNegativeTaylorQuadraticPartial
        (reflectedDifferenceWavefunction left right) terms))

/-- Each finite polarized coefficient is the genuine source/target
all-spin double-Haar coefficient. -/
theorem reflectedPhysicalTaylorPartial_eq_geometric
    (left right : EdgeLabelling) :
    ∀ terms : Nat,
      reflectedPhysicalTaylorPartial left right terms ≈
        geometricMehlerTaylorPartial left right terms
  | 0 => by
      change
        Q'.mkPos 1 4 (by decide) * (0 + -0) ≈ 0
      decide
  | terms + 1 => by
      change
        Q'.mkPos 1 4 (by decide) *
            ((compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedSumWavefunction left right) terms +
                compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedSumWavefunction left right)
                    (reflectedSumWavefunction left right))
                  terms) +
              -(compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedDifferenceWavefunction left right) terms +
                compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedDifferenceWavefunction left right)
                    (reflectedDifferenceWavefunction left right))
                  terms)) ≈
          geometricMehlerTaylorPartial left right terms +
            geometricMehlerTaylorTerm left right terms
      let source := reflectedSourceWavefunction left
      let target := reflectedTargetWavefunction right
      let kernel :=
        negativeExponentialPolynomialTerm
          compactCoupledBF4ActionPolynomial terms
      have hterm :
          Q'.mkPos 1 4 (by decide) *
              (compactPhysicalNegativeTaylorHaarTerm
                    (polyMul
                      (reflectedSumWavefunction left right)
                      (reflectedSumWavefunction left right))
                    terms +
                -(compactPhysicalNegativeTaylorHaarTerm
                    (polyMul
                      (reflectedDifferenceWavefunction left right)
                      (reflectedDifferenceWavefunction left right))
                    terms)) ≈
            geometricMehlerTaylorTerm left right terms := by
        change
          Q'.mkPos 1 4 (by decide) *
              (weightedHaar
                  (polyAdd source target)
                  (polyAdd source target) kernel +
                -(weightedHaar
                  (polyAdd source (polySmul (-1) target))
                  (polyAdd source (polySmul (-1) target))
                  kernel)) ≈
            weightedHaar source target kernel
        exact weightedHaar_polarization source target kernel
      have hprevious :=
        reflectedPhysicalTaylorPartial_eq_geometric
          left right terms
      change
        Q'.mkPos 1 4 (by decide) *
            ((compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedSumWavefunction left right) terms +
                compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedSumWavefunction left right)
                    (reflectedSumWavefunction left right))
                  terms) +
              -(compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedDifferenceWavefunction left right) terms +
                compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedDifferenceWavefunction left right)
                    (reflectedDifferenceWavefunction left right))
                  terms)) ≈
          geometricMehlerTaylorPartial left right terms +
            geometricMehlerTaylorTerm left right terms
      refine Q'.eqv_trans _
        (Q'.mkPos 1 4 (by decide) *
            ((compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedSumWavefunction left right) terms +
                -(compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedDifferenceWavefunction left right) terms)) +
              (compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedSumWavefunction left right)
                    (reflectedSumWavefunction left right))
                  terms +
                -(compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedDifferenceWavefunction left right)
                    (reflectedDifferenceWavefunction left right))
                  terms)))) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left
          (Q'.mkPos 1 4 (by decide)) _ _ (by q_ring)
      refine Q'.eqv_trans _
        (Q'.mkPos 1 4 (by decide) *
              (compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedSumWavefunction left right) terms +
                -(compactPhysicalNegativeTaylorQuadraticPartial
                  (reflectedDifferenceWavefunction left right) terms)) +
          Q'.mkPos 1 4 (by decide) *
              (compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedSumWavefunction left right)
                    (reflectedSumWavefunction left right))
                  terms +
                -(compactPhysicalNegativeTaylorHaarTerm
                  (polyMul
                    (reflectedDifferenceWavefunction left right)
                    (reflectedDifferenceWavefunction left right))
                  terms))) _ (Q'.mul_add_eqv _ _ _) ?_
      exact Q'.add_eqv_congr' hprevious hterm

/-- The located reflected source/target coefficient obtained solely from
the two already-located diagonal physical quadratics. -/
def reflectedPhysicalCoefficient
    (left right : EdgeLabelling) : CReal :=
  CReal.mul
    (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
    (CReal.add
      (compactPhysicalNegativeTaylorQuadraticLimit
        (reflectedSumWavefunction left right)
        (reflectedSumWavefunction_supported left right))
      (CReal.neg
        (compactPhysicalNegativeTaylorQuadraticLimit
          (reflectedDifferenceWavefunction left right)
          (reflectedDifferenceWavefunction_supported left right))))

private theorem scale_two_sided
    (a u v delta : Q') (hdelta : (0 : Q') ≤ delta)
    (hlower : -delta ≤ u + -v)
    (hupper : u + -v ≤ delta) :
    a * u + -(a * v) ≤ Q'.abs a * delta ∧
      -(Q'.abs a * delta) ≤ a * u + -(a * v) := by
  have hfactor :
      a * u + -(a * v) ≈
        a * (u + -v) := by
    refine Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv a u (-v)) ?_)
    exact Q'.add_eqv_congr_left
      (a * u) _ _
      (Q'.mul_neg_eqv a v)
  have haUpper : a ≤ Q'.abs a :=
    Q'.le_abs_self a
  have haLower : -(Q'.abs a) ≤ a := by
    have hneg := Q'.neg_le_neg (Q'.neg_le_abs a)
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv (Q'.neg_neg_eqv a))
  have habs0 : (0 : Q') ≤ Q'.abs a :=
    Q'.abs_nonneg a
  have hpositive :
      a * (u + -v) ≤ Q'.abs a * delta :=
    Q'.mul_le_of_bounds
      habs0 hdelta haLower haUpper
      hlower hupper
  have hnegative :
      -(Q'.abs a * delta) ≤ a * (u + -v) := by
    have hnegLower : -(Q'.abs a) ≤ -a :=
      Q'.neg_le_neg haUpper
    have hnegUpper : -a ≤ Q'.abs a :=
      Q'.neg_le_abs a
    have hmul :
        (-a) * (u + -v) ≤
          Q'.abs a * delta :=
      Q'.mul_le_of_bounds
        habs0 hdelta hnegLower hnegUpper
        hlower hupper
    have hnegMul :
        (-a) * (u + -v) ≈
          -(a * (u + -v)) :=
      Q'.neg_mul_eqv a (u + -v)
    have hto :
        -(a * (u + -v)) ≤
          Q'.abs a * delta :=
      Q'.le_trans' _ _ _
        (Q'.ge_of_eqv hnegMul) hmul
    have hflip := Q'.neg_le_neg hto
    exact Q'.le_trans' _ _ _ hflip
      (Q'.le_of_eqv
        (Q'.neg_neg_eqv (a * (u + -v))))
  exact
    ⟨Q'.le_trans' _ _ _
      (Q'.le_of_eqv hfactor) hpositive,
     Q'.le_trans' _ _ _ hnegative
      (Q'.ge_of_eqv hfactor)⟩

/-- Rational constant scaling preserves constructive convergence. -/
private theorem convergesTo_scale
    (a : Q') {sequence : Nat → CReal} {limit : CReal}
    (hconverges : CReal.ConvergesTo sequence limit) :
    CReal.ConvergesTo
      (fun terms =>
        CReal.mul (CReal.ofQ' a) (sequence terms))
      (CReal.mul (CReal.ofQ' a) limit) := by
  intro epsilon hepsilon
  obtain ⟨delta, hdeltaPos, hdelta⟩ :=
    CReal.exists_mul_le
      (Q'.abs_nonneg a) hepsilon
  obtain ⟨stage, hstage⟩ :=
    hconverges delta hdeltaPos
  refine ⟨stage, fun terms hterms => ?_⟩
  obtain ⟨approximation, happ⟩ :=
    hstage terms hterms
  refine ⟨approximation, fun n hn => ?_⟩
  obtain ⟨hforward, hbackward⟩ :=
    happ n hn
  have hupper :
      (sequence terms).approx n +
          -(limit.approx n) ≤ delta :=
    Q'.sub_le_of_le_add hforward
  have hlower :
      -delta ≤
        (sequence terms).approx n +
          -(limit.approx n) :=
    Q'.neg_le_sub_of_le_add hbackward
  have hscaled :=
    (scale_two_sided a
      ((sequence terms).approx n)
      (limit.approx n) delta
      (Q'.le_of_lt hdeltaPos)
      hlower hupper).1
  have hupper' :
      limit.approx n +
          -((sequence terms).approx n) ≤ delta :=
    Q'.sub_le_of_le_add hbackward
  have hlower' :
      -delta ≤
        limit.approx n +
          -((sequence terms).approx n) :=
    Q'.neg_le_sub_of_le_add hforward
  have hscaled' :=
    (scale_two_sided a
      (limit.approx n)
      ((sequence terms).approx n) delta
      (Q'.le_of_lt hdeltaPos)
      hlower' hupper').1
  change
    a * (sequence terms).approx n ≤
          a * limit.approx n + epsilon ∧
      a * limit.approx n ≤
          a * (sequence terms).approx n + epsilon
  exact
    ⟨Q'.le_add_of_sub_le
      (Q'.le_trans' _ _ _ hscaled hdelta),
     Q'.le_add_of_sub_le
      (Q'.le_trans' _ _ _ hscaled' hdelta)⟩

/-- The finite polarized physical partials converge to the polarization of
the two located diagonal compact-action limits. -/
theorem reflectedPhysicalTaylorPartial_converges
    (left right : EdgeLabelling) :
    CReal.ConvergesTo
      (fun terms =>
        CReal.ofQ'
          (reflectedPhysicalTaylorPartial
            left right terms))
      (reflectedPhysicalCoefficient left right) := by
  let plusPartial :=
    fun terms =>
      compactPhysicalNegativeTaylorQuadraticPartial
        (reflectedSumWavefunction left right) terms
  let minusPartial :=
    fun terms =>
      compactPhysicalNegativeTaylorQuadraticPartial
        (reflectedDifferenceWavefunction left right) terms
  let plusLimit :=
    compactPhysicalNegativeTaylorQuadraticLimit
      (reflectedSumWavefunction left right)
      (reflectedSumWavefunction_supported left right)
  let minusLimit :=
    compactPhysicalNegativeTaylorQuadraticLimit
      (reflectedDifferenceWavefunction left right)
      (reflectedDifferenceWavefunction_supported left right)
  have hplus :
      CReal.ConvergesTo
        (fun terms => CReal.ofQ' (plusPartial terms))
        plusLimit :=
    compactPhysicalNegativeTaylorQuadraticPartial_converges
      (reflectedSumWavefunction left right)
      (reflectedSumWavefunction_supported left right)
  have hminus :
      CReal.ConvergesTo
        (fun terms => CReal.ofQ' (minusPartial terms))
        minusLimit :=
    compactPhysicalNegativeTaylorQuadraticPartial_converges
      (reflectedDifferenceWavefunction left right)
      (reflectedDifferenceWavefunction_supported left right)
  have hnegative :=
    YMGap.Constructive.TrigAddCReal.convergesTo_neg
      hminus
  have hadd :=
    YMGap.Constructive.TrigAddCReal.convergesTo_add
      hplus hnegative
  have hdifference :
      CReal.ConvergesTo
        (fun terms =>
          CReal.ofQ'
            (plusPartial terms + -(minusPartial terms)))
        (CReal.add plusLimit (CReal.neg minusLimit)) := by
    exact
      YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
        (fun terms =>
          YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
            (fun _ => Q'.eqv_refl _))
        hadd
  have hscaled :=
    convergesTo_scale
      (Q'.mkPos 1 4 (by decide))
      hdifference
  exact
    YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (fun terms =>
        YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
          (fun _ => Q'.eqv_refl _))
      hscaled

/-- **Reflected all-spin Peter--Weyl bridge.**  Constructive polarization of
the physical compact diagonal limit is exactly the coupled geometric
source/target double-Haar endpoint coefficient. -/
theorem reflectedPhysicalCoefficient_equiv_geometric
    (left right : EdgeLabelling) :
    CReal.Equiv
      (reflectedPhysicalCoefficient left right)
      (geometricMehlerHaarCoefficient left right) := by
  have hgeometric :
      CReal.ConvergesTo
        (fun terms =>
          CReal.ofQ'
            (geometricMehlerTaylorPartial
              left right terms))
        (geometricMehlerHaarCoefficient
          left right) := by
    simpa using
      CReal.convergesTo_self
        (geometricMehlerHaarCoefficient left right)
  exact CReal.Equiv_of_limit_of_equal
    (fun terms =>
      YMGap.Constructive.TrigAdd.equiv_ofQ'_of_eqv
        (reflectedPhysicalTaylorPartial_eq_geometric
          left right terms))
    (reflectedPhysicalTaylorPartial_converges
      left right)
    hgeometric

end YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge

#print axioms YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge.geometricBF4WavefunctionOfState_supported_ten
#print axioms YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge.weightedHaar_polarization
#print axioms YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge.reflectedPhysicalTaylorPartial_eq_geometric
#print axioms YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge.reflectedPhysicalCoefficient
#print axioms YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge.reflectedPhysicalCoefficient_equiv_geometric
