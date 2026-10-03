/-
# Exact antipodal jets of the original two-block heat prefix

The lower quaternion is the identity and the upper quaternion its antipode.
The selected upper rotation is the literal coordinate-plane field D_(4,5).
All packet labels through the inclusive K are retained. These are evaluation
identities, not Haar inequalities, curvature certificates, or an interacting
Wilson-action counterexample. The scalar second jet is cleared by THREE.
-/

import YMGap.Continuum.SU2HeatAntipodalPrefixBounds
import YMGap.Continuum.QuaternionHaarCharacterDerivative
import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.RationalQuaternionRatPoly
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.SU2QuaternionAngularSupport

namespace YMGap.Continuum.SU2QuaternionAntipodalHeatJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum const_mul_finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq evalMono)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.QuaternionHaarCharacterDerivative
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt heatAt)
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState (coeffAt_heatKernelPacket)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RGTransport (dimQ c4)
open YMGap.Continuum.HeatKernelRGStep (ofNat_mul_eqv)
open YMGap.Continuum.SU2HeatAntipodalPrefixBounds (endpointValue endpointSecondThree)

local infix:50 " ≈ " => Q'.eqv

/-- Original lower identity and upper antipode; unused coordinates are zero. -/
def antipodalEnvironment : Nat → Q'
  | 0 => 1
  | 4 => -1
  | _ => 0

/-- The actual upper coordinate-plane angular derivative. -/
def upperAngular (p : RatPoly) : RatPoly := angularDerivative 4 5 p

/-- Both original quaternion blocks are unit points. -/
theorem antipodalEnvironment_unit (block : Nat) (hb : block < 2) :
    ((antipodalEnvironment (4*block))*(antipodalEnvironment (4*block)) +
      (antipodalEnvironment (4*block+1))*(antipodalEnvironment (4*block+1))) +
    ((antipodalEnvironment (4*block+2))*(antipodalEnvironment (4*block+2)) +
      (antipodalEnvironment (4*block+3))*(antipodalEnvironment (4*block+3))) ≈ 1 := by
  have h : block=0 ∨ block=1 := by omega
  rcases h with rfl | rfl <;> decide

private def E (p : RatPoly) : Q' := evalRatPoly antipodalEnvironment p
private def sigma (j : Nat) : Q' := (-1 : Q')^j

private def packetTerm (w : Q') (K j : Nat) : RatPoly :=
  polySmul (SU2CharacterVacuumHaar.coeffAt
    (Z4FiniteBoxHeatKernelPacketState.heatKernelPacket K w) j)
    (characterPolynomial (scalarAt 0 1) j)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)

private theorem eval_coeff {p q : RatPoly} (h : RatPolyCoeffEqv p q) : E p ≈ E q := by
  simpa only [weighted_eval] using h (evalMono antipodalEnvironment)

private theorem eval_cap (c : Q') : E (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul _ c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one _))
      (Q'.mul_one_eqv _))

private theorem eval_add (p q : RatPoly) : E (polyAdd p q) ≈ E p+E q :=
  evalRatPoly_add _ p q

private theorem eval_mul (p q : RatPoly) : E (polyMul p q) ≈ E p*E q :=
  evalRatPoly_mul _ p q

private theorem eval_smul (c : Q') (p : RatPoly) : E (polySmul c p) ≈ c*E p :=
  evalRatPoly_smul _ c p

private theorem scalar_value : E (scalarAt 0 1) ≈ -1 := by decide
private theorem scalar_first : E (upperAngular (scalarAt 0 1)) ≈ 0 := by decide
private theorem scalar_second : E (upperAngular (upperAngular (scalarAt 0 1))) ≈ 1 := by decide

private theorem sigma_succ (n : Nat) : sigma (n+1) ≈ -(sigma n) :=
  poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
    (by decide) (fun _ => sigma n)

private theorem sigma_two (n : Nat) : sigma (n+2) ≈ sigma n :=
  poly_identity_of_normal_eq
    (.mul (.const (-1)) (.mul (.const (-1)) (.var 0))) (.var 0)
    (by decide) (fun _ => sigma n)

private theorem sigma_three (n : Nat) : sigma (n+3) ≈ -(sigma n) :=
  Q'.eqv_trans _ _ _ (sigma_succ (n+2)) (Q'.neg_eqv_congr _ _ (sigma_two n))

private theorem nat_shift (n k : Nat) : Q'.ofNat (n+k) ≈ Q'.ofNat n+Q'.ofNat k :=
  Q'.ofNat_add_eqv n k

private theorem character_value : ∀ n : Nat,
    E (characterPolynomial (scalarAt 0 1) n) ≈ sigma n*Q'.ofNat (n+1)
  | 0 => evalRatPoly_one _
  | 1 => Q'.eqv_trans _ _ _ (eval_smul 2 _)
      (Q'.eqv_trans _ _ _ (mul_congr (Q'.eqv_refl 2) scalar_value)
        (Q'.mul_comm_eqv 2 (-1)))
  | n+2 => by
    let x := scalarAt 0 1
    let z := Q'.ofNat n
    have hn : E (characterPolynomial x n) ≈ sigma n*(z+1) :=
      Q'.eqv_trans _ _ _ (character_value n)
        (mul_congr (Q'.eqv_refl _) (nat_shift n 1))
    have hp : E (characterPolynomial x (n+1)) ≈ (-(sigma n))*(z+2) :=
      Q'.eqv_trans _ _ _ (character_value (n+1))
        (mul_congr (sigma_succ n) (nat_shift n 2))
    have h : E (characterPolynomial x (n+2)) ≈
        (2*(-1))*((-(sigma n))*(z+2))+(-1)*(sigma n*(z+1)) :=
      Q'.eqv_trans _ _ _ (eval_add _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (eval_mul _ _)
            (mul_congr (Q'.eqv_trans _ _ _ (eval_smul 2 x)
              (mul_congr (Q'.eqv_refl _) scalar_value)) hp))
          (Q'.eqv_trans _ _ _ (eval_smul (-1) _) (mul_congr (Q'.eqv_refl _) hn)))
    refine Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ (sigma n*(z+3)) _ ?_ ?_)
    · exact poly_identity_of_normal_eq
        (.add (.mul (.mul (.const 2) (.const (-1)))
          (.mul (.neg (.var 0)) (.add (.var 1) (.const 2))))
          (.mul (.const (-1)) (.mul (.var 0) (.add (.var 1) (.const 1)))))
        (.mul (.var 0) (.add (.var 1) (.const 3)))
        (by decide) (fun
          | 0 => sigma n
          | _ => z)
    · exact Q'.eqv_symm (mul_congr (sigma_two n) (nat_shift n 3))

private theorem derivative_value_three : ∀ n : Nat,
    3*E (derivativePolynomial (scalarAt 0 1) n) ≈
      sigma (n+1)*((Q'.ofNat n*Q'.ofNat (n+1))*Q'.ofNat (n+2))
  | 0 => by decide
  | 1 => by decide
  | n+2 => by
    let x := scalarAt 0 1
    let z := Q'.ofNat n
    have hn : 3*E (derivativePolynomial x n) ≈
        (-(sigma n))*((z*(z+1))*(z+2)) :=
      Q'.eqv_trans _ _ _ (derivative_value_three n)
        (mul_congr (sigma_succ n)
          (mul_congr (mul_congr (Q'.eqv_refl _) (nat_shift n 1)) (nat_shift n 2)))
    have hp : E (characterPolynomial x (n+1)) ≈ (-(sigma n))*(z+2) :=
      Q'.eqv_trans _ _ _ (character_value (n+1))
        (mul_congr (sigma_succ n) (nat_shift n 2))
    have hterm : E (polyMul (cap 2)
        (polyMul (cap (Q'.ofNat (n+2))) (characterPolynomial x (n+1)))) ≈
        2*((z+2)*((-(sigma n))*(z+2))) :=
      Q'.eqv_trans _ _ _ (eval_mul _ _)
        (mul_congr (eval_cap 2) (Q'.eqv_trans _ _ _ (eval_mul _ _)
          (mul_congr (Q'.eqv_trans _ _ _ (eval_cap _) (nat_shift n 2)) hp)))
    have h : 3*E (derivativePolynomial x (n+2)) ≈
        (-(sigma n))*((z*(z+1))*(z+2)) +
          3*(2*((z+2)*((-(sigma n))*(z+2)))) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_add _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
          (Q'.add_eqv_congr' hn (mul_congr (Q'.eqv_refl _) hterm)))
    refine Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ ((-(sigma n))*(((z+2)*(z+3))*(z+4))) _ ?_ ?_)
    · exact poly_identity_of_normal_eq
        (.add (.mul (.neg (.var 0))
          (.mul (.mul (.var 1) (.add (.var 1) (.const 1))) (.add (.var 1) (.const 2))))
          (.mul (.const 3) (.mul (.const 2)
            (.mul (.add (.var 1) (.const 2))
              (.mul (.neg (.var 0)) (.add (.var 1) (.const 2)))))))
        (.mul (.neg (.var 0)) (.mul
          (.mul (.add (.var 1) (.const 2)) (.add (.var 1) (.const 3)))
          (.add (.var 1) (.const 4))))
        (by decide) (fun
          | 0 => sigma n
          | _ => z)
    · exact Q'.eqv_symm (mul_congr (sigma_three n)
        (mul_congr (mul_congr (nat_shift n 2) (nat_shift n 3)) (nat_shift n 4)))

private theorem character_first (j : Nat) :
    E (upperAngular (characterPolynomial (scalarAt 0 1) j)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (eval_coeff (angularDerivative_character_at 4 5 _ j))
    (Q'.eqv_trans _ _ _ (eval_mul _ _)
      (Q'.eqv_trans _ _ _ (mul_congr (Q'.eqv_refl _) scalar_first) (Q'.mul_zero_eqv _)))

private theorem character_second (j : Nat) :
    E (upperAngular (upperAngular (characterPolynomial (scalarAt 0 1) j))) ≈
      E (derivativePolynomial (scalarAt 0 1) j) := by
  let x := scalarAt 0 1
  let p := derivativePolynomial x j
  have h := (angularDerivative_congr 4 5 (angularDerivative_character_at 4 5 x j)).trans
    (angularDerivative_mul 4 5 p (upperAngular x))
  refine Q'.eqv_trans _ _ _ (eval_coeff h) (Q'.eqv_trans _ _ _ (eval_add _ _) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (eval_mul _ _) (mul_congr (Q'.eqv_refl _) scalar_first))
    (Q'.eqv_trans _ _ _ (eval_mul _ _) (mul_congr (Q'.eqv_refl _) scalar_second))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.const 0)) (.mul (.var 1) (.const 1))) (.var 1)
    (by decide) (fun
      | 0 => E (upperAngular p)
      | _ => E p)

private theorem finite_append (p : Nat → RatPoly) : ∀ xs ys : List Nat,
    finitePolySum p (xs++ys) = polyAdd (finitePolySum p xs) (finitePolySum p ys)
  | [], _ => rfl
  | j::xs, ys => by
      rw [List.cons_append]
      change polyAdd (p j) (finitePolySum p (xs++ys)) = _
      rw [finite_append p xs ys]
      exact (List.append_assoc _ _ _).symm

private theorem eval_range (p : Nat → RatPoly) : ∀ count,
    E (finitePolySum p (List.range count)) ≈ finSum (fun j => E (p j)) count
  | 0 => Q'.eqv_refl 0
  | count+1 => by
      rw [List.range_succ, finite_append]
      exact Q'.eqv_trans _ _ _ (eval_add _ _)
        (Q'.add_eqv_congr' (eval_range p count)
          (Q'.eqv_trans _ _ _ (eval_add _ _) (QPoly.q_add_zero_eqv _)))

private theorem sum_congr {p q : Nat → Q'} : ∀ count,
    (∀ j, j < count → p j ≈ q j) → finSum p count ≈ finSum q count
  | 0, _ => Q'.eqv_refl 0
  | count+1, h => Q'.add_eqv_congr'
      (sum_congr count (fun j hj => h j (by omega))) (h count (by omega))

private theorem nat_square (n : Nat) :
    Q'.ofNat (n^2) ≈ Q'.ofNat n*Q'.ofNat n := by
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using ofNat_mul_eqv n n

private theorem term_value (w : Q') (j : Nat) :
    coeffW w j*E (characterPolynomial (scalarAt 0 1) j) ≈
      sigma j*Q'.ofNat ((j+1)^2)*RGTransport.qpow w (c4 j) := by
  refine Q'.eqv_trans _ _ _ (mul_congr (Q'.eqv_refl _) (character_value j)) ?_
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 0)))
    (.mul (.mul (.var 2) (.mul (.var 0) (.var 0))) (.var 1))
    (by decide) (fun
      | 0 => Q'.ofNat (j+1)
      | 1 => RGTransport.qpow w (c4 j)
      | _ => sigma j)) ?_
  exact mul_congr (mul_congr (Q'.eqv_refl _)
    (Q'.eqv_symm (nat_square (j+1)))) (Q'.eqv_refl _)

private theorem term_second_three (w : Q') (j : Nat) :
    3*(coeffW w j*E (upperAngular (upperAngular (characterPolynomial (scalarAt 0 1) j)))) ≈
      sigma (j+1)*Q'.ofNat ((j+1)^2*c4 j)*RGTransport.qpow w (c4 j) := by
  have hp :
      3*(coeffW w j*E (upperAngular (upperAngular
        (characterPolynomial (scalarAt 0 1) j)))) ≈
      coeffW w j*(sigma (j+1)*
        ((Q'.ofNat j*Q'.ofNat (j+1))*Q'.ofNat (j+2))) :=
    Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.const 3) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.const 3) (.var 1)))
      (by decide) (fun
        | 0 => coeffW w j
        | _ => E (upperAngular
            (upperAngular (characterPolynomial (scalarAt 0 1) j)))))
    (mul_congr (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mul_congr (Q'.eqv_refl _) (character_second j)) (derivative_value_three j)))
  refine Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ ((sigma (j+1)*
      ((Q'.ofNat (j+1)*Q'.ofNat (j+1))*(Q'.ofNat j*Q'.ofNat (j+2))))*
        RGTransport.qpow w (c4 j)) _ ?_ ?_)
  · exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.mul (.var 3) (.var 0)) (.var 4))))
      (.mul (.mul (.var 2) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 4)))) (.var 1))
      (by decide) (fun
        | 0 => Q'.ofNat (j+1)
        | 1 => RGTransport.qpow w (c4 j)
        | 2 => sigma (j+1)
        | 3 => Q'.ofNat j
        | _ => Q'.ofNat (j+2))
  · have hc : Q'.ofNat ((j+1)^2*c4 j) ≈
        (Q'.ofNat (j+1)*Q'.ofNat (j+1))*(Q'.ofNat j*Q'.ofNat (j+2)) :=
      Q'.eqv_trans _ _ _ (ofNat_mul_eqv _ _)
        (mul_congr (nat_square (j+1)) (ofNat_mul_eqv j (j+2)))
    exact mul_congr (mul_congr (Q'.eqv_refl _) (Q'.eqv_symm hc)) (Q'.eqv_refl _)

/-- The actual original packet at the two-block antipode. -/
theorem heatAt_antipodal_value (w : Q') (K : Nat) :
    evalRatPoly antipodalEnvironment (heatAt 0 1 w K) ≈ endpointValue w K := by
  refine Q'.eqv_trans _ _ _ (eval_range (packetTerm w K) (K+1)) ?_
  apply sum_congr (K+1)
  intro j hj
  change E (polySmul (SU2CharacterVacuumHaar.coeffAt
    (Z4FiniteBoxHeatKernelPacketState.heatKernelPacket K w) j)
    (characterPolynomial (scalarAt 0 1) j)) ≈ _
  rw [coeffAt_heatKernelPacket hj]
  exact Q'.eqv_trans _ _ _ (eval_smul _ _) (term_value w j)

/-- The literal selected upper angular first jet vanishes. -/
theorem heatAt_antipodal_first (w : Q') (K : Nat) :
    evalRatPoly antipodalEnvironment (upperAngular (heatAt 0 1 w K)) ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (eval_coeff
    (angularDerivative_finitePolySum 4 5 (packetTerm w K) (List.range (K+1)))) ?_
  refine Q'.eqv_trans _ _ _ (eval_range _ (K+1)) ?_
  refine Q'.eqv_trans _ _ _ (sum_congr (K+1) (p := fun j =>
    E (upperAngular (packetTerm w K j)))
    (q := fun _ => 0) ?_) ?_
  · intro j _
    exact Q'.eqv_trans _ _ _ (eval_coeff (angularDerivative_smul 4 5 _ _))
      (Q'.eqv_trans _ _ _ (eval_smul _ _)
        (Q'.eqv_trans _ _ _ (mul_congr (Q'.eqv_refl _) (character_first j))
          (Q'.mul_zero_eqv _)))
  · simpa only [RationalTail.finSum_zero_seq] using Q'.eqv_refl (0 : Q')

/-- Exact second angular jet, cleared by three, with every original label. -/
theorem heatAt_antipodal_second_three (w : Q') (K : Nat) :
    3*evalRatPoly antipodalEnvironment (upperAngular (upperAngular (heatAt 0 1 w K))) ≈
      endpointSecondThree w K := by
  have hsum := (angularDerivative_congr 4 5
    (angularDerivative_finitePolySum 4 5 (packetTerm w K) (List.range (K+1)))).trans
    (angularDerivative_finitePolySum 4 5
      (fun j => upperAngular (packetTerm w K j)) (List.range (K+1)))
  have h : E (upperAngular (upperAngular (heatAt 0 1 w K))) ≈
      finSum (fun j => E (upperAngular (upperAngular
        (polySmul (SU2CharacterVacuumHaar.coeffAt
          (Z4FiniteBoxHeatKernelPacketState.heatKernelPacket K w) j)
          (characterPolynomial (scalarAt 0 1) j))))) (K+1) :=
    Q'.eqv_trans _ _ _ (eval_coeff hsum) (eval_range _ (K+1))
  refine Q'.eqv_trans _ _ _ (mul_congr (Q'.eqv_refl _) h) ?_
  refine Q'.eqv_trans _ _ _ (const_mul_finSum _ 3 (K+1)) ?_
  apply sum_congr (K+1)
  intro j hj
  rw [coeffAt_heatKernelPacket hj]
  have hjpin := (angularDerivative_congr 4 5
    (angularDerivative_smul 4 5 (coeffW w j) (characterPolynomial (scalarAt 0 1) j))).trans
    (angularDerivative_smul 4 5 (coeffW w j)
      (angularDerivative 4 5 (characterPolynomial (scalarAt 0 1) j)))
  exact Q'.eqv_trans _ _ _ (mul_congr (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
    (eval_coeff hjpin) (eval_smul _ _))) (term_second_three w j)

#print axioms antipodalEnvironment_unit
#print axioms heatAt_antipodal_value
#print axioms heatAt_antipodal_first
#print axioms heatAt_antipodal_second_three

end YMGap.Continuum.SU2QuaternionAntipodalHeatJets
