/-
# Same-action Haar realization for arbitrary signed BF4 boundary observables

Every exact finite signed slab bilinear form is the literal 116-link Haar
integral of a lower observable polynomial, the fixed-plane heat insertion,
and a reflected-upper observable polynomial. The three label sums are
separated before integration, using coefficient-probe distributivity and
the actual heat-weighted face factorization.

This realizes ALL boundary coefficients, not just the vacuum/constant
probes. No multiplicity-product law, diagonal comparison norm, or centering
condition is used. The formula is not itself reflection positivity: its
middle insertion still needs a positive reflected-channel resolution on
the literal link carrier. No physical transfer, spectral gap, continuum
modulus, or Clay theorem is claimed here.
-/

import YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization

namespace YMGap.Continuum.BF4ExactSlabObservableHaarForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr {A : Type} (left right : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (left a) (right a)) :
    ∀ items : List A, RatPolyCoeffEqv (finitePolySum left items) (finitePolySum right items)
  | [] => RatPolyCoeffEqv.refl _
  | a :: rest => (h a).add (sum_congr left right h rest)

private theorem sum_mul_right {A : Type} (f : A → RatPoly) (p : RatPoly) :
    ∀ items : List A, RatPolyCoeffEqv (polyMul (finitePolySum f items) p)
      (finitePolySum (fun a => polyMul (f a) p) items)
  | [] => RatPolyCoeffEqv.refl _
  | a :: rest => by
    change RatPolyCoeffEqv (polyMul (polyAdd (f a) (finitePolySum f rest)) p)
      (polyAdd (polyMul (f a) p) (finitePolySum (fun a => polyMul (f a) p) rest))
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (sum_mul_right f p rest)

private theorem mul_sum_right {A : Type} (p : RatPoly) (f : A → RatPoly) :
    ∀ items : List A, RatPolyCoeffEqv (polyMul p (finitePolySum f items))
      (finitePolySum (fun a => polyMul p (f a)) items)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | _ :: rest =>
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (mul_sum_right p f rest))

private theorem three_sums_expansion {A B C : Type}
    (left : A → RatPoly) (middle : B → RatPoly) (right : C → RatPoly)
    (ls : List A) (ms : List B) (rs : List C) :
    RatPolyCoeffEqv
      (polyMul (finitePolySum left ls)
        (polyMul (finitePolySum middle ms) (finitePolySum right rs)))
      (finitePolySum (fun l => finitePolySum (fun r => finitePolySum
        (fun m => polyMul (left l) (polyMul (middle m) (right r))) ms) rs) ls) := by
  let mr := fun r => polyMul (finitePolySum middle ms) (right r)
  refine ((mul_sum_right (finitePolySum middle ms) right rs).mul_left _).trans ?_
  refine (sum_mul_right left (finitePolySum mr rs) ls).trans ?_
  apply sum_congr
  intro l
  refine (mul_sum_right (left l) mr rs).trans ?_
  apply sum_congr
  intro r
  exact ((sum_mul_right middle (right r) ms).mul_left (left l)).trans
    (mul_sum_right (left l) (fun m => polyMul (middle m) (right r)) ms)

private theorem haar_eq_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by
    unfold quaternionHaar ratWeightedSum
    rw [haar_eq_weighted blocks rest]

private theorem haar_of_coeff_eqv (blocks : Nat) {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) : quaternionHaar blocks left ≈ quaternionHaar blocks right := by
  rw [haar_eq_weighted, haar_eq_weighted]
  exact h (quaternionHaarMono blocks)

private theorem scaled_three (a b : Q') (left middle right : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul a left) (polyMul middle (polySmul b right)))
      (polySmul (a * b) (polyMul left (polyMul middle right))) :=
  ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).mul_left _).trans
    ((RatPolyCoeffEqv.polyMul_smul_left _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right _ _ _).smul _).trans
        (RatPolyCoeffEqv.smul_assoc _ _ _)))

/-- The actual lower boundary observable, dressed by its own face heat weights. -/
def lowerObservable (w : Q') (K : Nat) (coefficient : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun state => polySmul (coefficient state) (lowerPolynomial w K state))
    (centralHalfStates K 0)

/-- The upper observable uses the literal reflected face labelling, on the
same physical link coordinates as the lower observable. -/
def upperObservable (w : Q') (K : Nat) (coefficient : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun state => polySmul (coefficient state) (upperPolynomial w K state))
    (centralHalfStates K 0)

/-- Sum over precisely the existing fixed-interface label carrier. -/
def interfaceHeatInsertion (w : Q') (K : Nat) : RatPoly :=
  finitePolySum (interfacePolynomial w K) (centralBoundaryChannels K 0)

/-- The literal action-side integrand, before any link is integrated. -/
def observableIntegrand (w : Q') (K : Nat) (left right : EdgeLabelling → Q') : RatPoly :=
  polyMul (lowerObservable w K left)
    (polyMul (interfaceHeatInsertion w K) (upperObservable w K right))

/-- Exact finite Fubini keeps every signed coefficient and all 116 link
variables, separating lower, interface, and upper label sums. -/
theorem observableIntegrand_haar_expansion (w : Q') (K : Nat)
    (left right : EdgeLabelling → Q') :
    quaternionHaar 116 (observableIntegrand w K left right) ≈
      listQSum (fun l => listQSum (fun r => listQSum
        (fun b => (left l * right r) * quaternionHaar 116
          (polyMul (lowerPolynomial w K l)
            (polyMul (interfacePolynomial w K b) (upperPolynomial w K r))))
        (centralBoundaryChannels K 0)) (centralHalfStates K 0)) (centralHalfStates K 0) := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff_eqv 116
    (three_sums_expansion
      (fun l => polySmul (left l) (lowerPolynomial w K l))
      (interfacePolynomial w K)
      (fun r => polySmul (right r) (upperPolynomial w K r))
      (centralHalfStates K 0) (centralBoundaryChannels K 0) (centralHalfStates K 0))) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_finitePolySum₃ 116 _
    (centralHalfStates K 0) (centralHalfStates K 0) (centralBoundaryChannels K 0)) ?_
  apply listQSum_congr
  intro l
  apply listQSum_congr
  intro r
  apply listQSum_congr
  intro b
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv 116 (scaled_three _ _ _ _ _))
    (quaternionHaar_polySmul 116 _ _)

/-- Same-action realization of the ORIGINAL signed slab bilinear form for
arbitrary coefficient functions. No positivity or normalization replacement. -/
theorem exact_bilinear_eq_haar (w : Q') (K : Nat)
    (left right : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates K 0) left right
      (exactCorrectedSlabReflectedKernel w K 0) ≈
      quaternionHaar 116 (observableIntegrand w K left right) := by
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (observableIntegrand_haar_expansion w K left right))
  unfold finiteJointBilinear
  apply listQSum_congr
  intro l
  apply listQSum_congr
  intro r
  unfold exactCorrectedSlabReflectedKernel
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left (left l * right r) _
    (centralBoundaryChannels K 0))) ?_
  apply listQSum_congr
  intro b
  exact Q'.mul_eqv_congr_left _ _ _ (dualTerm_eq_threeFactorHaar w K l b r)

/-- The exact all-cutoff quadratic is this very same Haar integral, with
the same observable used on both sides of the geometric plane. -/
theorem exact_quadratic_eq_haar (w : Q') (K : Nat)
    (coefficient : EdgeLabelling → Q') :
    exactSlabAllCutoffQuadratic w K coefficient ≈
      quaternionHaar 116 (observableIntegrand w K coefficient coefficient) := by
  exact exact_bilinear_eq_haar w K coefficient coefficient

end YMGap.Continuum.BF4ExactSlabObservableHaarForm

#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.lowerObservable
#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.upperObservable
#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.interfaceHeatInsertion
#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.observableIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.observableIntegrand_haar_expansion
#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.exact_bilinear_eq_haar
#print axioms YMGap.Continuum.BF4ExactSlabObservableHaarForm.exact_quadratic_eq_haar
