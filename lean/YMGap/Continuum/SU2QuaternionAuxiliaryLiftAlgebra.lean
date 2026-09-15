/-
# Algebra and support for adjoining auxiliary Haar variables

The existing liftBoundary operation retains every original variable. Its
algebra, explicit support and normalized Haar pins are used to transport the
whole interacting insertion, not to declare its factors independent.
Supported Haar equality is used only on its stated carrier; common padding
does not license silently dropping coordinates outside that carrier.
-/

import YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
import YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation

namespace YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.QuaternionHaarSquareCertificate

theorem lift_add (n : Nat) (p q : RatPoly) :
    liftBoundary n (polyAdd p q) = polyAdd (liftBoundary n p) (liftBoundary n q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftBoundary, ih, liftBoundary, liftBoundary]; exact List.map_append

theorem lift_smul (n : Nat) (a : Q') (p : RatPoly) :
    liftBoundary n (polySmul a p) = polySmul a (liftBoundary n p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [liftBoundary, ih, liftBoundary]
      simp only [liftHead, polySmul, List.map_map]
      rfl

theorem lift_product (n : Nat) (p q : RatPoly) :
    liftBoundary n (polyMul p q) = polyMul (liftBoundary n p) (liftBoundary n q) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftBoundary, ih, liftHead_mul]

private theorem lift_weight (w : List Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum w (liftHead p) = ratWeightedSum (fun m => w (0::0::0::0::m)) p
  | [] => rfl
  | t :: rest => congrArg (fun x => t.2 * w (0::0::0::0::t.1) + x) (lift_weight w rest)

theorem lift_coeff (n : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (liftBoundary n p) (liftBoundary n q) := by
  induction n with
  | zero => exact h
  | succ n ih => intro w; rw [liftBoundary, liftBoundary, lift_weight, lift_weight]; exact ih _

theorem lift_supported {blocks : Nat} {p : RatPoly} (h : SupportedQuaternionBlocks blocks p) :
    ∀ n, SupportedQuaternionBlocks (blocks+n) (liftBoundary n p)
  | 0 => h
  | n+1 => by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have hh := lift_supported h n s hs
      simp only [List.length_cons]
      omega

private theorem zeros_exponent : ∀ n i, exponentAt (List.replicate n 0) i = 0
  | 0, _ => rfl
  | _+1, 0 => rfl
  | n+1, i+1 => zeros_exponent n i

private theorem lift_one_list : ∀ n, liftBoundary n polyOne = [(List.replicate (4*n) 0, (1 : Q'))]
  | 0 => rfl
  | n+1 => by
      rw [liftBoundary, lift_one_list]
      simp only [liftHead, List.map_cons, List.map_nil, Nat.mul_succ,
        List.replicate_succ]

theorem lift_one (blocks n : Nat) : PaddedPolynomialCoeffEqv blocks (liftBoundary n polyOne) polyOne := by
  apply PaddedPolynomialCoeffEqv.of_prefix
  rw [lift_one_list]
  exact .cons ⟨Q'.eqv_refl _, fun i _ => zeros_exponent (4*n) i⟩ .nil

theorem lift_character (blocks n : Nat) (p : RatPoly) : ∀ spin,
    PaddedPolynomialCoeffEqv blocks (liftBoundary n (characterPolynomial p spin))
      (characterPolynomial (liftBoundary n p) spin)
  | 0 => lift_one blocks n
  | 1 => by rw [characterPolynomial, lift_smul]; exact .refl _ _
  | spin+2 => by
      rw [characterPolynomial, lift_add, lift_product, lift_smul, lift_smul]
      exact ((PaddedPolynomialCoeffEqv.refl _ _).mul (lift_character blocks n p (spin+1))).add
        ((lift_character blocks n p spin).smul (-1))

theorem padded_apply {n : Nat} (hn : 0 < n) (steps : List (SelectedTranslationStep n))
    {p q : RatPoly} (h : PaddedPolynomialCoeffEqv (n+1) p q) :
    PaddedPolynomialCoeffEqv (n+1) (applySelectedTranslationSteps hn steps p)
      (applySelectedTranslationSteps hn steps q) := by
  have hh : PaddedQuaternionCoeffEqv (n+1) ⟨p,polyZero,polyZero,polyZero⟩ ⟨q,polyZero,polyZero,polyZero⟩ :=
    ⟨h, RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩
  exact (hh.applySteps hn steps).scalar

/-- Equality tested only against insertions on the stated finite carrier. -/
def SupportedHaarEqv (blocks : Nat) (p q : RatPoly) : Prop :=
  ∀ i : RatPoly, SupportedQuaternionBlocks blocks i →
    (quaternionHaar blocks (polyMul i p)).eqv (quaternionHaar blocks (polyMul i q))

namespace SupportedHaarEqv

theorem refl (blocks : Nat) (p : RatPoly) : SupportedHaarEqv blocks p p := fun _ _ => Q'.eqv_refl _

theorem trans {blocks : Nat} {p q r : RatPoly}
    (h : SupportedHaarEqv blocks p q) (k : SupportedHaarEqv blocks q r) : SupportedHaarEqv blocks p r :=
  fun i hi => Q'.eqv_trans _ _ _ (h i hi) (k i hi)

theorem symm {blocks : Nat} {p q : RatPoly} (h : SupportedHaarEqv blocks p q) : SupportedHaarEqv blocks q p :=
  fun i hi => Q'.eqv_symm (h i hi)

theorem of_carrier {blocks : Nat} {p q : RatPoly} (h : HaarCarrierEqv blocks p q) : SupportedHaarEqv blocks p q :=
  fun i _ => h i

theorem of_padded {blocks : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) : SupportedHaarEqv blocks p q :=
  fun i hi => h.haar_insert hp hq i hi

theorem add {blocks : Nat} {p p' q q' : RatPoly}
    (hp : SupportedHaarEqv blocks p p') (hq : SupportedHaarEqv blocks q q') :
    SupportedHaarEqv blocks (polyAdd p q) (polyAdd p' q') := by
  intro i hi
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right blocks i p q)
    (Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (hp i hi)) (Q'.add_eqv_congr_left _ _ _ (hq i hi)))
      (Q'.eqv_symm (quaternionHaar_polyMul_add_right blocks i p' q')))

theorem smul {blocks : Nat} {p q : RatPoly} (h : SupportedHaarEqv blocks p q) (a : Q') :
    SupportedHaarEqv blocks (polySmul a p) (polySmul a q) := by
  intro i hi
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks a i p)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (h i hi))
      (Q'.eqv_symm (quaternionHaar_polyMul_smul_right blocks a i q)))

theorem mul {blocks : Nat} {p p' q q' : RatPoly}
    (hp : SupportedHaarEqv blocks p p') (hq : SupportedHaarEqv blocks q q')
    (hsq : SupportedQuaternionBlocks blocks q) (hsp' : SupportedQuaternionBlocks blocks p') :
    SupportedHaarEqv blocks (polyMul p q) (polyMul p' q') := by
  intro i hi
  have hleft := hp (polyMul i q) (supported_polyMul hi hsq)
  have hright := hq (polyMul i p') (supported_polyMul hi hsp')
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_middle_comm blocks i p q)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc blocks i q p))
      (Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_assoc blocks i q p')
          (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_middle_comm blocks i q p')
            (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_assoc blocks i p' q))
              (Q'.eqv_trans _ _ _ hright (quaternionHaar_polyMul_assoc blocks i p' q')))))))

end SupportedHaarEqv

end YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_add
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_smul
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_product
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_coeff
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_supported
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_one
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.lift_character
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.padded_apply
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.refl
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.trans
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.symm
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.of_carrier
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.of_padded
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.add
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.smul
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra.SupportedHaarEqv.mul
