/-
# Finite polynomial trace-kernel quadratics are explicit weighted Gram squares

Arbitrary complex polynomial coefficients are synthesized into actual
representation columns. The ORIGINAL trace-kernel quadratic is proved
coefficientwise equal to the positive-weighted Hermitian squares of those
syntheses. Exact product-Haar positivity follows for supported syntheses.
No positivity of the trace kernel is assumed.

This is a local representation-kernel theorem. The physical reflected
interface still needs its literal half-word identification and link gluing;
no slab OS positivity, physical transfer gap or continuum theorem is claimed.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
import YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
import YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport

namespace YMGap.Continuum.SU2QuaternionPolynomialGramPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSolidZonalGaussianTransport
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈c " => ComplexCoeffEqv
local infixl:65 " ⊞ " => complexRatPolyAdd
local infixl:70 " ⊠ " => complexRatPolyMul
local notation "star" => complexRatPolyConj
local notation "𝟘" => complexRatPolyZero

private theorem sum_zero : ∀ n, polynomialSum n (fun _ => 𝟘) ≈c 𝟘
  | 0 => ComplexCoeffEqv.refl _
  | n + 1 => ((sum_zero n).add (ComplexCoeffEqv.refl 𝟘)).trans (add_zero _)

theorem sum_swap : ∀ m n (f : Nat → Nat → ComplexRatPoly),
    polynomialSum m (fun i => polynomialSum n (f i)) ≈c
      polynomialSum n (fun j => polynomialSum m (fun i => f i j))
  | 0, n, _ => (sum_zero n).symm
  | m + 1, n, f => ((sum_swap m n f).add (ComplexCoeffEqv.refl _)).trans (sum_add n _ _).symm

theorem sum_realScale (s : Q') : ∀ n (f : Nat → ComplexRatPoly),
    polynomialSum n (fun i => polyRealScale s (f i)) ≈c polyRealScale s (polynomialSum n f)
  | 0, _ => ComplexCoeffEqv.refl _
  | n + 1, f => ((sum_realScale s n f).add (ComplexCoeffEqv.refl _)).trans
      ⟨(RatPolyCoeffEqv.smul_add s _ _).symm, (RatPolyCoeffEqv.smul_add s _ _).symm⟩

private theorem realScale_as_mul (s : Q') (z : ComplexRatPoly) :
    (realPolynomial (polySmul s polyOne) ⊠ z) ≈c polyRealScale s z := by
  have h (p : RatPoly) : RatPolyCoeffEqv (polyMul (polySmul s polyOne) p) (polySmul s p) :=
    (RatPolyCoeffEqv.polyMul_smul_left s polyOne p).trans ((RatPolyCoeffEqv.one_mul p).smul s)
  exact ⟨((h z.1).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left _))).trans
      (RatPolyCoeffEqv.add_zero _),
    ((h z.2).add (RatPolyCoeffEqv.mul_zero_left _)).trans (RatPolyCoeffEqv.add_zero _)⟩

private theorem mul_realScale (s : Q') (a z : ComplexRatPoly) :
    (a ⊠ polyRealScale s z) ≈c polyRealScale s (a ⊠ z) :=
  ((ComplexCoeffEqv.refl a).mul (realScale_as_mul s z).symm).trans
    ((mul_assoc _ _ _).symm.trans
      (((mul_comm _ _).mul (ComplexCoeffEqv.refl z)).trans
        ((mul_assoc _ _ _).trans (realScale_as_mul s (a ⊠ z)))))

private theorem inner_zero_left : ∀ (n : Nat) (x : PolyTensor n),
    polyTensorInner n (polyEmbed n (fun _ => 𝟘)) x ≈c 𝟘
  | 0, x => zero_mul x
  | n + 1, x => ((inner_zero_left n (x false)).add (inner_zero_left n (x true))).trans (zero_add _)

private theorem inner_zero_right : ∀ (n : Nat) (x : PolyTensor n),
    polyTensorInner n x (polyEmbed n (fun _ => 𝟘)) ≈c 𝟘
  | 0, x => mul_zero (star x)
  | n + 1, x => ((inner_zero_right n (x false)).add (inner_zero_right n (x true))).trans (zero_add _)

/-- Constructive finite synthesis, with arbitrary complex polynomial
coefficients and without a global coordinate-assignment enumeration. -/
def polySynthesis (n : Nat) : Nat → (Nat → ComplexRatPoly) → (Nat → PolyTensor n) → PolyTensor n
  | 0, _, _ => polyEmbed n (fun _ => 𝟘)
  | count + 1, c, x => polyTensorAdd n (polySynthesis n count c x) (polyTensorScale n (c count) (x count))

private theorem inner_synthesis_right (n : Nat) (x : PolyTensor n) : ∀ count c y,
    polyTensorInner n x (polySynthesis n count c y) ≈c
      polynomialSum count (fun j => c j ⊠ polyTensorInner n x (y j))
  | 0, _, _ => inner_zero_right n x
  | count + 1, c, y => (inner_add_right n _ _ _).trans
      ((inner_synthesis_right n x count c y).add (inner_scale_right (c count) n x (y count)))

private theorem inner_synthesis_left (n : Nat) (y : PolyTensor n) : ∀ count c x,
    polyTensorInner n (polySynthesis n count c x) y ≈c
      polynomialSum count (fun i => star (c i) ⊠ polyTensorInner n (x i) y)
  | 0, _, _ => inner_zero_left n y
  | count + 1, c, x => (inner_add_left n _ _ _).trans
      ((inner_synthesis_left n y count c x).add (inner_scale_left (c count) n (x count) y))

theorem inner_synthesis (n count : Nat) (c d : Nat → ComplexRatPoly) (x y : Nat → PolyTensor n) :
    polyTensorInner n (polySynthesis n count c x) (polySynthesis n count d y) ≈c
      polynomialSum count (fun i => polynomialSum count (fun j =>
        star (c i) ⊠ (d j ⊠ polyTensorInner n (x i) (y j)))) :=
  (inner_synthesis_left n _ count c x).trans (sum_congr count (fun i _ =>
    ((ComplexCoeffEqv.refl _).mul (inner_synthesis_right n (x i) count d y)).trans (sum_scale _ _ _).symm))

/-- Quadratic of an arbitrary finite polynomial-valued kernel. -/
def kernelQuadratic (count : Nat) (c : Nat → ComplexRatPoly) (kernel : Nat → Nat → ComplexRatPoly) : ComplexRatPoly :=
  polynomialSum count (fun i => polynomialSum count (fun j => star (c i) ⊠ (c j ⊠ kernel i j)))

/-- The finite Gram identity retains all coefficient probes. Its weights
are parameters here; the actual trace consumer uses the proved positive
binomial reciprocals, not an assumed positivity certificate. -/
theorem kernelQuadratic_gram (n width count : Nat) (w : Nat → Q')
    (c : Nat → ComplexRatPoly) (x : Nat → Nat → PolyTensor n) :
    kernelQuadratic count c (fun i j => polynomialSum width (fun k =>
      polyRealScale (w k) (polyTensorInner n (x i k) (x j k)))) ≈c
    polynomialSum width (fun k => polyRealScale (w k)
      (polyTensorInner n (polySynthesis n count c (fun i => x i k))
        (polySynthesis n count c (fun i => x i k)))) := by
  let f := fun i j k => star (c i) ⊠ (c j ⊠ polyTensorInner n (x i k) (x j k))
  have hterm (i j : Nat) :
      (star (c i) ⊠ (c j ⊠ polynomialSum width (fun k =>
        polyRealScale (w k) (polyTensorInner n (x i k) (x j k))))) ≈c
      polynomialSum width (fun k => polyRealScale (w k) (f i j k)) := by
    refine (((ComplexCoeffEqv.refl _).mul (sum_scale _ _ _).symm).trans (sum_scale _ _ _).symm).trans ?_
    exact sum_congr width (fun k _ =>
      (((ComplexCoeffEqv.refl _).mul (mul_realScale _ _ _)).trans (mul_realScale _ _ _)))
  refine (sum_congr count (fun i _ => sum_congr count (fun j _ => hterm i j))).trans ?_
  refine (sum_congr count (fun i _ => sum_swap count width (fun j k => polyRealScale (w k) (f i j k)))).trans ?_
  refine (sum_swap count width (fun i k => polynomialSum count (fun j => polyRealScale (w k) (f i j k)))).trans ?_
  exact sum_congr width (fun k _ =>
    ((sum_congr count (fun i _ => sum_realScale (w k) count (fun j => f i j k))).trans
      (sum_realScale (w k) count _)).trans
      (polyRealScale_congr (Q'.eqv_refl _) (inner_synthesis n count c c _ _).symm))

/-- The ORIGINAL actual trace kernel, not a Gram kernel substituted by definition. -/
def traceKernelQuadratic (p : Nat → RatPolyQuaternion) (n count : Nat) (c : Nat → ComplexRatPoly) : ComplexRatPoly :=
  kernelQuadratic count c (fun i j => polynomialTrace
    (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj (p i)) (p j)) n)

/-- All finite complex-polynomial quadratics of the ORIGINAL trace kernel
are explicit positive-weighted squares of actual column syntheses. -/
theorem traceKernelQuadratic_eq_squares (p : Nat → RatPolyQuaternion) (n count : Nat) (c : Nat → ComplexRatPoly) :
    traceKernelQuadratic p n count c ≈c
      polynomialSum (n + 1) (fun k => polyRealScale (basisInverseWeight n k)
        (polyTensorInner n (polySynthesis n count c (fun i => polynomialColumn (p i) n k))
          (polySynthesis n count c (fun i => polynomialColumn (p i) n k)))) :=
  (sum_congr count (fun i _ => sum_congr count (fun j _ =>
    (ComplexCoeffEqv.refl _).mul ((ComplexCoeffEqv.refl _).mul (polynomialTrace_conj_mul_eq_gram (p i) (p j) n))))).trans
    (kernelQuadratic_gram n (n + 1) count (basisInverseWeight n) c (fun i k => polynomialColumn (p i) n k))

/-- Syntactic finite-coordinate support of both components of every tensor
entry. This is a finite polynomial-domain condition, not positivity. -/
def PolyTensorSupported (blocks : Nat) : (n : Nat) → PolyTensor n → Prop
  | 0, x => SupportedQuaternionBlocks blocks x.1 ∧ SupportedQuaternionBlocks blocks x.2
  | n + 1, x => ∀ b, PolyTensorSupported blocks n (x b)

private theorem haar_coeff {blocks : Nat} {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    (quaternionHaar blocks p).eqv (quaternionHaar blocks q) :=
  QuaternionHaarCarrierEqv.haar (RatPolyCoeffEqv.haarCarrier h)

private theorem real_self_square (x : ComplexRatPoly) :
    RatPolyCoeffEqv (star x ⊠ x).1 (polyAdd (polyMul x.1 x.1) (polyMul x.2 x.2)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.neg (.var 1)) (.var 1))))
    (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
    (fun i => if i = 0 then x.1 else x.2)

/-- Positivity of the actual Hermitian square follows from the existing
all-polynomial Haar square theorem, applied to real and imaginary entries. -/
theorem polyTensorInner_haar_nonneg (blocks : Nat) : ∀ n (x : PolyTensor n), PolyTensorSupported blocks n x →
    (0 : Q') ≤ quaternionHaar blocks (polyTensorInner n x x).1
  | 0, x, hx => by
    have hs := Q'.zero_le_add _ _ (quaternionHaar_square_nonnegative blocks x.1 hx.1)
      (quaternionHaar_square_nonnegative blocks x.2 hx.2)
    exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (haar_coeff (real_self_square x)) (quaternionHaar_append blocks _ _))))
  | n + 1, x, hx =>
    Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ (polyTensorInner_haar_nonneg blocks n (x false) (hx false))
      (polyTensorInner_haar_nonneg blocks n (x true) (hx true)))
      (Q'.le_of_eqv (Q'.eqv_symm (quaternionHaar_append blocks _ _)))

private theorem haar_sum_nonneg (blocks : Nat) : ∀ m (f : Nat → ComplexRatPoly),
    (∀ k, k < m → (0 : Q') ≤ quaternionHaar blocks (f k).1) →
      (0 : Q') ≤ quaternionHaar blocks (polynomialSum m f).1
  | 0, _, _ => show (0 : Q') ≤ 0 from by decide
  | m + 1, f, h => Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _ (haar_sum_nonneg blocks m f (fun k hk => h k (by omega))) (h m (by omega)))
      (Q'.le_of_eqv (Q'.eqv_symm (quaternionHaar_append blocks _ _)))

/-- Positive semidefiniteness after exact product-Haar integration for every
finite family and every complex polynomial coefficient vector whose column
syntheses are supported on that SAME finite carrier. -/
theorem traceKernelQuadratic_haar_nonneg (blocks : Nat) (p : Nat → RatPolyQuaternion)
    (n count : Nat) (c : Nat → ComplexRatPoly)
    (hsupport : ∀ k, k ≤ n → PolyTensorSupported blocks n
      (polySynthesis n count c (fun i => polynomialColumn (p i) n k))) :
    (0 : Q') ≤ quaternionHaar blocks (traceKernelQuadratic p n count c).1 := by
  have hs : (0 : Q') ≤ quaternionHaar blocks
      (polynomialSum (n + 1) (fun k => polyRealScale (basisInverseWeight n k)
        (polyTensorInner n (polySynthesis n count c (fun i => polynomialColumn (p i) n k))
          (polySynthesis n count c (fun i => polynomialColumn (p i) n k))))).1 := by
    apply haar_sum_nonneg blocks
    intro k hk
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (basisInverseWeight_pos n k))
        (polyTensorInner_haar_nonneg blocks n _ (hsupport k (by omega))))
      (Q'.le_of_eqv (Q'.eqv_symm (quaternionHaar_polySmul blocks _ _)))
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_symm
    (haar_coeff (traceKernelQuadratic_eq_squares p n count c).1)))

private def ComplexHaarEqv (blocks : Nat) (x y : ComplexRatPoly) : Prop :=
  QuaternionHaarCarrierEqv blocks x.1 y.1 ∧ QuaternionHaarCarrierEqv blocks x.2 y.2

private theorem haar_mul_left {blocks : Nat} (a : ComplexRatPoly) {x y : ComplexRatPoly}
    (h : ComplexHaarEqv blocks x y) : ComplexHaarEqv blocks (a ⊠ x) (a ⊠ y) :=
  ⟨QuaternionHaarCarrierEqv.add (QuaternionHaarCarrierEqv.mul_left a.1 h.1)
      (HaarCarrierEqv.neg (QuaternionHaarCarrierEqv.mul_left a.2 h.2)),
    QuaternionHaarCarrierEqv.add (QuaternionHaarCarrierEqv.mul_left a.1 h.2)
      (QuaternionHaarCarrierEqv.mul_left a.2 h.1)⟩

private theorem haar_complex_sum (blocks : Nat) : ∀ m (f g : Nat → ComplexRatPoly),
    (∀ i, i < m → ComplexHaarEqv blocks (f i) (g i)) →
      ComplexHaarEqv blocks (polynomialSum m f) (polynomialSum m g)
  | 0, _, _, _ => ⟨QuaternionHaarCarrierEqv.refl blocks _, QuaternionHaarCarrierEqv.refl blocks _⟩
  | m + 1, f, g, h =>
    ⟨QuaternionHaarCarrierEqv.add (haar_complex_sum blocks m f g (fun i hi => h i (by omega))).1
        (h m (by omega)).1,
      QuaternionHaarCarrierEqv.add (haar_complex_sum blocks m f g (fun i hi => h i (by omega))).2
        (h m (by omega)).2⟩

/-- The ORIGINAL BF4 character polynomial of each conjugate product, with
arbitrary complex-polynomial coefficients in its finite quadratic. -/
def characterKernelQuadratic (p : Nat → RatPolyQuaternion) (n count : Nat) (c : Nat → ComplexRatPoly) : ComplexRatPoly :=
  kernelQuadratic count c (fun i j => realPolynomial
    (characterPolynomial (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj (p i)) (p j)).r n))

/-- The trace and character quadratics agree under every Haar insertion.
Each input word supplies only its own Haar-unit radius; the product-radius
relations and all complex spectator transports are proved. -/
theorem traceKernelQuadratic_haar_character (blocks : Nat) (p : Nat → RatPolyQuaternion)
    (n count : Nat) (c : Nat → ComplexRatPoly)
    (hradii : ∀ i, i < count → QuaternionHaarCarrierEqv blocks (radiusPolynomial (p i)) polyOne) :
    QuaternionHaarCarrierEqv blocks (traceKernelQuadratic p n count c).1 (characterKernelQuadratic p n count c).1 ∧
    QuaternionHaarCarrierEqv blocks (traceKernelQuadratic p n count c).2 (characterKernelQuadratic p n count c).2 := by
  apply haar_complex_sum blocks count
  intro i hi
  apply haar_complex_sum blocks count
  intro j hj
  apply haar_mul_left
  apply haar_mul_left
  exact polynomialTrace_haar_character
    (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj (p i)) (p j))
    (haarRadius_conj_mul (hradii i hi) (hradii j hj)) n

/-- Positive semidefiniteness of the ORIGINAL local all-spin character
kernel, not an assumed character model. All hypotheses are explicit word
radius relations and finite polynomial support on the SAME Haar carrier. -/
theorem characterKernelQuadratic_haar_nonneg (blocks : Nat) (p : Nat → RatPolyQuaternion)
    (n count : Nat) (c : Nat → ComplexRatPoly)
    (hradii : ∀ i, i < count → QuaternionHaarCarrierEqv blocks (radiusPolynomial (p i)) polyOne)
    (hsupport : ∀ k, k ≤ n → PolyTensorSupported blocks n
      (polySynthesis n count c (fun i => polynomialColumn (p i) n k))) :
    (0 : Q') ≤ quaternionHaar blocks (characterKernelQuadratic p n count c).1 :=
  Q'.le_trans' _ _ _ (traceKernelQuadratic_haar_nonneg blocks p n count c hsupport)
    (Q'.le_of_eqv (QuaternionHaarCarrierEqv.haar (traceKernelQuadratic_haar_character blocks p n count c hradii).1))

end YMGap.Continuum.SU2QuaternionPolynomialGramPositivity

#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.sum_swap
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.sum_realScale
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.polySynthesis
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.inner_synthesis
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.kernelQuadratic
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.kernelQuadratic_gram
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.traceKernelQuadratic
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.traceKernelQuadratic_eq_squares
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.PolyTensorSupported
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.polyTensorInner_haar_nonneg
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.traceKernelQuadratic_haar_nonneg
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.characterKernelQuadratic
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.traceKernelQuadratic_haar_character
#print axioms YMGap.Continuum.SU2QuaternionPolynomialGramPositivity.characterKernelQuadratic_haar_nonneg
