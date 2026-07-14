/-
# Normalized row weights and nested transvectant coefficient factorization

The closed binary Gram determines every raw coefficient-row weight after the
reciprocal monomial metric is restored.  Nested left- and right-associated
transvectants then factor pointwise into an inner Hahn coefficient and one
outer binary transvectant coefficient.  These are the two normalization and
coefficient identities needed by the all-label rational F-matrix synthesis.
-/

import YMGap.Continuum.SU2TransvectantClosedBinaryGram
import YMGap.Continuum.SU2GeneralShellHahnMatrix

namespace YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantRowNormConstancy
open YMGap.Continuum.SU2TransvectantNormalizedRows
open YMGap.Continuum.SU2TransvectantClosedBinaryGram
open YMGap.Continuum.SU2GeneralShellHahnMatrix

local infix:50 " ≈ " => Q'.eqv

/-- Removing the output monomial norm from a normalized row restores exactly
the reciprocal-binomial input weight. -/
theorem binaryRawRowNorm_factorial_product (m n k s : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hs : s ≤ m + n - 2 * k) :
    binaryRawRowNorm m n k s ≈
      tvBinomQ (m + n - 2 * k) s * binaryRowFactorialProduct m n k := by
  let d := m + n - 2 * k
  let w := symMonomialNormSq d s
  let b := tvBinomQ d s
  let R := binaryRawRowNorm m n k s
  let P := binaryRowFactorialProduct m n k
  have hnormalized : w * R ≈ P := by
    simpa only [binaryNormalizedRowNorm, d, w, R, P] using
      binaryNormalizedRowNorm_factorial_product m n k s hm hn hs
  have hrecip0 : w * b ≈ 1 :=
    symMonomialNormSq_mul_tvBinomQ d s hs
  have hrecip : b * w ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv b w) hrecip0
  refine Q'.eqv_trans _ (1 * R) _ (Q'.eqv_symm (Q'.one_mul_eqv R)) ?_
  refine Q'.eqv_trans _ ((b * w) * R) _
    (Q'.mul_eqv_congr_right _ _ R (Q'.eqv_symm hrecip)) ?_
  refine Q'.eqv_trans _ (b * (w * R)) _ (Q'.mul_assoc_eqv b w R) ?_
  exact Q'.mul_eqv_congr_left b _ _ hnormalized

/-- A left-associated nested monomial coefficient is the inner Hahn entry
times the outer binary coefficient. -/
theorem triLeft_monomial_factorization (a b c d e i j l s : Nat)
    (hr : couplingOrder a b e ≤ i + j) :
    triLeft a b c d e (mono i) (mono j) (mono l) s ≈
      hahnEntry a b (i + j) (couplingOrder a b e) i *
        transvect e c (couplingOrder e c d)
          (tprod (mono (i + j - couplingOrder a b e)) (mono l)) s := by
  let r := couplingOrder a b e
  let q := couplingOrder e c d
  let t := i + j - r
  let h := hahnEntry a b (i + j) r i
  have hinner := shellBasis_transvect_form a b (i + j) r i (by omega) hr
  have htprod : BForm2Eqv
      (tprod (transvect a b r (tprod (mono i) (mono j))) (mono l))
      (bscale h (tprod (mono t) (mono l))) := by
    intro x y
    have hx : transvect a b r (tprod (mono i) (mono j)) x ≈
        h * mono t x := by
      simpa only [shellBasis, r, t, h,
        show i + j - i = j by omega] using hinner x
    refine Q'.eqv_trans _ ((h * mono t x) * mono l y) _
      (Q'.mul_eqv_congr_right _ _ _ hx) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hcongr := transvect_congr e c q htprod s
  have hscale := transvect_scale e c q h (tprod (mono t) (mono l)) s
  simpa only [triLeft, r, q, t, h] using
    Q'.eqv_trans _ _ _ hcongr hscale

/-- A right-associated nested monomial coefficient is the inner Hahn entry
times the outer binary coefficient. -/
theorem triRight_monomial_factorization (a b c d f i j l s : Nat)
    (hp : couplingOrder b c f ≤ j + l) :
    triRight a b c d f (mono i) (mono j) (mono l) s ≈
      hahnEntry b c (j + l) (couplingOrder b c f) j *
        transvect a f (couplingOrder a f d)
          (tprod (mono i) (mono (j + l - couplingOrder b c f))) s := by
  let p := couplingOrder b c f
  let q := couplingOrder a f d
  let t := j + l - p
  let h := hahnEntry b c (j + l) p j
  have hinner := shellBasis_transvect_form b c (j + l) p j (by omega) hp
  have htprod : BForm2Eqv
      (tprod (mono i) (transvect b c p (tprod (mono j) (mono l))))
      (bscale h (tprod (mono i) (mono t))) := by
    intro x y
    have hy : transvect b c p (tprod (mono j) (mono l)) y ≈
        h * mono t y := by
      simpa only [shellBasis, p, t, h,
        show j + l - j = l by omega] using hinner y
    refine Q'.eqv_trans _ (mono i x * (h * mono t y)) _
      (Q'.mul_eqv_congr_left _ _ _ hy) ?_
    refine Q'.eqv_trans _ ((mono i x * h) * mono t y) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ ((h * mono i x) * mono t y) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hcongr := transvect_congr a f q htprod s
  have hscale := transvect_scale a f q h (tprod (mono i) (mono t)) s
  simpa only [triRight, p, q, t, h] using
    Q'.eqv_trans _ _ _ hcongr hscale

end YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization

#print axioms YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization.binaryRawRowNorm_factorial_product
#print axioms YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization.triLeft_monomial_factorization
#print axioms YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization.triRight_monomial_factorization
