/-
`FusionBoxBernsteinReconstruction` -- exact compilation of the physical
fusion-box difference into an integer Bernstein row.

For a cutoff `N`, put `D = 2 * c4 N`.  Every active summand of the
Cauchy--Binet box difference has an even heat exponent `2e`, with `e <= D`.
After the physical substitution

    u = 4 * w^2,

multiplication by the common positive integer `4^D` turns that summand into
the integer monomial `4^(D-e) * mass * u^e`.  This file performs that
compilation constructively, sums the corresponding elevated Pascal rows, and
proves exact reconstruction against the ACTUAL `boxSum` difference.

The public prefix carrier is deliberately term-based: it sums all cleared
monomial masses whose half-exponent is below a requested cutoff.  Thus it is
exactly `4^D` times the prefix of the physical power coefficients
`a_(2e)/4^e`, while avoiding a costly second bucketing pass.  A subsequent
Abel/prefix theorem can consume this carrier without changing the row used by
the reconstruction theorem.

Honest scope: this module proves reconstruction, not coefficient positivity.
It constructs `FiniteTriangleBernsteinCertificate N` from ONLY the finite
coefficient checks for the canonical rows.  Proving those checks uniformly in
`N` is the remaining sign theorem.

Axiom gate: pure `Nat`/`Int`/`Q'`, structural recursion, and finite sums.  No
`Classical`, `native_decide`, `sorry`, axiom, or noncomputable declaration.
-/

import YMGap.Continuum.FusionWeightedInterlacingCertificate
import YMGap.Continuum.BernsteinSignedMonomialReconstruction
import YMGap.Continuum.CoreBUniversalSquareGap
import YMGap.Continuum.LaplaceMarginDeep
import YMGap.Continuum.BernsteinPrefixAbel

namespace YMGap.Continuum.FusionBoxBernsteinReconstruction

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinSignedMonomialReconstruction
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.CoreBBernsteinConsumer
open YMGap.Continuum.CoreBUniversalSquareGap
open YMGap.Continuum.FusionWeightedInterlacingCertificate
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.BernsteinPrefixAbel
open YMGap.RG

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. The canonical degree and the four-index monomial ledger -/

/-- One global Bernstein degree covers every four-label monomial at cutoff
`N`: four Casimirs are at most `4*c4 N`, hence the half-exponent is at most
`2*c4 N`. -/
def boxBernsteinDegree (N : Nat) : Nat :=
  2 * c4 N

/-- The heat exponent of one four-label Cauchy--Binet cell. -/
def boxQuadExponent (a a' b b' : Nat) : Nat :=
  (c4 a + c4 b) + (c4 a' + c4 b')

/-- The physical `u`-exponent.  It is used only on active cells, where fusion
parity proves that `boxQuadExponent` is even. -/
def boxQuadHalfExponent (a a' b b' : Nat) : Nat :=
  boxQuadExponent a a' b b' / 2

/-- Product of the four SU(2) representation dimensions. -/
def boxQuadDimension (a a' b b' : Nat) : Nat :=
  ((a + 1) * (b + 1)) * ((a' + 1) * (b' + 1))

/-- Unsigned multiplicity of the product of two fusion-box cells. -/
def boxProductMultiplicity
    (leftChannel rightChannel a a' b b' : Nat) : Nat :=
  if fusionOK a b leftChannel && fusionOK a' b' rightChannel then
    boxQuadDimension a a' b b'
  else 0

/-- The positive middle-square multiplicity in `quadW`. -/
def boxPositiveMultiplicity (s a a' b b' : Nat) : Nat :=
  boxProductMultiplicity (s + 1) (s + 1) a a' b b'

/-- The negative outer-product multiplicity in `quadW`. -/
def boxNegativeMultiplicity (s a a' b b' : Nat) : Nat :=
  boxProductMultiplicity s (s + 2) a a' b b'

/-- Integer clearing factor of one unsigned cell. -/
def boxCellClearedMultiplicity
    (N : Nat) (multiplicity a a' b b' : Nat) : Nat :=
  multiplicity *
    4 ^ (boxBernsteinDegree N - boxQuadHalfExponent a a' b b')

/-- The signed cleared power coefficient contributed by one four-index cell. -/
def boxCellClearedCoefficient
    (N s a a' b b' : Nat) : Int :=
  Int.ofNat
      (boxCellClearedMultiplicity N
        (boxPositiveMultiplicity s a a' b b') a a' b b') -
    Int.ofNat
      (boxCellClearedMultiplicity N
        (boxNegativeMultiplicity s a a' b b') a a' b b')

/-! ## 2. Fusion parity and the global degree bound -/

private theorem c4_mono_local {a b : Nat} (hab : a ≤ b) :
    c4 a ≤ c4 b := by
  unfold c4
  exact Nat.mul_le_mul hab (by omega)

/-- Two active fusion cells whose channels have the same parity carry an even
total Casimir exponent. -/
theorem boxQuadExponent_even_of_active
    {leftChannel rightChannel a a' b b' : Nat}
    (hparity : leftChannel % 2 = rightChannel % 2)
    (hleft : fusionOK a b leftChannel = true)
    (hright : fusionOK a' b' rightChannel = true) :
    boxQuadExponent a a' b b' % 2 = 0 := by
  have hp :=
    ((YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff
      a b leftChannel).mp hleft).2.2
  have hp' :=
    ((YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff
      a' b' rightChannel).mp hright).2.2
  have ha := c4_mod_two a
  have hb := c4_mod_two b
  have ha' := c4_mod_two a'
  have hb' := c4_mod_two b'
  unfold boxQuadExponent
  omega

/-- Every in-box half-exponent fits the single degree `2*c4 N`. -/
theorem boxQuadHalfExponent_le_degree
    {N a a' b b' : Nat}
    (ha : a ≤ N) (ha' : a' ≤ N) (hb : b ≤ N) (hb' : b' ≤ N) :
    boxQuadHalfExponent a a' b b' ≤ boxBernsteinDegree N := by
  have hca := c4_mono_local ha
  have hca' := c4_mono_local ha'
  have hcb := c4_mono_local hb
  have hcb' := c4_mono_local hb'
  unfold boxQuadHalfExponent boxQuadExponent boxBernsteinDegree
  omega

/-! ## 3. Exact physical scaling of one even monomial -/

private theorem qpow_eqv_pow_local (w : Q') : ∀ n,
    qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := qpow_eqv_pow_local w n
      show qpow w n * w ≈ w * w ^ n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih) ?_
      exact Q'.mul_comm_eqv (w ^ n) w

private theorem mul_pow_eqv_local (a b : Q') : ∀ n : Nat,
    (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | n + 1 => by
      have ih := mul_pow_eqv_local a b n
      show (a * b) * (a * b) ^ n ≈
        (a * a ^ n) * (b * b ^ n)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      ring_qeqv

private theorem ofNat_pow_eqv_local (a : Nat) : ∀ n,
    (Q'.ofNat a) ^ n ≈ Q'.ofNat (a ^ n)
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := ofNat_pow_eqv_local a n
      show Q'.ofNat a * (Q'.ofNat a) ^ n ≈ Q'.ofNat (a ^ (n + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat a) _ _ ih) ?_
      rw [Nat.pow_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (Q'.ofNat a) (Q'.ofNat (a ^ n))) ?_
      exact Q'.eqv_symm (ofNat_mul_eqv (a ^ n) a)

/-- The physical coordinate satisfies
`(4*w^2)^e ≃ 4^e*w^(2e)`. -/
theorem physicalSquareCoordinate_pow_eqv
    (w : Q') (e : Nat) :
    physicalSquareCoordinate w ^ e ≈
      Q'.ofNat (4 ^ e) * qpow w (e + e) := by
  unfold physicalSquareCoordinate
  refine Q'.eqv_trans _ _ _
    (mul_pow_eqv_local (4 : Q') (qpow w 2) e) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (4 ^ e) * (qpow w 2) ^ e) _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_pow_eqv_local 4 e)) ?_
  refine Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ e)) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (qpow_eqv_pow_local (qpow w 2) e)) ?_
  refine Q'.eqv_trans _ _ _ (qpow_qpow w 2 e) ?_
  exact Q'.eqv_of_eq (congrArg (qpow w) (by omega : 2 * e = e + e))

/-- Common integer clearing of an even physical monomial. -/
theorem cleared_physical_monomial_eqv
    (w : Q') (D e : Nat) (he : e ≤ D) :
    (Q'.ofNat (4 ^ (D - e)) * physicalSquareCoordinate w ^ e).eqv
      (Q'.ofNat (4 ^ D) * qpow w (e + e)) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (4 ^ (D - e)) *
      (Q'.ofNat (4 ^ e) * qpow w (e + e))) _
    (Q'.mul_eqv_congr_left _ _ _
      (physicalSquareCoordinate_pow_eqv w e)) ?_
  have hpow : 4 ^ (D - e) * 4 ^ e = 4 ^ D := by
    rw [← Nat.pow_add]
    congr 1
    omega
  refine Q'.eqv_trans _
    ((Q'.ofNat (4 ^ (D - e)) * Q'.ofNat (4 ^ e)) *
      qpow w (e + e)) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat (4 ^ (D - e)))
        (Q'.ofNat (4 ^ e)) (qpow w (e + e)))) ?_
  refine Q'.mul_eqv_congr_right _ _ (qpow w (e + e)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (ofNat_mul_eqv (4 ^ (D - e)) (4 ^ e))) ?_
  exact Q'.eqv_of_eq (congrArg Q'.ofNat hpow)

/-! ## 4. One Cauchy--Binet cell as one elevated row -/

private theorem coeffW_four_eqv
    (w : Q') (a a' b b' : Nat) :
    ((coeffW w a * coeffW w b) *
        (coeffW w a' * coeffW w b')).eqv
      (Q'.ofNat (boxQuadDimension a a' b b') *
        qpow w (boxQuadExponent a a' b b')) := by
  have hab := coeffW_mul_ofNat w a b
  have hab' := coeffW_mul_ofNat w a' b'
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hab)
      (Q'.mul_eqv_congr_left _ _ _ hab')) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat ((a + 1) * (b + 1)) *
        Q'.ofNat ((a' + 1) * (b' + 1))) *
      (qpow w (c4 a + c4 b) *
        qpow w (c4 a' + c4 b'))) _
    (mul_four_regroup _ _ _ _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (((a + 1) * (b + 1)) *
        ((a' + 1) * (b' + 1))) *
      (qpow w (c4 a + c4 b) *
        qpow w (c4 a' + c4 b'))) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (ofNat_mul_eqv ((a + 1) * (b + 1))
          ((a' + 1) * (b' + 1))))) ?_
  unfold boxQuadDimension boxQuadExponent
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (qpow_add w (c4 a + c4 b) (c4 a' + c4 b')))

/-- Product of two box-kernel cells is its fusion multiplicity times the
single four-Casimir monomial. -/
theorem boxKer_product_eqv_monomial
    (w : Q') (leftChannel rightChannel a a' b b' : Nat) :
    (boxKer w leftChannel a b * boxKer w rightChannel a' b').eqv
      (Q'.ofNat
          (boxProductMultiplicity leftChannel rightChannel a a' b b') *
        qpow w (boxQuadExponent a a' b b')) := by
  by_cases hleft : fusionOK a b leftChannel = true
  · by_cases hright : fusionOK a' b' rightChannel = true
    · have hcoeff := coeffW_four_eqv w a a' b b'
      unfold boxKer fusionInd boxProductMultiplicity
      simp only [hleft, hright, Bool.true_and, if_true]
      let x := coeffW w a * coeffW w b
      let y := coeffW w a' * coeffW w b'
      have hnorm : (((1 : Q') * x) * ((1 : Q') * y)).eqv (x * y) := by
        refine Q'.eqv_trans _ (x * ((1 : Q') * y)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv x)
        · exact Q'.mul_eqv_congr_left x _ _ (Q'.one_mul_eqv y)
      exact Q'.eqv_trans _ _ _ hnorm hcoeff
    · have hfalse : fusionOK a' b' rightChannel = false := by
        cases h : fusionOK a' b' rightChannel <;> simp_all
      unfold boxKer fusionInd boxProductMultiplicity
      simp only [hleft, hfalse, Bool.true_and, Bool.false_eq_true,
        if_false, if_true]
      refine Q'.eqv_trans _ 0 _ ?_ ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
        exact Q'.mul_zero_eqv _
      · exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  · have hfalse : fusionOK a b leftChannel = false := by
      cases h : fusionOK a b leftChannel <;> simp_all
    unfold boxKer fusionInd boxProductMultiplicity
    simp only [hfalse, Bool.false_and, Bool.false_eq_true, if_false]
    refine Q'.eqv_trans _ 0 _ ?_ ?_
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _)) ?_
      exact Q'.zero_mul_eqv _
    · exact Q'.eqv_symm (Q'.zero_mul_eqv _)

/-- The unsigned elevated row for one product of two box cells. -/
def boxProductBernsteinRow
    (N leftChannel rightChannel a a' b b' : Nat) : Nat → Int :=
  signedRowScale
    (Int.ofNat
      (boxCellClearedMultiplicity N
        (boxProductMultiplicity leftChannel rightChannel a a' b b')
        a a' b b'))
    (thetaMonoBernCoeff (boxBernsteinDegree N)
      (boxQuadHalfExponent a a' b b'))

/-- Exact reconstruction of one unsigned active/inactive product cell. -/
theorem boxProductBernsteinRow_eval
    (w : Q') (N leftChannel rightChannel a a' b b' : Nat)
    (hparity : leftChannel % 2 = rightChannel % 2)
    (ha : a ≤ N) (ha' : a' ≤ N) (hb : b ≤ N) (hb' : b' ≤ N) :
    signedBernsteinEval (boxBernsteinDegree N)
        (boxProductBernsteinRow N leftChannel rightChannel a a' b b')
        (physicalSquareCoordinate w) ≈
      Q'.ofNat (4 ^ boxBernsteinDegree N) *
        (boxKer w leftChannel a b * boxKer w rightChannel a' b') := by
  let D := boxBernsteinDegree N
  let e := boxQuadHalfExponent a a' b b'
  let m := boxProductMultiplicity leftChannel rightChannel a a' b b'
  have heD : e ≤ D := boxQuadHalfExponent_le_degree ha ha' hb hb'
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_scale D
      (Int.ofNat (boxCellClearedMultiplicity N m a a' b b'))
      (thetaMonoBernCoeff D e) (physicalSquareCoordinate w)) ?_
  refine Q'.eqv_trans _
    (Q'.ofInt (Int.ofNat (boxCellClearedMultiplicity N m a a' b b')) *
      physicalSquareCoordinate w ^ e) _
    (Q'.mul_eqv_congr_left _ _ _
      (thetaMonoBernCoeff_eval D e (physicalSquareCoordinate w) heD)) ?_
  by_cases hleft : fusionOK a b leftChannel = true
  · by_cases hright : fusionOK a' b' rightChannel = true
    · have heven : boxQuadExponent a a' b b' % 2 = 0 :=
        boxQuadExponent_even_of_active hparity hleft hright
      have hdouble : e + e = boxQuadExponent a a' b b' := by
        unfold e boxQuadHalfExponent
        omega
      have hscale := cleared_physical_monomial_eqv w D e heD
      have hproduct :=
        boxKer_product_eqv_monomial w leftChannel rightChannel a a' b b'
      have hproductActive :
          (boxKer w leftChannel a b * boxKer w rightChannel a' b').eqv
            (Q'.ofNat (boxQuadDimension a a' b b') *
              qpow w (boxQuadExponent a a' b b')) := by
        simpa only [boxProductMultiplicity, hleft, hright, Bool.true_and,
          if_true] using hproduct
      unfold m boxCellClearedMultiplicity boxProductMultiplicity
      simp only [hleft, hright, Bool.true_and, if_true]
      refine Q'.eqv_trans _
        (Q'.ofNat (boxQuadDimension a a' b b') *
          (Q'.ofNat (4 ^ (D - e)) * physicalSquareCoordinate w ^ e)) _ ?_ ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (ofNat_mul_eqv (boxQuadDimension a a' b b')
              (4 ^ (D - e)))) ?_
        ring_qeqv
      · refine Q'.eqv_trans _
          (Q'.ofNat (boxQuadDimension a a' b b') *
            (Q'.ofNat (4 ^ D) * qpow w (e + e))) _
          (Q'.mul_eqv_congr_left _ _ _ hscale) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (4 ^ D) *
            (Q'.ofNat (boxQuadDimension a a' b b') *
              qpow w (boxQuadExponent a a' b b'))) _ ?_ ?_
        · rw [hdouble]
          ring_qeqv
        · exact Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ D)) _ _
            (Q'.eqv_symm hproductActive)
    · have hfalse : fusionOK a' b' rightChannel = false := by
        cases h : fusionOK a' b' rightChannel <;> simp_all
      unfold m boxCellClearedMultiplicity boxProductMultiplicity
      simp only [hleft, hfalse, Bool.true_and, Bool.false_eq_true,
        if_false, Nat.zero_mul, Int.ofNat_zero]
      refine Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _) ?_
      refine Q'.eqv_symm (Q'.eqv_trans
        (Q'.ofNat (4 ^ D) *
          (boxKer w leftChannel a b * boxKer w rightChannel a' b'))
        (Q'.ofNat (4 ^ D) * 0) 0 ?_
        (Q'.mul_zero_eqv (Q'.ofNat (4 ^ D))))
      refine Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ D)) _ 0 ?_
      refine Q'.eqv_trans _
        (Q'.ofNat 0 * qpow w (boxQuadExponent a a' b b')) 0 ?_ ?_
      · simpa only [boxProductMultiplicity, hleft, hfalse, Bool.true_and,
          Bool.false_eq_true, if_false] using
          (boxKer_product_eqv_monomial
            w leftChannel rightChannel a a' b b')
      · exact Q'.zero_mul_eqv _
  · have hfalse : fusionOK a b leftChannel = false := by
      cases h : fusionOK a b leftChannel <;> simp_all
    unfold m boxCellClearedMultiplicity boxProductMultiplicity
    simp only [hfalse, Bool.false_and, Bool.false_eq_true,
      if_false, Nat.zero_mul, Int.ofNat_zero]
    refine Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _) ?_
    refine Q'.eqv_symm (Q'.eqv_trans
      (Q'.ofNat (4 ^ D) *
        (boxKer w leftChannel a b * boxKer w rightChannel a' b'))
      (Q'.ofNat (4 ^ D) * 0) 0 ?_
      (Q'.mul_zero_eqv (Q'.ofNat (4 ^ D))))
    refine Q'.mul_eqv_congr_left (Q'.ofNat (4 ^ D)) _ 0 ?_
    refine Q'.eqv_trans _
      (Q'.ofNat 0 * qpow w (boxQuadExponent a a' b b')) 0 ?_ ?_
    · simpa only [boxProductMultiplicity, hfalse, Bool.false_and,
        Bool.false_eq_true, if_false] using
        (boxKer_product_eqv_monomial
          w leftChannel rightChannel a a' b b')
    · exact Q'.zero_mul_eqv _

/-- The signed two-monomial row for one `quadW` cell. -/
def boxCellBernsteinRow
    (N s a a' b b' : Nat) : Nat → Int :=
  signedRowAdd
    (boxProductBernsteinRow N (s + 1) (s + 1) a a' b b')
    (signedRowScale (-1)
      (boxProductBernsteinRow N s (s + 2) a a' b b'))

/-- Exact reconstruction of one signed `quadW` cell. -/
theorem boxCellBernsteinRow_eval
    (w : Q') (N s a a' b b' : Nat)
    (ha : a ≤ N) (ha' : a' ≤ N) (hb : b ≤ N) (hb' : b' ≤ N) :
    signedBernsteinEval (boxBernsteinDegree N)
        (boxCellBernsteinRow N s a a' b b')
        (physicalSquareCoordinate w) ≈
      Q'.ofNat (4 ^ boxBernsteinDegree N) *
        quadW w s a a' b b' := by
  let D := boxBernsteinDegree N
  let u := physicalSquareCoordinate w
  let P := boxProductBernsteinRow N (s + 1) (s + 1) a a' b b'
  let M := boxProductBernsteinRow N s (s + 2) a a' b b'
  have hp := boxProductBernsteinRow_eval w N (s + 1) (s + 1)
    a a' b b' (by omega) ha ha' hb hb'
  have hm := boxProductBernsteinRow_eval w N s (s + 2)
    a a' b b' (by omega) ha ha' hb hb'
  unfold boxCellBernsteinRow
  refine Q'.eqv_trans _ _ _
    (signedBernsteinEval_add D P (signedRowScale (-1) M) u) ?_
  refine Q'.eqv_trans _
    (signedBernsteinEval D P u +
      Q'.ofInt (-1) * signedBernsteinEval D M u) _
    (Q'.add_eqv_congr_left _ _ _
      (signedBernsteinEval_scale D (-1) M u)) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (4 ^ D) *
        (boxKer w (s + 1) a b * boxKer w (s + 1) a' b')) +
      Q'.ofInt (-1) *
        (Q'.ofNat (4 ^ D) *
          (boxKer w s a b * boxKer w (s + 2) a' b'))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (by simpa [D, P, u] using hp)
      (Q'.mul_eqv_congr_left (Q'.ofInt (-1)) _ _
        (by simpa [D, M, u] using hm))
  · unfold quadW
    let A := boxKer w (s + 1) a b * boxKer w (s + 1) a' b'
    let B := boxKer w s a b * boxKer w (s + 2) a' b'
    let C := Q'.ofNat (4 ^ D)
    change _ ≈ Q'.ofNat (4 ^ D) * (_ + -_)
    change C * A + Q'.ofInt (-1) * (C * B) ≈ C * (A + -B)
    have hminusOne : Q'.ofInt (-1) ≈ -(1 : Q') := Q'.eqv_of_eq rfl
    refine Q'.eqv_trans _ (C * A + -(C * B)) _ ?_ ?_
    · refine Q'.add_eqv_congr_left (C * A) _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (C * B) hminusOne) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (C * B)) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (C * B))
    · refine Q'.eqv_trans _ (C * A + C * (-B)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left (C * A) _ _
          (Q'.eqv_symm (Q'.mul_neg_eqv C B))
      · exact Q'.eqv_symm (Q'.mul_add_eqv C A (-B))

/-! ## 5. Four nested finite row sums -/

/-- Pointwise sum of the first `n` signed rows. -/
def signedRowFsum (row : Nat → Nat → Int) : Nat → Nat → Int
  | 0, _ => 0
  | n + 1, j => signedRowFsum row n j + row n j

theorem signedBernsteinEval_signedRowFsum
    (D : Nat) (row : Nat → Nat → Int) (u : Q') : ∀ n,
    signedBernsteinEval D (signedRowFsum row n) u ≈
      fsum (fun i => signedBernsteinEval D (row i) u) n
  | 0 => by
      unfold signedBernsteinEval
      change finSum (fun j => (0 : Q') * bernsteinBasis D u j) (D + 1) ≈ 0
      refine Q'.eqv_trans _ _ _
        (finSum_eqv_congr _ (fun _ => (0 : Q'))
          (fun _ => Q'.zero_mul_eqv _) (D + 1)) ?_
      exact Q'.eqv_of_eq (finSum_zero_seq (D + 1))
  | n + 1 => by
      have ih := signedBernsteinEval_signedRowFsum D row u n
      have hadd : signedRowFsum row (n + 1) =
          signedRowAdd (signedRowFsum row n) (row n) := by
        funext j
        rfl
      rw [hadd]
      refine Q'.eqv_trans _ _ _
        (signedBernsteinEval_add D (signedRowFsum row n) (row n) u) ?_
      exact Q'.add_eqv_congr_right _ _ _ ih

/-- The canonical integer Bernstein row of one actual box difference. -/
def boxBernsteinCoefficient (N s : Nat) : Nat → Int :=
  signedRowFsum (fun a =>
    signedRowFsum (fun a' =>
      signedRowFsum (fun b =>
        signedRowFsum (fun b' =>
          boxCellBernsteinRow N s a a' b b') (N + 1))
        (N + 1))
      (N + 1))
    (N + 1)

/-- A reducible integer sum, used for the prefix-facing power carrier. -/
def intFsum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => intFsum f n + f n

/-- Four nested integer folds, matching the actual box ledger order. -/
def intFsum4 (F : Nat → Nat → Nat → Nat → Int) (n : Nat) : Int :=
  intFsum (fun a => intFsum (fun a' =>
    intFsum (fun b => intFsum (fun b' => F a a' b b') n) n) n) n

/-- The denominator-cleared coefficient bucket at one physical exponent. -/
def boxClearedPowerBucket (N s k : Nat) : Int :=
  intFsum4 (fun a a' b b' =>
    if boxQuadHalfExponent a a' b b' = k then
      boxCellClearedCoefficient N s a a' b b'
    else 0) (N + 1)

/-- `4^D` times the prefix of the physical power coefficients.  The first
`K` half-exponents are included.  This term-based form is extensionally the
usual bucketed coefficient prefix but evaluates without constructing a sparse
map. -/
def boxClearedPowerPrefix (N s K : Nat) : Int :=
  intFsum4 (fun a a' b b' =>
    if boxQuadHalfExponent a a' b b' < K then
      boxCellClearedCoefficient N s a a' b b'
    else 0) (N + 1)

/-! ## 5a. Division-free Abel summation for the already-cleared ledger

`BernsteinPrefixAbel` works with the raw coefficients and retains the powers
of four in its Pascal weights.  The physical cell compiler above has already
absorbed `4^(D-e)` into every term.  The following equivalent, simpler Abel
form is therefore the exact seam needed by the term-filtered prefix carrier.
-/

/-- Pascal weight after the physical powers of four have already been
absorbed into the coefficient bucket. -/
def clearedLedgerWeight (D j k : Nat) : Int :=
  Int.ofNat (RG.binom (D - k) (j - k))

/-- Abel payment between two adjacent already-cleared Pascal weights. -/
def clearedLedgerPayment (D j k : Nat) : Int :=
  Int.ofNat (RG.binom (D - k - 1) (j - k))

theorem clearedLedgerWeight_pred
    (D j n : Nat) (hn : 0 < n) (hnj : n ≤ j) (hjD : j ≤ D) :
    clearedLedgerWeight D j (n - 1) =
      clearedLedgerWeight D j n + clearedLedgerPayment D j (n - 1) := by
  have hD : D - (n - 1) = (D - n) + 1 := by omega
  have hj : j - (n - 1) = (j - n) + 1 := by omega
  unfold clearedLedgerWeight clearedLedgerPayment
  rw [hD, hj, RG.binom_succ_succ]
  simp only [Nat.add_sub_cancel, Int.ofNat_eq_natCast, Int.natCast_add]

theorem clearedLedgerPayment_nonnegative (D j k : Nat) :
    0 ≤ clearedLedgerPayment D j k := by
  unfold clearedLedgerPayment
  exact Int.natCast_nonneg _

/-- Bernstein coefficient of an already-cleared power bucket. -/
def clearedLedgerBernsteinCoefficient
    (D : Nat) (b : Nat → Int) (j : Nat) : Int :=
  intPrefixSum (fun k => b k * clearedLedgerWeight D j k) (j + 1)

/-- Prefix-positive Abel form for an already-cleared bucket. -/
def clearedLedgerAbelCoefficient
    (D : Nat) (b : Nat → Int) (j : Nat) : Int :=
  intPrefixSum b (j + 1) +
    intPrefixSum (fun k =>
      intPrefixSum b (k + 1) * clearedLedgerPayment D j k) j

theorem clearedLedgerPrefix_eq_abelPrefix
    (D j : Nat) (b : Nat → Int) (hjD : j ≤ D) : ∀ n,
    n ≤ j →
    intPrefixSum (fun k => b k * clearedLedgerWeight D j k) (n + 1) =
      intPrefixSum b (n + 1) * clearedLedgerWeight D j n +
        intPrefixSum (fun k =>
          intPrefixSum b (k + 1) * clearedLedgerPayment D j k) n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp only [intPrefixSum_succ, intPrefixSum_zero,
        Int.zero_add, Int.add_zero]
  | succ n ih =>
      intro hnj
      have hweight :
          clearedLedgerWeight D j n =
            clearedLedgerWeight D j (n + 1) +
              clearedLedgerPayment D j n := by
        simpa using
          (clearedLedgerWeight_pred D j (n + 1) (by omega) hnj hjD)
      calc
        intPrefixSum
              (fun k => b k * clearedLedgerWeight D j k) ((n + 1) + 1) =
            intPrefixSum
                (fun k => b k * clearedLedgerWeight D j k) (n + 1) +
              b (n + 1) * clearedLedgerWeight D j (n + 1) := rfl
        _ =
            (intPrefixSum b (n + 1) * clearedLedgerWeight D j n +
              intPrefixSum (fun k =>
                intPrefixSum b (k + 1) * clearedLedgerPayment D j k) n) +
              b (n + 1) * clearedLedgerWeight D j (n + 1) := by
            rw [ih (by omega)]
        _ =
            intPrefixSum b ((n + 1) + 1) *
                clearedLedgerWeight D j (n + 1) +
              intPrefixSum (fun k =>
                intPrefixSum b (k + 1) * clearedLedgerPayment D j k)
                (n + 1) := by
            rw [hweight]
            change
              ((intPrefixSum b (n + 1) *
                    (clearedLedgerWeight D j (n + 1) +
                      clearedLedgerPayment D j n) +
                  intPrefixSum (fun k =>
                    intPrefixSum b (k + 1) * clearedLedgerPayment D j k) n) +
                b (n + 1) * clearedLedgerWeight D j (n + 1)) =
              ((intPrefixSum b (n + 1) + b (n + 1)) *
                    clearedLedgerWeight D j (n + 1) +
                (intPrefixSum (fun k =>
                    intPrefixSum b (k + 1) * clearedLedgerPayment D j k) n +
                  intPrefixSum b (n + 1) * clearedLedgerPayment D j n))
            simp only [Int.mul_add, Int.add_mul]
            ac_rfl

theorem clearedLedgerWeight_diagonal (D j : Nat) :
    clearedLedgerWeight D j j = 1 := by
  unfold clearedLedgerWeight
  rw [Nat.sub_self, RG.binom_zero_right]
  rfl

theorem clearedLedgerBernsteinCoefficient_eq_abel
    (D : Nat) (b : Nat → Int) (j : Nat) (hjD : j ≤ D) :
    clearedLedgerBernsteinCoefficient D b j =
      clearedLedgerAbelCoefficient D b j := by
  unfold clearedLedgerBernsteinCoefficient clearedLedgerAbelCoefficient
  rw [clearedLedgerPrefix_eq_abelPrefix D j b hjD j (by omega),
    clearedLedgerWeight_diagonal, Int.mul_one]

theorem clearedLedgerBernsteinCoefficient_nonnegative_of_prefixes
    (D : Nat) (b : Nat → Int)
    (hprefix : ∀ k, k ≤ D → 0 ≤ intPrefixSum b (k + 1)) :
    ∀ j, j ≤ D → 0 ≤ clearedLedgerBernsteinCoefficient D b j := by
  intro j hjD
  rw [clearedLedgerBernsteinCoefficient_eq_abel D b j hjD]
  unfold clearedLedgerAbelCoefficient
  exact Int.add_nonneg
    (hprefix j hjD)
    (intPrefixSum_nonnegative _ j (fun k hk =>
      Int.mul_nonneg (hprefix k (by omega))
        (clearedLedgerPayment_nonnegative D j k)))

private theorem intFsum_congr
    {f g : Nat → Int} (h : ∀ i, f i = g i) : ∀ n,
    intFsum f n = intFsum g n
  | 0 => rfl
  | n + 1 => by rw [intFsum, intFsum, intFsum_congr h n, h n]

private theorem intFsum_add (f g : Nat → Int) : ∀ n,
    intFsum (fun i => f i + g i) n = intFsum f n + intFsum g n
  | 0 => by simp only [intFsum, Int.add_zero]
  | n + 1 => by
      rw [intFsum, intFsum, intFsum, intFsum_add f g n]
      omega

private theorem intFsum_mul_right (f : Nat → Int) (z : Int) : ∀ n,
    intFsum f n * z = intFsum (fun i => f i * z) n
  | 0 => by simp only [intFsum, Int.zero_mul]
  | n + 1 => by
      rw [intFsum, intFsum, Int.add_mul, intFsum_mul_right f z n]

private theorem intFsum_zero : ∀ n,
    intFsum (fun _ => (0 : Int)) n = 0
  | 0 => rfl
  | n + 1 => by rw [intFsum, intFsum_zero n, Int.add_zero]

private theorem intFsum4_congr
    {F G : Nat → Nat → Nat → Nat → Int}
    (h : ∀ a a' b b', F a a' b b' = G a a' b b') (n : Nat) :
    intFsum4 F n = intFsum4 G n := by
  unfold intFsum4
  apply intFsum_congr
  intro a
  apply intFsum_congr
  intro a'
  apply intFsum_congr
  intro b
  apply intFsum_congr
  exact h a a' b

private theorem intFsum4_mul_right
    (F : Nat → Nat → Nat → Nat → Int) (z : Int) (n : Nat) :
    intFsum4 F n * z = intFsum4 (fun a a' b b' => F a a' b b' * z) n := by
  unfold intFsum4
  rw [intFsum_mul_right]
  apply intFsum_congr
  intro a
  rw [intFsum_mul_right]
  apply intFsum_congr
  intro a'
  rw [intFsum_mul_right]
  apply intFsum_congr
  intro b
  exact intFsum_mul_right _ _ n

private theorem intPrefixSum_intFsum_swap
    (F : Nat → Nat → Int) (n : Nat) : ∀ K,
    intPrefixSum (fun k => intFsum (fun i => F i k) n) K =
      intFsum (fun i => intPrefixSum (fun k => F i k) K) n
  | 0 => by
      simp only [intPrefixSum_zero]
      exact (intFsum_zero n).symm
  | K + 1 => by
      rw [intPrefixSum_succ, intPrefixSum_intFsum_swap F n K]
      rw [← intFsum_add]
      apply intFsum_congr
      intro i
      rfl

private theorem intPrefixSum_intFsum4_swap
    (F : Nat → Nat → Nat → Nat → Nat → Int)
    (n K : Nat) :
    intPrefixSum (fun k => intFsum4 (fun a a' b b' => F a a' b b' k) n) K =
      intFsum4 (fun a a' b b' => intPrefixSum (fun k => F a a' b b' k) K) n := by
  unfold intFsum4
  rw [intPrefixSum_intFsum_swap]
  apply intFsum_congr
  intro a
  rw [intPrefixSum_intFsum_swap]
  apply intFsum_congr
  intro a'
  rw [intPrefixSum_intFsum_swap]
  apply intFsum_congr
  intro b
  exact intPrefixSum_intFsum_swap _ n K

private theorem intPrefixSum_singleton_lt (e K : Nat) (z : Int) :
    intPrefixSum (fun k => if e = k then z else 0) K =
      if e < K then z else 0 := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [intPrefixSum_succ, ih]
      by_cases heK : e < K
      · have hne : e ≠ K := by omega
        rw [if_pos heK, if_neg hne, Int.add_zero, if_pos (by omega)]
      · by_cases heq : e = K
        · subst e
          rw [if_neg (by omega), if_pos rfl, Int.zero_add,
            if_pos (by omega)]
        · have hgt : K < e := by omega
          rw [if_neg heK, if_neg heq, Int.zero_add, if_neg (by omega)]

theorem boxClearedPowerPrefix_eq_bucketPrefix (N s K : Nat) :
    boxClearedPowerPrefix N s K =
      intPrefixSum (boxClearedPowerBucket N s) K := by
  unfold boxClearedPowerPrefix boxClearedPowerBucket
  rw [intPrefixSum_intFsum4_swap]
  apply intFsum4_congr
  intro a a' b b'
  exact (intPrefixSum_singleton_lt
    (boxQuadHalfExponent a a' b b') K
    (boxCellClearedCoefficient N s a a' b b')).symm

private theorem signedRowFsum_apply_eq_intFsum
    (row : Nat → Nat → Int) (j : Nat) : ∀ n,
    signedRowFsum row n j = intFsum (fun i => row i j) n
  | 0 => rfl
  | n + 1 => by
      rw [signedRowFsum, intFsum, signedRowFsum_apply_eq_intFsum row j n]

theorem boxBernsteinCoefficient_eq_cellFsum
    (N s j : Nat) :
    boxBernsteinCoefficient N s j =
      intFsum4 (fun a a' b b' => boxCellBernsteinRow N s a a' b b' j)
        (N + 1) := by
  unfold boxBernsteinCoefficient intFsum4
  rw [signedRowFsum_apply_eq_intFsum]
  apply intFsum_congr
  intro a
  rw [signedRowFsum_apply_eq_intFsum]
  apply intFsum_congr
  intro a'
  rw [signedRowFsum_apply_eq_intFsum]
  apply intFsum_congr
  intro b
  exact signedRowFsum_apply_eq_intFsum _ j (N + 1)

theorem boxCellBernsteinRow_apply
    (N s a a' b b' j : Nat) :
    boxCellBernsteinRow N s a a' b b' j =
      boxCellClearedCoefficient N s a a' b b' *
        thetaMonoBernCoeff (boxBernsteinDegree N)
          (boxQuadHalfExponent a a' b b') j := by
  unfold boxCellBernsteinRow boxProductBernsteinRow signedRowAdd signedRowScale
    boxCellClearedCoefficient boxPositiveMultiplicity boxNegativeMultiplicity
  rw [Int.sub_mul, Int.neg_one_mul, Int.sub_eq_add_neg]

private theorem thetaMonoBernCoeff_eq_clearedLedgerWeight
    (D e j : Nat) (he : e ≤ j) :
    thetaMonoBernCoeff D e j = clearedLedgerWeight D j e := by
  unfold thetaMonoBernCoeff clearedLedgerWeight
  simp only [he, if_true, pnChoose_eq_binom]

private theorem intPrefixSum_weighted_singleton
    (D e j : Nat) (z : Int) :
    intPrefixSum (fun k =>
      (if e = k then z else 0) * clearedLedgerWeight D j k) (j + 1) =
      z * thetaMonoBernCoeff D e j := by
  by_cases he : e ≤ j
  · have helt : e < j + 1 := by omega
    have hsingle := intPrefixSum_singleton_lt e (j + 1)
      (z * clearedLedgerWeight D j e)
    rw [if_pos helt] at hsingle
    calc
      intPrefixSum (fun k =>
          (if e = k then z else 0) * clearedLedgerWeight D j k) (j + 1) =
          intPrefixSum (fun k =>
            if e = k then z * clearedLedgerWeight D j e else 0) (j + 1) := by
            apply congrArg (fun x => intPrefixSum x (j + 1))
            funext k
            by_cases hek : e = k
            · subst k
              simp
            · rw [if_neg hek, Int.zero_mul, if_neg hek]
      _ = z * clearedLedgerWeight D j e := hsingle
      _ = z * thetaMonoBernCoeff D e j := by
        exact congrArg (fun x => z * x)
          (thetaMonoBernCoeff_eq_clearedLedgerWeight D e j he).symm
  · have helt : ¬ e < j + 1 := by omega
    have hsingle := intPrefixSum_singleton_lt e (j + 1)
      (z * clearedLedgerWeight D j e)
    rw [if_neg helt] at hsingle
    have htheta : thetaMonoBernCoeff D e j = 0 := by
      unfold thetaMonoBernCoeff
      exact if_neg he
    calc
      intPrefixSum (fun k =>
          (if e = k then z else 0) * clearedLedgerWeight D j k) (j + 1) =
          intPrefixSum (fun k =>
            if e = k then z * clearedLedgerWeight D j e else 0) (j + 1) := by
            apply congrArg (fun x => intPrefixSum x (j + 1))
            funext k
            by_cases hek : e = k
            · subst k
              simp
            · rw [if_neg hek, Int.zero_mul, if_neg hek]
      _ = 0 := hsingle
      _ = z * thetaMonoBernCoeff D e j := by rw [htheta, Int.mul_zero]

theorem boxBernsteinCoefficient_eq_clearedLedger
    (N s j : Nat) :
    boxBernsteinCoefficient N s j =
      clearedLedgerBernsteinCoefficient (boxBernsteinDegree N)
        (boxClearedPowerBucket N s) j := by
  rw [boxBernsteinCoefficient_eq_cellFsum]
  unfold clearedLedgerBernsteinCoefficient boxClearedPowerBucket
  apply Eq.symm
  calc
    intPrefixSum (fun k =>
        intFsum4 (fun a a' b b' =>
          if boxQuadHalfExponent a a' b b' = k then
            boxCellClearedCoefficient N s a a' b b'
          else 0) (N + 1) *
          clearedLedgerWeight (boxBernsteinDegree N) j k) (j + 1) =
      intPrefixSum (fun k =>
        intFsum4 (fun a a' b b' =>
          (if boxQuadHalfExponent a a' b b' = k then
            boxCellClearedCoefficient N s a a' b b'
          else 0) * clearedLedgerWeight (boxBernsteinDegree N) j k)
          (N + 1)) (j + 1) := by
        apply congrArg (fun f => intPrefixSum f (j + 1))
        funext k
        exact intFsum4_mul_right _ _ (N + 1)
    _ = intFsum4 (fun a a' b b' =>
          intPrefixSum (fun k =>
            (if boxQuadHalfExponent a a' b b' = k then
              boxCellClearedCoefficient N s a a' b b'
            else 0) * clearedLedgerWeight (boxBernsteinDegree N) j k)
            (j + 1)) (N + 1) :=
      intPrefixSum_intFsum4_swap _ (N + 1) (j + 1)
    _ = intFsum4 (fun a a' b b' =>
          boxCellBernsteinRow N s a a' b b' j) (N + 1) := by
      apply intFsum4_congr
      intro a a' b b'
      rw [boxCellBernsteinRow_apply]
      exact intPrefixSum_weighted_singleton
        (boxBernsteinDegree N) (boxQuadHalfExponent a a' b b') j
        (boxCellClearedCoefficient N s a a' b b')

/-- Direct all-degree Abel seam from the term-filtered physical prefixes to
the actual reconstructed Bernstein row. -/
theorem boxBernsteinCoefficient_nonnegative_of_cleared_prefixes
    (N s : Nat)
    (hprefix : ∀ K, K ≤ boxBernsteinDegree N + 1 →
      0 ≤ boxClearedPowerPrefix N s K) :
    ∀ j, j ≤ boxBernsteinDegree N →
      0 ≤ boxBernsteinCoefficient N s j := by
  intro j hj
  rw [boxBernsteinCoefficient_eq_clearedLedger]
  exact clearedLedgerBernsteinCoefficient_nonnegative_of_prefixes
    (boxBernsteinDegree N) (boxClearedPowerBucket N s)
    (fun k hk => by
      rw [← boxClearedPowerPrefix_eq_bucketPrefix]
      exact hprefix (k + 1) (by omega)) j hj

private theorem const_mul_fsum4
    (c : Q') (F : Nat → Nat → Nat → Nat → Q') (n : Nat) :
    (c * fsum (fun a => fsum (fun a' =>
      fsum (fun b => fsum (fun b' => F a a' b b') n) n) n) n).eqv
      (fsum (fun a => fsum (fun a' =>
        fsum (fun b => fsum (fun b' => c * F a a' b b') n) n) n) n) := by
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun a => fsum (fun a' =>
      fsum (fun b => fsum (fun b' => F a a' b b') n) n) n) n) ?_
  refine fsum_eqv_congr _ _ (fun a => ?_) n
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun a' =>
      fsum (fun b => fsum (fun b' => F a a' b b') n) n) n) ?_
  refine fsum_eqv_congr _ _ (fun a' => ?_) n
  refine Q'.eqv_trans _ _ _
    (fsum_const_mul c (fun b => fsum (fun b' => F a a' b b') n) n) ?_
  refine fsum_eqv_congr _ _ (fun b => ?_) n
  exact fsum_const_mul c (fun b' => F a a' b b') n

/-- Exact reconstruction of the canonical row against the actual
Cauchy--Binet quadruple difference. -/
theorem boxBernsteinCoefficient_eval
    (w : Q') (N s : Nat) :
    signedBernsteinEval (boxBernsteinDegree N)
        (boxBernsteinCoefficient N s) (physicalSquareCoordinate w) ≈
      Q'.ofNat (4 ^ boxBernsteinDegree N) * quadDiff w N s := by
  let D := boxBernsteinDegree N
  let u := physicalSquareCoordinate w
  let n := N + 1
  unfold boxBernsteinCoefficient
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
      signedBernsteinEval D (boxCellBernsteinRow N s a a' b b') u)
      n) n) n) n) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (signedBernsteinEval_signedRowFsum D _ u n) ?_
    refine fsum_eqv_congr _ _ (fun a => ?_) n
    refine Q'.eqv_trans _ _ _
      (signedBernsteinEval_signedRowFsum D _ u n) ?_
    refine fsum_eqv_congr _ _ (fun a' => ?_) n
    refine Q'.eqv_trans _ _ _
      (signedBernsteinEval_signedRowFsum D _ u n) ?_
    refine fsum_eqv_congr _ _ (fun b => ?_) n
    exact signedBernsteinEval_signedRowFsum D _ u n
  · refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
        Q'.ofNat (4 ^ D) * quadW w s a a' b b') n) n) n) n) _ ?_ ?_
    · refine fsum_eqv_congr_lt _ _ n (fun a ha => ?_)
      refine fsum_eqv_congr_lt _ _ n (fun a' ha' => ?_)
      refine fsum_eqv_congr_lt _ _ n (fun b hb => ?_)
      refine fsum_eqv_congr_lt _ _ n (fun b' hb' => ?_)
      have haN : a ≤ N := by dsimp [n] at ha; omega
      have haN' : a' ≤ N := by dsimp [n] at ha'; omega
      have hbN : b ≤ N := by dsimp [n] at hb; omega
      have hbN' : b' ≤ N := by dsimp [n] at hb'; omega
      exact boxCellBernsteinRow_eval w N s a a' b b'
        haN haN' hbN hbN'
    · unfold quadDiff
      exact Q'.eqv_symm
        (const_mul_fsum4 (Q'.ofNat (4 ^ D))
          (fun a a' b b' => quadW w s a a' b b') n)

/-- Reconstruction in the exact orientation required by
`FiniteTriangleBernsteinCertificate`. -/
theorem boxDiff_scaled_reconstruction
    (w : Q') (N s : Nat) :
    (Q'.ofNat (4 ^ boxBernsteinDegree N) *
      (boxSum w N (s + 1) * boxSum w N (s + 1) +
        -(boxSum w N s * boxSum w N (s + 2)))).eqv
      (signedBernsteinEval (boxBernsteinDegree N)
        (boxBernsteinCoefficient N s) (physicalSquareCoordinate w)) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (4 ^ boxBernsteinDegree N) * quadDiff w N s) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (boxDiff_eq_quadDiff w N s)
  · exact Q'.eqv_symm (boxBernsteinCoefficient_eval w N s)

/-! ## 6. The reconstruction-free finite certificate constructor -/

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

/-- The only input is the finite reflected coefficient check.  Degree,
integer row, positive clearing scale, and exact reconstruction are supplied
canonically by this module. -/
def finiteTriangleBernsteinCertificateOfCanonicalChecks
    (N : Nat)
    (hcheck : ∀ s, s + 2 ≤ 2 * N →
      bernsteinRowNonnegativeCheck (boxBernsteinDegree N)
        (boxBernsteinCoefficient N s) = true) :
    FiniteTriangleBernsteinCertificate N where
  degree := fun _ => boxBernsteinDegree N
  zeroOrder := fun _ => 0
  coefficient := fun s => boxBernsteinCoefficient N s
  scale := fun _ => Q'.ofNat (4 ^ boxBernsteinDegree N)
  scale_positive := fun _ _ =>
    ofNat_pos_of_pos
      (Nat.pow_pos (by decide : 0 < 4) : 0 < 4 ^ boxBernsteinDegree N)
  coefficient_check := hcheck
  boxDiff_scaled_reconstruction := by
    intro w s _
    refine Q'.eqv_trans _
      (signedBernsteinEval (boxBernsteinDegree N)
        (boxBernsteinCoefficient N s) (physicalSquareCoordinate w)) _
      (boxDiff_scaled_reconstruction w N s) ?_
    exact Q'.eqv_symm
      (Q'.one_mul_eqv
        (signedBernsteinEval (boxBernsteinDegree N)
          (boxBernsteinCoefficient N s) (physicalSquareCoordinate w)))

/-- Symbolic all-mode constructor: a nonnegative cleared physical prefix at
every exponent populates the Boolean checker by completeness, with no row
evaluation. -/
def finiteTriangleBernsteinCertificateOfClearedPrefixes
    (N : Nat)
    (hprefix : ∀ s, s + 2 ≤ 2 * N → ∀ K,
      K ≤ boxBernsteinDegree N + 1 →
        0 ≤ boxClearedPowerPrefix N s K) :
    FiniteTriangleBernsteinCertificate N :=
  finiteTriangleBernsteinCertificateOfCanonicalChecks N (fun s hs =>
    YMGap.Continuum.FusionWeightedInterlacingCertificate.bernsteinRowNonnegativeCheck_complete
      (boxBernsteinDegree N) (boxBernsteinCoefficient N s)
      (boxBernsteinCoefficient_nonnegative_of_cleared_prefixes N s
        (hprefix s hs)))

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxQuadExponent_even_of_active
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxQuadHalfExponent_le_degree
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.physicalSquareCoordinate_pow_eqv
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.cleared_physical_monomial_eqv
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxKer_product_eqv_monomial
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxProductBernsteinRow_eval
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxCellBernsteinRow_eval
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.signedBernsteinEval_signedRowFsum
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxClearedPowerPrefix_eq_bucketPrefix
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxBernsteinCoefficient_eq_clearedLedger
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxBernsteinCoefficient_nonnegative_of_cleared_prefixes
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxBernsteinCoefficient_eval
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.boxDiff_scaled_reconstruction
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.finiteTriangleBernsteinCertificateOfCanonicalChecks
#print axioms YMGap.Continuum.FusionBoxBernsteinReconstruction.finiteTriangleBernsteinCertificateOfClearedPrefixes

end YMGap.Continuum.FusionBoxBernsteinReconstruction
