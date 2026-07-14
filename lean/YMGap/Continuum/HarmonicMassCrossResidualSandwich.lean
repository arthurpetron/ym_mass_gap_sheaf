/-
One-scale sandwich mechanism for the sharp physical Pascal cross.

Writing `r_k = R_k / I_k`, the exact cross residual asks for

  r_k <= r_(k+1) + 3 u_k^2.

The separated estimates `r_k <= 7 u_k^2` and
`5 u_(k+1)^2 <= r_(k+1)` suffice from `k = 7` onward, because

  7 u_k^2 <= 3 u_k^2 + 5 u_(k+1)^2.

This file proves that implication without division, closes the first seven
scales exactly, and records that the scalar comparison is false at `k = 6`.
Thus a proof through this route must either start at seven or sharpen one of
the two one-scale constants.
-/

import YMGap.Continuum.HarmonicMassCrossPascalReduction
import YMGap.Continuum.HarmonicVariableAnchorRetune
import YMGap.Continuum.HarmonicVariableAnchorThetaBridge
import YMGap.Continuum.HarmonicThetaTermwiseFence

namespace YMGap.Continuum.HarmonicMassCrossResidualSandwich

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossPascalReduction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicHalfEdgeDominance
open YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPhysicalClosure
open YMGap.Continuum.HarmonicThetaTermwiseFence
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicVariableAnchorRetune
open YMGap.Continuum.HarmonicVariableAnchorThetaBridge
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem sandwich_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "sandwich_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, sandwich_neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def lowerSixGapPolyL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let L := RingNormaliser.PolyExpr.var 2
  let twoMinusU := .add (.const 2) (.neg u)
  .add
    (.add
      (.mul (.mul (.mul twoMinusU twoMinusU) twoMinusU) I)
      (.neg (.mul (.const 8) L)))
    (.neg (.mul (.mul (.const 6) (.mul u u)) I))

private def lowerSixGapPolyR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let I := RingNormaliser.PolyExpr.var 1
  let L := RingNormaliser.PolyExpr.var 2
  .add
    (.add
      (.add
        (.mul (.const 8) I)
        (.neg (.mul (.const 12) (.mul u I))))
      (.neg (.mul (.const 8) L)))
    (.neg (.mul (.mul (.mul u u) u) I))

private theorem lowerSixGapPoly_normal :
    RingNormaliser.normalize lowerSixGapPolyL =
      RingNormaliser.normalize lowerSixGapPolyR := by decide

private theorem lower_six_gap_algebra (u I L : Q') :
    (((Q'.ofNat 2 + -u) * (Q'.ofNat 2 + -u)) *
          (Q'.ofNat 2 + -u)) * I +
        -(Q'.ofNat 8 * L) +
        -(Q'.ofNat 6 * (u * u) * I) ≈
      (Q'.ofNat 8 * I + -(Q'.ofNat 12 * (u * I)) +
          -(Q'.ofNat 8 * L)) +
        -(((u * u) * u) * I) := by
  simpa [lowerSixGapPolyL, lowerSixGapPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      lowerSixGapPolyL lowerSixGapPolyR lowerSixGapPoly_normal
      (fun | 0 => u | 1 => I | _ => L))

/-- One-scale upper half of the normalized residual sandwich, stated without
division by the positive integer theta head. -/
def PhysicalResidualUpperSeven (k : Nat) : Prop :=
  physicalPascalResidual k ≤
    (Q'.ofNat 7 * (harmU k * harmU k)) * physicalIntegerTheta k

/-- The upper envelope after paying the exact one-unit cost of transporting
from the linear growing head to the physical quadratic cutoff. -/
def PhysicalResidualUpperEight (k : Nat) : Prop :=
  physicalPascalResidual k ≤
    (Q'.ofNat 8 * (harmU k * harmU k)) * physicalIntegerTheta k

/-- One-scale lower half of the normalized residual sandwich, stated without
division. -/
def PhysicalResidualLowerFive (k : Nat) : Prop :=
  (Q'.ofNat 5 * (harmU k * harmU k)) * physicalIntegerTheta k ≤
    physicalPascalResidual k

/-- Six-unit physical lower envelope, paired with the transported
eight-unit upper envelope. -/
def PhysicalResidualLowerSix (k : Nat) : Prop :=
  (Q'.ofNat 6 * (harmU k * harmU k)) * physicalIntegerTheta k ≤
    physicalPascalResidual k

/-- Lower envelope at the linear growing head. -/
def GrowingResidualLowerFive (k : Nat) : Prop :=
  (Q'.ofNat 5 * (harmU k * harmU k)) *
      integerThetaSum (harmW k) (growingAnchor k) ≤
    growingPascalResidual k

/-- Six-unit lower envelope at the linear growing head. -/
def GrowingResidualLowerSix (k : Nat) : Prop :=
  (Q'.ofNat 6 * (harmU k * harmU k)) *
      integerThetaSum (harmW k) (growingAnchor k) ≤
    growingPascalResidual k

/-- Expanded cubic-tangent margin exactly equivalent to the six-unit lower
residual gap.  It isolates the remaining content into a single same-scale
weighted theta inequality. -/
def GrowingResidualLowerSixCubicMargin (k : Nat) : Prop :=
  let u := harmU k
  let I := integerThetaSum (harmW k) (growingAnchor k)
  let L := harmW k * halfThetaSum (harmW k) (growingAnchor k + 1)
  (0 : Q') ≤
    (Q'.ofNat 8 * I + -(Q'.ofNat 12 * (u * I)) +
        -(Q'.ofNat 8 * L)) +
      -(((u * u) * u) * I)

/-- Exact algebraic identification of the lower-six gap with the cubic
tangent margin. -/
theorem growingLowerSixGap_eqv_cubicMargin (k : Nat) :
    growingPascalResidual k +
        -((Q'.ofNat 6 * (harmU k * harmU k)) *
          integerThetaSum (harmW k) (growingAnchor k)) ≈
      let u := harmU k
      let I := integerThetaSum (harmW k) (growingAnchor k)
      let L := harmW k * halfThetaSum (harmW k) (growingAnchor k + 1)
      (Q'.ofNat 8 * I + -(Q'.ofNat 12 * (u * I)) +
          -(Q'.ofNat 8 * L)) +
        -(((u * u) * u) * I) := by
  let u := harmU k
  let I := integerThetaSum (harmW k) (growingAnchor k)
  let L := harmW k * halfThetaSum (harmW k) (growingAnchor k + 1)
  let x := Q'.ofNat 2 + -u
  have h11 : (1 : Q') + (1 : Q') ≈ Q'.ofNat 2 := by decide
  have hbase : (1 : Q') + harmW k ≈ x := by
    dsimp only [x, u]
    unfold harmW oneSub
    refine Q'.eqv_trans _ (((1 : Q') + (1 : Q')) + -(harmU k)) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _ h11
  have hpow0 := qpow_eqv_congr_base hbase 3
  have hpow1 : qpow x 3 ≈ (x * x) * x := by
    change (((1 : Q') * x) * x) * x ≈ (x * x) * x
    exact Q'.mul_eqv_congr_right _ _ x
      (Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x))
  have hpow : qpow ((1 : Q') + harmW k) 3 ≈ (x * x) * x :=
    Q'.eqv_trans _ _ _ hpow0 hpow1
  have hmain :
      qpow ((1 : Q') + harmW k) 3 * I + -(Q'.ofNat 8 * L) ≈
        ((x * x) * x) * I + -(Q'.ofNat 8 * L) := by
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ I hpow)
  unfold growingPascalResidual growingHeadScaledThetaResidual
  change
    (qpow ((1 : Q') + harmW k) 3 * I + -(Q'.ofNat 8 * L)) +
        -(Q'.ofNat 6 * (u * u) * I) ≈ _
  refine Q'.eqv_trans _
    (((x * x) * x) * I + -(Q'.ofNat 8 * L) +
      -(Q'.ofNat 6 * (u * u) * I)) _
    (Q'.add_eqv_congr_right _ _ _ hmain) ?_
  dsimp only [x]
  exact lower_six_gap_algebra u I L

/-- The cubic-tangent margin is a sufficient (indeed, by the exact identity,
equivalent) one-scale certificate for the six-unit growing lower envelope. -/
theorem growingResidualLowerSix_of_cubicMargin {k : Nat}
    (hmargin : GrowingResidualLowerSixCubicMargin k) :
    GrowingResidualLowerSix k := by
  have heq := growingLowerSixGap_eqv_cubicMargin k
  have hgap : (0 : Q') ≤
      growingPascalResidual k +
        -((Q'.ofNat 6 * (harmU k * harmU k)) *
          integerThetaSum (harmW k) (growingAnchor k)) := by
    exact Q'.le_trans' _ _ _ hmargin (Q'.ge_of_eqv heq)
  unfold GrowingResidualLowerSix
  exact Q'.le_of_sub_nonneg hgap

/-- The seven-unit upper half is already closed at the growing head by the
Pascal/Bernstein certificate.  This pins down which part of the physical
sandwich is new: only the passage from the linear growing head to the
quadratic physical cutoff. -/
theorem growingResidualUpperSeven (k : Nat) :
    growingPascalResidual k ≤
      (Q'.ofNat 7 * (harmU k * harmU k)) *
        integerThetaSum (harmW k) (growingAnchor k) := by
  have h := sevenUnitResidualGap_pascal_nonnegative k
  unfold sevenUnitResidualGap at h
  exact Q'.le_of_sub_nonneg h

private theorem eighth_diag_one_le_adj_one {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (h23 : Q'.mkPos 2 3 (by decide) ≤ w) :
    Q'.mkPos 1 8 (by decide) * coordNormSq w 1 ≤ adjCorr w 1 := by
  have hw3lo : qpow (Q'.mkPos 2 3 (by decide)) 3 ≤ qpow w 3 :=
    qpow_mono (by decide) h23 3
  have h18w3 : Q'.mkPos 1 8 (by decide) ≤ qpow w 3 :=
    Q'.le_trans' _ _ _ (by decide) hw3lo
  have hx1 : qpow w 3 ≤ (1 : Q') := qpow_le_one hw0 hw1 3
  have hxx : qpow w 3 * qpow w 3 ≤ qpow w 3 := by
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 3) hx1
      (qpow_nonneg w hw0 3)
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hfour : Q'.ofNat 4 * (qpow w 3 * qpow w 3) ≤
      Q'.ofNat 4 * qpow w 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hxx (by decide)
  have hone : (1 : Q') ≤ Q'.ofNat 8 * qpow w 3 := by
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8) h18w3
      (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hs
  have hsum : (1 : Q') + Q'.ofNat 4 * (qpow w 3 * qpow w 3) ≤
      Q'.ofNat 16 * qpow w 3 := by
    have ha := Q'.add_le_add hone hfour
    have h1216 : Q'.ofNat 8 * qpow w 3 +
        Q'.ofNat 4 * qpow w 3 ≤ Q'.ofNat 16 * qpow w 3 := by
      have hc : Q'.ofNat 12 ≤ Q'.ofNat 16 := by decide
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w 3) hc
        (qpow_nonneg w hw0 3)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.add_mul_eqv (Q'.ofNat 8) (Q'.ofNat 4) (qpow w 3)))) hm
    exact Q'.le_trans' _ _ _ ha h1216
  have hs := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 1 8 (by decide)) hsum (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      unfold coordNormSq
      simp only [fsum_succ, fsum_zero, coeffW_zero, Q'.zero_add']
      rw [coeffW_one]
      unfold dimQ heatKernelSep
      sandwich_ring))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (by
      unfold adjCorr
      simp only [fsum_succ, fsum_zero, coeffW_zero, Q'.zero_add']
      rw [coeffW_one]
      unfold dimQ heatKernelSep
      sandwich_ring)))

/-- The retained adjacent quotient is uniformly at least `1/8`.  The proof
starts at the explicit one-edge quotient and propagates it by cutoff PF2
monotonicity; it does not appeal to the desired mass cross. -/
theorem eighth_mul_growing_diag_le_growing_adj {k : Nat} (hk : 1 ≤ k) :
    Q'.mkPos 1 8 (by decide) *
        coordNormSq (harmW k) (growingAnchor k) ≤
      adjCorr (harmW k) (growingAnchor k + 1) := by
  let w := harmW k
  let b := growingAnchor k
  have hb : 1 ≤ b := by
    dsimp only [b]
    unfold growingAnchor
    omega
  have hbase : Q'.mkPos 1 8 (by decide) * coordNormSq w 1 ≤
      adjCorr w 1 := by
    apply eighth_diag_one_le_adj_one (harmW_nonneg k) (harmW_le_one k)
    exact twoThirds_le_harmW k hk
  have hmono := finite_cutoff_tail_compare
    (harmW_nonneg k) (harmW_le_one k) (harmW_pos k) 1 (b - 1)
  have hidx : 1 + (b - 1) = b := Nat.add_sub_of_le hb
  rw [hidx] at hmono
  have hDb0 : (0 : Q') ≤ coordNormSq w b :=
    coordNormSq_nonneg (harmW_nonneg k) b
  have hD1p : (0 : Q') < coordNormSq w 1 :=
    coordNormSq_pos (harmW_nonneg k) 1
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _
    (coordNormSq w b) hbase hDb0
  have hchain : coordNormSq w 1 *
        (Q'.mkPos 1 8 (by decide) * coordNormSq w b) ≤
      coordNormSq w 1 * adjCorr w b := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by sandwich_ring))
      (Q'.le_trans' _ _ _ hscale
        (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv (by sandwich_ring))))
  have hbnd : Q'.mkPos 1 8 (by decide) * coordNormSq w b ≤
      adjCorr w b := Q'.le_of_mul_le_mul_left hchain hD1p
  have hedge0 : (0 : Q') ≤ coeffW w b * coeffW w (b + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg (harmW_nonneg k) b)
      (coeffW_nonneg (harmW_nonneg k) (b + 1))
  have hgrow : adjCorr w b ≤ adjCorr w (b + 1) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (adjCorr w b) _ hedge0)
      (Q'.ge_of_eqv (adjCorr_succ w b))
  exact Q'.le_trans' _ _ _ hbnd hgrow

/-- The exact growing-anchor coefficient cross already fits below `1/8`.
This is the scalar input needed to propagate the *actual retained-head
quotient*, instead of weakening it to the retune cube. -/
theorem growing_anchor_scalar_cross_eighth (k : Nat) :
    Q'.ofNat (growingAnchor k + 2) *
        qpow (harmW k) (2 * growingAnchor k + 3) ≤
      Q'.mkPos 1 8 (by decide) *
        Q'.ofNat (growingAnchor k + 1) := by
  let b := growingAnchor k
  let p := qpow (harmW k) (2 * b + 3)
  have hnat : b + 2 ≤ 2 * (b + 1) := by omega
  have hcoef : Q'.ofNat (b + 2) ≤ Q'.ofNat (2 * (b + 1)) :=
    MovingCutoff.ofNat_le_ofNat' hnat
  have hp0 : (0 : Q') ≤ p := qpow_nonneg _ (harmW_nonneg k) _
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ p hcoef hp0
  have hleft : Q'.ofNat (2 * (b + 1)) * p ≈
      (Q'.ofNat 2 * p) * Q'.ofNat (b + 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ p
        (HeatKernelRGStep.ofNat_mul_eqv 2 (b + 1))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.ofNat (b + 1)) (growing_anchor_multiplier_le_eighth k)
    (HeatKernelRGStep.zero_le_ofNat _)
  change Q'.ofNat (b + 2) * p ≤
    Q'.mkPos 1 8 (by decide) * Q'.ofNat (b + 1)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hscale)

/-- The single half-edge missed by replacing the physical quotient with the
growing-head quotient fits inside one inverse-square unit. -/
theorem four_growing_terminal_edge_le_u_sq_diag (k : Nat) :
    Q'.ofNat 4 *
        (coeffW (harmW k) (growingAnchor k) *
          coeffW (harmW k) (growingAnchor k + 1)) ≤
      (harmU k * harmU k) *
        coordNormSq (harmW k) (growingAnchor k) := by
  let p := 2 * (k + 2) + 3
  let q := 2 * (k + 2) + 6
  let r := 4 * (k + 2) + 7
  let t := 2 * (k + 2) + 5
  have hc := growingAnchor_coeff_le_linear_dyad k
  have hd := growingAnchor_succ_coeff_le_linear_dyad k
  have hprod := Q'.mul_le_mul_of_nonneg hc hd (dyad_nonneg p)
    (coeffW_nonneg (harmW_nonneg k) (growingAnchor k + 1))
  have hpq : p + q = r + 2 := by
    dsimp only [p, q, r]
    omega
  have hprodEq : dyad p * dyad q ≈ dyad (r + 2) := by
    unfold dyad
    rw [← hpq]
    exact Q'.eqv_symm (SU3CharFactor.pow_add_eqv HalfPow.half p q)
  have hshift : Q'.ofNat 4 * dyad (r + 2) ≈ dyad r := by
    unfold dyad
    refine Q'.eqv_trans _
      (Q'.ofNat 4 * (HalfPow.half ^ r * HalfPow.half ^ 2)) _
      (Q'.mul_eqv_congr_left _ _ _
        (SU3CharFactor.pow_add_eqv HalfPow.half r 2)) ?_
    have hconst : Q'.ofNat 4 * HalfPow.half ^ 2 ≈ (1 : Q') := by decide
    refine Q'.eqv_trans _ ((Q'.ofNat 4 * HalfPow.half ^ 2) *
      HalfPow.half ^ r) _ (by sandwich_ring) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hconst) (Q'.one_mul_eqv _)
  have h4prod := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hprod
    (by decide)
  have hedgeDyad : Q'.ofNat 4 *
      (coeffW (harmW k) (growingAnchor k) *
        coeffW (harmW k) (growingAnchor k + 1)) ≤ dyad r :=
    Q'.le_trans' _ _ _ h4prod
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hprodEq))
        (Q'.le_of_eqv hshift))
  have htr : t ≤ r := by
    dsimp only [t, r]
    omega
  obtain ⟨d, hrd⟩ := Nat.le.dest htr
  have hry : dyad r ≤ dyad t := by
    unfold dyad
    rw [← hrd]
    exact ExpNeg.pow_half_antitone t d
  have htu : dyad t ≤ harmU k * harmU k := by
    dsimp only [t]
    exact linear_dyad_le_harmU_sq k
  have hD1 : (1 : Q') ≤ coordNormSq (harmW k) (growingAnchor k) :=
    coordNormSq_ge_one (harmW_nonneg k) (growingAnchor k)
  have hu0 : (0 : Q') ≤ harmU k * harmU k :=
    Q'.mul_nonneg _ _ (harmU_nonneg k) (harmU_nonneg k)
  have huD := Q'.mul_le_mul_of_nonneg_left _ _ (harmU k * harmU k)
    hD1 hu0
  exact Q'.le_trans' _ _ _ hedgeDyad
    (Q'.le_trans' _ _ _ hry
      (Q'.le_trans' _ _ _ htu
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) huD)))

private theorem theta_residual_corr_eqv (w : Q') (N M : Nat) :
    qpow ((1 : Q') + w) 3 * integerThetaSum w N +
        -(Q'.ofNat 8 * (w * halfThetaSum w M)) ≈
      qpow w 2 *
        (qpow ((1 : Q') + w) 3 * coordNormSq w N +
          -(Q'.ofNat 8 * adjCorr w M)) := by
  let q := qpow w 2
  let C := qpow ((1 : Q') + w) 3
  let I := integerThetaSum w N
  let H := halfThetaSum w M
  let D := coordNormSq w N
  let A := adjCorr w M
  have hD : q * D ≈ I := coordNormSq_theta_eqv w N
  have hA : w * A ≈ H := adjCorr_theta_eqv w M
  have hq : q ≈ w * w := by
    change ((1 : Q') * w) * w ≈ w * w
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)
  have hwH : w * H ≈ q * A := by
    refine Q'.eqv_trans _ (w * (w * A)) _
      (Q'.mul_eqv_congr_left w _ _ (Q'.eqv_symm hA)) ?_
    refine Q'.eqv_trans _ ((w * w) * A) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hq)
  dsimp only [q, C, I, H, D, A] at hD hA hq hwH ⊢
  refine Q'.eqv_trans _
    (qpow ((1 : Q') + w) 3 * (qpow w 2 * coordNormSq w N) +
      -(Q'.ofNat 8 * (qpow w 2 * adjCorr w M))) _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hD))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hwH))) ?_
  sandwich_ring

private theorem physical_corr_cross_le_growing_plus_u {k : Nat} (hk : 1 ≤ k) :
    let w := harmW k
    let b := growingAnchor k
    let N := Ncut k
    let C := qpow ((1 : Q') + w) 3
    let u2 := harmU k * harmU k
    let Db := coordNormSq w b
    let DN := coordNormSq w N
    let Ag := adjCorr w (b + 1)
    let AN := adjCorr w N
    (C * DN + -(Q'.ofNat 8 * AN)) * Db ≤
      ((C * Db + -(Q'.ofNat 8 * Ag)) + u2 * Db) * DN := by
  dsimp only
  let w := harmW k
  let b := growingAnchor k
  let N := Ncut k
  let C := qpow ((1 : Q') + w) 3
  let u2 := harmU k * harmU k
  let Db := coordNormSq w b
  let DN := coordNormSq w N
  let Ab := adjCorr w b
  let Ag := adjCorr w (b + 1)
  let AN := adjCorr w N
  let e := coeffW w b * coeffW w (b + 1)
  have hbN : b + 1 ≤ N := by
    dsimp only [b, N]
    exact growingAnchor_succ_le_Ncut hk
  have hbL : b ≤ N - 1 := by omega
  have hN : 1 ≤ N := Nat.le_trans (by omega) hbN
  have hLN : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hraw := harmonic_halfEdge_full k (p := b) hbL
  dsimp only at hraw
  change profileD (coeffW w) (N - 1 + 1) *
      halfEdgeNum (coeffW w) b ≤
    (profileA (coeffW w) (N - 1 + 1) +
      profileA (coeffW w) (N - 1 + 1)) * profileD (coeffW w) b at hraw
  rw [hLN] at hraw
  have hAg : Ab + e ≈ Ag := by
    dsimp only [Ab, Ag, e]
    exact adjCorr_succ w b
  have hhalfEdge : halfEdgeNum (coeffW w) b ≈ Ab + Ag := by
    unfold halfEdgeNum
    change (Ab + Ab) + e ≈ Ab + Ag
    refine Q'.eqv_trans _ (Ab + (Ab + e)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    exact Q'.add_eqv_congr_left Ab _ _ hAg
  have hhalf : DN * (Ab + Ag) ≤ (AN + AN) * Db := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left DN _ _ hhalfEdge))
      (by simpa [DN, AN, Db, profileD, profileA] using hraw)
  have hadd := Q'.add_le_add_right _ _ (e * DN) hhalf
  have hsum : (Ab + Ag) + e ≈ Ag + Ag := by
    refine Q'.eqv_trans _ (Ag + (Ab + e)) _ (by sandwich_ring) ?_
    exact Q'.add_eqv_congr_left Ag _ _ hAg
  have hleft : DN * (Ab + Ag) + e * DN ≈
      Q'.ofNat 2 * (Ag * DN) := by
    refine Q'.eqv_trans _ (DN * ((Ab + Ag) + e)) _
      (by sandwich_ring) ?_
    refine Q'.eqv_trans _ (DN * (Ag + Ag)) _
      (Q'.mul_eqv_congr_left DN _ _ hsum) ?_
    have htwo : Q'.ofNat 2 ≈ (1 : Q') + (1 : Q') := by decide
    refine Q'.eqv_trans _ ((Ag + Ag) * DN) _ (by sandwich_ring) ?_
    exact Q'.eqv_symm (Q'.eqv_trans _
      (((1 : Q') + (1 : Q')) * (Ag * DN)) _
      (Q'.mul_eqv_congr_right _ _ _ htwo) (by sandwich_ring))
  have hright : (AN + AN) * Db + e * DN ≈
      Q'.ofNat 2 * (AN * Db) + e * DN := by
    have htwo : Q'.ofNat 2 ≈ (1 : Q') + (1 : Q') := by decide
    refine Q'.add_eqv_congr_right _ _ (e * DN) ?_
    exact Q'.eqv_symm (Q'.eqv_trans _
      (((1 : Q') + (1 : Q')) * (AN * Db)) _
      (Q'.mul_eqv_congr_right _ _ _ htwo) (by sandwich_ring))
  have hprime : Q'.ofNat 2 * (Ag * DN) ≤
      Q'.ofNat 2 * (AN * Db) + e * DN :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))
  have hdiff : Q'.ofNat 2 * (Ag * DN) +
      -(Q'.ofNat 2 * (AN * Db)) ≤ e * DN :=
    Q'.sub_le_of_le_add hprime
  have h4 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hdiff
    (by decide)
  have h4left : Q'.ofNat 8 * (Ag * DN + -(AN * Db)) ≈
      Q'.ofNat 4 *
        (Q'.ofNat 2 * (Ag * DN) +
          -(Q'.ofNat 2 * (AN * Db))) := by
    sandwich_ring
  have h8diff : Q'.ofNat 8 * (Ag * DN + -(AN * Db)) ≤
      Q'.ofNat 4 * (e * DN) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv h4left) h4
  have hedge := four_growing_terminal_edge_le_u_sq_diag k
  have hDN0 : (0 : Q') ≤ DN := by
    dsimp only [DN, w, N]
    exact coordNormSq_nonneg (harmW_nonneg k) (Ncut k)
  have hedgeN := Q'.mul_le_mul_of_nonneg_right _ _ DN hedge hDN0
  have hbudgetLeft : Q'.ofNat 4 * (e * DN) ≈
      (Q'.ofNat 4 * e) * DN := by
    sandwich_ring
  have hbudget : Q'.ofNat 4 * (e * DN) ≤ (u2 * Db) * DN := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hbudgetLeft) hedgeN
  have h8budget : Q'.ofNat 8 * (Ag * DN + -(AN * Db)) ≤
      (u2 * Db) * DN := Q'.le_trans' _ _ _ h8diff hbudget
  have hshift := Q'.add_le_add_left
    (-(Q'.ofNat 8 * (Ag * DN))) _ _ h8budget
  have hshiftLeft :
      -(Q'.ofNat 8 * (Ag * DN)) +
          Q'.ofNat 8 * (Ag * DN + -(AN * Db)) ≈
        -(Q'.ofNat 8 * (AN * Db)) := by
    refine Q'.eqv_trans _
      (-(Q'.ofNat 8 * (Ag * DN)) +
        (Q'.ofNat 8 * (Ag * DN) +
          -(Q'.ofNat 8 * (AN * Db)))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _
        (Q'.ofNat 8 * (Ag * DN) +
          Q'.ofNat 8 * -(AN * Db)) _
        (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)))
    · refine Q'.eqv_trans _
        ((-(Q'.ofNat 8 * (Ag * DN)) +
          Q'.ofNat 8 * (Ag * DN)) +
            -(Q'.ofNat 8 * (AN * Db))) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      exact Q'.eqv_trans _
        ((0 : Q') + -(Q'.ofNat 8 * (AN * Db))) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv _))
        (QPoly.q_zero_add_eqv _)
  have hshiftRight :
      -(Q'.ofNat 8 * (Ag * DN)) + (u2 * Db) * DN ≈
        (u2 * Db) * DN + -(Q'.ofNat 8 * (Ag * DN)) := by
    exact Q'.add_comm_eqv _ _
  have hnegative : -(Q'.ofNat 8 * (AN * Db)) ≤
      (u2 * Db) * DN + -(Q'.ofNat 8 * (Ag * DN)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hshiftLeft)
      (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hshiftRight))
  have hcommon := Q'.add_le_add_left (C * (DN * Db)) _ _ hnegative
  have htargetLeft :
      (C * DN + -(Q'.ofNat 8 * AN)) * Db ≈
        C * (DN * Db) + -(Q'.ofNat 8 * (AN * Db)) := by
    sandwich_ring
  have htargetRight :
      ((C * Db + -(Q'.ofNat 8 * Ag)) + u2 * Db) * DN ≈
        C * (DN * Db) +
          ((u2 * Db) * DN + -(Q'.ofNat 8 * (Ag * DN))) := by
    sandwich_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargetLeft)
    (Q'.le_trans' _ _ _ hcommon (Q'.ge_of_eqv htargetRight))

/-- The physical normalized residual is at most the growing-head normalized
residual plus one exact `u²` unit.  This is the upper counterpart to the
lossless lower transfer proved below. -/
theorem physical_residual_cross_le_growing_plus_u {k : Nat} (hk : 1 ≤ k) :
    physicalPascalResidual k *
        integerThetaSum (harmW k) (growingAnchor k) ≤
      (growingPascalResidual k +
          (harmU k * harmU k) *
            integerThetaSum (harmW k) (growingAnchor k)) *
        physicalIntegerTheta k := by
  let w := harmW k
  let b := growingAnchor k
  let N := Ncut k
  let q := qpow w 2
  let C := qpow ((1 : Q') + w) 3
  let u2 := harmU k * harmU k
  let Db := coordNormSq w b
  let DN := coordNormSq w N
  let Ag := adjCorr w (b + 1)
  let AN := adjCorr w N
  let Xg := C * Db + -(Q'.ofNat 8 * Ag)
  let Xp := C * DN + -(Q'.ofNat 8 * AN)
  let Ig := integerThetaSum w b
  let Ip := integerThetaSum w N
  let Rg := growingPascalResidual k
  let Rp := physicalPascalResidual k
  have hcorr := physical_corr_cross_le_growing_plus_u hk
  change Xp * Db ≤ (Xg + u2 * Db) * DN at hcorr
  have hq0 : (0 : Q') ≤ q * q :=
    Q'.mul_nonneg _ _ (qpow_nonneg w (harmW_nonneg k) 2)
      (qpow_nonneg w (harmW_nonneg k) 2)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (q * q) hcorr hq0
  have hRp : Rp ≈ q * Xp := by
    dsimp only [Rp, q, Xp, C, DN, AN, w, N]
    unfold physicalPascalResidual cumulativeScaledThetaResidual
    exact theta_residual_corr_eqv (harmW k) (Ncut k) (Ncut k)
  have hRg : Rg ≈ q * Xg := by
    dsimp only [Rg, q, Xg, C, Db, Ag, w, b]
    unfold growingPascalResidual growingHeadScaledThetaResidual
    exact theta_residual_corr_eqv (harmW k) (growingAnchor k)
      (growingAnchor k + 1)
  have hIg : q * Db ≈ Ig := by
    dsimp only [q, Db, Ig, w, b]
    exact coordNormSq_theta_eqv (harmW k) (growingAnchor k)
  have hIp : q * DN ≈ Ip := by
    dsimp only [q, DN, Ip, w, N]
    exact coordNormSq_theta_eqv (harmW k) (Ncut k)
  have hleft : (q * q) * (Xp * Db) ≈ Rp * Ig := by
    refine Q'.eqv_trans _ ((q * Xp) * (q * Db)) _
      (by sandwich_ring) ?_
    exact Q'.eqv_trans _ (Rp * (q * Db)) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hRp))
      (Q'.mul_eqv_congr_left Rp _ _ hIg)
  have hright : (q * q) * ((Xg + u2 * Db) * DN) ≈
      (Rg + u2 * Ig) * Ip := by
    refine Q'.eqv_trans _
      ((q * Xg + u2 * (q * Db)) * (q * DN)) _
      (by sandwich_ring) ?_
    have hsum : q * Xg + u2 * (q * Db) ≈ Rg + u2 * Ig :=
      Q'.add_eqv_congr'
        (Q'.eqv_symm hRg)
        (Q'.mul_eqv_congr_left u2 _ _ hIg)
    exact Q'.eqv_trans _ ((Rg + u2 * Ig) * (q * DN)) _
      (Q'.mul_eqv_congr_right _ _ _ hsum)
      (Q'.mul_eqv_congr_left (Rg + u2 * Ig) _ _ hIp)
  dsimp only [Rp, Rg, Ig, Ip, u2, w, b, N] at hleft hright ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright))

/-- The physical matched cutoff quotient is bounded above by the mismatched
growing-head quotient.  This is the missing direction not supplied by the
usual cutoff-quotient monotonicity.  The proof propagates the actual head
ratio with PF2 and the exact `1/8` scalar cross. -/
theorem physical_adj_diag_cross_le_growing_head {k : Nat} (hk : 1 ≤ k) :
    adjCorr (harmW k) (Ncut k) *
        coordNormSq (harmW k) (growingAnchor k) ≤
      adjCorr (harmW k) (growingAnchor k + 1) *
        coordNormSq (harmW k) (Ncut k) := by
  let w := harmW k
  let b := growingAnchor k
  let N := Ncut k
  let D := coordNormSq w b
  let A := adjCorr w (b + 1)
  let R := Q'.divPos A D (coordNormSq_pos (harmW_nonneg k) b)
  have hD : (0 : Q') < D := coordNormSq_pos (harmW_nonneg k) b
  have hR0 : (0 : Q') ≤ R := by
    dsimp only [R]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _ (adjCorr_nonneg (harmW_nonneg k) (b + 1))
      (Q'.le_of_lt (Q'.recipPos_pos D hD))
  have hhead : adjCorr w (b + 1) ≤ R * coordNormSq w b := by
    change A ≤ R * D
    exact Q'.ge_of_eqv (Q'.divPos_mul_eqv A D hD)
  have hRlower : Q'.mkPos 1 8 (by decide) ≤ R := by
    apply Q'.le_divPos_of_mul_le A D hD
    dsimp only [A, D, w, b]
    exact eighth_mul_growing_diag_le_growing_adj hk
  have hcross : Q'.ofNat (b + 2) * qpow w (2 * b + 3) ≤
      R * Q'.ofNat (b + 1) := by
    have hs := growing_anchor_scalar_cross_eighth k
    have hr := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat (b + 1))
      hRlower (HeatKernelRGStep.zero_le_ofNat _)
    exact Q'.le_trans' _ _ _ hs hr
  have hbN : b + 1 ≤ N := by
    dsimp only [b, N]
    exact growingAnchor_succ_le_Ncut hk
  have hprop := variable_anchor_all_later_cutoffs b (N - (b + 1))
    (harmW_nonneg k) (harmW_le_one k) (harmW_pos k) hR0 hhead hcross
  have hidx : b + 1 + (N - (b + 1)) = N := Nat.add_sub_of_le hbN
  rw [hidx] at hprop
  have hDb0 : (0 : Q') ≤ D := Q'.le_of_lt hD
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ D hprop hDb0
  have hright : (R * coordNormSq w N) * D ≈ A * coordNormSq w N := by
    refine Q'.eqv_trans _ ((R * D) * coordNormSq w N) _
      (by sandwich_ring) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.divPos_mul_eqv A D hD)
  dsimp only [w, b, N, D, A] at hm hright ⊢
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright)

/-- Theta-sector form of the physical-to-growing quotient comparison. -/
theorem physical_theta_quotient_cross_le_growing_head {k : Nat} (hk : 1 ≤ k) :
    halfThetaSum (harmW k) (Ncut k) *
        integerThetaSum (harmW k) (growingAnchor k) ≤
      halfThetaSum (harmW k) (growingAnchor k + 1) *
        integerThetaSum (harmW k) (Ncut k) := by
  let w := harmW k
  let b := growingAnchor k
  let N := Ncut k
  let q := qpow w 2
  have hcross := physical_adj_diag_cross_le_growing_head hk
  have hS0 : (0 : Q') ≤ w * q :=
    Q'.mul_nonneg _ _ (harmW_nonneg k) (qpow_nonneg w (harmW_nonneg k) 2)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (w * q) hcross hS0
  have scaled_cross_eqv (A D : Q') :
      (w * q) * (A * D) ≈ (w * A) * (q * D) := by
    sandwich_ring
  have hleft : (w * q) *
        (adjCorr w N * coordNormSq w b) ≈
      halfThetaSum w N * integerThetaSum w b := by
    refine Q'.eqv_trans _ ((w * adjCorr w N) *
      (q * coordNormSq w b)) _ (scaled_cross_eqv _ _) ?_
    refine Q'.eqv_trans _
      (halfThetaSum w N * (q * coordNormSq w b)) _
      (Q'.mul_eqv_congr_right _ _ _ (adjCorr_theta_eqv w N)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (coordNormSq_theta_eqv w b)
  have hright : (w * q) *
        (adjCorr w (b + 1) * coordNormSq w N) ≈
      halfThetaSum w (b + 1) * integerThetaSum w N := by
    refine Q'.eqv_trans _ ((w * adjCorr w (b + 1)) *
      (q * coordNormSq w N)) _ (scaled_cross_eqv _ _) ?_
    refine Q'.eqv_trans _
      (halfThetaSum w (b + 1) * (q * coordNormSq w N)) _
      (Q'.mul_eqv_congr_right _ _ _ (adjCorr_theta_eqv w (b + 1))) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (coordNormSq_theta_eqv w N)
  dsimp only [w, b, N, q] at hm hleft hright ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright))

/-- The normalized physical Pascal residual is at least the normalized
growing-head residual.  It is kept division-free for direct use by lower
residual envelopes. -/
theorem growing_residual_cross_le_physical {k : Nat} (hk : 1 ≤ k) :
    growingPascalResidual k * physicalIntegerTheta k ≤
      physicalPascalResidual k *
        integerThetaSum (harmW k) (growingAnchor k) := by
  let w := harmW k
  let Ig := integerThetaSum w (growingAnchor k)
  let Ip := integerThetaSum w (Ncut k)
  let Hg := halfThetaSum w (growingAnchor k + 1)
  let Hp := halfThetaSum w (Ncut k)
  let C := qpow ((1 : Q') + w) 3
  have htheta := physical_theta_quotient_cross_le_growing_head hk
  have hw0 : (0 : Q') ≤ w := harmW_nonneg k
  have hwtheta := Q'.mul_le_mul_of_nonneg_left _ _ w htheta hw0
  have h8theta := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8)
    hwtheta (by decide)
  have hneg := Q'.neg_le_neg h8theta
  have hadd := Q'.add_le_add_left (C * (Ig * Ip)) _ _ hneg
  have hL : growingPascalResidual k * physicalIntegerTheta k ≈
      C * (Ig * Ip) + -(Q'.ofNat 8 * (w * (Hg * Ip))) := by
    unfold growingPascalResidual growingHeadScaledThetaResidual
      physicalIntegerTheta
    dsimp only [C, Ig, Ip, Hg, w]
    sandwich_ring
  have hR : physicalPascalResidual k * Ig ≈
      C * (Ig * Ip) + -(Q'.ofNat 8 * (w * (Hp * Ig))) := by
    unfold physicalPascalResidual cumulativeScaledThetaResidual
    dsimp only [C, Ig, Ip, Hp, w]
    sandwich_ring
  dsimp only [w, Ig, Ip, Hg, Hp] at htheta hwtheta h8theta hneg hadd hL hR ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hR))

theorem growingIntegerTheta_pos (k : Nat) :
    (0 : Q') < integerThetaSum (harmW k) (growingAnchor k) := by
  have hp : (0 : Q') < qpow (harmW k) 2 *
      coordNormSq (harmW k) (growingAnchor k) :=
    Q'.mul_pos (qpow_pos (harmW_pos k) 2)
      (coordNormSq_pos (harmW_nonneg k) (growingAnchor k))
  exact q_lt_of_lt_of_le hp
    (Q'.le_of_eqv
      (coordNormSq_theta_eqv (harmW k) (growingAnchor k)))

/-- The seven-unit growing-head certificate and the exact one-unit transport
cost give an eight-unit physical-cutoff certificate. -/
theorem physicalResidualUpperEight_of_growing {k : Nat} (hk : 1 ≤ k) :
    PhysicalResidualUpperEight k := by
  let B7 := Q'.ofNat 7 * (harmU k * harmU k)
  let B8 := Q'.ofNat 8 * (harmU k * harmU k)
  let U := (harmU k * harmU k)
  let Ig := integerThetaSum (harmW k) (growingAnchor k)
  let Ip := physicalIntegerTheta k
  let Rg := growingPascalResidual k
  let Rp := physicalPascalResidual k
  have hg : Rg ≤ B7 * Ig := by
    simpa [B7, Ig, Rg] using growingResidualUpperSeven k
  have hadd := Q'.add_le_add_right _ _ (U * Ig) hg
  have h78 : Q'.ofNat 7 + (1 : Q') ≈ Q'.ofNat 8 := by decide
  have hB : B7 + U ≈ B8 := by
    dsimp only [B7, B8]
    refine Q'.eqv_trans _
      (Q'.ofNat 7 * U + (1 : Q') * U) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv U))) ?_
    refine Q'.eqv_trans _ ((Q'.ofNat 7 + (1 : Q')) * U) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ U h78
  have hBIg : B7 * Ig + U * Ig ≈ B8 * Ig := by
    refine Q'.eqv_trans _ ((B7 + U) * Ig) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ Ig hB
  have hsum : Rg + U * Ig ≤ B8 * Ig :=
    Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hBIg)
  have hIp0 : (0 : Q') ≤ Ip := by
    dsimp only [Ip]
    exact physicalIntegerTheta_nonnegative k
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ Ip hsum hIp0
  have hcross : Rp * Ig ≤ (Rg + U * Ig) * Ip := by
    dsimp only [Rp, Rg, U, Ig, Ip]
    exact physical_residual_cross_le_growing_plus_u hk
  have hchain : Rp * Ig ≤ (B8 * Ig) * Ip :=
    Q'.le_trans' _ _ _ hcross hscale
  have hcancel : Ig * Rp ≤ Ig * (B8 * Ip) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv (by sandwich_ring)))
  have hout : Rp ≤ B8 * Ip :=
    Q'.le_of_mul_le_mul_left hcancel (by
      dsimp only [Ig]
      exact growingIntegerTheta_pos k)
  simpa [PhysicalResidualUpperEight, Rp, B8, Ip] using hout

/-- The physical eight-unit upper residual envelope holds at every scale.
Scale zero is a closed exact rational computation; every positive scale uses
the symbolic growing-head transport. -/
theorem physicalResidualUpperEight_all (k : Nat) :
    PhysicalResidualUpperEight k := by
  by_cases hk : k = 0
  · subst k
    unfold PhysicalResidualUpperEight physicalPascalResidual
      physicalIntegerTheta cumulativeScaledThetaResidual integerThetaSum
      halfThetaSum integerThetaTerm halfThetaTerm Ncut harmW harmU oneSub
      unit qpow finSum
    decide
  · exact physicalResidualUpperEight_of_growing (by omega)

/-- A five-unit lower envelope proved at the growing head transfers
losslessly to the actual quadratic cutoff. -/
theorem physicalResidualLowerFive_of_growing {k : Nat} (hk : 1 ≤ k)
    (hgrowing : GrowingResidualLowerFive k) :
    PhysicalResidualLowerFive k := by
  let B := Q'.ofNat 5 * (harmU k * harmU k)
  let Ig := integerThetaSum (harmW k) (growingAnchor k)
  let Ip := physicalIntegerTheta k
  let Rg := growingPascalResidual k
  let Rp := physicalPascalResidual k
  have hg : B * Ig ≤ Rg := by
    simpa [GrowingResidualLowerFive, B, Ig, Rg] using hgrowing
  have hIp0 : (0 : Q') ≤ Ip := by
    dsimp only [Ip]
    exact physicalIntegerTheta_nonnegative k
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ Ip hg hIp0
  have hcross : Rg * Ip ≤ Rp * Ig := by
    dsimp only [Rg, Ip, Rp, Ig]
    exact growing_residual_cross_le_physical hk
  have hchain : (B * Ig) * Ip ≤ Rp * Ig :=
    Q'.le_trans' _ _ _ hscale hcross
  have hcancel : Ig * (B * Ip) ≤ Ig * Rp :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by sandwich_ring))
      (Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  have hout : B * Ip ≤ Rp :=
    Q'.le_of_mul_le_mul_left hcancel (by
      dsimp only [Ig]
      exact growingIntegerTheta_pos k)
  simpa [PhysicalResidualLowerFive, B, Ip, Rp] using hout

/-- The lossless lower transfer is constant-independent; in particular the
six-unit growing envelope transfers to the physical cutoff. -/
theorem physicalResidualLowerSix_of_growing {k : Nat} (hk : 1 ≤ k)
    (hgrowing : GrowingResidualLowerSix k) :
    PhysicalResidualLowerSix k := by
  let B := Q'.ofNat 6 * (harmU k * harmU k)
  let Ig := integerThetaSum (harmW k) (growingAnchor k)
  let Ip := physicalIntegerTheta k
  let Rg := growingPascalResidual k
  let Rp := physicalPascalResidual k
  have hg : B * Ig ≤ Rg := by
    simpa [GrowingResidualLowerSix, B, Ig, Rg] using hgrowing
  have hIp0 : (0 : Q') ≤ Ip := by
    dsimp only [Ip]
    exact physicalIntegerTheta_nonnegative k
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ Ip hg hIp0
  have hcross : Rg * Ip ≤ Rp * Ig := by
    dsimp only [Rg, Ip, Rp, Ig]
    exact growing_residual_cross_le_physical hk
  have hchain : (B * Ig) * Ip ≤ Rp * Ig :=
    Q'.le_trans' _ _ _ hscale hcross
  have hcancel : Ig * (B * Ip) ≤ Ig * Rp :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by sandwich_ring))
      (Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  have hout : B * Ip ≤ Rp :=
    Q'.le_of_mul_le_mul_left hcancel (by
      dsimp only [Ig]
      exact growingIntegerTheta_pos k)
  simpa [PhysicalResidualLowerSix, B, Ip, Rp] using hout

/-- Exact scalar overlap for the transported `[8,6]` sandwich.  Its sharp
integer threshold is `k = 9`. -/
theorem eight_sq_le_three_sq_add_six_succ_sq {k : Nat} (hk : 9 ≤ k) :
    Q'.ofNat 8 * (harmU k * harmU k) ≤
      Q'.ofNat 3 * (harmU k * harmU k) +
        Q'.ofNat 6 * (harmU (k + 1) * harmU (k + 1)) := by
  let t := k - 9
  have hkt : k = t + 9 := by
    dsimp only [t]
    omega
  have hnat : 5 * ((k + 3) * (k + 3)) ≤
      6 * ((k + 2) * (k + 2)) := by
    rw [hkt]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have h56 : Q'.ofNat 5 * (harmU k * harmU k) ≤
      Q'.ofNat 6 * (harmU (k + 1) * harmU (k + 1)) := by
    unfold harmU unit
    show _ * (_ : Int) ≤ _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
    push_cast
    exact_mod_cast hnat
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 3 * (harmU k * harmU k)) _ _ h56
  have h35 : Q'.ofNat 3 + Q'.ofNat 5 ≈ Q'.ofNat 8 := by decide
  have hsplit : Q'.ofNat 8 * (harmU k * harmU k) ≈
      Q'.ofNat 3 * (harmU k * harmU k) +
        Q'.ofNat 5 * (harmU k * harmU k) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 3 + Q'.ofNat 5) * (harmU k * harmU k)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h35)
    · exact Q'.add_mul_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hadd

/-- The `[8,6]` scalar overlap genuinely starts at nine. -/
theorem eight_six_scalar_overlap_fails_k8 :
    ¬ (Q'.ofNat 8 * (harmU 8 * harmU 8) ≤
      Q'.ofNat 3 * (harmU 8 * harmU 8) +
        Q'.ofNat 6 * (harmU 9 * harmU 9)) := by decide

/-- Exact scalar overlap of the seven-unit upper envelope and five-unit
lower envelope.  The threshold `k = 7` is sharp for these two constants. -/
theorem seven_sq_le_three_sq_add_five_succ_sq {k : Nat} (hk : 7 ≤ k) :
    Q'.ofNat 7 * (harmU k * harmU k) ≤
      Q'.ofNat 3 * (harmU k * harmU k) +
        Q'.ofNat 5 * (harmU (k + 1) * harmU (k + 1)) := by
  let t := k - 7
  have hkt : k = t + 7 := by
    dsimp only [t]
    omega
  have hnat : 4 * ((k + 3) * (k + 3)) ≤
      5 * ((k + 2) * (k + 2)) := by
    rw [hkt]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have h45 : Q'.ofNat 4 * (harmU k * harmU k) ≤
      Q'.ofNat 5 * (harmU (k + 1) * harmU (k + 1)) := by
    unfold harmU unit
    show _ * (_ : Int) ≤ _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
    push_cast
    exact_mod_cast hnat
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 3 * (harmU k * harmU k)) _ _ h45
  have h34 : Q'.ofNat 3 + Q'.ofNat 4 ≈ Q'.ofNat 7 := by decide
  have hsplit : Q'.ofNat 7 * (harmU k * harmU k) ≈
      Q'.ofNat 3 * (harmU k * harmU k) +
        Q'.ofNat 4 * (harmU k * harmU k) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 3 + Q'.ofNat 4) * (harmU k * harmU k)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h34)
    · exact Q'.add_mul_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hadd

/-- The scalar threshold cannot be lowered to `k = 6` with constants seven,
five, and three. -/
theorem seven_five_scalar_overlap_fails_k6 :
    ¬ (Q'.ofNat 7 * (harmU 6 * harmU 6) ≤
      Q'.ofNat 3 * (harmU 6 * harmU 6) +
        Q'.ofNat 5 * (harmU 7 * harmU 7)) := by decide

/-- The two independent one-scale sandwich estimates imply the exact
cross-scale residual, with no division and no positivity cancellation. -/
theorem physicalPascalCrossResidual_of_five_seven
    {k : Nat} (hk : 7 ≤ k)
    (hupper : PhysicalResidualUpperSeven k)
    (hlower : PhysicalResidualLowerFive (k + 1)) :
    PhysicalPascalCrossResidual k := by
  let I0 := physicalIntegerTheta k
  let I1 := physicalIntegerTheta (k + 1)
  let R0 := physicalPascalResidual k
  let R1 := physicalPascalResidual (k + 1)
  let U0 := harmU k * harmU k
  let U1 := harmU (k + 1) * harmU (k + 1)
  let P := I0 * I1
  let A := Q'.ofNat 7 * U0
  let B := Q'.ofNat 3 * U0
  let C := Q'.ofNat 5 * U1
  have hI0 : (0 : Q') ≤ I0 := by
    dsimp only [I0]
    exact physicalIntegerTheta_nonnegative k
  have hI1 : (0 : Q') ≤ I1 := by
    dsimp only [I1]
    exact physicalIntegerTheta_nonnegative (k + 1)
  have hP : (0 : Q') ≤ P := by
    dsimp only [P]
    exact Q'.mul_nonneg _ _ hI0 hI1
  have hA : R0 ≤ A * I0 := by
    simpa [PhysicalResidualUpperSeven, R0, A, U0, I0] using hupper
  have hC : C * I1 ≤ R1 := by
    simpa [PhysicalResidualLowerFive, R1, C, U1, I1] using hlower
  have hcoef : A ≤ B + C := by
    simpa [A, B, C, U0, U1] using
      (seven_sq_le_three_sq_add_five_succ_sq hk)
  have hAI1 := Q'.mul_le_mul_of_nonneg_right _ _ I1 hA hI1
  have hAP : R0 * I1 ≤ A * P := by
    exact Q'.le_trans' _ _ _ hAI1 (Q'.le_of_eqv (by
      dsimp only [P]
      sandwich_ring))
  have hcoefP := Q'.mul_le_mul_of_nonneg_right _ _ P hcoef hP
  have hBC : A * P ≤ B * P + C * P := by
    exact Q'.le_trans' _ _ _ hcoefP (Q'.le_of_eqv (Q'.add_mul_eqv _ _ _))
  have hCI0 := Q'.mul_le_mul_of_nonneg_right _ _ I0 hC hI0
  have hCP : C * P ≤ R1 * I0 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      dsimp only [P]
      sandwich_ring)) hCI0
  have hadd := Q'.add_le_add_left (B * P) _ _ hCP
  have hout : R0 * I1 ≤ B * P + R1 * I0 :=
    Q'.le_trans' _ _ _ hAP
      (Q'.le_trans' _ _ _ hBC hadd)
  unfold PhysicalPascalCrossResidual
  dsimp only [R0, R1, I0, I1, B, P, U0] at hout ⊢
  exact Q'.le_trans' _ _ _ hout (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

/-- The transported physical `[8,6]` sandwich implies the sharp cross-scale
residual from scale nine onward. -/
theorem physicalPascalCrossResidual_of_six_eight
    {k : Nat} (hk : 9 ≤ k)
    (hupper : PhysicalResidualUpperEight k)
    (hlower : PhysicalResidualLowerSix (k + 1)) :
    PhysicalPascalCrossResidual k := by
  let I0 := physicalIntegerTheta k
  let I1 := physicalIntegerTheta (k + 1)
  let R0 := physicalPascalResidual k
  let R1 := physicalPascalResidual (k + 1)
  let U0 := harmU k * harmU k
  let U1 := harmU (k + 1) * harmU (k + 1)
  let P := I0 * I1
  let A := Q'.ofNat 8 * U0
  let B := Q'.ofNat 3 * U0
  let C := Q'.ofNat 6 * U1
  have hI0 : (0 : Q') ≤ I0 := by
    dsimp only [I0]
    exact physicalIntegerTheta_nonnegative k
  have hI1 : (0 : Q') ≤ I1 := by
    dsimp only [I1]
    exact physicalIntegerTheta_nonnegative (k + 1)
  have hP : (0 : Q') ≤ P := by
    dsimp only [P]
    exact Q'.mul_nonneg _ _ hI0 hI1
  have hA : R0 ≤ A * I0 := by
    simpa [PhysicalResidualUpperEight, R0, A, U0, I0] using hupper
  have hC : C * I1 ≤ R1 := by
    simpa [PhysicalResidualLowerSix, R1, C, U1, I1] using hlower
  have hcoef : A ≤ B + C := by
    simpa [A, B, C, U0, U1] using
      (eight_sq_le_three_sq_add_six_succ_sq hk)
  have hAI1 := Q'.mul_le_mul_of_nonneg_right _ _ I1 hA hI1
  have hAP : R0 * I1 ≤ A * P := by
    exact Q'.le_trans' _ _ _ hAI1 (Q'.le_of_eqv (by
      dsimp only [P]
      sandwich_ring))
  have hcoefP := Q'.mul_le_mul_of_nonneg_right _ _ P hcoef hP
  have hBC : A * P ≤ B * P + C * P := by
    exact Q'.le_trans' _ _ _ hcoefP
      (Q'.le_of_eqv (Q'.add_mul_eqv _ _ _))
  have hCI0 := Q'.mul_le_mul_of_nonneg_right _ _ I0 hC hI0
  have hCP : C * P ≤ R1 * I0 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      dsimp only [P]
      sandwich_ring)) hCI0
  have hadd := Q'.add_le_add_left (B * P) _ _ hCP
  have hout : R0 * I1 ≤ B * P + R1 * I0 :=
    Q'.le_trans' _ _ _ hAP (Q'.le_trans' _ _ _ hBC hadd)
  unfold PhysicalPascalCrossResidual
  dsimp only [R0, R1, I0, I1, B, P, U0] at hout ⊢
  exact Q'.le_trans' _ _ _ hout (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

/-- Exact finite prefix.  These are kernel decisions on closed rational
character sums, not numerical measurements. -/
theorem physicalPascalCrossResidual_below_seven {k : Nat} (hk : k < 7) :
    PhysicalPascalCrossResidual k := by
  have hcases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold PhysicalPascalCrossResidual physicalPascalResidual
      physicalIntegerTheta cumulativeScaledThetaResidual integerThetaSum
      halfThetaSum integerThetaTerm halfThetaTerm Ncut harmW harmU oneSub
      unit qpow finSum <;> decide

/-- Exact finite prefix required by the `[8,6]` tail sandwich. -/
theorem physicalPascalCrossResidual_below_nine {k : Nat} (hk : k < 9) :
    PhysicalPascalCrossResidual k := by
  by_cases h7 : k < 7
  · exact physicalPascalCrossResidual_below_seven h7
  · have hcases : k = 7 ∨ k = 8 := by omega
    rcases hcases with rfl | rfl <;>
      unfold PhysicalPascalCrossResidual physicalPascalResidual
        physicalIntegerTheta cumulativeScaledThetaResidual integerThetaSum
        halfThetaSum integerThetaTerm halfThetaTerm Ncut harmW harmU oneSub
        unit qpow finSum <;> decide

/-- The all-scale sharp residual is reduced to one single-weight symbolic
tail statement: the six-unit growing-head lower envelope from scale ten.
The physical upper half and the first nine scales are unconditional. -/
theorem physicalPascalCrossResidual_all_of_growing_lower_six
    (hlower : ∀ k, 10 ≤ k → GrowingResidualLowerSix k) :
    ∀ k, PhysicalPascalCrossResidual k := by
  intro k
  by_cases hk : 9 ≤ k
  · apply physicalPascalCrossResidual_of_six_eight hk
      (physicalResidualUpperEight_all k)
    exact physicalResidualLowerSix_of_growing (by omega)
      (hlower (k + 1) (by omega))
  · exact physicalPascalCrossResidual_below_nine (by omega)

/-- Full exact consumer for a symbolic tail sandwich.  The open content is
now two separate one-weight inequalities, rather than one two-weight
determinant inequality. -/
theorem physicalPascalCrossResidual_all_of_tail_sandwich
    (hupper : ∀ k, 7 ≤ k → PhysicalResidualUpperSeven k)
    (hlower : ∀ k, 8 ≤ k → PhysicalResidualLowerFive k) :
    ∀ k, PhysicalPascalCrossResidual k := by
  intro k
  by_cases hk : 7 ≤ k
  · exact physicalPascalCrossResidual_of_five_seven hk
      (hupper k hk) (hlower (k + 1) (by omega))
  · exact physicalPascalCrossResidual_below_seven (by omega)

#print axioms growingLowerSixGap_eqv_cubicMargin
#print axioms growingResidualLowerSix_of_cubicMargin
#print axioms growingResidualUpperSeven
#print axioms eighth_mul_growing_diag_le_growing_adj
#print axioms growing_anchor_scalar_cross_eighth
#print axioms four_growing_terminal_edge_le_u_sq_diag
#print axioms physical_residual_cross_le_growing_plus_u
#print axioms physical_adj_diag_cross_le_growing_head
#print axioms physical_theta_quotient_cross_le_growing_head
#print axioms growing_residual_cross_le_physical
#print axioms growingIntegerTheta_pos
#print axioms physicalResidualUpperEight_of_growing
#print axioms physicalResidualUpperEight_all
#print axioms physicalResidualLowerFive_of_growing
#print axioms physicalResidualLowerSix_of_growing
#print axioms eight_sq_le_three_sq_add_six_succ_sq
#print axioms eight_six_scalar_overlap_fails_k8
#print axioms seven_sq_le_three_sq_add_five_succ_sq
#print axioms seven_five_scalar_overlap_fails_k6
#print axioms physicalPascalCrossResidual_of_five_seven
#print axioms physicalPascalCrossResidual_of_six_eight
#print axioms physicalPascalCrossResidual_below_seven
#print axioms physicalPascalCrossResidual_below_nine
#print axioms physicalPascalCrossResidual_all_of_growing_lower_six
#print axioms physicalPascalCrossResidual_all_of_tail_sandwich

end YMGap.Continuum.HarmonicMassCrossResidualSandwich
