/-
Track 11.7-fusion / R3i -- Pascal normal form for the block theta deficit.

# Result

For the physical block schedule, write

    I_k = integerThetaSum w_k N_k,
    T_k = I_k - w_k H_k,
    R_k = (1+w_k)^3 I_k - 8 w_k H_k,
    M_k = 8 - (1+w_k)^3.

Then `8 T_k = M_k I_k + R_k` exactly.  Consequently the normalized
half-contraction is compiled from the strictly smaller residual recursion

    2 I_k R_(k+1)
      <= (M_k - 2 M_(k+1)) I_k I_(k+1) + R_k I_(k+1).

This separates the explicit quarter-schedule scalar reserve from the genuine
cross-cutoff theta residual.  It is a proof about the algebra of the finite
computation; no fusion table or large canonical evaluation is performed.

# Constructivity

Finite theta sums and constant-size reflected polynomial normalization.  No
`Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaDeficit
import YMGap.Continuum.P2BlockCompatibleHeatPower
import YMGap.Continuum.HarmonicThetaCumulativeResidual

namespace YMGap.Continuum.P2BlockCompatibleThetaPascal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleHeatPower
open YMGap.Continuum.P2BlockCompatibleThetaCross
open YMGap.Continuum.P2BlockCompatibleThetaDeficit
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem pascal_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "pascal_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, pascal_neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem le_sub_of_add_le_local {a b c : Q'} (h : a + b <= c) :
    a <= c + -b := by
  have hs := Q'.add_le_add_right (a + b) c (-b) h
  have hleft : (a + b) + -b ≈ a := by
    refine Q'.eqv_trans _ (a + (b + -b)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ (a + 0) _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv b)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hs

private theorem rg_qpow_three_eqv (x : Q') :
    qpow x 3 ≈ x * x * x := by
  change (((1 : Q') * x) * x) * x ≈ x * x * x
  exact Q'.mul_eqv_congr_right _ _ x
    (Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x))

private def marginProfileCubeL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let x := .add (.const 1) (.add (.const 1) (.neg u))
  .add (.const 8) (.neg (.mul (.mul x x) x))

private def marginProfileCubeR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  .mul u
    (.add (.add (.const 12) (.neg (.mul (.const 6) u)))
      (.mul u u))

private theorem marginProfileCube_normal :
    RingNormaliser.normalize marginProfileCubeL =
      RingNormaliser.normalize marginProfileCubeR := by decide

private theorem margin_profile_cube_algebra (u : Q') :
    Q'.ofNat 8 +
        -((((1 : Q') + ((1 : Q') + -u)) *
          ((1 : Q') + ((1 : Q') + -u))) *
          ((1 : Q') + ((1 : Q') + -u))) ≈
      u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u * u) := by
  simpa [marginProfileCubeL, marginProfileCubeR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      marginProfileCubeL marginProfileCubeR marginProfileCube_normal
      (fun _ => u))

private def marginLowerSplitL : RingNormaliser.PolyExpr :=
  marginProfileCubeR

private def marginLowerSplitR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  .add (.mul (.const 11) u)
    (.mul u
      (.add (.add (.const 1) (.neg (.mul (.const 6) u)))
        (.mul u u)))

private theorem marginLowerSplit_normal :
    RingNormaliser.normalize marginLowerSplitL =
      RingNormaliser.normalize marginLowerSplitR := by decide

private theorem margin_lower_split (u : Q') :
    u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u * u) ≈
      Q'.ofNat 11 * u +
        u * (((1 : Q') + -(Q'.ofNat 6 * u)) + u * u) := by
  simpa [marginLowerSplitL, marginLowerSplitR, marginProfileCubeR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      marginLowerSplitL marginLowerSplitR marginLowerSplit_normal
      (fun _ => u))

private def marginExpandedL : RingNormaliser.PolyExpr :=
  marginProfileCubeR

private def marginExpandedR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  .add
    (.add (.mul (.const 12) u)
      (.neg (.mul (.const 6) (.mul u u))))
    (.mul u (.mul u u))

private theorem marginExpanded_normal :
    RingNormaliser.normalize marginExpandedL =
      RingNormaliser.normalize marginExpandedR := by decide

private theorem margin_expanded (u : Q') :
    u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u * u) ≈
      (Q'.ofNat 12 * u + -(Q'.ofNat 6 * (u * u))) +
        u * (u * u) := by
  simpa [marginExpandedL, marginExpandedR, marginProfileCubeR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      marginExpandedL marginExpandedR marginExpanded_normal
      (fun _ => u))

private def marginUpperCancelL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  .add
    (.add (.mul (.const 12) u)
      (.neg (.mul (.const 6) (.mul u u))))
    (.mul (.const 6) (.mul u u))

private def marginUpperCancelR : RingNormaliser.PolyExpr :=
  .mul (.const 12) (.var 0)

private theorem marginUpperCancel_normal :
    RingNormaliser.normalize marginUpperCancelL =
      RingNormaliser.normalize marginUpperCancelR := by decide

private theorem margin_upper_cancel (u : Q') :
    (Q'.ofNat 12 * u + -(Q'.ofNat 6 * (u * u))) +
        Q'.ofNat 6 * (u * u) ≈ Q'.ofNat 12 * u := by
  simpa [marginUpperCancelL, marginUpperCancelR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      marginUpperCancelL marginUpperCancelR marginUpperCancel_normal
      (fun _ => u))

private def fiveSixL : RingNormaliser.PolyExpr :=
  .add (.mul (.const 5) (.var 0)) (.mul (.const 6) (.var 0))

private def fiveSixR : RingNormaliser.PolyExpr :=
  .mul (.const 11) (.var 0)

private theorem fiveSix_normal :
    RingNormaliser.normalize fiveSixL =
      RingNormaliser.normalize fiveSixR := by decide

private theorem five_add_six_mul_eqv_eleven (u : Q') :
    Q'.ofNat 5 * u + Q'.ofNat 6 * u ≈ Q'.ofNat 11 * u := by
  simpa [fiveSixL, fiveSixR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fiveSixL fiveSixR fiveSix_normal (fun _ => u))

private def fullResidualL : RingNormaliser.PolyExpr :=
  let M0 := RingNormaliser.PolyExpr.var 0
  let M1 := RingNormaliser.PolyExpr.var 1
  let I0 := RingNormaliser.PolyExpr.var 2
  let I1 := RingNormaliser.PolyExpr.var 3
  let R0 := RingNormaliser.PolyExpr.var 4
  .add
    (.mul (.const 2) (.mul M1 (.mul I0 I1)))
    (.add
      (.mul (.add M0 (.neg (.mul (.const 2) M1))) (.mul I0 I1))
      (.mul R0 I1))

private def fullResidualR : RingNormaliser.PolyExpr :=
  let M0 := RingNormaliser.PolyExpr.var 0
  let I0 := RingNormaliser.PolyExpr.var 2
  let I1 := RingNormaliser.PolyExpr.var 3
  let R0 := RingNormaliser.PolyExpr.var 4
  .mul (.add (.mul M0 I0) R0) I1

private theorem fullResidual_normal :
    RingNormaliser.normalize fullResidualL =
      RingNormaliser.normalize fullResidualR := by decide

private theorem full_residual_rearrange
    (M0 M1 I0 I1 R0 : Q') :
    Q'.ofNat 2 * (M1 * (I0 * I1)) +
        ((M0 + -(Q'.ofNat 2 * M1)) * (I0 * I1) + R0 * I1) ≈
      (M0 * I0 + R0) * I1 := by
  simpa [fullResidualL, fullResidualR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      fullResidualL fullResidualR fullResidual_normal
      (fun | 0 => M0 | 1 => M1 | 2 => I0 | 3 => I1 | _ => R0))

private def deficitPascalL : RingNormaliser.PolyExpr :=
  .mul (.const 8) (.add (.var 0) (.neg (.var 1)))

private def deficitPascalR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.const 8) (.neg (.var 2))) (.var 0))
    (.add (.mul (.var 2) (.var 0))
      (.neg (.mul (.const 8) (.var 1))))

private theorem deficitPascal_normal :
    RingNormaliser.normalize deficitPascalL =
      RingNormaliser.normalize deficitPascalR := by decide

private theorem deficit_pascal_algebra (I A F : Q') :
    Q'.ofNat 8 * (I + -A) ≈
      (Q'.ofNat 8 + -F) * I +
        (F * I + -(Q'.ofNat 8 * A)) := by
  simpa [deficitPascalL, deficitPascalR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      deficitPascalL deficitPascalR deficitPascal_normal
      (fun | 0 => I | 1 => A | _ => F))

/-- Common-cutoff Pascal residual on the physical block schedule. -/
def blockPascalResidual (k : Nat) : Q' :=
  cumulativeScaledThetaResidual (blockWeight k) (blockNcut k)

/-- Scalar part of eight times the physical theta deficit. -/
def blockPascalMargin (k : Nat) : Q' :=
  Q'.ofNat 8 + -(qpow ((1 : Q') + blockWeight k) 3)

/-- Scalar reserve remaining after the factor-two comparison. -/
def blockPascalMarginReserve (k : Nat) : Q' :=
  blockPascalMargin k +
    -(Q'.ofNat 2 * blockPascalMargin (k + 1))

/-- Exact cubic profile of the block Pascal margin. -/
theorem blockPascalMargin_profile_eqv (k : Nat) :
    blockPascalMargin k ≈
      blockMargin k *
        ((Q'.ofNat 12 + -(Q'.ofNat 6 * blockMargin k)) +
          blockMargin k * blockMargin k) := by
  let u := blockMargin k
  let x := (1 : Q') + ((1 : Q') + -u)
  have hp : qpow x 3 ≈ x * x * x := rg_qpow_three_eqv x
  unfold blockPascalMargin blockWeight
  change Q'.ofNat 8 + -(qpow x 3) ≈
    u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u * u)
  refine Q'.eqv_trans _ (Q'.ofNat 8 + -(x * x * x)) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hp)) ?_
  exact margin_profile_cube_algebra u

/-- The coarse scalar margin retains at least eleven heat-time units. -/
theorem eleven_mul_blockMargin_le_blockPascalMargin (k : Nat) :
    Q'.ofNat 11 * blockMargin k <= blockPascalMargin k := by
  let u := blockMargin k
  have hu0 : (0 : Q') <= u := blockMargin_nonneg k
  have h6u : Q'.ofNat 6 * u <= (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg_left u
      (Q'.mkPos 1 12 (by decide)) (Q'.ofNat 6)
      (blockMargin_le_q112 k) (by decide)
    exact Q'.le_trans' _ _ _ h (by decide)
  have hone : (0 : Q') <= (1 : Q') + -(Q'.ofNat 6 * u) :=
    Q'.sub_nonneg_of_le h6u
  have hu2 : (0 : Q') <= u * u := Q'.mul_nonneg _ _ hu0 hu0
  have hinner : (0 : Q') <=
      ((1 : Q') + -(Q'.ofNat 6 * u)) + u * u :=
    Q'.zero_le_add _ _ hone hu2
  have hrem : (0 : Q') <=
      u * (((1 : Q') + -(Q'.ofNat 6 * u)) + u * u) :=
    Q'.mul_nonneg _ _ hu0 hinner
  have hsplit : Q'.ofNat 11 * u <=
      u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u * u) :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hrem)
      (Q'.ge_of_eqv (margin_lower_split u))
  exact Q'.le_trans' _ _ _ (by simpa only [u] using hsplit)
    (Q'.le_of_eqv (Q'.eqv_symm (blockPascalMargin_profile_eqv k)))

/-- The same scalar margin never exceeds twelve heat-time units. -/
theorem blockPascalMargin_le_twelve_mul_blockMargin (k : Nat) :
    blockPascalMargin k <= Q'.ofNat 12 * blockMargin k := by
  let u := blockMargin k
  have hu0 : (0 : Q') <= u := blockMargin_nonneg k
  have hu6 : u <= Q'.ofNat 6 :=
    Q'.le_trans' _ _ _ (blockMargin_le_one k) (by decide)
  have hu2 : (0 : Q') <= u * u := Q'.mul_nonneg _ _ hu0 hu0
  have hcube : u * (u * u) <= Q'.ofNat 6 * (u * u) :=
    Q'.mul_le_mul_of_nonneg_right _ _ (u * u) hu6 hu2
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 12 * u + -(Q'.ofNat 6 * (u * u))) _ _ hcube
  have hprofile :
      u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u * u) <=
        Q'.ofNat 12 * u := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (margin_expanded u))
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (margin_upper_cancel u)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (blockPascalMargin_profile_eqv k))
    (by simpa only [u] using hprofile)

/-- The quarter schedule leaves a uniform positive scalar reserve: after the
factor-two fine-scale payment, at least five coarse heat-time units remain. -/
theorem five_mul_blockMargin_le_blockPascalMarginReserve (k : Nat) :
    Q'.ofNat 5 * blockMargin k <= blockPascalMarginReserve k := by
  let u := blockMargin k
  let v := blockMargin (k + 1)
  let M0 := blockPascalMargin k
  let M1 := blockPascalMargin (k + 1)
  have hM0 : Q'.ofNat 11 * u <= M0 := by
    simpa only [u, M0] using eleven_mul_blockMargin_le_blockPascalMargin k
  have hM1 : M1 <= Q'.ofNat 12 * v := by
    simpa only [M1, v] using
      blockPascalMargin_le_twelve_mul_blockMargin (k + 1)
  have h2 := Q'.mul_le_mul_of_nonneg_left M1 (Q'.ofNat 12 * v)
    (Q'.ofNat 2) hM1 (by decide)
  have h4v : Q'.ofNat 4 * v ≈ u := by
    simpa only [u, v] using four_mul_blockMargin_succ_eqv k
  have h2M1 : Q'.ofNat 2 * M1 <= Q'.ofNat 6 * u := by
    exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (by pascal_ring :
        Q'.ofNat 2 * (Q'.ofNat 12 * v) ≈
          Q'.ofNat 6 * (Q'.ofNat 4 * v))
      (Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _ h4v)))
  have hadd := Q'.add_le_add_left (Q'.ofNat 5 * u) _ _ h2M1
  have hsum : Q'.ofNat 5 * u + Q'.ofNat 2 * M1 <= M0 :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (five_add_six_mul_eqv_eleven u)) hM0)
  have hout := le_sub_of_add_le_local hsum
  simpa only [u, M0, M1, blockPascalMarginReserve] using hout

/-- Exact Pascal decomposition of the finite physical theta deficit. -/
theorem eight_mul_blockThetaDeficit_eqv (k : Nat) :
    Q'.ofNat 8 * blockThetaDeficit k ≈
      blockPascalMargin k * blockIntegerTheta k +
        blockPascalResidual k := by
  unfold blockThetaDeficit blockPascalMargin blockPascalResidual
    cumulativeScaledThetaResidual blockIntegerTheta blockHalfTheta
  exact deficit_pascal_algebra _ _ _

/-- The strictly reduced cross-cutoff residual atom.  The explicit scalar
reserve is kept on the right, so this field contains only the transport of
the cumulative Pascal residual through the changing cutoff. -/
structure BlockCompatibleP2PascalResidualHalfContraction : Type where
  residual : forall k, 4 <= k ->
    Q'.ofNat 2 *
        (blockIntegerTheta k * blockPascalResidual (k + 1)) <=
      blockPascalMarginReserve k *
          (blockIntegerTheta k * blockIntegerTheta (k + 1)) +
        blockPascalResidual k * blockIntegerTheta (k + 1)

/-- The Pascal residual recursion reconstructs the normalized theta-deficit
half-contraction exactly. -/
def BlockCompatibleP2PascalResidualHalfContraction.toThetaDeficitHalfContraction
    (P : BlockCompatibleP2PascalResidualHalfContraction) :
    BlockCompatibleP2ThetaDeficitHalfContraction where
  contraction := fun k hk => by
    let I0 := blockIntegerTheta k
    let I1 := blockIntegerTheta (k + 1)
    let T0 := blockThetaDeficit k
    let T1 := blockThetaDeficit (k + 1)
    let M0 := blockPascalMargin k
    let M1 := blockPascalMargin (k + 1)
    let R0 := blockPascalResidual k
    let R1 := blockPascalResidual (k + 1)
    have hres : Q'.ofNat 2 * (I0 * R1) <=
        (M0 + -(Q'.ofNat 2 * M1)) * (I0 * I1) + R0 * I1 := by
      simpa only [I0, I1, M0, M1, R0, R1,
        blockPascalMarginReserve] using P.residual k hk
    have hadd := Q'.add_le_add_left
      (Q'.ofNat 2 * (M1 * (I0 * I1))) _ _ hres
    have hfull :
        Q'.ofNat 2 * (I0 * (M1 * I1 + R1)) <=
          (M0 * I0 + R0) * I1 := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (by pascal_ring :
          Q'.ofNat 2 * (I0 * (M1 * I1 + R1)) ≈
            Q'.ofNat 2 * (M1 * (I0 * I1)) +
              Q'.ofNat 2 * (I0 * R1)))
        (Q'.le_trans' _ _ _ hadd
          (Q'.le_of_eqv (full_residual_rearrange M0 M1 I0 I1 R0)))
    have hT0 : Q'.ofNat 8 * T0 ≈ M0 * I0 + R0 := by
      simpa only [T0, M0, I0, R0] using
        eight_mul_blockThetaDeficit_eqv k
    have hT1 : Q'.ofNat 8 * T1 ≈ M1 * I1 + R1 := by
      simpa only [T1, M1, I1, R1] using
        eight_mul_blockThetaDeficit_eqv (k + 1)
    have hscaled :
        Q'.ofNat 8 * (Q'.ofNat 2 * (I0 * T1)) <=
          Q'.ofNat 8 * (T0 * I1) := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (by pascal_ring :
            Q'.ofNat 8 * (Q'.ofNat 2 * (I0 * T1)) ≈
              Q'.ofNat 2 * (I0 * (Q'.ofNat 8 * T1)))
          (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
            (Q'.mul_eqv_congr_left I0 _ _ hT1))))
        (Q'.le_trans' _ _ _ hfull
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
            (by pascal_ring :
              Q'.ofNat 8 * (T0 * I1) ≈
                (Q'.ofNat 8 * T0) * I1)
            (Q'.mul_eqv_congr_right _ _ I1 hT0)))))
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)

#print axioms eight_mul_blockThetaDeficit_eqv
#print axioms blockPascalMargin_profile_eqv
#print axioms five_mul_blockMargin_le_blockPascalMarginReserve
#print axioms BlockCompatibleP2PascalResidualHalfContraction.toThetaDeficitHalfContraction

end YMGap.Continuum.P2BlockCompatibleThetaPascal
