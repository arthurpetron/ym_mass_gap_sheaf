/-
Explicit uniform lower bound carried by the harmonic retune cube.

For `u_k=1/(k+2)` and `w_k=1-u_k`, the retune base is
`1-u_k/2`.  The elementary factorization

  1 - (1-b)^3 - 2b = b(1-3b+b^2),   b=u_k/2,

is nonnegative because `b≤1/4`.  This file proves the resulting rational
floor without division, classical choice, or an asymptotic estimate.
-/

import YMGap.Continuum.HarmonicVariableAnchorThetaBridge

namespace YMGap.Continuum.HarmonicRetuneFloor

set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicVariableAnchorThetaBridge
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

open YMGap.Continuum.RingNormaliser

private def cubicFloorLHS : PolyExpr :=
  .add
    (.add (.const 1)
      (.neg (.pow (.add (.const 1) (.neg (.var 0))) 3)))
    (.neg (.add (.var 0) (.var 0)))

private def cubicFloorRHS : PolyExpr :=
  .mul (.var 0)
    (.add
      (.add (.const 1) (.neg (.mul (.const 3) (.var 0))))
      (.mul (.var 0) (.var 0)))

private theorem cubicFloor_normal :
    normalize cubicFloorLHS = normalize cubicFloorRHS := by decide

private theorem cubic_floor_factor (b : Q') :
    (((1 : Q') - RGTransport.qpow ((1 : Q') + -b) 3) + -(b + b)) ≈
      b * (((1 : Q') + -(Q'.ofNat 3 * b)) + b * b) := by
  have h := poly_identity_of_normal_eq cubicFloorLHS cubicFloorRHS
    cubicFloor_normal (fun _ => b)
  simpa [RingNormaliser.eval, cubicFloorLHS, cubicFloorRHS,
    RingNormaliser.qpow, RGTransport.qpow] using h

/-- Every harmonic unit lies below one half. -/
theorem harmU_le_half (k : Nat) :
    harmU k ≤ Q'.mkPos 1 2 (by decide) := by
  unfold harmU
  exact unit_antitone (by decide) (by omega) (by omega)

/-- The retune-cube complement retains at least one harmonic unit. -/
theorem harmU_le_retune_floor (k : Nat) :
    harmU k ≤ (1 : Q') - retuneCube (harmW k) := by
  let h : Q' := Q'.mkPos 1 2 (by decide)
  let q : Q' := Q'.mkPos 1 4 (by decide)
  let u : Q' := harmU k
  let b : Q' := h * u
  have hu0 : (0 : Q') ≤ u := by
    unfold u
    exact harmU_nonneg k
  have huh : u ≤ h := by
    unfold u h
    exact harmU_le_half k
  have hb0 : (0 : Q') ≤ b := by
    unfold b h
    exact Q'.mul_nonneg _ _ (by decide) hu0
  have hbq : b ≤ q := by
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ h huh (by
      unfold h
      decide)
    exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (by
      unfold h q
      decide))
  have h3b : Q'.ofNat 3 * b ≤ (1 : Q') := by
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3) hbq (by decide)
    exact Q'.le_trans' _ _ _ hs (by
      unfold q
      decide)
  have hcore0 : (0 : Q') ≤
      ((1 : Q') + -(Q'.ofNat 3 * b)) + b * b := by
    exact Q'.zero_le_add _ _ (Q'.sub_nonneg_of_le h3b)
      (Q'.mul_nonneg _ _ hb0 hb0)
  have hfactor0 : (0 : Q') ≤
      b * (((1 : Q') + -(Q'.ofNat 3 * b)) + b * b) :=
    Q'.mul_nonneg _ _ hb0 hcore0
  have hbase : retuneBase (harmW k) ≈ (1 : Q') + -b := by
    unfold retuneBase harmW oneSub b h
    change Q'.mkPos 1 2 (by decide) *
        ((1 : Q') + ((1 : Q') + -harmU k)) ≈
      (1 : Q') + -(Q'.mkPos 1 2 (by decide) * harmU k)
    refine Q'.eqv_trans _
      (Q'.mkPos 1 2 (by decide) *
        (((1 : Q') + (1 : Q')) + -harmU k)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') 1 (-harmU k)))
    · refine Q'.eqv_trans _
        (Q'.mkPos 1 2 (by decide) * ((1 : Q') + 1) +
          Q'.mkPos 1 2 (by decide) * (-harmU k)) _
        (Q'.mul_add_eqv _ _ _) ?_
      exact Q'.add_eqv_congr'
        (by decide)
        (Q'.mul_neg_eqv (Q'.mkPos 1 2 (by decide)) (harmU k))
  have hcube : retuneCube (harmW k) ≈
      RGTransport.qpow ((1 : Q') + -b) 3 := by
    unfold retuneCube
    exact BondMovingRelResidual.qpow_eqv_congr_base hbase 3
  have hreplace :
      (((1 : Q') - retuneCube (harmW k)) + -u) ≈
        (((1 : Q') - RGTransport.qpow ((1 : Q') + -b) 3) + -u) := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl 1)
        (Q'.neg_eqv_congr _ _ hcube))
      (Q'.eqv_refl (-u))
  have hub : u ≈ b + b := by
    apply Q'.eqv_symm
    unfold b
    have hh : h + h ≈ (1 : Q') := by
      unfold h
      decide
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv h h u)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (h + h) 1 u hh) ?_
    exact Q'.one_mul_eqv u
  have hpoly :
      (((1 : Q') - RGTransport.qpow ((1 : Q') + -b) 3) + -u) ≈
        b * (((1 : Q') + -(Q'.ofNat 3 * b)) + b * b) := by
    refine Q'.eqv_trans _
      (((1 : Q') - RGTransport.qpow ((1 : Q') + -b) 3) + -(b + b)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_refl ((1 : Q') - RGTransport.qpow ((1 : Q') + -b) 3))
        (Q'.neg_eqv_congr _ _ hub)
    · exact cubic_floor_factor b
  have hfactor :
      (((1 : Q') - retuneCube (harmW k)) + -u) ≈
        b * (((1 : Q') + -(Q'.ofNat 3 * b)) + b * b) := by
    exact Q'.eqv_trans _ _ _ hreplace hpoly
  have hdiff0 : (0 : Q') ≤
      ((1 : Q') - retuneCube (harmW k)) + -u :=
    Q'.le_trans' _ _ _ hfactor0 (Q'.ge_of_eqv hfactor)
  unfold u at hdiff0
  exact Q'.le_of_sub_nonneg hdiff0

/-- Once the explicit theta head is supplied, the physical harmonic mass is
at least `1/(k+2)` at every non-base scale. -/
theorem harmU_le_harmonicMass_of_theta_head {k : Nat} (hk : 1 ≤ k)
    (htheta : harmW k *
          HarmonicThetaRepresentation.halfThetaSum
            (harmW k) (HarmonicGrowingAnchorPF2.growingAnchor k + 1) ≤
        retuneCube (harmW k) *
          HarmonicThetaRepresentation.integerThetaSum
            (harmW k) (HarmonicGrowingAnchorPF2.growingAnchor k)) :
    harmU k ≤ HarmonicFusedSchurObstruction.harmonicMass k := by
  exact Q'.le_trans' _ _ _ (harmU_le_retune_floor k)
    (harmonicMass_floor_of_theta_head hk htheta)

#print axioms harmU_le_half
#print axioms harmU_le_retune_floor
#print axioms harmU_le_harmonicMass_of_theta_head

end YMGap.Continuum.HarmonicRetuneFloor
