/-
Track 11.7-fusion / R4am -- centered successor-profile compiler.

The exact local reserve atom in `P2HalfTimeShiftTail` contains a symmetric
successor expression indexed by `p` and `s-p`.  Expanding every `p` is the
wrong computational interface: once the one-variable successor profile is
discretely concave, every such pair is bounded by the one or two central
indices.

This module proves that reduction constructively for arbitrary `Q'`-valued
profiles.  It is proof about computation: a local second-difference law is
compiled first to antitonic forward differences, then to arbitrary-width
inward exchanges, and finally to the centered-pair bound.  The second half
identifies the actual heat-successor profile and inhabits the finite-interval
compiler at every physical cutoff.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeShiftTail
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.P2HalfTimeCenteredProfile

open YMGap.Constructive
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.RGTransport
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2HalfTimeShiftTail
open YMGap.Continuum.ReciprocalBernoulliUpper

local infix:50 " ≈ " => Q'.eqv

/-- Forward difference in the additive rational presentation. -/
def forwardDifference (f : Nat -> Q') (n : Nat) : Q' :=
  f (n + 1) + -(f n)

/-- Constructive discrete concavity, stated without division. -/
structure DiscreteConcaveProfile (f : Nat -> Q') : Type where
  localConcavity : forall n, f n + f (n + 2) <= f (n + 1) + f (n + 1)

private theorem local_to_difference_step {f : Nat -> Q'} {n : Nat}
    (h : f n + f (n + 2) <= f (n + 1) + f (n + 1)) :
    forwardDifference f (n + 1) <= forwardDifference f n := by
  have hadd := Q'.add_le_add_right _ _ (-(f n) + -(f (n + 1))) h
  have eleft :
      ((f n + f (n + 2)) + (-(f n) + -(f (n + 1)))).eqv
        (forwardDifference f (n + 1)) := by
    unfold forwardDifference
    refine Q'.eqv_trans _
      ((f n + -(f n)) + (f (n + 2) + -(f (n + 1)))) _
      (Q'.add_swap_inner _ _ _ _) ?_
    have hz : (f n + -(f n)).eqv (0 : Q') := by
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.neg_add_self_eqv _)
    exact Q'.eqv_trans _ ((0 : Q') +
        (f (n + 2) + -(f (n + 1)))) _
      (Q'.add_eqv_congr_right _ _ _ hz)
      (Q'.eqv_of_eq (Q'.zero_add' _))
  have eright :
      ((f (n + 1) + f (n + 1)) + (-(f n) + -(f (n + 1)))).eqv
        (forwardDifference f n) := by
    unfold forwardDifference
    refine Q'.eqv_trans _
      ((f (n + 1) + -(f n)) + (f (n + 1) + -(f (n + 1)))) _
      (Q'.add_swap_inner _ _ _ _) ?_
    have hz : (f (n + 1) + -(f (n + 1))).eqv (0 : Q') := by
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.neg_add_self_eqv _)
    exact Q'.eqv_trans _ ((f (n + 1) + -(f n)) + 0) _
      (Q'.add_eqv_congr_left _ _ _ hz)
      (Q'.eqv_of_eq (Q'.add_zero' _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

/-- Local discrete concavity makes the forward differences antitone over an
arbitrary index displacement. -/
theorem DiscreteConcaveProfile.forwardDifference_antitone
    {f : Nat -> Q'} (P : DiscreteConcaveProfile f) (a d : Nat) :
    forwardDifference f (a + d) <= forwardDifference f a := by
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hstep : forwardDifference f (a + d + 1) <=
          forwardDifference f (a + d) := by
        exact local_to_difference_step (P.localConcavity (a + d))
      exact Q'.le_trans' _ _ _ (by simpa only [Nat.add_assoc] using hstep) ih

private theorem difference_to_inward {f : Nat -> Q'} {a b : Nat}
    (h : forwardDifference f b <= forwardDifference f a) :
    f a + f (b + 1) <= f (a + 1) + f b := by
  have hadd := Q'.add_le_add_right _ _ (f a + f b) h
  have eleft :
      (forwardDifference f b + (f a + f b)).eqv
        (f a + f (b + 1)) := by
    unfold forwardDifference
    refine Q'.eqv_trans _
      ((f (b + 1) + f a) + (-(f b) + f b)) _
      (Q'.add_swap_inner _ _ _ _) ?_
    have hz : (-(f b) + f b).eqv (0 : Q') := Q'.neg_add_self_eqv _
    exact Q'.eqv_trans _ ((f (b + 1) + f a) + 0) _
      (Q'.add_eqv_congr_left _ _ _ hz)
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
        (Q'.add_comm_eqv _ _))
  have eright :
      (forwardDifference f a + (f a + f b)).eqv
        (f (a + 1) + f b) := by
    unfold forwardDifference
    refine Q'.eqv_trans _ ((f (a + 1) + -(f a)) + (f b + f a)) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)) ?_
    refine Q'.eqv_trans _
      ((f (a + 1) + f b) + (-(f a) + f a)) _
      (Q'.add_swap_inner _ _ _ _) ?_
    have hz : (-(f a) + f a).eqv (0 : Q') := Q'.neg_add_self_eqv _
    exact Q'.eqv_trans _ ((f (a + 1) + f b) + 0) _
      (Q'.add_eqv_congr_left _ _ _ hz)
      (Q'.eqv_of_eq (Q'.add_zero' _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

/-- Every wide pair may be moved one step inward.  This is the reusable
Monge/exchange form of discrete concavity. -/
theorem DiscreteConcaveProfile.inward_exchange
    {f : Nat -> Q'} (P : DiscreteConcaveProfile f) (a d : Nat) :
    f a + f (a + d + 2) <= f (a + 1) + f (a + d + 1) := by
  have hdiff := P.forwardDifference_antitone a (d + 1)
  have hin := difference_to_inward hdiff
  simpa only [Nat.add_assoc] using hin

/-- A symmetric pair of a discretely concave profile is bounded by the two
central indices.  The proof is a terminating inward-exchange program; its
recursion depth is the pair separation, not the size of any rational term. -/
theorem DiscreteConcaveProfile.pair_le_centers
    {f : Nat -> Q'} (P : DiscreteConcaveProfile f) :
    forall a d,
      f a + f (a + d) <=
        f (a + d / 2) + f (a + (d + 1) / 2) := by
  have hpair : forall d,
      (forall a, f a + f (a + d) <=
        f (a + d / 2) + f (a + (d + 1) / 2)) ∧
      (forall a, f a + f (a + (d + 1)) <=
        f (a + (d + 1) / 2) + f (a + (d + 1 + 1) / 2)) := by
    intro d
    induction d with
    | zero =>
        constructor
        · intro a
          exact Q'.le_refl' _
        · intro a
          exact Q'.le_refl' _
    | succ d ih =>
        constructor
        · exact ih.2
        · intro a
          have hstep := P.inward_exchange a d
          have hinner : f (a + 1) + f (a + d + 1) <=
              f (a + 1 + d / 2) + f (a + 1 + (d + 1) / 2) := by
            simpa only [show (a + 1) + d = a + d + 1 by omega] using
              ih.1 (a + 1)
          have hchain : f a + f (a + d + 2) <=
              f (a + 1 + d / 2) + f (a + 1 + (d + 1) / 2) :=
            Q'.le_trans' _ _ _ hstep hinner
          simpa only [
            show a + (d + 1 + 1) = a + d + 2 by omega,
            show a + (d + 1 + 1) / 2 = a + 1 + d / 2 by omega,
            show a + (d + 1 + 1 + 1) / 2 =
              a + 1 + (d + 1) / 2 by omega] using hchain
  intro a d
  exact (hpair d).1 a

/-! ## 1b. Finite-interval compiler -/

/-- Discrete concavity restricted to the interval `0,...,N`.  This is the
honest carrier for cutoff profiles: no curvature premise is requested beyond
the last supported index. -/
structure DiscreteConcaveProfileOn (f : Nat -> Q') (N : Nat) : Type where
  localConcavity : forall n, n + 2 <= N ->
    f n + f (n + 2) <= f (n + 1) + f (n + 1)

/-- On a finite concavity interval, forward differences remain antitone as
long as both endpoint differences are supported. -/
theorem DiscreteConcaveProfileOn.forwardDifference_antitone
    {f : Nat -> Q'} {N : Nat} (P : DiscreteConcaveProfileOn f N)
    (a d : Nat) (hN : a + d + 1 <= N) :
    forwardDifference f (a + d) <= forwardDifference f a := by
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      have hstep : forwardDifference f (a + d + 1) <=
          forwardDifference f (a + d) := by
        exact local_to_difference_step
          (P.localConcavity (a + d) (by omega))
      exact Q'.le_trans' _ _ _
        (by simpa only [Nat.add_assoc] using hstep)
        (ih (by omega))

/-- A supported wide pair may be moved inward without consulting any value
past the finite concavity interval. -/
theorem DiscreteConcaveProfileOn.inward_exchange
    {f : Nat -> Q'} {N : Nat} (P : DiscreteConcaveProfileOn f N)
    (a d : Nat) (hN : a + d + 2 <= N) :
    f a + f (a + d + 2) <= f (a + 1) + f (a + d + 1) := by
  have hdiff := P.forwardDifference_antitone a (d + 1) (by omega)
  have hin := difference_to_inward hdiff
  simpa only [Nat.add_assoc] using hin

/-- Every supported pair is bounded by its central one or two entries.  The
certificate performs only as many symbolic inward exchanges as the pair
width and never evaluates a heat-kernel coefficient. -/
theorem DiscreteConcaveProfileOn.pair_le_centers
    {f : Nat -> Q'} {N : Nat} (P : DiscreteConcaveProfileOn f N) :
    forall a d, a + d <= N ->
      f a + f (a + d) <=
        f (a + d / 2) + f (a + (d + 1) / 2) := by
  have hpair : forall d,
      (forall a, a + d <= N -> f a + f (a + d) <=
        f (a + d / 2) + f (a + (d + 1) / 2)) ∧
      (forall a, a + (d + 1) <= N -> f a + f (a + (d + 1)) <=
        f (a + (d + 1) / 2) + f (a + (d + 1 + 1) / 2)) := by
    intro d
    induction d with
    | zero =>
        constructor
        · intro a _
          exact Q'.le_refl' _
        · intro a _
          exact Q'.le_refl' _
    | succ d ih =>
        constructor
        · exact ih.2
        · intro a hN
          have hstep := P.inward_exchange a d (by omega)
          have hinner : f (a + 1) + f (a + d + 1) <=
              f (a + 1 + d / 2) + f (a + 1 + (d + 1) / 2) := by
            simpa only [show (a + 1) + d = a + d + 1 by omega] using
              ih.1 (a + 1) (by omega)
          have hchain : f a + f (a + d + 2) <=
              f (a + 1 + d / 2) + f (a + 1 + (d + 1) / 2) :=
            Q'.le_trans' _ _ _ hstep hinner
          simpa only [
            show a + (d + 1 + 1) = a + d + 2 by omega,
            show a + (d + 1 + 1) / 2 = a + 1 + d / 2 by omega,
            show a + (d + 1 + 1 + 1) / 2 =
              a + 1 + (d + 1) / 2 by omega] using hchain
  intro a d hN
  exact (hpair d).1 a hN

/-- Order-free midpoint form of the finite centered-pair compiler. -/
theorem DiscreteConcaveProfileOn.pair_le_midpoint
    {f : Nat -> Q'} {N : Nat} (P : DiscreteConcaveProfileOn f N)
    (a b : Nat) (ha : a <= N) (hb : b <= N) :
    f a + f b <= f ((a + b) / 2) + f ((a + b + 1) / 2) := by
  rcases Nat.le_total a b with hab | hba
  · have h := P.pair_le_centers a (b - a) (by omega)
    simpa only [
      show a + (b - a) = b by omega,
      show a + (b - a) / 2 = (a + b) / 2 by omega,
      show a + (b - a + 1) / 2 = (a + b + 1) / 2 by omega] using h
  · have h := P.pair_le_centers b (a - b) (by omega)
    have h' : f b + f a <=
        f ((a + b) / 2) + f ((a + b + 1) / 2) := by
      simpa only [
        show b + (a - b) = a by omega,
        show b + (a - b) / 2 = (a + b) / 2 by omega,
        show b + (a - b + 1) / 2 = (a + b + 1) / 2 by omega] using h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_comm_eqv (f a) (f b))) h'

/-! ## 2. The physical scalar curvature budget -/

/-- The physical heat denominator dominates the cutoff with the four-index
buffer needed by the successor-profile second difference.  The induction is
linear in the scale recurrence; no exponent is evaluated. -/
theorem blockNcut_add_four_le_physicalWeightDen (k : Nat) :
    blockNcut k + 4 <= physicalWeightDen k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [blockNcut_succ]
      unfold physicalWeightDen at ih ⊢
      rw [Nat.pow_succ]
      omega

private theorem scaled_double_recip_le_two (n D : Nat) (hD : 0 < D)
    (hnD : n <= D) :
    Q'.ofNat n * (Q'.ofNat 2 * Q'.mkPos 1 D hD) <= Q'.ofNat 2 := by
  show (Q'.ofNat n * (Q'.ofNat 2 * Q'.mkPos 1 D hD)).num *
      ((Q'.ofNat 2).den : Int) <=
    (Q'.ofNat 2).num *
      ((Q'.ofNat n * (Q'.ofNat 2 * Q'.mkPos 1 D hD)).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  push_cast
  exact_mod_cast (by simpa only [Nat.mul_comm] using
    Nat.mul_le_mul_left 2 hnD)

/-- Uniform near-one curvature budget on every supported physical index:

`(p+4) * (1-w_k^2) <= 2` for `p <= N_k`.

This is the exact scalar condition under which the normalized heat successor
profile has nonpositive second difference.  It follows from Bernoulli at
power two and the schedule inequality `N_k+4 <= D_k`. -/
theorem physical_successor_profile_curvature_budget
    (k p : Nat) (hp : p <= blockNcut k) :
    Q'.ofNat (p + 4) *
        ((1 : Q') - qpow (blockWeight k) 2) <= Q'.ofNat 2 := by
  let D := physicalWeightDen k
  have hD : 0 < D := by
    simpa only [D] using physicalWeightDen_pos k
  have hpD : p + 4 <= D :=
    Nat.le_trans (Nat.add_le_add_right hp 4)
      (by simpa only [D] using blockNcut_add_four_le_physicalWeightDen k)
  have hbern : (1 : Q') - qpow (blockWeight k) 2 <=
      Q'.ofNat 2 * ((1 : Q') - blockWeight k) :=
    oneSub_qpow_le (blockWeight_nonneg k) (blockWeight_le_one k) 2
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (p + 4))
    hbern (zero_le_ofNat (p + 4))
  have hmargin : ((1 : Q') - blockWeight k) ≈
      Q'.mkPos 1 D hD :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (by simpa only [D] using blockMargin_eqv_closed k)
  have eright :
      (Q'.ofNat (p + 4) *
        (Q'.ofNat 2 * ((1 : Q') - blockWeight k))).eqv
      (Q'.ofNat (p + 4) *
        (Q'.ofNat 2 * Q'.mkPos 1 D hD)) := by
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hmargin)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv eright)
      (scaled_double_recip_le_two (p + 4) D
        hD hpD))

/-! ## 3. Linear-geometric curvature without coefficient evaluation -/

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

private theorem ofInt_num_cast (z : Int) : (Q'.ofInt z).num = z := rfl

private theorem ofInt_den_cast (z : Int) : ((Q'.ofInt z).den : Int) = 1 := rfl

private theorem zero_num_cast : ((0 : Q').num) = 0 := rfl

private theorem zero_den_cast : (((0 : Q').den : Int)) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               ofInt_num_cast, ofInt_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast,
               Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero, Int.neg_zero] <;>
             ac_rfl))

private theorem mul_eqv_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' := by
  exact Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private def qone : Q' := Q'.ofInt 1

private def qtwo : Q' := Q'.ofInt 2

private def linearCurvatureL : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let one := RingNormaliser.PolyExpr.const 1
  let two := RingNormaliser.PolyExpr.const 2
  let u := RingNormaliser.PolyExpr.add one (.neg z)
  .add
    (.add P (.mul (.add P two) (.mul z z)))
    (.mul u (.add two (.neg (.mul (.add P two) u))))

private def linearCurvatureR : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let one := RingNormaliser.PolyExpr.const 1
  .add (.mul (.add P one) z) (.mul (.add P one) z)

private theorem linearCurvature_normal :
    RingNormaliser.normalize linearCurvatureL =
      RingNormaliser.normalize linearCurvatureR := by decide

private theorem linearCurvature_eqv (P z : Q') :
    P + (P + qtwo) * (z * z) +
        ((1 : Q') + -z) *
          (qtwo + -((P + qtwo) * ((1 : Q') + -z))) ≈
      (P + (1 : Q')) * z + (P + (1 : Q')) * z := by
  simpa [linearCurvatureL, linearCurvatureR, RingNormaliser.eval, qtwo] using
    (RingNormaliser.poly_identity_of_normal_eq
      linearCurvatureL linearCurvatureR linearCurvature_normal
      (fun | 0 => P | _ => z))

private def reciprocalConvexL : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let one := RingNormaliser.PolyExpr.const 1
  let two := RingNormaliser.PolyExpr.const 2
  let u := RingNormaliser.PolyExpr.add one (.neg z)
  let left := .add
    (.mul (.mul A (.add A two)) z)
    (.mul (.mul A (.add A two)) z)
  let slack := .add
    (.mul (.mul u u) (.mul A (.add A one)))
    (.add (.mul (.mul two u) A) two)
  .add left slack

private def reciprocalConvexR : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let z := RingNormaliser.PolyExpr.var 1
  let one := RingNormaliser.PolyExpr.const 1
  let two := RingNormaliser.PolyExpr.const 2
  .add
    (.mul (.add A one) (.add A two))
    (.mul (.mul A (.add A one)) (.mul z z))

private theorem reciprocalConvex_normal :
    RingNormaliser.normalize reciprocalConvexL =
      RingNormaliser.normalize reciprocalConvexR := by decide

private theorem reciprocalConvex_eqv (A z : Q') :
    ((A * (A + qtwo) * z + A * (A + qtwo) * z) +
        (((qone + -z) * (qone + -z) * (A * (A + qone))) +
          (qtwo * (qone + -z) * A + qtwo))) ≈
      (A + qone) * (A + qtwo) + A * (A + qone) * (z * z) := by
  simpa [reciprocalConvexL, reciprocalConvexR, RingNormaliser.eval,
    qone, qtwo] using
    (RingNormaliser.poly_identity_of_normal_eq
      reciprocalConvexL reciprocalConvexR reciprocalConvex_normal
      (fun | 0 => A | _ => z))

/-- The `r=0` part of the normalized successor profile.  Its curvature is the
single polynomial `(1-z) * (2-(p+4)(1-z))`; keeping it as a function avoids
ever evaluating a physical power. -/
def linearGeometricProfile (z : Q') (p : Nat) : Q' :=
  Q'.ofNat (p + 2) * qpow z p

theorem linearGeometricProfile_localConcavity
    {z : Q'} (hz0 : (0 : Q') <= z) (hz1 : z <= (1 : Q'))
    (p : Nat)
    (hbudget : Q'.ofNat (p + 4) * ((1 : Q') - z) <= qtwo) :
    linearGeometricProfile z p + linearGeometricProfile z (p + 2) <=
      linearGeometricProfile z (p + 1) +
        linearGeometricProfile z (p + 1) := by
  let P := Q'.ofNat (p + 2)
  let Z := qpow z p
  let u := (1 : Q') - z
  have hZ0 : (0 : Q') <= Z := by
    exact qpow_nonneg z hz0 p
  have hu0 : (0 : Q') <= u := by
    exact Q'.sub_nonneg_of_le hz1
  have eP2 : P + qtwo ≈ Q'.ofNat (p + 4) := by
    exact Q'.eqv_trans _ _ _
      (by
        unfold P qtwo
        exact Q'.eqv_symm (Q'.ofNat_add_eqv (p + 2) 2))
      (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
  have ebudget : (P + qtwo) * u ≈
      Q'.ofNat (p + 4) * ((1 : Q') - z) := by
    exact Q'.mul_eqv_congr_right _ _ _ eP2
  have hbudgetP : (P + qtwo) * u <= qtwo :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv ebudget) hbudget
  have hrem : (0 : Q') <= qtwo + -((P + qtwo) * u) :=
    Q'.sub_nonneg_of_le hbudgetP
  have hslack : (0 : Q') <=
      u * (qtwo + -((P + qtwo) * u)) :=
    Q'.mul_nonneg _ _ hu0 hrem
  have hpoly :
      P + (P + qtwo) * (z * z) <=
        (P + (1 : Q')) * z + (P + (1 : Q')) * z := by
    have hadd := Q'.add_le_self_of_nonneg
      (P + (P + qtwo) * (z * z))
      (u * (qtwo + -((P + qtwo) * u))) hslack
    have eid :
        P + (P + qtwo) * (z * z) +
            u * (qtwo + -((P + qtwo) * u)) ≈
          (P + (1 : Q')) * z + (P + (1 : Q')) * z := by
      dsimp only [u]
      change P + (P + qtwo) * (z * z) +
          ((1 : Q') + -z) *
            (qtwo + -((P + qtwo) * ((1 : Q') + -z))) ≈
        (P + (1 : Q')) * z + (P + (1 : Q')) * z
      exact linearCurvature_eqv P z
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eid)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ Z hpoly hZ0
  have eP1 : Q'.ofNat (p + 3) ≈ P + (1 : Q') := by
    unfold P
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
      (Q'.ofNat_add_eqv (p + 2) 1)
  have e0 : linearGeometricProfile z p ≈ Z * P := by
    unfold linearGeometricProfile Z P
    exact Q'.mul_comm_eqv _ _
  have e1 : linearGeometricProfile z (p + 1) ≈
      Z * ((P + (1 : Q')) * z) := by
    unfold linearGeometricProfile
    change (Q'.ofNat (p + 3) * (Z * z)).eqv _
    refine Q'.eqv_trans _ ((P + (1 : Q')) * (Z * z)) _
      (Q'.mul_eqv_congr_right _ _ _ eP1) ?_
    ring_qeqv
  have e2 : linearGeometricProfile z (p + 2) ≈
      Z * ((P + qtwo) * (z * z)) := by
    unfold linearGeometricProfile
    change (Q'.ofNat (p + 4) * ((Z * z) * z)).eqv _
    refine Q'.eqv_trans _ ((P + qtwo) * ((Z * z) * z)) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm eP2)) ?_
    ring_qeqv
  have eleft :
      linearGeometricProfile z p + linearGeometricProfile z (p + 2) ≈
        Z * (P + (P + qtwo) * (z * z)) := by
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' e0 e2) (by ring_qeqv)
  have eright :
      Z * ((P + (1 : Q')) * z + (P + (1 : Q')) * z) ≈
        linearGeometricProfile z (p + 1) +
          linearGeometricProfile z (p + 1) := by
    exact Q'.eqv_trans _ _ _ (by ring_qeqv)
      (Q'.add_eqv_congr' (Q'.eqv_symm e1) (Q'.eqv_symm e1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv eright))

/-- The reciprocal correction `z^p/(a+p+1)` is convex.  The proof clears its
three adjacent denominators once, then invokes a two-variable reflected
polynomial identity whose slack is
`u^2 A(A+1) + 2uA + 2`. -/
theorem invSuccGeometric_localConvex
    {z : Q'} (hz1 : z <= (1 : Q')) (a : Nat) :
    Q'.invSucc (a + 1) * z + Q'.invSucc (a + 1) * z <=
      Q'.invSucc a + Q'.invSucc (a + 2) * (z * z) := by
  let A0 := Q'.ofNat (a + 1)
  let A1 := Q'.ofNat (a + 2)
  let A2 := Q'.ofNat (a + 3)
  let C := A0 * (A1 * A2)
  let u := qone + -z
  have hA0 : (0 : Q') <= A0 := zero_le_ofNat _
  have hz1' : z <= qone := by
    simpa only [qone] using hz1
  have hu0 : (0 : Q') <= u := by
    unfold u
    change (0 : Q') <= qone - z
    exact Q'.sub_nonneg_of_le hz1'
  have hCpos : (0 : Q') < C := by
    exact Q'.mul_pos (Q'.ofNat_succ_pos a)
      (Q'.mul_pos (Q'.ofNat_succ_pos (a + 1))
        (Q'.ofNat_succ_pos (a + 2)))
  have ec0 : C * Q'.invSucc a ≈ A1 * A2 := by
    refine Q'.eqv_trans _ ((A1 * A2) * (A0 * Q'.invSucc a)) _
      (by unfold C; ring_qeqv) ?_
    exact Q'.eqv_trans _ ((A1 * A2) * (1 : Q')) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.ofNat_succ_mul_invSucc a))
      (Q'.mul_one_eqv _)
  have ec1 : C * Q'.invSucc (a + 1) ≈ A0 * A2 := by
    refine Q'.eqv_trans _ ((A0 * A2) * (A1 * Q'.invSucc (a + 1))) _
      (by unfold C; ring_qeqv) ?_
    exact Q'.eqv_trans _ ((A0 * A2) * (1 : Q')) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.ofNat_succ_mul_invSucc (a + 1)))
      (Q'.mul_one_eqv _)
  have ec2 : C * Q'.invSucc (a + 2) ≈ A0 * A1 := by
    refine Q'.eqv_trans _ ((A0 * A1) * (A2 * Q'.invSucc (a + 2))) _
      (by unfold C; ring_qeqv) ?_
    exact Q'.eqv_trans _ ((A0 * A1) * (1 : Q')) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.ofNat_succ_mul_invSucc (a + 2)))
      (Q'.mul_one_eqv _)
  have eA1 : A1 ≈ A0 + qone := by
    unfold A0 A1 qone
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
      (Q'.ofNat_add_eqv (a + 1) 1)
  have eA2 : A2 ≈ A0 + qtwo := by
    unfold A0 A2 qtwo
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
      (Q'.ofNat_add_eqv (a + 1) 2)
  have hslack : (0 : Q') <=
      (u * u * (A0 * (A0 + qone))) +
        (qtwo * u * A0 + qtwo) := by
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ hu0 hu0)
        (Q'.mul_nonneg _ _ hA0
          (Q'.zero_le_add _ _ hA0 (by decide))))
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (by decide) hu0) hA0)
        (by decide))
  have hpoly :
      A0 * (A0 + qtwo) * z + A0 * (A0 + qtwo) * z <=
        (A0 + qone) * (A0 + qtwo) +
          A0 * (A0 + qone) * (z * z) := by
    have hadd := Q'.add_le_self_of_nonneg
      (A0 * (A0 + qtwo) * z + A0 * (A0 + qtwo) * z)
      ((u * u * (A0 * (A0 + qone))) +
        (qtwo * u * A0 + qtwo)) hslack
    have eid' :
        (A0 * (A0 + qtwo) * z + A0 * (A0 + qtwo) * z) +
            ((u * u * (A0 * (A0 + qone))) +
              (qtwo * u * A0 + qtwo)) ≈
          (A0 + qone) * (A0 + qtwo) +
            A0 * (A0 + qone) * (z * z) := by
      unfold u
      exact reciprocalConvex_eqv A0 z
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eid')
  have eleft :
      C * (Q'.invSucc (a + 1) * z + Q'.invSucc (a + 1) * z) ≈
        A0 * (A0 + qtwo) * z + A0 * (A0 + qtwo) * z := by
    refine Q'.eqv_trans _
      ((C * Q'.invSucc (a + 1)) * z +
        (C * Q'.invSucc (a + 1)) * z) _ (by ring_qeqv) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ z
        (Q'.eqv_trans _ _ _ ec1
          (mul_eqv_congr
            (Q'.eqv_refl A0) eA2)))
      (Q'.mul_eqv_congr_right _ _ z
        (Q'.eqv_trans _ _ _ ec1
          (mul_eqv_congr
            (Q'.eqv_refl A0) eA2)))
  have eright :
      C * (Q'.invSucc a + Q'.invSucc (a + 2) * (z * z)) ≈
        (A0 + qone) * (A0 + qtwo) +
          A0 * (A0 + qone) * (z * z) := by
    refine Q'.eqv_trans _
      (C * Q'.invSucc a +
        (C * Q'.invSucc (a + 2)) * (z * z)) _ (by ring_qeqv) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ ec0
        (mul_eqv_congr eA1 eA2))
      (Q'.mul_eqv_congr_right _ _ (z * z)
        (Q'.eqv_trans _ _ _ ec2
          (mul_eqv_congr
            (Q'.eqv_refl A0) eA1)))
  have hscaled :
      C * (Q'.invSucc (a + 1) * z + Q'.invSucc (a + 1) * z) <=
        C * (Q'.invSucc a + Q'.invSucc (a + 2) * (z * z)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hpoly (Q'.ge_of_eqv eright))
  exact Q'.le_of_mul_le_mul_left hscaled hCpos

/-- The reciprocal correction in the successor profile.  Its `r` factor is
kept outside the inverse so that the adjacent-denominator certificate above
can be reused at every shift and every index. -/
def reciprocalGeometricProfile (z : Q') (r p : Nat) : Q' :=
  Q'.ofNat r * (Q'.invSucc (r + p) * qpow z p)

/-- Multiplying the reciprocal kernel by the nonnegative common factor
`r*z^p` preserves its local convexity. -/
theorem reciprocalGeometricProfile_localConvex
    {z : Q'} (hz0 : (0 : Q') <= z) (hz1 : z <= (1 : Q'))
    (r p : Nat) :
    reciprocalGeometricProfile z r (p + 1) +
        reciprocalGeometricProfile z r (p + 1) <=
      reciprocalGeometricProfile z r p +
        reciprocalGeometricProfile z r (p + 2) := by
  let S := Q'.ofNat r * qpow z p
  have hS0 : (0 : Q') <= S :=
    Q'.mul_nonneg _ _ (zero_le_ofNat r) (qpow_nonneg z hz0 p)
  have hbase := invSuccGeometric_localConvex hz1 (r + p)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ S hbase hS0
  have e0 : reciprocalGeometricProfile z r p ≈
      S * Q'.invSucc (r + p) := by
    unfold reciprocalGeometricProfile S
    ring_qeqv
  have e1 : reciprocalGeometricProfile z r (p + 1) ≈
      S * (Q'.invSucc (r + p + 1) * z) := by
    unfold reciprocalGeometricProfile S
    change
      (Q'.ofNat r *
        (Q'.invSucc (r + p + 1) * (qpow z p * z))) ≈ _
    ring_qeqv
  have e2 : reciprocalGeometricProfile z r (p + 2) ≈
      S * (Q'.invSucc (r + p + 2) * (z * z)) := by
    unfold reciprocalGeometricProfile S
    change
      (Q'.ofNat r *
        (Q'.invSucc (r + p + 2) * ((qpow z p * z) * z))) ≈ _
    ring_qeqv
  have eleft :
      reciprocalGeometricProfile z r (p + 1) +
          reciprocalGeometricProfile z r (p + 1) ≈
        S * (Q'.invSucc (r + p + 1) * z +
          Q'.invSucc (r + p + 1) * z) := by
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' e1 e1) (by ring_qeqv)
  have eright :
      S * (Q'.invSucc (r + p) +
          Q'.invSucc (r + p + 2) * (z * z)) ≈
        reciprocalGeometricProfile z r p +
          reciprocalGeometricProfile z r (p + 2) := by
    exact Q'.eqv_trans _ _ _ (by ring_qeqv)
      (Q'.add_eqv_congr' (Q'.eqv_symm e0) (Q'.eqv_symm e2))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv eright))

/-- Algebraic core of the normalized physical successor profile:
`(p+2)z^p - r z^p/(r+p+1)`. -/
def successorProfileCore (z : Q') (r p : Nat) : Q' :=
  linearGeometricProfile z p + -(reciprocalGeometricProfile z r p)

/-- The linear-geometric curvature budget and reciprocal convexity combine
to give local concavity of the full normalized successor core. -/
theorem successorProfileCore_localConcavity
    {z : Q'} (hz0 : (0 : Q') <= z) (hz1 : z <= (1 : Q'))
    (r p : Nat)
    (hbudget : Q'.ofNat (p + 4) * ((1 : Q') - z) <= qtwo) :
    successorProfileCore z r p + successorProfileCore z r (p + 2) <=
      successorProfileCore z r (p + 1) +
        successorProfileCore z r (p + 1) := by
  have hlinear := linearGeometricProfile_localConcavity hz0 hz1 p hbudget
  have hrecip := reciprocalGeometricProfile_localConvex hz0 hz1 r p
  have hneg := Q'.neg_le_neg hrecip
  have hadd := Q'.add_le_add hlinear hneg
  have eleft :
      successorProfileCore z r p + successorProfileCore z r (p + 2) ≈
        (linearGeometricProfile z p + linearGeometricProfile z (p + 2)) +
          -(reciprocalGeometricProfile z r p +
            reciprocalGeometricProfile z r (p + 2)) := by
    unfold successorProfileCore
    ring_qeqv
  have eright :
      (linearGeometricProfile z (p + 1) +
          linearGeometricProfile z (p + 1)) +
          -(reciprocalGeometricProfile z r (p + 1) +
            reciprocalGeometricProfile z r (p + 1)) ≈
        successorProfileCore z r (p + 1) +
          successorProfileCore z r (p + 1) := by
    unfold successorProfileCore
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

/-- The normalized successor profile in its original coefficient form.  The
factor `(p+1)(r+p+2)/(r+p+1)` is the one produced by the weighted successor
identity before restoring the common physical heat power. -/
def normalizedSuccessorProfile (z : Q') (r p : Nat) : Q' :=
  (Q'.ofNat (p + 1) *
    (Q'.ofNat (r + p + 2) * Q'.invSucc (r + p))) * qpow z p

private theorem normalizedSuccessorCoefficient_eqv_core (r p : Nat) :
    Q'.ofNat (p + 1) *
        (Q'.ofNat (r + p + 2) * Q'.invSucc (r + p)) ≈
      Q'.ofNat (p + 2) +
        -(Q'.ofNat r * Q'.invSucc (r + p)) := by
  let P := Q'.ofNat (p + 1)
  let R := Q'.ofNat r
  let D := Q'.ofNat (r + p + 1)
  let I := Q'.invSucc (r + p)
  let B := Q'.ofNat (r + p + 2)
  have eD : D ≈ R + P := by
    unfold D R P
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
      (Q'.ofNat_add_eqv r (p + 1))
  have eB : B ≈ (R + P) + qone := by
    have eB0 : B ≈ D + qone := by
      unfold B D qone
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
        (Q'.ofNat_add_eqv (r + p + 1) 1)
    exact Q'.eqv_trans _ _ _ eB0
      (Q'.add_eqv_congr_right _ _ _ eD)
  have eDI : (R + P) * I ≈ (1 : Q') := by
    refine Q'.eqv_trans _ (D * I) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm eD)) ?_
    unfold D I
    exact Q'.ofNat_succ_mul_invSucc (r + p)
  have eP2 : P + qone ≈ Q'.ofNat (p + 2) := by
    unfold P qone
    exact Q'.eqv_symm (Q'.ofNat_add_eqv (p + 1) 1)
  have esum :
      P * (B * I) + R * I ≈ P + qone := by
    refine Q'.eqv_trans _
      (P * (((R + P) + qone) * I) + R * I) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ eB))) ?_
    refine Q'.eqv_trans _ ((P + qone) * ((R + P) * I)) _
      (by unfold qone; ring_qeqv) ?_
    exact Q'.eqv_trans _ ((P + qone) * (1 : Q')) _
      (Q'.mul_eqv_congr_left _ _ _ eDI)
      (Q'.mul_one_eqv _)
  have esub : P * (B * I) ≈ (P + qone) + -(R * I) := by
    refine Q'.eqv_trans _
      (R * I + (P * (B * I) + -(R * I))) _
      (Q'.add_sub_cancel_eqv (P * (B * I)) (R * I)) ?_
    refine Q'.eqv_trans _ ((P * (B * I) + R * I) + -(R * I)) _
      (by ring_qeqv) ?_
    exact Q'.add_eqv_congr_right _ _ _ esum
  refine Q'.eqv_trans _ (P * (B * I)) _ (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _ ((P + qone) + -(R * I)) _ esub ?_
  exact Q'.add_eqv_congr_right _ _ _ eP2

/-- The coefficient identity above identifies the original normalized
successor profile with the linear-minus-reciprocal core, without evaluating
any power or denominator. -/
theorem normalizedSuccessorProfile_eqv_core (z : Q') (r p : Nat) :
    normalizedSuccessorProfile z r p ≈ successorProfileCore z r p := by
  let Z := qpow z p
  have hcoeff := normalizedSuccessorCoefficient_eqv_core r p
  refine Q'.eqv_trans _
    ((Q'.ofNat (p + 2) +
      -(Q'.ofNat r * Q'.invSucc (r + p))) * Z) _
    (by
      unfold normalizedSuccessorProfile Z
      exact Q'.mul_eqv_congr_right _ _ _ hcoeff) ?_
  unfold successorProfileCore linearGeometricProfile reciprocalGeometricProfile Z
  ring_qeqv

/-- Local concavity in the original normalized coefficient coordinates. -/
theorem normalizedSuccessorProfile_localConcavity
    {z : Q'} (hz0 : (0 : Q') <= z) (hz1 : z <= (1 : Q'))
    (r p : Nat)
    (hbudget : Q'.ofNat (p + 4) * ((1 : Q') - z) <= qtwo) :
    normalizedSuccessorProfile z r p +
        normalizedSuccessorProfile z r (p + 2) <=
      normalizedSuccessorProfile z r (p + 1) +
        normalizedSuccessorProfile z r (p + 1) := by
  have hcore := successorProfileCore_localConcavity hz0 hz1 r p hbudget
  have ep := normalizedSuccessorProfile_eqv_core z r p
  have ep1 := normalizedSuccessorProfile_eqv_core z r (p + 1)
  have ep2 := normalizedSuccessorProfile_eqv_core z r (p + 2)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' ep ep2))
    (Q'.le_trans' _ _ _ hcore
      (Q'.le_of_eqv
        (Q'.add_eqv_congr' (Q'.eqv_symm ep1) (Q'.eqv_symm ep1))))

/-- The actual untruncated heat-successor profile at shift `r`.  Its exponent
is exactly the Casimir increment `2(r+p)+3` appearing when index `r+p` is
raised by one. -/
def heatSuccessorProfile (w : Q') (r p : Nat) : Q' :=
  (Q'.ofNat (p + 1) *
    (Q'.ofNat (r + p + 2) * Q'.invSucc (r + p))) *
      qpow w (2 * (r + p) + 3)

private theorem heatSuccessorPower_split (w : Q') (r p : Nat) :
    qpow w (2 * (r + p) + 3) ≈
      qpow w (2 * r + 3) * qpow (qpow w 2) p := by
  refine Q'.eqv_trans _ (qpow w ((2 * r + 3) + 2 * p)) _
    (Q'.eqv_of_eq (congrArg (qpow w) (by omega))) ?_
  refine Q'.eqv_trans _
    (qpow w (2 * r + 3) * qpow w (2 * p)) _
    (HeatKernelRGStep.qpow_add w (2 * r + 3) (2 * p)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (HeatKernelRGStep.qpow_qpow w 2 p))

/-- Physical heat powers factor into a common nonnegative shift power and the
normalized profile at `z=w^2`. -/
theorem heatSuccessorProfile_eqv_normalized (w : Q') (r p : Nat) :
    heatSuccessorProfile w r p ≈
      qpow w (2 * r + 3) *
        normalizedSuccessorProfile (qpow w 2) r p := by
  have epow := heatSuccessorPower_split w r p
  unfold heatSuccessorProfile normalizedSuccessorProfile
  refine Q'.eqv_trans _
    ((Q'.ofNat (p + 1) *
      (Q'.ofNat (r + p + 2) * Q'.invSucc (r + p))) *
        (qpow w (2 * r + 3) * qpow (qpow w 2) p)) _
    (Q'.mul_eqv_congr_left _ _ _ epow) ?_
  ring_qeqv

/-- The reciprocal correction in the normalized successor profile is
nonnegative on a nonnegative geometric base. -/
theorem reciprocalGeometricProfile_nonneg {z : Q'}
    (hz0 : (0 : Q') <= z) (r p : Nat) :
    (0 : Q') <= reciprocalGeometricProfile z r p := by
  unfold reciprocalGeometricProfile
  exact Q'.mul_nonneg _ _ (zero_le_ofNat r)
    (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg (r + p))
      (qpow_nonneg z hz0 p))

/-- Dropping the nonnegative reciprocal correction gives the elementary
linear-geometric majorant `(p+2)z^p`. -/
theorem normalizedSuccessorProfile_le_linear {z : Q'}
    (hz0 : (0 : Q') <= z) (r p : Nat) :
    normalizedSuccessorProfile z r p <= linearGeometricProfile z p := by
  have hrec := reciprocalGeometricProfile_nonneg hz0 r p
  have hneg : -(reciprocalGeometricProfile z r p) <= (0 : Q') := by
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hrec)
      (Q'.le_of_eqv (by decide : -(0 : Q') ≈ (0 : Q')))
  have hcore : successorProfileCore z r p <= linearGeometricProfile z p := by
    have h := Q'.add_le_add
      (Q'.le_refl' (linearGeometricProfile z p)) hneg
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv
        (Q'.eqv_of_eq (Q'.add_zero' (linearGeometricProfile z p))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedSuccessorProfile_eqv_core z r p)) hcore

/-- A denominator-free majorant for one heat-successor profile value. -/
theorem heatSuccessorProfile_le_coarse
    {w : Q'} (hw0 : (0 : Q') <= w) (r p : Nat) :
    heatSuccessorProfile w r p <=
      Q'.ofNat (p + 2) * qpow w (2 * (r + p) + 3) := by
  have hz0 : (0 : Q') <= qpow w 2 := qpow_nonneg w hw0 2
  have hnormalized := normalizedSuccessorProfile_le_linear hz0 r p
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow w (2 * r + 3)) hnormalized
    (qpow_nonneg w hw0 (2 * r + 3))
  have eleft := heatSuccessorProfile_eqv_normalized w r p
  have epow := heatSuccessorPower_split w r p
  have eright :
      qpow w (2 * r + 3) *
          linearGeometricProfile (qpow w 2) p ≈
        Q'.ofNat (p + 2) * qpow w (2 * (r + p) + 3) := by
    unfold linearGeometricProfile
    refine Q'.eqv_trans _
      (Q'.ofNat (p + 2) *
        (qpow w (2 * r + 3) * qpow (qpow w 2) p)) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm epow)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv eright))

/-- The two central successor values admit a denominator-free common-power
majorant.  The floor/ceiling coefficients add exactly to `s+4`, while both
heat exponents contain the common factor `w^(s+2+2r)`. -/
theorem centeredSuccessorPair_le_coarse
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (r s : Nat) :
    heatSuccessorProfile w r (s / 2) +
        heatSuccessorProfile w r ((s + 1) / 2) <=
      Q'.ofNat (s + 4) * qpow w (s + 2 + 2 * r) := by
  let p := s / 2
  let q := (s + 1) / 2
  let W := qpow w (s + 2 + 2 * r)
  have hp := heatSuccessorProfile_le_coarse hw0 r p
  have hq := heatSuccessorProfile_le_coarse hw0 r q
  have hep : s + 2 + 2 * r <= 2 * (r + p) + 3 := by
    unfold p
    omega
  have heq : s + 2 + 2 * r <= 2 * (r + q) + 3 := by
    unfold q
    omega
  have hwp : qpow w (2 * (r + p) + 3) <= W := by
    exact qpow_antitone hw0 hw1 _ _ hep
  have hwq : qpow w (2 * (r + q) + 3) <= W := by
    exact qpow_antitone hw0 hw1 _ _ heq
  have hpscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (p + 2)) hwp (zero_le_ofNat (p + 2))
  have hqscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (q + 2)) hwq (zero_le_ofNat (q + 2))
  have hadd := Q'.add_le_add
    (Q'.le_trans' _ _ _ hp hpscaled)
    (Q'.le_trans' _ _ _ hq hqscaled)
  have hpq : p + q = s := by
    unfold p q
    omega
  have ecoeff : Q'.ofNat (p + 2) + Q'.ofNat (q + 2) ≈
      Q'.ofNat (s + 4) := by
    refine Q'.eqv_trans _ (Q'.ofNat ((p + 2) + (q + 2))) _
      (Q'.eqv_symm (Q'.ofNat_add_eqv (p + 2) (q + 2))) ?_
    exact Q'.eqv_of_eq (congrArg Q'.ofNat (by omega))
  have eright :
      Q'.ofNat (p + 2) * W + Q'.ofNat (q + 2) * W ≈
        Q'.ofNat (s + 4) * W := by
    refine Q'.eqv_trans _
      ((Q'.ofNat (p + 2) + Q'.ofNat (q + 2)) * W) _
      (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ _ ecoeff
  simpa only [p, q, W] using
    Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright)

/-- Exact ceiling threshold for the centered payment
`physicalWeightDen k <= r*(s+2)`. -/
def physicalCenteredTailStart (k s : Nat) : Nat :=
  physicalWeightDen k / (s + 2) +
    if physicalWeightDen k % (s + 2) = 0 then 0 else 1

/-- The centered threshold pays its defining natural product exactly; this is
the sole arithmetic input needed by the centered row compiler. -/
theorem physicalCenteredTailStart_payment (k s : Nat) :
    physicalWeightDen k <= physicalCenteredTailStart k s * (s + 2) := by
  let D := physicalWeightDen k
  let S := s + 2
  have hS : 0 < S := by omega
  have hsplit := Nat.mod_add_div D S
  by_cases hrem : D % S = 0
  · have hD : D = (D / S) * S := by
      rw [hrem, Nat.zero_add] at hsplit
      rw [Nat.mul_comm]
      exact hsplit.symm
    unfold physicalCenteredTailStart
    rw [if_pos hrem, Nat.add_zero]
    simpa only [D, S] using Nat.le_of_eq hD
  · have hlt := Nat.mod_lt D hS
    have hD : D = D % S + S * (D / S) := hsplit.symm
    unfold physicalCenteredTailStart
    rw [if_neg hrem]
    change D <= (D / S + 1) * S
    calc
      D = D % S + S * (D / S) := hD
      _ <= S + S * (D / S) :=
        Nat.add_le_add_right (Nat.le_of_lt hlt) _
      _ = S * (D / S) + S := Nat.add_comm _ _
      _ = (D / S + 1) * S := by
        simp only [S, Nat.add_mul, Nat.mul_add, Nat.one_mul]
        ac_rfl

/-- The pure-Nat payment `D_k <= r(s+2)` supplies exactly the two units of
coefficient slack required by the centered pair. -/
private theorem physical_center_payment_q (k r s : Nat)
    (hpay : physicalWeightDen k <= r * (s + 2)) :
    Q'.ofNat 2 <=
      Q'.ofNat (s + 2) *
        (Q'.ofNat (2 * r) * blockMargin k) := by
  let D := physicalWeightDen k
  let P := (s + 2) * (2 * r)
  have hcross : 2 * D <= 1 * P := by
    have hscaled := Nat.mul_le_mul_left 2 hpay
    simpa only [D, P, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hscaled
  have hraw : Q'.ofNat 2 <=
      Q'.mkPos 1 D (physicalWeightDen_pos k) * Q'.ofNat P := by
    exact P2RetunedFenceIntegralCertificate.ofNat_le_mkPos_mul_of_cross
      2 P 1 D (physicalWeightDen_pos k) hcross
  have hclosed : blockMargin k ≈
      Q'.mkPos 1 D (physicalWeightDen_pos k) := by
    simpa only [D] using blockMargin_eqv_closed k
  have eP : Q'.ofNat P ≈
      Q'.ofNat (s + 2) * Q'.ofNat (2 * r) := by
    unfold P
    exact HeatKernelRGStep.ofNat_mul_eqv (s + 2) (2 * r)
  have etarget :
      Q'.mkPos 1 D (physicalWeightDen_pos k) * Q'.ofNat P ≈
        Q'.ofNat (s + 2) *
          (Q'.ofNat (2 * r) * blockMargin k) := by
    refine Q'.eqv_trans _
      (blockMargin k *
        (Q'.ofNat (s + 2) * Q'.ofNat (2 * r))) _ ?_ ?_
    · exact mul_eqv_congr
        (Q'.eqv_symm hclosed) eP
    · ring_qeqv
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv etarget)

/-- Reciprocal Bernoulli turns the pure-Nat centered payment into the exact
decay inequality needed after the common heat power has been factored out. -/
theorem physical_centeredDecay_of_payment (k r s : Nat)
    (hpay : physicalWeightDen k <= r * (s + 2)) :
    Q'.ofNat (s + 4) * qpow (blockWeight k) (2 * r) <=
      Q'.ofNat (s + 2) := by
  let u := blockMargin k
  let w := blockWeight k
  let S := Q'.ofNat (s + 2)
  let E := Q'.ofNat (s + 4)
  have htwo : Q'.ofNat 2 <= S * (Q'.ofNat (2 * r) * u) := by
    simpa only [S, u] using physical_center_payment_q k r s hpay
  have hcoeff : E <= S * bernDen u (2 * r) := by
    have hadd := Q'.add_le_add (Q'.le_refl' S) htwo
    have eleft : E ≈ S + Q'.ofNat 2 := by
      unfold E S
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega)))
        (Q'.ofNat_add_eqv (s + 2) 2)
    have eright :
        S + S * (Q'.ofNat (2 * r) * u) ≈
          S * bernDen u (2 * r) := by
      unfold bernDen
      ring_qeqv
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))
  have hw0 : (0 : Q') <= w := by
    simpa only [w] using blockWeight_nonneg k
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _
    (qpow w (2 * r)) hcoeff (qpow_nonneg w hw0 (2 * r))
  have hbern : qpow w (2 * r) * bernDen u (2 * r) <= (1 : Q') := by
    simpa only [w, u, blockWeight, oneSub] using
      oneSub_pow_mul_bernDen_le (blockMargin_nonneg k)
        (blockMargin_le_one k) (2 * r)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ S hbern
    (zero_le_ofNat (s + 2))
  have emiddle :
      (S * bernDen u (2 * r)) * qpow w (2 * r) ≈
        S * (qpow w (2 * r) * bernDen u (2 * r)) := by
    ring_qeqv
  have eend : S * (1 : Q') ≈ S := Q'.mul_one_eqv S
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv emiddle)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv eend)))

/-- Exact coefficient-level meaning of the successor profile.  Multiplying a
coefficient at index `r+p+1` by its convolution weight `p+1` is the previous
coefficient times `heatSuccessorProfile w r p`; an arbitrary spectator
coefficient is retained so this theorem matches the local reserve atom. -/
theorem coeffW_weightedSuccessor_eqv_heatSuccessorProfile
    (w : Q') (r p : Nat) (y : Q') :
    Q'.ofNat (p + 1) *
        (coeffW w (r + p + 1) * y) ≈
      (coeffW w (r + p) * y) *
        heatSuccessorProfile w r p := by
  let L := Q'.ofNat (p + 1) *
    (coeffW w (r + p + 1) * y)
  have hunit : Q'.ofNat (r + p + 1) * Q'.invSucc (r + p) ≈
      (1 : Q') := by
    exact Q'.ofNat_succ_mul_invSucc (r + p)
  have hcross := coeffW_succ_cross_eqv w (r + p)
  refine Q'.eqv_trans L ((1 : Q') * L) _
    (Q'.eqv_symm (Q'.one_mul_eqv L)) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (r + p + 1) * Q'.invSucc (r + p)) * L) _
    (Q'.mul_eqv_congr_right _ _ L (Q'.eqv_symm hunit)) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (r + p + 1) * coeffW w (r + p + 1)) *
      ((Q'.ofNat (p + 1) * Q'.invSucc (r + p)) *
        y)) _ (by unfold L; ring_qeqv) ?_
  refine Q'.eqv_trans _
    (((Q'.ofNat (r + p + 2) * qpow w (2 * (r + p) + 3)) *
        coeffW w (r + p)) *
      ((Q'.ofNat (p + 1) * Q'.invSucc (r + p)) *
        y)) _
    (Q'.mul_eqv_congr_right _ _ _ hcross) ?_
  unfold heatSuccessorProfile
  ring_qeqv

/-- The heat-successor profile is nonnegative on every nonnegative heat
weight. -/
theorem heatSuccessorProfile_nonneg {w : Q'} (hw0 : (0 : Q') <= w)
    (r p : Nat) : (0 : Q') <= heatSuccessorProfile w r p := by
  unfold heatSuccessorProfile
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (zero_le_ofNat (p + 1))
      (Q'.mul_nonneg _ _ (zero_le_ofNat (r + p + 2))
        (Q'.invSucc_nonneg (r + p))))
    (qpow_nonneg w hw0 (2 * (r + p) + 3))

/-- The coefficient/profile identity survives a sharp cutoff as an upper
bound.  It is exact in the active interior; at the terminal mask boundary
the weighted successor is zero and the profile majorant remains nonnegative. -/
theorem cutoffCoeff_weightedSuccessor_le_heatSuccessorProfile
    {w : Q'} (hw0 : (0 : Q') <= w) (N r p q : Nat) :
    Q'.ofNat (p + 1) *
        (cutoffCoeff w N r (p + 1) * cutoffCoeff w N r q) <=
      (cutoffCoeff w N r p * cutoffCoeff w N r q) *
        heatSuccessorProfile w r p := by
  by_cases hp : p + r < N + 1
  · have ep : cutoffCoeff w N r p = coeffW w (r + p) := by
      unfold cutoffCoeff
      rw [if_pos hp]
      congr 1
      omega
    by_cases hp1 : p + 1 + r < N + 1
    · have ep1 : cutoffCoeff w N r (p + 1) =
          coeffW w (r + p + 1) := by
        unfold cutoffCoeff
        rw [if_pos hp1]
        congr 1
        omega
      rw [ep, ep1]
      exact Q'.le_of_eqv
        (coeffW_weightedSuccessor_eqv_heatSuccessorProfile
          w r p (cutoffCoeff w N r q))
    · have ep1 : cutoffCoeff w N r (p + 1) = (0 : Q') := by
        unfold cutoffCoeff
        rw [if_neg hp1]
      rw [ep, ep1]
      have hright : (0 : Q') <=
          (coeffW w (r + p) * cutoffCoeff w N r q) *
            heatSuccessorProfile w r p :=
        Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 (r + p))
            (cutoffCoeff_nonneg hw0 N r q))
          (heatSuccessorProfile_nonneg hw0 r p)
      have eleft :
          Q'.ofNat (p + 1) * ((0 : Q') * cutoffCoeff w N r q) ≈
            (0 : Q') := by
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.zero_mul_eqv (cutoffCoeff w N r q)))
          (Q'.mul_zero_eqv (Q'.ofNat (p + 1)))
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv eleft) hright
  · have hp1 : ¬ p + 1 + r < N + 1 := by omega
    have ep : cutoffCoeff w N r p = (0 : Q') := by
      unfold cutoffCoeff
      rw [if_neg hp]
    have ep1 : cutoffCoeff w N r (p + 1) = (0 : Q') := by
      unfold cutoffCoeff
      rw [if_neg hp1]
    rw [ep, ep1]
    have eleft :
        Q'.ofNat (p + 1) * ((0 : Q') * cutoffCoeff w N r q) ≈
          (0 : Q') := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.zero_mul_eqv (cutoffCoeff w N r q)))
        (Q'.mul_zero_eqv (Q'.ofNat (p + 1)))
    have eright :
        (((0 : Q') * cutoffCoeff w N r q) *
          heatSuccessorProfile w r p) ≈ (0 : Q') := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.zero_mul_eqv (cutoffCoeff w N r q)))
        (Q'.zero_mul_eqv (heatSuccessorProfile w r p))
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ eleft (Q'.eqv_symm eright))

/-- Spectator-on-the-left form of the cutoff successor bound. -/
theorem cutoffCoeff_weightedRightSuccessor_le_heatSuccessorProfile
    {w : Q'} (hw0 : (0 : Q') <= w) (N r p q : Nat) :
    Q'.ofNat (p + 1) *
        (cutoffCoeff w N r q * cutoffCoeff w N r (p + 1)) <=
      (cutoffCoeff w N r q * cutoffCoeff w N r p) *
        heatSuccessorProfile w r p := by
  have h := cutoffCoeff_weightedSuccessor_le_heatSuccessorProfile
    hw0 N r p q
  have eleft :
      Q'.ofNat (p + 1) *
          (cutoffCoeff w N r q * cutoffCoeff w N r (p + 1)) ≈
        Q'.ofNat (p + 1) *
          (cutoffCoeff w N r (p + 1) * cutoffCoeff w N r q) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv (cutoffCoeff w N r q)
        (cutoffCoeff w N r (p + 1)))
  have eright :
      (cutoffCoeff w N r p * cutoffCoeff w N r q) *
          heatSuccessorProfile w r p ≈
        (cutoffCoeff w N r q * cutoffCoeff w N r p) *
          heatSuccessorProfile w r p :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv (cutoffCoeff w N r p)
        (cutoffCoeff w N r q))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv eright))

/-- Both successor directions in one cutoff convolution atom are bounded by
the base product times the sum of their two profile values. -/
theorem cutoffCoeff_successorPair_le_heatSuccessorPair
    {w : Q'} (hw0 : (0 : Q') <= w) (N r p q : Nat) :
    Q'.ofNat (p + 1) *
          (cutoffCoeff w N r (p + 1) * cutoffCoeff w N r q) +
        Q'.ofNat (q + 1) *
          (cutoffCoeff w N r p * cutoffCoeff w N r (q + 1)) <=
      (cutoffCoeff w N r p * cutoffCoeff w N r q) *
        (heatSuccessorProfile w r p + heatSuccessorProfile w r q) := by
  have hleft := cutoffCoeff_weightedSuccessor_le_heatSuccessorProfile
    hw0 N r p q
  have hright := cutoffCoeff_weightedRightSuccessor_le_heatSuccessorProfile
    hw0 N r q p
  have hadd := Q'.add_le_add hleft hright
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv
      (cutoffCoeff w N r p * cutoffCoeff w N r q)
      (heatSuccessorProfile w r p) (heatSuccessorProfile w r q))))

/-- The actual heat-successor profile is locally concave whenever the same
scalar near-one budget holds for `z=w^2`. -/
theorem heatSuccessorProfile_localConcavity
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (r p : Nat)
    (hbudget : Q'.ofNat (p + 4) *
      ((1 : Q') - qpow w 2) <= qtwo) :
    heatSuccessorProfile w r p + heatSuccessorProfile w r (p + 2) <=
      heatSuccessorProfile w r (p + 1) +
        heatSuccessorProfile w r (p + 1) := by
  let z := qpow w 2
  let K := qpow w (2 * r + 3)
  have hz0 : (0 : Q') <= z := qpow_nonneg w hw0 2
  have hz1 : z <= (1 : Q') :=
    YMGap.Continuum.HeatKernelGap.qpow_le_one hw0 hw1 2
  have hnorm := normalizedSuccessorProfile_localConcavity
    hz0 hz1 r p (by simpa only [z] using hbudget)
  have hK0 : (0 : Q') <= K := qpow_nonneg w hw0 (2 * r + 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ K hnorm hK0
  have ep := heatSuccessorProfile_eqv_normalized w r p
  have ep1 := heatSuccessorProfile_eqv_normalized w r (p + 1)
  have ep2 := heatSuccessorProfile_eqv_normalized w r (p + 2)
  have eleft :
      heatSuccessorProfile w r p + heatSuccessorProfile w r (p + 2) ≈
        K * (normalizedSuccessorProfile z r p +
          normalizedSuccessorProfile z r (p + 2)) := by
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ep ep2) (by
      unfold K z
      ring_qeqv)
  have eright :
        K * (normalizedSuccessorProfile z r (p + 1) +
          normalizedSuccessorProfile z r (p + 1)) ≈
        heatSuccessorProfile w r (p + 1) +
          heatSuccessorProfile w r (p + 1) := by
    exact Q'.eqv_trans _ _ _ (by
      unfold K z
      ring_qeqv)
      (Q'.add_eqv_congr' (Q'.eqv_symm ep1) (Q'.eqv_symm ep1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv eright))

/-- Every supported physical index satisfies the actual heat-successor
concavity inequality. -/
theorem physical_heatSuccessorProfile_localConcavity
    (k r p : Nat) (hp : p <= blockNcut k) :
    heatSuccessorProfile (blockWeight k) r p +
        heatSuccessorProfile (blockWeight k) r (p + 2) <=
      heatSuccessorProfile (blockWeight k) r (p + 1) +
        heatSuccessorProfile (blockWeight k) r (p + 1) := by
  have hb0 := physical_successor_profile_curvature_budget k p hp
  have hb : Q'.ofNat (p + 4) *
      ((1 : Q') - qpow (blockWeight k) 2) <= qtwo :=
    Q'.le_trans' _ _ _ hb0 (Q'.le_of_eqv (by unfold qtwo; ring_qeqv))
  exact heatSuccessorProfile_localConcavity
    (blockWeight_nonneg k) (blockWeight_le_one k) r p hb

/-- The physical successor profile inhabits the finite concavity compiler at
every scale and shift. -/
def physicalHeatSuccessorProfileConcaveOn (k r : Nat) :
    DiscreteConcaveProfileOn
      (heatSuccessorProfile (blockWeight k) r) (blockNcut k) where
  localConcavity p hp :=
    physical_heatSuccessorProfile_localConcavity k r p (by omega)

/-- All supported physical successor pairs are controlled by the central
one or two indices, uniformly in scale, cutoff, shift, and pair width. -/
theorem physical_heatSuccessorProfile_pair_le_centers
    (k r a d : Nat) (hN : a + d <= blockNcut k) :
    heatSuccessorProfile (blockWeight k) r a +
        heatSuccessorProfile (blockWeight k) r (a + d) <=
      heatSuccessorProfile (blockWeight k) r (a + d / 2) +
        heatSuccessorProfile (blockWeight k) r (a + (d + 1) / 2) := by
  exact (physicalHeatSuccessorProfileConcaveOn k r).pair_le_centers a d hN

/-- Order-free physical form: any two supported successor indices are bounded
by the two midpoint indices with the same total. -/
theorem physical_heatSuccessorProfile_pair_le_midpoint
    (k r a b : Nat) (ha : a <= blockNcut k) (hb : b <= blockNcut k) :
    heatSuccessorProfile (blockWeight k) r a +
        heatSuccessorProfile (blockWeight k) r b <=
      heatSuccessorProfile (blockWeight k) r ((a + b) / 2) +
        heatSuccessorProfile (blockWeight k) r ((a + b + 1) / 2) := by
  exact (physicalHeatSuccessorProfileConcaveOn k r).pair_le_midpoint
    a b ha hb

/-- The two weighted successors in a physical cutoff atom are bounded by the
base coefficient product times the two central profile values. -/
theorem physical_cutoffCoeff_successorPair_le_centered
    (k N r p q : Nat) (hp : p <= blockNcut k) (hq : q <= blockNcut k) :
    Q'.ofNat (p + 1) *
          (cutoffCoeff (blockWeight k) N r (p + 1) *
            cutoffCoeff (blockWeight k) N r q) +
        Q'.ofNat (q + 1) *
          (cutoffCoeff (blockWeight k) N r p *
            cutoffCoeff (blockWeight k) N r (q + 1)) <=
      (cutoffCoeff (blockWeight k) N r p *
          cutoffCoeff (blockWeight k) N r q) *
        (heatSuccessorProfile (blockWeight k) r ((p + q) / 2) +
          heatSuccessorProfile (blockWeight k) r ((p + q + 1) / 2)) := by
  have hpair := cutoffCoeff_successorPair_le_heatSuccessorPair
    (blockWeight_nonneg k) N r p q
  have hprofile := physical_heatSuccessorProfile_pair_le_midpoint
    k r p q hp hq
  have hbase : (0 : Q') <=
      cutoffCoeff (blockWeight k) N r p *
        cutoffCoeff (blockWeight k) N r q :=
    Q'.mul_nonneg _ _
      (cutoffCoeff_nonneg (blockWeight_nonneg k) N r p)
      (cutoffCoeff_nonneg (blockWeight_nonneg k) N r q)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (cutoffCoeff (blockWeight k) N r p *
      cutoffCoeff (blockWeight k) N r q) hprofile hbase
  exact Q'.le_trans' _ _ _ hpair hscaled

/-- The only scalar profile datum left after centering a local reserve atom. -/
def physicalCenteredSuccessorPair (k r s : Nat) : Q' :=
  heatSuccessorProfile (blockWeight k) r (s / 2) +
    heatSuccessorProfile (blockWeight k) r ((s + 1) / 2)

/-- The centered scalar certificate is discharged by the same pure-Nat
payment, now with no coefficient denominator and no row enumeration. -/
theorem physicalCenteredSuccessorPair_le_of_payment (k r s : Nat)
    (hpay : physicalWeightDen k <= r * (s + 2)) :
    physicalCenteredSuccessorPair k r s <=
      qpow (blockWeight k) (s + 2) * Q'.ofNat (s + 2) := by
  have hcoarse := centeredSuccessorPair_le_coarse
    (blockWeight_nonneg k) (blockWeight_le_one k) r s
  have hdecay := physical_centeredDecay_of_payment k r s hpay
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (blockWeight k) (s + 2)) hdecay
    (qpow_nonneg (blockWeight k) (blockWeight_nonneg k) (s + 2))
  have epow := qpow_add (blockWeight k) (s + 2) (2 * r)
  have eleft :
      Q'.ofNat (s + 4) * qpow (blockWeight k) (s + 2 + 2 * r) ≈
        qpow (blockWeight k) (s + 2) *
          (Q'.ofNat (s + 4) * qpow (blockWeight k) (2 * r)) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (s + 4) *
        (qpow (blockWeight k) (s + 2) *
          qpow (blockWeight k) (2 * r))) _
      (Q'.mul_eqv_congr_left _ _ _ epow) ?_
    ring_qeqv
  exact Q'.le_trans' _ _ _ hcoarse
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft) hscaled)

/-- On active supported indices, a bound for the two central profile values
implies nonnegativity of the exact physical local reserve atom. -/
theorem physical_autoStepReserve_nonneg_of_centered_active
    (k N r s p : Nat) (hps : p <= s)
    (hpN : p <= blockNcut k) (hqN : s - p <= blockNcut k)
    (hcenter : physicalCenteredSuccessorPair k r s <=
      qpow (blockWeight k) (s + 2) * Q'.ofNat (s + 2)) :
    (0 : Q') <= autoStepReserve
      (qpow (blockWeight k) (s + 2))
      (fun n => cutoffCoeff (blockWeight k) N r n) s p := by
  let x := fun n => cutoffCoeff (blockWeight k) N r n
  let B := x p * x (s - p)
  let S := Q'.ofNat (p + 1) * (x (p + 1) * x (s - p)) +
    Q'.ofNat (s - p + 1) * (x p * x (s - p + 1))
  let T := qpow (blockWeight k) (s + 2) * (Q'.ofNat (s + 2) * B)
  have hsucc : S <= B * physicalCenteredSuccessorPair k r s := by
    have h := physical_cutoffCoeff_successorPair_le_centered
      k N r p (s - p) hpN hqN
    simpa only [x, B, S, physicalCenteredSuccessorPair,
      show p + (s - p) = s by omega] using h
  have hB0 : (0 : Q') <= B :=
    Q'.mul_nonneg _ _
      (cutoffCoeff_nonneg (blockWeight_nonneg k) N r p)
      (cutoffCoeff_nonneg (blockWeight_nonneg k) N r (s - p))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ B hcenter hB0
  have ereorder :
      B * (qpow (blockWeight k) (s + 2) * Q'.ofNat (s + 2)) ≈ T := by
    unfold T
    ring_qeqv
  have hST : S <= T :=
    Q'.le_trans' _ _ _ hsucc
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ereorder))
  have hadd := Q'.add_le_add_right _ _ (-S) hST
  have ezero : S + -S ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv S (-S))
      (Q'.neg_add_self_eqv S)
  have hnonneg : (0 : Q') <= T + -S :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv ezero) hadd
  simpa only [autoStepReserve, x, B, S, T] using hnonneg

/-- Cutoff-complete local compiler.  If the physical cutoff `N` is supported
at scale `k`, the same centered scalar certificate proves every local atom;
outside the active coefficient rectangle the atom vanishes identically. -/
theorem physical_autoStepReserve_nonneg_of_centered
    (k N r s p : Nat) (hN : N <= blockNcut k) (hps : p <= s)
    (hcenter : physicalCenteredSuccessorPair k r s <=
      qpow (blockWeight k) (s + 2) * Q'.ofNat (s + 2)) :
    (0 : Q') <= autoStepReserve
      (qpow (blockWeight k) (s + 2))
      (fun n => cutoffCoeff (blockWeight k) N r n) s p := by
  by_cases hp : p + r < N + 1
  · by_cases hq : (s - p) + r < N + 1
    · have hpN : p <= blockNcut k := by omega
      have hqN : s - p <= blockNcut k := by omega
      exact physical_autoStepReserve_nonneg_of_centered_active
        k N r s p hps hpN hqN hcenter
    · have hq1 : ¬ (s - p + 1) + r < N + 1 := by omega
      have eq : cutoffCoeff (blockWeight k) N r (s - p) = (0 : Q') := by
        unfold cutoffCoeff
        rw [if_neg hq]
      have eq1 : cutoffCoeff (blockWeight k) N r (s - p + 1) =
          (0 : Q') := by
        unfold cutoffCoeff
        rw [if_neg hq1]
      unfold autoStepReserve
      dsimp only
      rw [eq, eq1]
      apply Q'.ge_of_eqv
      ring_qeqv
  · have hp1 : ¬ (p + 1) + r < N + 1 := by omega
    have ep : cutoffCoeff (blockWeight k) N r p = (0 : Q') := by
      unfold cutoffCoeff
      rw [if_neg hp]
    have ep1 : cutoffCoeff (blockWeight k) N r (p + 1) = (0 : Q') := by
      unfold cutoffCoeff
      rw [if_neg hp1]
    unfold autoStepReserve
    dsimp only
    rw [ep, ep1]
    apply Q'.ge_of_eqv
    ring_qeqv

/-- A finite sum is nonnegative when each term in its actual bounded prefix
is nonnegative.  Keeping the index bound in the premise is essential for
cutoff-sensitive certificate compilers. -/
theorem fsum_nonnegative_lt (f : Nat -> Q') : forall n,
    (forall i, i < n -> (0 : Q') <= f i) -> (0 : Q') <= fsum f n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      show (0 : Q') <= fsum f n + f n
      exact Q'.zero_le_add _ _
        (fsum_nonnegative_lt f n (fun i hi => h i (by omega)))
        (h n (by omega))

/-- Row-level centered-profile compiler.  A single midpoint bound proves all
`s+1` local reserve atoms and hence the exact physical high-shift row reserve.
The only cutoff hypothesis is the physical support condition `N <= blockNcut
k`; no enumeration of the row is required. -/
theorem physicalHighShiftRowReserve_nonneg_of_centered
    (k N r s : Nat) (hN : N <= blockNcut k)
    (hcenter : physicalCenteredSuccessorPair k r s <=
      qpow (blockWeight k) (s + 2) * Q'.ofNat (s + 2)) :
    (0 : Q') <= physicalHighShiftRowReserve k N s r := by
  let atoms := fun p => autoStepReserve
    (qpow (blockWeight k) (s + 2))
    (fun n => cutoffCoeff (blockWeight k) N r n) s p
  have hsum : (0 : Q') <= fsum atoms (s + 1) := by
    apply fsum_nonnegative_lt
    intro p hp
    exact physical_autoStepReserve_nonneg_of_centered
      k N r s p hN (by omega) hcenter
  have hrow := physicalHighShiftRowReserve_eq_stepSum k N s r
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hrow)

/-- Fully arithmetic row discharge.  The natural inequality
`physicalWeightDen k <= r*(s+2)` is compiled through centered concavity and
reciprocal Bernoulli into nonnegativity of the exact cutoff row reserve. -/
theorem physicalHighShiftRowReserve_nonneg_of_centerPayment
    (k N r s : Nat) (hN : N <= blockNcut k)
    (hpay : physicalWeightDen k <= r * (s + 2)) :
    (0 : Q') <= physicalHighShiftRowReserve k N s r := by
  exact physicalHighShiftRowReserve_nonneg_of_centered k N r s hN
    (physicalCenteredSuccessorPair_le_of_payment k r s hpay)

private theorem centered_le_of_reserve_nonneg {left right : Q'}
    (h : (0 : Q') <= right + -left) : left <= right := by
  have hadd := Q'.add_le_add_right _ _ left h
  have eleft : ((0 : Q') + left).eqv left :=
    Q'.eqv_of_eq (Q'.zero_add' left)
  have eright : ((right + -left) + left).eqv right := by
    exact Q'.eqv_trans _ (right + (-left + left)) _
      (Q'.add_assoc_eqv right (-left) left)
      (Q'.eqv_trans _ (right + 0) _
        (Q'.add_eqv_congr_left right _ _ (Q'.neg_add_self_eqv left))
        (Q'.eqv_of_eq (Q'.add_zero' right)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eleft))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

/-- Rectangular pure-Nat corollary of the centered payment.  With
`A = 2^k`, every channel `s+2 >= 3A` and row `r >= 4A` satisfies
`D_k <= r(s+2)`.  Unlike the exact quotient threshold, this region has fixed
row width and can be spliced directly into trapezoid arguments. -/
theorem physical_centeredRectangularPayment (k r s : Nat)
    (hs : 3 * 2 ^ k <= s + 2) (hr : 4 * 2 ^ k <= r) :
    physicalWeightDen k <= r * (s + 2) := by
  let A := 2 ^ k
  have hscaled := Nat.mul_le_mul_left (4 * A) hs
  have hden : physicalWeightDen k = (4 * A) * (3 * A) := by
    unfold physicalWeightDen
    rw [CasimirMoment.four_pow_eq]
    change (4 * 3) * (A * A) = (4 * A) * (3 * A)
    ac_rfl
  have hbase : physicalWeightDen k <= (4 * A) * (s + 2) := by
    rw [hden]
    simpa only [A] using hscaled
  have hrow := Nat.mul_le_mul_right (s + 2) hr
  exact Nat.le_trans hbase hrow

/-- Constant-width rectangular row discharge extracted from the centered
profile theorem. -/
theorem physicalHighShiftRowReserve_nonneg_centeredRectangle
    (k N r s : Nat) (hN : N <= blockNcut k)
    (hs : 3 * 2 ^ k <= s + 2) (hr : 4 * 2 ^ k <= r) :
    (0 : Q') <= physicalHighShiftRowReserve k N s r := by
  exact physicalHighShiftRowReserve_nonneg_of_centerPayment k N r s hN
    (physical_centeredRectangularPayment k r s hs hr)

/-- Inequality form of the same rectangular row certificate. -/
theorem cutoffShiftRow_physical_halfTime_centeredRectangle
    (k N r s : Nat) (hN : N <= blockNcut k)
    (hs : 3 * 2 ^ k <= s + 2) (hr : 4 * 2 ^ k <= r) :
    dimQ s * cutoffShiftRow (blockWeight k) N (s + 1) r <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * cutoffShiftRow (blockWeight k) N s r) := by
  apply centered_le_of_reserve_nonneg
  simpa only [physicalHighShiftRowReserve] using
    physicalHighShiftRowReserve_nonneg_centeredRectangle
      k N r s hN hs hr

/-- Clamp the constant rectangular row boundary `4*2^k` to the cutoff. -/
def physicalCenteredRectangleSplitStart (k N : Nat) : Nat :=
  Nat.min (4 * 2 ^ k) (N + 1)

/-- Fixed-width prefix left by the rectangular centered theorem. -/
def physicalCenteredRectangleLowShiftSum (k N t : Nat) : Q' :=
  fsum (fun r => cutoffShiftRow (blockWeight k) N t r)
    (physicalCenteredRectangleSplitStart k N)

/-- Rectangular high sector beginning at row `4*2^k`. -/
def physicalCenteredRectangleHighShiftSum (k N t : Nat) : Q' :=
  let R := physicalCenteredRectangleSplitStart k N
  fsum (fun j => cutoffShiftRow (blockWeight k) N t (R + j))
    (N + 1 - R)

theorem physicalCenteredRectangleSplitStart_le (k N : Nat) :
    physicalCenteredRectangleSplitStart k N <= N + 1 :=
  Nat.min_le_right _ _

private theorem physical_fourPow_le_rectangleSplit_add {k N j : Nat}
    (hj : j < N + 1 - physicalCenteredRectangleSplitStart k N) :
    4 * 2 ^ k <= physicalCenteredRectangleSplitStart k N + j := by
  by_cases hR : 4 * 2 ^ k <= N + 1
  · simp only [physicalCenteredRectangleSplitStart, Nat.min_eq_left hR]
    omega
  · have hNR : N + 1 <= 4 * 2 ^ k := Nat.le_of_not_ge hR
    simp only [physicalCenteredRectangleSplitStart, Nat.min_eq_right hNR] at hj
    omega

/-- Exact line-sum decomposition at the fixed rectangular row boundary. -/
theorem lineSum_eq_physicalCenteredRectangleLow_add_high
    (k N t : Nat) :
    (lineSum (lagCorr (blockWeight k) N) t).eqv
      (physicalCenteredRectangleLowShiftSum k N t +
        physicalCenteredRectangleHighShiftSum k N t) := by
  let R := physicalCenteredRectangleSplitStart k N
  have hR : R <= N + 1 := physicalCenteredRectangleSplitStart_le k N
  have hcount : R + (N + 1 - R) = N + 1 := by omega
  have hsplit := fsum_split_at
    (fun r => cutoffShiftRow (blockWeight k) N t r)
    R (N + 1 - R)
  rw [hcount] at hsplit
  exact Q'.eqv_trans _ _ _
    (lineSum_eq_cutoffShiftRows (blockWeight k) N t)
    (by
      simpa only [physicalCenteredRectangleLowShiftSum,
        physicalCenteredRectangleHighShiftSum, R] using hsplit)

/-- Aggregate rectangular theorem: above channel `3*2^k-2`, every supported
cutoff leaves at most the fixed prefix `r < 4*2^k`. -/
theorem physicalCenteredRectangleHighShiftSum_halfTime
    (k N s : Nat) (hN : N <= blockNcut k)
    (hs : 3 * 2 ^ k <= s + 2) :
    dimQ s * physicalCenteredRectangleHighShiftSum k N (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) *
          physicalCenteredRectangleHighShiftSum k N s) := by
  let R := physicalCenteredRectangleSplitStart k N
  let L := N + 1 - R
  let q := qpow (blockWeight k) (s + 2)
  have hterms :
      fsum (fun j => dimQ s *
        cutoffShiftRow (blockWeight k) N (s + 1) (R + j)) L <=
      fsum (fun j => q * (dimQ (s + 1) *
        cutoffShiftRow (blockWeight k) N s (R + j))) L := by
    apply fsum_mono_lt
    intro j hj
    exact cutoffShiftRow_physical_halfTime_centeredRectangle
      k N (R + j) s hN hs
        (physical_fourPow_le_rectangleSplit_add
          (by simpa only [R, L] using hj))
  have eleft :
      (dimQ s * physicalCenteredRectangleHighShiftSum k N (s + 1)).eqv
        (fsum (fun j => dimQ s *
          cutoffShiftRow (blockWeight k) N (s + 1) (R + j)) L) := by
    unfold physicalCenteredRectangleHighShiftSum
    simpa only [R, L] using
      fsum_const_mul (dimQ s)
        (fun j => cutoffShiftRow (blockWeight k) N (s + 1) (R + j)) L
  have eright :
      (fsum (fun j => q * (dimQ (s + 1) *
        cutoffShiftRow (blockWeight k) N s (R + j))) L).eqv
        (q * (dimQ (s + 1) *
          physicalCenteredRectangleHighShiftSum k N s)) := by
    refine Q'.eqv_trans _
      (q * fsum (fun j => dimQ (s + 1) *
        cutoffShiftRow (blockWeight k) N s (R + j)) L) _
      (Q'.eqv_symm (fsum_const_mul q _ L)) ?_
    apply Q'.mul_eqv_congr_left q
    refine Q'.eqv_trans _
      (dimQ (s + 1) * fsum (fun j =>
        cutoffShiftRow (blockWeight k) N s (R + j)) L) _
      (Q'.eqv_symm (fsum_const_mul (dimQ (s + 1)) _ L)) ?_
    apply Q'.mul_eqv_congr_left (dimQ (s + 1))
    unfold physicalCenteredRectangleHighShiftSum
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hterms (Q'.le_of_eqv eright))

/-- Pointwise upper-channel splice.  Once the fixed prefix `r < 4*2^k` is
controlled, the rectangular centered theorem closes the complete physical
line-sum cell. -/
theorem physicalLineSum_halfTime_of_centeredRectangleLow
    (k N s : Nat) (hN : N <= blockNcut k)
    (hs : 3 * 2 ^ k <= s + 2)
    (hlow :
      dimQ s * physicalCenteredRectangleLowShiftSum k N (s + 1) <=
        qpow (blockWeight k) (s + 2) *
          (dimQ (s + 1) *
            physicalCenteredRectangleLowShiftSum k N s)) :
    dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * lineSum (lagCorr (blockWeight k) N) s) := by
  let q := qpow (blockWeight k) (s + 2)
  let low1 := physicalCenteredRectangleLowShiftSum k N (s + 1)
  let high1 := physicalCenteredRectangleHighShiftSum k N (s + 1)
  let low0 := physicalCenteredRectangleLowShiftSum k N s
  let high0 := physicalCenteredRectangleHighShiftSum k N s
  have hsum := Q'.add_le_add hlow
    (physicalCenteredRectangleHighShiftSum_halfTime k N s hN hs)
  have eleft :
      (dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1)).eqv
        (dimQ s * low1 + dimQ s * high1) := by
    refine Q'.eqv_trans _ (dimQ s * (low1 + high1)) _
      (Q'.mul_eqv_congr_left (dimQ s) _ _ (by
        simpa only [low1, high1] using
          lineSum_eq_physicalCenteredRectangleLow_add_high
            k N (s + 1))) ?_
    exact Q'.mul_add_eqv _ _ _
  have eright :
      (q * (dimQ (s + 1) * low0) +
        q * (dimQ (s + 1) * high0)).eqv
        (q * (dimQ (s + 1) *
          lineSum (lagCorr (blockWeight k) N) s)) := by
    refine Q'.eqv_trans _
      (q * (dimQ (s + 1) * low0 + dimQ (s + 1) * high0)) _
      (Q'.eqv_symm (Q'.mul_add_eqv q _ _)) ?_
    apply Q'.mul_eqv_congr_left q
    refine Q'.eqv_trans _ (dimQ (s + 1) * (low0 + high0)) _
      (Q'.eqv_symm (Q'.mul_add_eqv (dimQ (s + 1)) low0 high0)) ?_
    apply Q'.mul_eqv_congr_left (dimQ (s + 1))
    simpa only [low0, high0] using
      Q'.eqv_symm
        (lineSum_eq_physicalCenteredRectangleLow_add_high k N s)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv eright))

/-- Every row at or above the explicit centered threshold is discharged at
every supported cutoff.  This exposes the new analytic region directly to
later low/high splices. -/
theorem physicalHighShiftRowReserve_nonneg_centeredTail
    (k N r s : Nat) (hN : N <= blockNcut k)
    (hr : physicalCenteredTailStart k s <= r) :
    (0 : Q') <= physicalHighShiftRowReserve k N s r := by
  have hscaled := Nat.mul_le_mul_right (s + 2) hr
  have hpay : physicalWeightDen k <= r * (s + 2) :=
    Nat.le_trans (physicalCenteredTailStart_payment k s) hscaled
  exact physicalHighShiftRowReserve_nonneg_of_centerPayment
    k N r s hN hpay

/-! ## Centered all-cutoff high-sector aggregation -/

/-- Clamp the centered analytic threshold to the finite cutoff row range. -/
def physicalCenteredSplitStart (k N s : Nat) : Nat :=
  Nat.min (physicalCenteredTailStart k s) (N + 1)

/-- Rows below the centered threshold.  This is the only residual sector left
after the symbolic centered-profile compiler has run. -/
def physicalCenteredLowShiftSum (k N s t : Nat) : Q' :=
  fsum (fun r => cutoffShiftRow (blockWeight k) N t r)
    (physicalCenteredSplitStart k N s)

/-- Rows at or above the centered threshold. -/
def physicalCenteredHighShiftSum (k N s t : Nat) : Q' :=
  let R := physicalCenteredSplitStart k N s
  fsum (fun j => cutoffShiftRow (blockWeight k) N t (R + j))
    (N + 1 - R)

theorem physicalCenteredSplitStart_le (k N s : Nat) :
    physicalCenteredSplitStart k N s <= N + 1 :=
  Nat.min_le_right _ _

private theorem physicalCenteredTailStart_le_split_add {k N s j : Nat}
    (hj : j < N + 1 - physicalCenteredSplitStart k N s) :
    physicalCenteredTailStart k s <=
      physicalCenteredSplitStart k N s + j := by
  by_cases hT : physicalCenteredTailStart k s <= N + 1
  · simp only [physicalCenteredSplitStart, Nat.min_eq_left hT]
    omega
  · have hNT : N + 1 <= physicalCenteredTailStart k s :=
      Nat.le_of_not_ge hT
    simp only [physicalCenteredSplitStart, Nat.min_eq_right hNT] at hj
    omega

/-- Exact low/high decomposition at the centered threshold. -/
theorem lineSum_eq_physicalCenteredLow_add_high (k N s t : Nat) :
    (lineSum (lagCorr (blockWeight k) N) t).eqv
      (physicalCenteredLowShiftSum k N s t +
        physicalCenteredHighShiftSum k N s t) := by
  let R := physicalCenteredSplitStart k N s
  have hR : R <= N + 1 := physicalCenteredSplitStart_le k N s
  have hcount : R + (N + 1 - R) = N + 1 := by omega
  have hsplit := fsum_split_at
    (fun r => cutoffShiftRow (blockWeight k) N t r)
    R (N + 1 - R)
  rw [hcount] at hsplit
  exact Q'.eqv_trans _ _ _
    (lineSum_eq_cutoffShiftRows (blockWeight k) N t)
    (by
      simpa only [physicalCenteredLowShiftSum,
        physicalCenteredHighShiftSum, R] using hsplit)

/-- Signed reserve of the complete centered high sector. -/
def physicalCenteredHighShiftReserve (k N s : Nat) : Q' :=
  qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * physicalCenteredHighShiftSum k N s s) +
    -(dimQ s * physicalCenteredHighShiftSum k N s (s + 1))

/-- The centered high reserve as a finite list of the exact physical row
reserves. -/
def physicalCenteredHighShiftRowReserveSum (k N s : Nat) : Q' :=
  let R := physicalCenteredSplitStart k N s
  fsum (fun j => physicalHighShiftRowReserve k N s (R + j))
    (N + 1 - R)

/-- Every term in the centered high sector is discharged symbolically, so its
aggregate reserve is nonnegative at every supported cutoff. -/
theorem physicalCenteredHighShiftRowReserveSum_nonneg
    (k N s : Nat) (hN : N <= blockNcut k) :
    (0 : Q') <= physicalCenteredHighShiftRowReserveSum k N s := by
  unfold physicalCenteredHighShiftRowReserveSum
  apply fsum_nonnegative_lt
  intro j hj
  exact physicalHighShiftRowReserve_nonneg_centeredTail
    k N (physicalCenteredSplitStart k N s + j) s hN
      (physicalCenteredTailStart_le_split_add hj)

/-- Summing the centered row reserves reconstructs the signed reserve of the
centered high-shift sum exactly. -/
theorem physicalCenteredHighShiftRowReserveSum_eq_reserve (k N s : Nat) :
    (physicalCenteredHighShiftRowReserveSum k N s).eqv
      (physicalCenteredHighShiftReserve k N s) := by
  let R := physicalCenteredSplitStart k N s
  let L := N + 1 - R
  let q := qpow (blockWeight k) (s + 2)
  let d0 := dimQ (s + 1)
  let d1 := dimQ s
  let row0 := fun j => cutoffShiftRow (blockWeight k) N s (R + j)
  let row1 := fun j => cutoffShiftRow (blockWeight k) N (s + 1) (R + j)
  have ed0 : (d0 * physicalCenteredHighShiftSum k N s s).eqv
      (fsum (fun j => d0 * row0 j) L) := by
    unfold physicalCenteredHighShiftSum
    simpa only [R, L, d0, row0] using fsum_const_mul d0 row0 L
  have eq0 : (q * (d0 * physicalCenteredHighShiftSum k N s s)).eqv
      (fsum (fun j => q * (d0 * row0 j)) L) := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ ed0)
      (fsum_const_mul q (fun j => d0 * row0 j) L)
  have ed1 : (d1 * physicalCenteredHighShiftSum k N s (s + 1)).eqv
      (fsum (fun j => d1 * row1 j) L) := by
    unfold physicalCenteredHighShiftSum
    simpa only [R, L, d1, row1] using fsum_const_mul d1 row1 L
  have eneg : (fsum (fun j => -(d1 * row1 j)) L).eqv
      (-(d1 * physicalCenteredHighShiftSum k N s (s + 1))) := by
    exact Q'.eqv_trans _ _ _ (fsum_neg (fun j => d1 * row1 j) L)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm ed1))
  unfold physicalCenteredHighShiftRowReserveSum physicalHighShiftRowReserve
  dsimp only
  exact Q'.eqv_trans _ _ _
    (fsum_add (fun j => q * (d0 * row0 j))
      (fun j => -(d1 * row1 j)) L)
    (Q'.eqv_trans _
      (q * (d0 * physicalCenteredHighShiftSum k N s s) +
        -(d1 * physicalCenteredHighShiftSum k N s (s + 1))) _
      (Q'.add_eqv_congr' (Q'.eqv_symm eq0) eneg)
      (by
        unfold physicalCenteredHighShiftReserve
        exact Q'.eqv_refl _))

/-- The entire centered high sector has nonnegative physical reserve. -/
theorem physicalCenteredHighShiftReserve_nonneg
    (k N s : Nat) (hN : N <= blockNcut k) :
    (0 : Q') <= physicalCenteredHighShiftReserve k N s := by
  exact Q'.le_trans' _ _ _
    (physicalCenteredHighShiftRowReserveSum_nonneg k N s hN)
    (Q'.le_of_eqv
      (physicalCenteredHighShiftRowReserveSum_eq_reserve k N s))

/-- Aggregate half-time inequality on the centered high sector, uniform in
the cutoff.  This is the form consumed by the remaining low/high splice. -/
theorem physicalCenteredHighShiftSum_halfTime
    (k N s : Nat) (hN : N <= blockNcut k) :
    dimQ s * physicalCenteredHighShiftSum k N s (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * physicalCenteredHighShiftSum k N s s) := by
  apply centered_le_of_reserve_nonneg
  simpa only [physicalCenteredHighShiftReserve] using
    physicalCenteredHighShiftReserve_nonneg k N s hN

/-! ## Best available symbolic tail and the all-scale consumer -/

/-- Pointwise minimum of the original product threshold and the new centered
threshold.  This retains whichever symbolic argument removes more rows in a
given channel. -/
def physicalBestTailStart (k s : Nat) : Nat :=
  Nat.min (physicalTailStart k s) (physicalCenteredTailStart k s)

/-- Every row above the best of the two proved thresholds is discharged. -/
theorem physicalHighShiftRowReserve_nonneg_bestTail
    (k N r s : Nat) (hN : N <= blockNcut k)
    (hr : physicalBestTailStart k s <= r) :
    (0 : Q') <= physicalHighShiftRowReserve k N s r := by
  by_cases h : physicalTailStart k s <= physicalCenteredTailStart k s
  · have htail : physicalTailStart k s <= r := by
      simpa only [physicalBestTailStart, Nat.min_eq_left h] using hr
    exact physicalHighShiftRowReserve_nonneg k N s r htail
  · have hc : physicalCenteredTailStart k s <= physicalTailStart k s :=
      Nat.le_of_not_ge h
    have htail : physicalCenteredTailStart k s <= r := by
      simpa only [physicalBestTailStart, Nat.min_eq_right hc] using hr
    exact physicalHighShiftRowReserve_nonneg_centeredTail k N r s hN htail

/-- Clamp the best symbolic threshold to the finite cutoff. -/
def physicalBestSplitStart (k N s : Nat) : Nat :=
  Nat.min (physicalBestTailStart k s) (N + 1)

def physicalBestLowShiftSum (k N s t : Nat) : Q' :=
  fsum (fun r => cutoffShiftRow (blockWeight k) N t r)
    (physicalBestSplitStart k N s)

def physicalBestHighShiftSum (k N s t : Nat) : Q' :=
  let R := physicalBestSplitStart k N s
  fsum (fun j => cutoffShiftRow (blockWeight k) N t (R + j))
    (N + 1 - R)

theorem physicalBestSplitStart_le (k N s : Nat) :
    physicalBestSplitStart k N s <= N + 1 :=
  Nat.min_le_right _ _

/-- Exact line-sum split at the pointwise best proved threshold. -/
theorem lineSum_eq_physicalBestLow_add_high (k N s t : Nat) :
    (lineSum (lagCorr (blockWeight k) N) t).eqv
      (physicalBestLowShiftSum k N s t +
        physicalBestHighShiftSum k N s t) := by
  let R := physicalBestSplitStart k N s
  have hR : R <= N + 1 := physicalBestSplitStart_le k N s
  have hcount : R + (N + 1 - R) = N + 1 := by omega
  have hsplit := fsum_split_at
    (fun r => cutoffShiftRow (blockWeight k) N t r)
    R (N + 1 - R)
  rw [hcount] at hsplit
  exact Q'.eqv_trans _ _ _
    (lineSum_eq_cutoffShiftRows (blockWeight k) N t)
    (by
      simpa only [physicalBestLowShiftSum, physicalBestHighShiftSum, R]
        using hsplit)

/-- The best-tail aggregate inherits the corresponding checked high-sector
theorem, with no new arithmetic certificate. -/
theorem physicalBestHighShiftSum_halfTime
    (k N s : Nat) (hN : N <= blockNcut k) :
    dimQ s * physicalBestHighShiftSum k N s (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * physicalBestHighShiftSum k N s s) := by
  by_cases h : physicalTailStart k s <= physicalCenteredTailStart k s
  · simpa only [physicalBestHighShiftSum, physicalBestSplitStart,
      physicalBestTailStart, Nat.min_eq_left h, physicalHighShiftSum,
      physicalSplitStart] using physicalHighShiftSum_halfTime k N s
  · have hc : physicalCenteredTailStart k s <= physicalTailStart k s :=
      Nat.le_of_not_ge h
    simpa only [physicalBestHighShiftSum, physicalBestSplitStart,
      physicalBestTailStart, Nat.min_eq_right hc,
      physicalCenteredHighShiftSum, physicalCenteredSplitStart] using
        physicalCenteredHighShiftSum_halfTime k N s hN

/-- Signed debt of the residual prefix left by the pointwise best symbolic
tail theorem. -/
def physicalBestLowShiftDebt (k N s : Nat) : Q' :=
  dimQ s * physicalBestLowShiftSum k N s (s + 1) +
    -(qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * physicalBestLowShiftSum k N s s))

/-- Signed surplus of the pointwise best high sector. -/
def physicalBestHighShiftReserve (k N s : Nat) : Q' :=
  qpow (blockWeight k) (s + 2) *
      (dimQ (s + 1) * physicalBestHighShiftSum k N s s) +
    -(dimQ s * physicalBestHighShiftSum k N s (s + 1))

theorem physicalBestHighShiftReserve_nonneg
    (k N s : Nat) (hN : N <= blockNcut k) :
    (0 : Q') <= physicalBestHighShiftReserve k N s := by
  let highL := dimQ s * physicalBestHighShiftSum k N s (s + 1)
  let highR := qpow (blockWeight k) (s + 2) *
    (dimQ (s + 1) * physicalBestHighShiftSum k N s s)
  have hadd := Q'.add_le_add_right _ _ (-highL)
    (physicalBestHighShiftSum_halfTime k N s hN)
  have eleft : (highL + -highL).eqv (0 : Q') := by
    exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv highL (-highL))
      (Q'.neg_add_self_eqv highL)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eleft)
    (by
      simpa only [physicalBestHighShiftReserve, highL, highR] using hadd)

private theorem best_balance_of_debt_le_reserve
    {lowL lowR highL highR : Q'}
    (h : lowL + -lowR <= highR + -highL) :
    lowL + highL <= lowR + highR := by
  have hadd := Q'.add_le_add_right _ _ (lowR + highL) h
  have eleft : ((lowL + -lowR) + (lowR + highL)).eqv
      (lowL + highL) := by
    refine Q'.eqv_trans _ (lowL + ((-lowR + lowR) + highL)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv lowL (-lowR) (lowR + highL))
        (Q'.add_eqv_congr_left lowL _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (-lowR) lowR highL)))
    · exact Q'.eqv_trans _ (lowL + ((0 : Q') + highL)) _
        (Q'.add_eqv_congr_left lowL _ _
          (Q'.add_eqv_congr_right _ _ highL
            (Q'.neg_add_self_eqv lowR)))
        (Q'.add_eqv_congr_left lowL _ _
          (Q'.eqv_of_eq (Q'.zero_add' highL)))
  have eright : ((highR + -highL) + (lowR + highL)).eqv
      (lowR + highR) := by
    refine Q'.eqv_trans _ (highR + ((-highL + lowR) + highL)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv highR (-highL) (lowR + highL))
        (Q'.add_eqv_congr_left highR _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (-highL) lowR highL)))
    · refine Q'.eqv_trans _ (highR + (lowR + (-highL + highL))) _ ?_ ?_
      · apply Q'.add_eqv_congr_left highR
        exact Q'.eqv_trans _ ((lowR + -highL) + highL) _
          (Q'.add_eqv_congr_right _ _ highL
            (Q'.add_comm_eqv (-highL) lowR))
          (Q'.add_assoc_eqv lowR (-highL) highL)
      · exact Q'.eqv_trans _ (highR + lowR) _
          (Q'.add_eqv_congr_left highR _ _
            (Q'.eqv_trans _ (lowR + 0) _
              (Q'.add_eqv_congr_left lowR _ _
                (Q'.neg_add_self_eqv highL))
              (Q'.eqv_of_eq (Q'.add_zero' lowR))))
          (Q'.add_comm_eqv highR lowR)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eleft))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eright))

 /-- One pointwise low-debt/high-reserve certificate closes the corresponding
physical line-sum cell.  This form lets later compilers choose a different
residual geometry in different channel regions without rebuilding an
all-channel carrier first. -/
theorem physicalLineSum_halfTime_of_bestLowHighReserve
    (k N s : Nat)
    (hreserve :
      physicalBestLowShiftDebt k N s <=
        physicalBestHighShiftReserve k N s) :
    dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * lineSum (lagCorr (blockWeight k) N) s) := by
    let q := qpow (blockWeight k) (s + 2)
    let lowL := dimQ s * physicalBestLowShiftSum k N s (s + 1)
    let lowR := q * (dimQ (s + 1) * physicalBestLowShiftSum k N s s)
    let highL := dimQ s * physicalBestHighShiftSum k N s (s + 1)
    let highR := q * (dimQ (s + 1) * physicalBestHighShiftSum k N s s)
    have hbalance : lowL + highL <= lowR + highR :=
      best_balance_of_debt_le_reserve (by
        simpa only [physicalBestLowShiftDebt,
          physicalBestHighShiftReserve, lowL, lowR, highL, highR, q] using
            hreserve)
    have eleft :
        (dimQ s * lineSum (lagCorr (blockWeight k) N) (s + 1)).eqv
          (lowL + highL) := by
      refine Q'.eqv_trans _
        (dimQ s * (physicalBestLowShiftSum k N s (s + 1) +
          physicalBestHighShiftSum k N s (s + 1))) _
        (Q'.mul_eqv_congr_left (dimQ s) _ _
          (lineSum_eq_physicalBestLow_add_high k N s (s + 1))) ?_
      simpa only [lowL, highL] using Q'.mul_add_eqv (dimQ s)
        (physicalBestLowShiftSum k N s (s + 1))
        (physicalBestHighShiftSum k N s (s + 1))
    have eright : (lowR + highR).eqv
        (q * (dimQ (s + 1) *
          lineSum (lagCorr (blockWeight k) N) s)) := by
      refine Q'.eqv_trans _
        (q * (dimQ (s + 1) * physicalBestLowShiftSum k N s s +
          dimQ (s + 1) * physicalBestHighShiftSum k N s s)) _ ?_ ?_
      · simpa only [lowR, highR] using
          Q'.eqv_symm (Q'.mul_add_eqv q
            (dimQ (s + 1) * physicalBestLowShiftSum k N s s)
            (dimQ (s + 1) * physicalBestHighShiftSum k N s s))
      · apply Q'.mul_eqv_congr_left q
        refine Q'.eqv_trans _
          (dimQ (s + 1) *
            (physicalBestLowShiftSum k N s s +
              physicalBestHighShiftSum k N s s)) _
          (Q'.eqv_symm (Q'.mul_add_eqv (dimQ (s + 1)) _ _)) ?_
        apply Q'.mul_eqv_congr_left (dimQ (s + 1))
        exact Q'.eqv_symm (lineSum_eq_physicalBestLow_add_high k N s s)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hbalance (Q'.le_of_eqv eright))

/-- Sharp remaining datum after taking the better of the two symbolic tail
arguments channel by channel. -/
structure P2PhysicalBestLowHighReserve (k N : Nat) : Type where
  reserve : forall s, 1 <= s -> s < 2 * N ->
    physicalBestLowShiftDebt k N s <= physicalBestHighShiftReserve k N s

/-- The minimized residual compiles directly to the physical line-sum ratio. -/
def P2PhysicalBestLowHighReserve.toLineSum {k N : Nat}
    (T : P2PhysicalBestLowHighReserve k N) :
    P2HalfTimeLineSumTailRatio N (blockWeight k) where
  tail := fun s hs hsN =>
    physicalLineSum_halfTime_of_bestLowHighReserve
      k N s (T.reserve s hs hsN)

/-- Schedule-wide minimized residual beginning after the checked finite
physical prefix. -/
structure BlockCompatibleP2BestLowHighReserveFromFour : Type where
  reserve : forall k, 4 <= k ->
    P2PhysicalBestLowHighReserve k (blockNcut k)

def BlockCompatibleP2BestLowHighReserveFromFour.toLineSumTail
    (T : BlockCompatibleP2BestLowHighReserveFromFour) :
    P2BlockCompatibleHalfTimeRatioCompiler.BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => (T.reserve k hk).toLineSum

/-- Compile the minimized residual to the common all-scale coefficient datum
used by the physical spectrum and blocking-map frontier. -/
def BlockCompatibleP2BestLowHighReserveFromFour.toCoeffTailData
    (T : BlockCompatibleP2BestLowHighReserveFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-- End-to-end compiler from the minimized exact residual to the reviewed
all-scale positive-exponent canonical bulk-control family. -/
def BlockCompatibleP2BestLowHighReserveFromFour.toControlFamily
    (T : BlockCompatibleP2BestLowHighReserveFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLineSumTail.toControlFamily

/-! ## Fixed-width upper-channel residual -/

/-- Region-split residual after the rectangular centered theorem.  Below the
upper-channel threshold it retains the pointwise best low/high balance.  At
and above that threshold it asks only for the fixed prefix `r < 4 * 2^k`;
the entire remaining cutoff-dependent row range is already a theorem. -/
structure P2PhysicalCenteredRectangleResidual (k N : Nat) : Type where
  lower : forall s, 1 <= s -> s < 2 * N -> s + 2 < 3 * 2 ^ k ->
    physicalBestLowShiftDebt k N s <= physicalBestHighShiftReserve k N s
  upper : forall s, 1 <= s -> s < 2 * N -> 3 * 2 ^ k <= s + 2 ->
    dimQ s * physicalCenteredRectangleLowShiftSum k N (s + 1) <=
      qpow (blockWeight k) (s + 2) *
        (dimQ (s + 1) * physicalCenteredRectangleLowShiftSum k N s)

/-- Compile the region-split residual to the complete physical line-sum
ratio.  The upper branch invokes the rectangular theorem, while the lower
branch invokes the pointwise best-tail balance. -/
def P2PhysicalCenteredRectangleResidual.toLineSum {k N : Nat}
    (T : P2PhysicalCenteredRectangleResidual k N)
    (hN : N <= blockNcut k) :
    P2HalfTimeLineSumTailRatio N (blockWeight k) where
  tail := fun s hs hsN => by
    by_cases hupper : 3 * 2 ^ k <= s + 2
    · exact physicalLineSum_halfTime_of_centeredRectangleLow k N s hN hupper
        (T.upper s hs hsN hupper)
    · exact physicalLineSum_halfTime_of_bestLowHighReserve k N s
        (T.lower s hs hsN (Nat.lt_of_not_ge hupper))

/-- Schedule-wide region-split coefficient residual beginning after the
checked finite physical prefix. -/
structure BlockCompatibleP2CenteredRectangleResidualFromFour : Type where
  residual : forall k, 4 <= k ->
    P2PhysicalCenteredRectangleResidual k (blockNcut k)

def BlockCompatibleP2CenteredRectangleResidualFromFour.toLineSumTail
    (T : BlockCompatibleP2CenteredRectangleResidualFromFour) :
    P2BlockCompatibleHalfTimeRatioCompiler.BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => (T.residual k hk).toLineSum (Nat.le_refl _)

/-- Compile the region-split residual to the common all-scale coefficient
datum used by the physical spectrum and blocking-map frontier. -/
def BlockCompatibleP2CenteredRectangleResidualFromFour.toCoeffTailData
    (T : BlockCompatibleP2CenteredRectangleResidualFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-- End-to-end positive-exponent control-family compiler from the
region-split residual. -/
def BlockCompatibleP2CenteredRectangleResidualFromFour.toControlFamily
    (T : BlockCompatibleP2CenteredRectangleResidualFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLineSumTail.toControlFamily

end YMGap.Continuum.P2HalfTimeCenteredProfile

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfile.forwardDifference_antitone
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfile.inward_exchange
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfile.pair_le_centers
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfileOn.forwardDifference_antitone
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfileOn.inward_exchange
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfileOn.pair_le_centers
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.DiscreteConcaveProfileOn.pair_le_midpoint
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.blockNcut_add_four_le_physicalWeightDen
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_successor_profile_curvature_budget
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.linearGeometricProfile_localConcavity
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.invSuccGeometric_localConvex
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.reciprocalGeometricProfile_localConvex
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.successorProfileCore_localConcavity
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.normalizedSuccessorProfile_eqv_core
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.normalizedSuccessorProfile_localConcavity
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.heatSuccessorProfile_eqv_normalized
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.reciprocalGeometricProfile_nonneg
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.normalizedSuccessorProfile_le_linear
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.heatSuccessorProfile_le_coarse
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.centeredSuccessorPair_le_coarse
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredTailStart_payment
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_centeredDecay_of_payment
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.coeffW_weightedSuccessor_eqv_heatSuccessorProfile
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.heatSuccessorProfile_nonneg
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.cutoffCoeff_weightedSuccessor_le_heatSuccessorProfile
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.cutoffCoeff_weightedRightSuccessor_le_heatSuccessorProfile
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.cutoffCoeff_successorPair_le_heatSuccessorPair
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.heatSuccessorProfile_localConcavity
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_heatSuccessorProfile_localConcavity
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_heatSuccessorProfile_pair_le_centers
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_heatSuccessorProfile_pair_le_midpoint
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_cutoffCoeff_successorPair_le_centered
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredSuccessorPair_le_of_payment
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_autoStepReserve_nonneg_of_centered_active
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_autoStepReserve_nonneg_of_centered
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.fsum_nonnegative_lt
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalHighShiftRowReserve_nonneg_of_centered
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalHighShiftRowReserve_nonneg_of_centerPayment
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physical_centeredRectangularPayment
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalHighShiftRowReserve_nonneg_centeredRectangle
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.cutoffShiftRow_physical_halfTime_centeredRectangle
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.lineSum_eq_physicalCenteredRectangleLow_add_high
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredRectangleHighShiftSum_halfTime
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalLineSum_halfTime_of_centeredRectangleLow
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalHighShiftRowReserve_nonneg_centeredTail
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.lineSum_eq_physicalCenteredLow_add_high
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredHighShiftRowReserveSum_nonneg
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredHighShiftRowReserveSum_eq_reserve
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredHighShiftReserve_nonneg
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalCenteredHighShiftSum_halfTime
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalHighShiftRowReserve_nonneg_bestTail
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.lineSum_eq_physicalBestLow_add_high
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalBestHighShiftSum_halfTime
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalBestHighShiftReserve_nonneg
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.physicalLineSum_halfTime_of_bestLowHighReserve
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.P2PhysicalBestLowHighReserve.toLineSum
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.BlockCompatibleP2BestLowHighReserveFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.BlockCompatibleP2BestLowHighReserveFromFour.toControlFamily
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.P2PhysicalCenteredRectangleResidual.toLineSum
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.BlockCompatibleP2CenteredRectangleResidualFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2HalfTimeCenteredProfile.BlockCompatibleP2CenteredRectangleResidualFromFour.toControlFamily
