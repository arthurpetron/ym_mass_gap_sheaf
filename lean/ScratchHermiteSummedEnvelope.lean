import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
import YMGap.Continuum.RDThetaCentered
import YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail

namespace YMGap.Continuum.ScratchHermiteSummedEnvelope

set_option maxHeartbeats 200000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RDThetaCentered
open YMGap.Continuum.MovingCutoff

local infix:50 " ≈ " => Q'.eqv

private theorem envelope_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "envelope_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               envelope_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private def pMassNetL : PE :=
  let M : PE := .var 0
  let A : PE := .var 1
  let W : PE := .var 2
  let C : PE := .var 3
  let S : PE := .var 4
  let Jp : PE := .var 5
  let Jn : PE := .var 6
  .add M
    (.add
      (.add (.mul A (.mul W C))
        (.neg (.add (.mul (.mul W S) Jp) (.neg (.mul W Jn)))))
      (.neg M))

private def pMassNetR : PE :=
  let A : PE := .var 1
  let W : PE := .var 2
  let C : PE := .var 3
  let S : PE := .var 4
  let Jp : PE := .var 5
  let Jn : PE := .var 6
  .mul W (.add (.mul A C) (.neg (.add (.mul S Jp) (.neg Jn))))

private theorem pMassNet_normal :
    RingNormaliser.normalize pMassNetL =
      RingNormaliser.normalize pMassNetR := by decide

private theorem massNet_algebra (M A W C S Jp Jn : Q') :
    M + (A * (W * C) + -((W * S) * Jp + -(W * Jn)) + -M) ≈
      W * (A * C + -(S * Jp + -Jn)) := by
  simpa [pMassNetL, pMassNetR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pMassNetL pMassNetR pMassNet_normal
      (fun | 0 => M | 1 => A | 2 => W | 3 => C | 4 => S | 5 => Jp | _ => Jn))

def fastQuadraticCoeff (m : Nat) : Nat := m * (m - 1) / 2

def fastTaylorFactor (k n : Nat) : Q' :=
  lowerSixWeightDriftFloor k n +
    Q'.ofNat (fastQuadraticCoeff (n * n)) *
      (lowerSixDriftExcess k * lowerSixDriftExcess k)

def fastTaylorCarrier (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * fastTaylorFactor k n * lowerSixModeCarrier (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)

/-- The weight-free bracket whose product with the positive old weight is
one `mass + remainder` cell. -/
def netBracket (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  Q'.ofNat 48 * RingNormaliser.qpow D 4 *
      fastTaylorCarrier k n +
    -(step * J (n + 1) + -J n)

/-- Exact bracket with the recursive Taylor coefficient, used in proofs. -/
def actualNetBracket (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  Q'.ofNat 48 * RingNormaliser.qpow D 4 *
      lowerSixQuadraticTaylorCarrier k n +
    -(step * J (n + 1) + -J n)

private theorem lowerSixModeWeight_succ_eqv (k n : Nat) :
    lowerSixModeWeight k (n + 1) ≈
      lowerSixModeWeight k n *
        qpow (harmW k * harmW k) (2 * n + 1) := by
  have hexp : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  unfold lowerSixModeWeight
  rw [hexp]
  exact HeatKernelRGStep.qpow_add (harmW k * harmW k) (n * n) (2 * n + 1)

/-- One `mass + remainder` cell is exactly positive old weight times the
weight-free net bracket.  This removes the enormous square exponent from
the remaining sign analysis. -/
theorem mass_add_remainder_eqv_weight_mul_netBracket (k n : Nat) :
    lowerSixDiscreteHermiteMassNumerator k n +
        lowerSixDiscreteHermiteRemainder k n ≈
      lowerSixModeWeight k n * actualNetBracket k n := by
  let D := Q'.ofNat (k + 2)
  let W := lowerSixModeWeight k n
  let Ws := lowerSixModeWeight k (n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let Jn := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n)
  let Jp := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1))
  let C := lowerSixQuadraticTaylorCarrier k n
  let A := Q'.ofNat 48 * RingNormaliser.qpow D 4
  let M := Q'.ofNat 6 * RingNormaliser.qpow D 3 * W
  have hw : Ws ≈ W * step := by
    dsimp only [Ws, W, step]
    exact lowerSixModeWeight_succ_eqv k n
  have hflux : Ws * Jp + -(W * Jn) ≈
      (W * step) * Jp + -(W * Jn) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hw)
  have hneg : -(Ws * Jp + -(W * Jn)) ≈
      -((W * step) * Jp + -(W * Jn)) :=
    Q'.neg_eqv_congr _ _ hflux
  unfold lowerSixDiscreteHermiteMassNumerator
    lowerSixDiscreteHermiteRemainder lowerSixQuadraticTaylorWeightedTerm
    lowerSixDiscreteHermiteFluxNumerator actualNetBracket
  change M + (A * (W * C) + -(Ws * Jp + -(W * Jn)) + -M) ≈
    W * (A * C + -(step * Jp + -Jn))
  refine Q'.eqv_trans _
    (M + (A * (W * C) +
      -((W * step) * Jp + -(W * Jn)) + -M)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_left _ _ _ hneg))
  · exact massNet_algebra M A W C step Jp Jn

/-- The exact all-mode B block in its short-step bracket coordinates. -/
def lowerSixWeightedNetBracketSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixModeWeight k (j + 1) * actualNetBracket k (j + 1))
    (growingAnchor k)

theorem massSum_add_remainderSum_eqv_weightedNetBracketSum (k : Nat) :
    finSum
        (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1))
        (growingAnchor k) +
      finSum
        (fun j => lowerSixDiscreteHermiteRemainder k (j + 1))
        (growingAnchor k) ≈
      lowerSixWeightedNetBracketSum k := by
  let M := fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)
  let R := fun j => lowerSixDiscreteHermiteRemainder k (j + 1)
  let B := fun j =>
    lowerSixModeWeight k (j + 1) * actualNetBracket k (j + 1)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (RationalTail.finSum_add M R (growingAnchor k))) ?_
  unfold lowerSixWeightedNetBracketSum
  exact RationalTail.finSum_eqv_congr _ _
    (fun j => mass_add_remainder_eqv_weight_mul_netBracket k (j + 1)) _

/-! ## A coarse summed-remainder interface

The numerical scout says that the exact remainder is roughly a small
negative fraction of the positive Hermite mass.  The following declarations
turn the robust quarter-margin version of that observation into a precise
proof interface.  They are deliberately stated for the complete growing
anchor, so a future theta-moment estimate can plug into them without any
termwise sign claim. -/

def lowerSixHermiteMassSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1))
    (growingAnchor k)

/-- Zeroth discrete-Gaussian moment over the physical nonzero modes. -/
def lowerSixHermiteWeightSum (k : Nat) : Q' :=
  finSum (fun j => lowerSixModeWeight k (j + 1)) (growingAnchor k)

def lowerSixHermiteRemainderSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDiscreteHermiteRemainder k (j + 1))
    (growingAnchor k)

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

private theorem ringQpow_positive {a : Q'} (ha : (0 : Q') < a) :
    ∀ m, (0 : Q') < RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_pos (ringQpow_positive ha m) ha

private theorem finSum_shift_one_with_head (f : Nat → Q') : ∀ N,
    f 0 + finSum (fun j => f (j + 1)) N ≈ finSum f (N + 1)
  | 0 => by
      refine Q'.eqv_trans _ (f 0) _ ?_ ?_
      · exact QPoly.q_add_zero_eqv _
      · exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | N + 1 => by
      rw [finSum_succ, finSum_succ]
      refine Q'.eqv_trans _
        ((f 0 + finSum (fun j => f (j + 1)) N) + f (N + 1)) _ ?_ ?_
      · exact Q'.eqv_symm
          (Q'.add_assoc_eqv (f 0)
            (finSum (fun j => f (j + 1)) N) (f (N + 1)))
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_shift_one_with_head f N)

private theorem modeWeight_eqv_thetaTerm0 (k n : Nat) :
    lowerSixModeWeight k n ≈
      thetaTerm (harmW k * harmW k) 0 n := by
  unfold lowerSixModeWeight thetaTerm
  rw [Nat.pow_zero]
  exact Q'.eqv_symm
    (Q'.eqv_trans _ ((1 : Q') *
        qpow (harmW k * harmW k) (n * n)) _
      (Q'.mul_eqv_congr_right _ _ _ (by decide))
      (Q'.one_mul_eqv _))

/-- The nonzero-mode weight sum is exactly the centered zeroth theta moment
with its `d=0` head removed.  This is the bridge to `RDThetaCentered` moment
bounds; no limit or real-valued normalization is used. -/
theorem one_add_lowerSixHermiteWeightSum_eqv_thetaCentered0 (k : Nat) :
    (1 : Q') + lowerSixHermiteWeightSum k ≈
      thetaCenteredSum (harmW k * harmW k) 0 (growingAnchor k) := by
  let σ := harmW k * harmW k
  let f := fun n => thetaTerm σ 0 n
  have hhead : f 0 ≈ (1 : Q') := by
    dsimp only [f, σ]
    unfold thetaTerm qpow
    change Q'.ofNat (0 ^ 0) * (1 : Q') ≈ (1 : Q')
    decide
  have htail : lowerSixHermiteWeightSum k ≈
      finSum (fun j => f (j + 1)) (growingAnchor k) := by
    unfold lowerSixHermiteWeightSum
    exact RationalTail.finSum_eqv_congr _ _
      (fun j => modeWeight_eqv_thetaTerm0 k (j + 1)) _
  unfold thetaCenteredSum
  refine Q'.eqv_trans _
      (f 0 + finSum (fun j => f (j + 1)) (growingAnchor k)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_symm hhead) htail
  · exact finSum_shift_one_with_head f (growingAnchor k)

/-- The Hermite mass is precisely `6D^3` times the zeroth nonzero-mode
theta moment. -/
theorem lowerSixHermiteMassSum_eqv_scaledWeightSum (k : Nat) :
    lowerSixHermiteMassSum k ≈
      (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
        lowerSixHermiteWeightSum k := by
  let C := Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  unfold lowerSixHermiteMassSum lowerSixHermiteWeightSum
  refine Q'.eqv_trans _
      (finSum (fun j => C * lowerSixModeWeight k (j + 1))
        (growingAnchor k)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _ (fun j => by
      unfold lowerSixDiscreteHermiteMassNumerator
      exact Q'.eqv_refl _) _
  · exact Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun j => lowerSixModeWeight k (j + 1)) C (growingAnchor k))

private theorem square_harmW_le_one (k : Nat) :
    harmW k * harmW k ≤ (1 : Q') := by
  have hmul := Q'.mul_le_mul_of_nonneg
    (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- A conservative, genuinely growing Bernoulli-flat head. -/
def lowerSixHermiteHeadCutoff (k : Nat) : Nat :=
  thetaWindowCenter k / 4

private def pOneSubSquareL : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .add (.const 1) (.neg (.mul w w))

private def pOneSubSquareR : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .mul u (.add (.const 1) w)

private theorem pOneSubSquare_normal :
    RingNormaliser.normalize pOneSubSquareL =
      RingNormaliser.normalize pOneSubSquareR := by decide

private theorem oneSubSquare_algebra (u : Q') :
    (1 : Q') + -(((1 : Q') + -u) * ((1 : Q') + -u)) ≈
      u * ((1 : Q') + ((1 : Q') + -u)) := by
  simpa [pOneSubSquareL, pOneSubSquareR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pOneSubSquareL pOneSubSquareR pOneSubSquare_normal (fun _ => u))

private theorem one_sub_harmW_square_eqv (k : Nat) :
    (1 : Q') - harmW k * harmW k ≈
      harmU k * ((1 : Q') + harmW k) := by
  change (1 : Q') + -(harmW k * harmW k) ≈
    harmU k * ((1 : Q') + harmW k)
  unfold harmW oneSub
  exact oneSubSquare_algebra _

private theorem one_sub_harmW_square_le_two_harmU (k : Nat) :
    (1 : Q') - harmW k * harmW k ≤ Q'.ofNat 2 * harmU k := by
  have hsum : (1 : Q') + harmW k ≤ (1 : Q') + 1 :=
    Q'.add_le_add_left (1 : Q') _ _ (harmW_le_one k)
  have hmul : harmU k * ((1 : Q') + harmW k) ≤
      harmU k * ((1 : Q') + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (harmU_nonneg k)
  have htwo : harmU k * ((1 : Q') + 1) ≈
      Q'.ofNat 2 * harmU k := by
    refine Q'.eqv_trans _ (((1 : Q') + 1) * harmU k) _
      (Q'.mul_comm_eqv _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (one_sub_harmW_square_eqv k))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv htwo))

private theorem lowerSixHermiteHeadCutoff_le_anchor
    {k : Nat} (hk : 38 ≤ k) :
    lowerSixHermiteHeadCutoff k ≤ growingAnchor k := by
  have hc := thetaWindowCenter_le_harmonicDen hk
  unfold lowerSixHermiteHeadCutoff growingAnchor
  have hdiv := Nat.div_le_self (thetaWindowCenter k) 4
  omega

private theorem lowerSixHermiteHeadCutoff_four_sq_le_den
    {k n : Nat} (hn : n ≤ lowerSixHermiteHeadCutoff k) :
    4 * (n * n) ≤ k + 2 := by
  let c := thetaWindowCenter k
  have h4n : 4 * n ≤ c := by
    dsimp only [c]
    unfold lowerSixHermiteHeadCutoff at hn
    omega
  have hsquare : (4 * n) * (4 * n) ≤ c * c :=
    Nat.mul_le_mul h4n h4n
  have hcSq : c * c ≤ 2 * (k + 2) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h16 : 16 * (n * n) ≤ 2 * (k + 2) + 1 := by
    have heq : 16 * (n * n) = (4 * n) * (4 * n) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    exact Nat.le_trans hsquare hcSq
  omega

private theorem lowerSixHermiteHeadCutoff_floor
    {k n : Nat} (hk : 38 ≤ k)
    (hn : n ≤ lowerSixHermiteHeadCutoff k) :
    Q'.ofNat 2 *
        (Q'.ofNat (n * n) *
          ((1 : Q') - harmW k * harmW k)) ≤ (1 : Q') := by
  have hmargin := one_sub_harmW_square_le_two_harmU k
  have hn0 : (0 : Q') ≤ Q'.ofNat (n * n) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hinner := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (n * n)) hmargin hn0
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hinner (by decide)
  have hnat := lowerSixHermiteHeadCutoff_four_sq_le_den hn
  have hunit :
      Q'.ofNat 2 *
          (Q'.ofNat (n * n) * (Q'.ofNat 2 * harmU k)) ≤
        (1 : Q') := by
    unfold harmU unit
    show (Q'.ofNat 2 *
          (Q'.ofNat (n * n) *
            (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega)))).num *
          ((1 : Q').den : Int) ≤
        (1 : Q').num *
          (Q'.ofNat 2 *
            (Q'.ofNat (n * n) *
              (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega)))).den
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
      Int.mul_one, Int.one_mul]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    push_cast
    have hnat' : 2 * (n * n * 2) ≤ k + 1 + 1 := by omega
    exact_mod_cast hnat'
  exact Q'.le_trans' _ _ _ htwo hunit

/-! The uniform-half head above is convenient, but wastes most of the
available Gaussian mass.  The linear Bernoulli profile extends to the wider
`thetaWindowLeft = floor(sqrt(2D+1))/2` head and retains the exact triangular
shape. -/

def lowerSixHermiteLinearHeadCell (k n : Nat) : Q' :=
  (1 : Q') - Q'.ofNat (n * n) *
    ((1 : Q') - harmW k * harmW k)

def lowerSixHermiteLinearHeadSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixHermiteLinearHeadCell k (j + 1))
    (thetaWindowLeft k)

def lowerSixHermiteLinearHeadMassFloor (k : Nat) : Q' :=
  (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
    lowerSixHermiteLinearHeadSum k

private theorem thetaWindowLeft_two_sq_le_den
    {k n : Nat} (hn : n ≤ thetaWindowLeft k) :
    2 * (n * n) ≤ k + 2 := by
  let c := thetaWindowCenter k
  have h2n : 2 * n ≤ c := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have hsquare : (2 * n) * (2 * n) ≤ c * c :=
    Nat.mul_le_mul h2n h2n
  have hcSq : c * c ≤ 2 * (k + 2) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hfour : 4 * (n * n) ≤ 2 * (k + 2) + 1 := by
    have heq : 4 * (n * n) = (2 * n) * (2 * n) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    exact Nat.le_trans hsquare hcSq
  omega

theorem lowerSixHermiteLinearHeadCell_nonnegative
    {k n : Nat} (hn : n ≤ thetaWindowLeft k) :
    (0 : Q') ≤ lowerSixHermiteLinearHeadCell k n := by
  have hmargin := one_sub_harmW_square_le_two_harmU k
  have hn0 : (0 : Q') ≤ Q'.ofNat (n * n) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (n * n)) hmargin hn0
  have hnat := thetaWindowLeft_two_sq_le_den hn
  have hunit :
      Q'.ofNat (n * n) * (Q'.ofNat 2 * harmU k) ≤ (1 : Q') := by
    unfold harmU unit
    show (Q'.ofNat (n * n) *
          (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega))).num *
          ((1 : Q').den : Int) ≤
        (1 : Q').num *
          (Q'.ofNat (n * n) *
            (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega))).den
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
      Int.mul_one, Int.one_mul]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    push_cast
    have hnat' : n * n * 2 ≤ k + 1 + 1 := by omega
    exact_mod_cast hnat'
  unfold lowerSixHermiteLinearHeadCell
  exact Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ hmul hunit)

theorem lowerSixHermiteLinearHeadSum_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixHermiteLinearHeadSum k := by
  unfold lowerSixHermiteLinearHeadSum
  let f := fun j => lowerSixHermiteLinearHeadCell k (j + 1)
  have hf : ∀ j, j < thetaWindowLeft k → (0 : Q') ≤ f j := by
    intro j hj
    exact lowerSixHermiteLinearHeadCell_nonnegative (by omega)
  have hrec : ∀ N, N ≤ thetaWindowLeft k → (0 : Q') ≤ finSum f N := by
    intro N hN
    induction N with
    | zero => exact Q'.le_refl' 0
    | succ M ih =>
        rw [finSum_succ]
        exact Q'.zero_le_add _ _ (ih (by omega)) (hf M (by omega))
  exact hrec _ (Nat.le_refl _)

private theorem finSum_one_eqv_ofNat : ∀ N,
    finSum (fun _ => (1 : Q')) N ≈ Q'.ofNat N
  | 0 => by decide
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _ (Q'.ofNat N + (1 : Q')) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ (finSum_one_eqv_ofNat N)
      · exact Q'.eqv_trans _ (Q'.ofNat N + Q'.ofNat 1) _
          (Q'.add_eqv_congr_left _ _ _ (by decide))
          (Q'.eqv_symm (Q'.ofNat_add_eqv N 1))

private theorem finSum_shifted_squares_eqv_sumSq : ∀ N,
    finSum (fun j => Q'.ofNat ((j + 1) * (j + 1))) N ≈
      Q'.ofNat (sumSq N)
  | 0 => by decide
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _
        (Q'.ofNat (sumSq N) + Q'.ofNat ((N + 1) * (N + 1))) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (finSum_shifted_squares_eqv_sumSq N)
      · rw [sumSq]
        exact Q'.eqv_symm
          (Q'.ofNat_add_eqv (sumSq N) ((N + 1) * (N + 1)))

/-- Closed polynomial form of the tapered head.  The only non-polynomial
datum left is the exact integer-square-root cutoff itself. -/
theorem lowerSixHermiteLinearHeadSum_eqv_closed (k : Nat) :
    lowerSixHermiteLinearHeadSum k ≈
      Q'.ofNat (thetaWindowLeft k) +
        -(((1 : Q') - harmW k * harmW k) *
          Q'.ofNat (sumSq (thetaWindowLeft k))) := by
  let d := thetaWindowLeft k
  let δ := (1 : Q') - harmW k * harmW k
  let Sq := fun j => Q'.ofNat ((j + 1) * (j + 1))
  have hterm : ∀ j, lowerSixHermiteLinearHeadCell k (j + 1) ≈
      (1 : Q') + (-δ) * Sq j := by
    intro j
    unfold lowerSixHermiteLinearHeadCell
    dsimp only [δ, Sq]
    apply Q'.add_eqv_congr_left
    refine Q'.eqv_trans _ (-(δ * Q'.ofNat ((j + 1) * (j + 1)))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _
        (Q'.mul_comm_eqv _ _)
    · exact Q'.eqv_symm (Q'.neg_mul_eqv _ _)
  have hpoint := RationalTail.finSum_eqv_congr _ _ hterm d
  have hsplit := RationalTail.finSum_add
    (fun _ => (1 : Q')) (fun j => (-δ) * Sq j) d
  have hscaled := Q'.eqv_symm
    (RationalTail.const_mul_finSum Sq (-δ) d)
  have hsquares : finSum Sq d ≈ Q'.ofNat (sumSq d) := by
    dsimp only [Sq, d]
    exact finSum_shifted_squares_eqv_sumSq _
  unfold lowerSixHermiteLinearHeadSum
  dsimp only [d, δ, Sq] at hpoint hsplit hscaled hsquares ⊢
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _
      (Q'.ofNat (thetaWindowLeft k) +
        (-((1 : Q') - harmW k * harmW k)) *
          Q'.ofNat (sumSq (thetaWindowLeft k))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (finSum_one_eqv_ofNat _)
      (Q'.eqv_trans _ _ _ hscaled
        (Q'.mul_eqv_congr_left _ _ _ hsquares))
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_mul_eqv _ _)

/-- Strong exact mass floor: the full mass dominates the linearly tapered
Bernoulli head through `thetaWindowLeft`. -/
theorem lowerSixHermiteLinearHeadMassFloor_le_mass
    {k : Nat} (hk : 38 ≤ k) :
    lowerSixHermiteLinearHeadMassFloor k ≤ lowerSixHermiteMassSum k := by
  let σ := harmW k * harmW k
  let W := fun j => lowerSixModeWeight k (j + 1)
  let L := fun j => lowerSixHermiteLinearHeadCell k (j + 1)
  let C := Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  have hσ0 : (0 : Q') ≤ σ :=
    Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : σ ≤ (1 : Q') := square_harmW_le_one k
  have hterm : ∀ j, j < thetaWindowLeft k → L j ≤ W j := by
    intro j _
    have hbern := MovingCutoff.qpow_ge_bernoulli hσ0 hσ1
      ((j + 1) * (j + 1))
    dsimp only [L, W, σ]
    unfold lowerSixHermiteLinearHeadCell lowerSixModeWeight
    exact hbern
  have hprefix : lowerSixHermiteLinearHeadSum k ≤
      finSum W (thetaWindowLeft k) := by
    unfold lowerSixHermiteLinearHeadSum
    exact YMGap.Constructive.finSum_le_lt L W (thetaWindowLeft k) hterm
  have hWnonneg : ∀ j, (0 : Q') ≤ W j := by
    intro j
    dsimp only [W]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hleft : thetaWindowLeft k ≤ growingAnchor k := by
    have hc := thetaWindowCenter_le_harmonicDen hk
    unfold thetaWindowLeft growingAnchor
    have hdiv := Nat.div_le_self (thetaWindowCenter k) 2
    omega
  have hfull : finSum W (thetaWindowLeft k) ≤
      lowerSixHermiteWeightSum k := by
    unfold lowerSixHermiteWeightSum
    exact RationalTail.finSum_monotone_of_nonneg W hWnonneg
      (thetaWindowLeft k) (growingAnchor k) hleft
  have hweight : lowerSixHermiteLinearHeadSum k ≤
      lowerSixHermiteWeightSum k := Q'.le_trans' _ _ _ hprefix hfull
  have hD : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC : (0 : Q') ≤ C :=
    Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C hweight hC
  unfold lowerSixHermiteLinearHeadMassFloor
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_symm
      (lowerSixHermiteMassSum_eqv_scaledWeightSum k)))

/-- Every Bernoulli-flat Gaussian head supplies a quantitative piece of the
Hermite mass.  This is the exact finite form needed to pay an upper bound on
the summed remainder: a head of length `d` contributes at least one half per
mode, before the positive factor `6D^3` is restored. -/
theorem lowerSixHermiteMassSum_ge_half_head
    {k d : Nat} (hd : d ≤ growingAnchor k)
    (hfloor : ∀ n, 1 ≤ n → n ≤ d →
      Q'.ofNat 2 *
        (Q'.ofNat (n * n) *
          ((1 : Q') - (harmW k * harmW k))) ≤ (1 : Q')) :
    (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
        (HalfPow.half * Q'.ofNat d) ≤
      lowerSixHermiteMassSum k := by
  let σ := harmW k * harmW k
  let W := fun j => lowerSixModeWeight k (j + 1)
  let H := fun j => HalfPow.half * Q'.ofNat (j ^ 0)
  let C := Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  have hσ0 : (0 : Q') ≤ σ :=
    Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : σ ≤ (1 : Q') := square_harmW_le_one k
  have hterm : ∀ j, j < d → H j ≤ W j := by
    intro j hj
    have hj1 : 1 ≤ j + 1 := by omega
    have hjd : j + 1 ≤ d := by omega
    have htheta := thetaTerm_ge_half hσ0 hσ1 0 (j + 1)
      (hfloor (j + 1) hj1 hjd)
    dsimp only [H, W, σ] at htheta ⊢
    rw [Nat.pow_zero] at htheta ⊢
    exact Q'.le_trans' _ _ _ htheta
      (Q'.le_of_eqv (Q'.eqv_symm
        (modeWeight_eqv_thetaTerm0 k (j + 1))))
  have hhead : HalfPow.half * Q'.ofNat d ≤ finSum W d := by
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (RDThetaCentered.head0_count d)) ?_
    exact YMGap.Constructive.finSum_le_lt H W d hterm
  have hWnonneg : ∀ j, (0 : Q') ≤ W j := by
    intro j
    dsimp only [W]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hfull : finSum W d ≤ lowerSixHermiteWeightSum k := by
    unfold lowerSixHermiteWeightSum
    exact RationalTail.finSum_monotone_of_nonneg W hWnonneg
      d (growingAnchor k) hd
  have hweight : HalfPow.half * Q'.ofNat d ≤
      lowerSixHermiteWeightSum k :=
    Q'.le_trans' _ _ _ hhead hfull
  have hD : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC : (0 : Q') ≤ C :=
    Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C hweight hC
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_symm
      (lowerSixHermiteMassSum_eqv_scaledWeightSum k)))

/-- Unconditional dynamic-head mass lower bound on the physical range.  The
cutoff is `floor(sqrt(2D+1))/4`, so this records the required `D^(7/2)` scale
entirely with exact rationals and integer square-root arithmetic. -/
theorem lowerSixHermiteMassSum_ge_dynamic_head
    {k : Nat} (hk : 48 ≤ k) :
    (Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) *
        (HalfPow.half * Q'.ofNat (lowerSixHermiteHeadCutoff k)) ≤
      lowerSixHermiteMassSum k := by
  apply lowerSixHermiteMassSum_ge_half_head
  · exact lowerSixHermiteHeadCutoff_le_anchor (by omega)
  · intro n _ hn
    exact lowerSixHermiteHeadCutoff_floor (by omega) hn

/-- The positive Hermite mass sum is nonnegative without any asymptotic
estimate. -/
theorem lowerSixHermiteMassSum_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixHermiteMassSum k := by
  unfold lowerSixHermiteMassSum
  let f := fun j => lowerSixDiscreteHermiteMassNumerator k (j + 1)
  have hf : ∀ j, (0 : Q') ≤ f j := by
    intro j
    dsimp only [f]
    unfold lowerSixDiscreteHermiteMassNumerator lowerSixModeWeight
    have hD : (0 : Q') ≤ Q'.ofNat (k + 2) :=
      HeatKernelRGStep.zero_le_ofNat _
    have hW : (0 : Q') ≤
        qpow (harmW k * harmW k) ((j + 1) * (j + 1)) :=
      RGTransport.qpow_nonneg _
        (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (ringQpow_nonnegative hD 3))
      hW
  have hsum := RationalTail.finSum_monotone_of_nonneg f hf
    0 (growingAnchor k) (Nat.zero_le _)
  exact hsum

private abbrev QuarterPE := RingNormaliser.PolyExpr

private def pQuarterEnvelopeL : QuarterPE :=
  let M : QuarterPE := .var 0
  let R : QuarterPE := .var 1
  .mul (.const 4) (.add M R)

private def pQuarterEnvelopeR : QuarterPE :=
  let M : QuarterPE := .var 0
  let R : QuarterPE := .var 1
  .add (.add M (.mul (.const 4) R)) (.mul (.const 3) M)

private theorem pQuarterEnvelope_normal :
    RingNormaliser.normalize pQuarterEnvelopeL =
      RingNormaliser.normalize pQuarterEnvelopeR := by decide

private theorem quarterEnvelope_algebra (M R : Q') :
    Q'.ofNat 4 * (M + R) ≈ (M + Q'.ofNat 4 * R) + Q'.ofNat 3 * M := by
  simpa [pQuarterEnvelopeL, pQuarterEnvelopeR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pQuarterEnvelopeL pQuarterEnvelopeR pQuarterEnvelope_normal
      (fun | 0 => M | _ => R))

/-- A quarter-mass bound on the *summed* remainder closes the complete
mass-plus-remainder block.  This is stronger than needed, but has a large
finite-D margin and avoids the false pointwise route. -/
theorem mass_add_remainderSum_nonnegative_of_quarter_envelope
    (k : Nat)
    (hquarter : (0 : Q') ≤
      lowerSixHermiteMassSum k +
        Q'.ofNat 4 * lowerSixHermiteRemainderSum k) :
    (0 : Q') ≤
      lowerSixHermiteMassSum k + lowerSixHermiteRemainderSum k := by
  let M := lowerSixHermiteMassSum k
  let R := lowerSixHermiteRemainderSum k
  have hM : (0 : Q') ≤ M := lowerSixHermiteMassSum_nonnegative k
  have h3M : (0 : Q') ≤ Q'.ofNat 3 * M :=
    Q'.mul_nonneg _ _ (by decide) hM
  have hsum : (0 : Q') ≤ (M + Q'.ofNat 4 * R) + Q'.ofNat 3 * M :=
    Q'.zero_le_add _ _ hquarter h3M
  have hscaled : (0 : Q') ≤ Q'.ofNat 4 * (M + R) :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (quarterEnvelope_algebra M R)))
  have hzero : Q'.ofNat 4 * (0 : Q') ≤ Q'.ofNat 4 * (M + R) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 4))) hscaled
  exact Q'.le_of_mul_le_mul_left hzero (by decide)

/-- Final interface for the current summed analysis.  It is enough to pay
four copies of the negative remainder by the explicit linear Bernoulli head;
the head is already proved to lie below the true Hermite mass. -/
theorem mass_add_remainderSum_nonnegative_of_linearHead_payment
    {k : Nat} (hk : 48 ≤ k)
    (hpayment :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k) :
    (0 : Q') ≤
      lowerSixHermiteMassSum k + lowerSixHermiteRemainderSum k := by
  let H := lowerSixHermiteLinearHeadMassFloor k
  let M := lowerSixHermiteMassSum k
  let R := lowerSixHermiteRemainderSum k
  have hHM : H ≤ M :=
    lowerSixHermiteLinearHeadMassFloor_le_mass (by omega)
  have hsub : (0 : Q') ≤ H + -(-(Q'.ofNat 4 * R)) :=
    Q'.sub_nonneg_of_le hpayment
  have hcancel : H + -(-(Q'.ofNat 4 * R)) ≈
      H + Q'.ofNat 4 * R :=
    Q'.add_eqv_congr_left H _ _ (Q'.neg_neg_eqv _)
  have hHplus : (0 : Q') ≤ H + Q'.ofNat 4 * R :=
    Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv hcancel)
  have hmove := Q'.add_le_add_right H M (Q'.ofNat 4 * R) hHM
  have hquarter : (0 : Q') ≤ M + Q'.ofNat 4 * R :=
    Q'.le_trans' _ _ _ hHplus hmove
  exact mass_add_remainderSum_nonnegative_of_quarter_envelope k hquarter

/-! ## Second Hermite flux for the remainder debt

The leading continuum density of `-4R` is `(8/15)P(y)D²`, where

`P = 2304y^10 + 10240y^8 - 32480y^6 + 29640y^4 - 9210y² - 15`.

Its Gaussian-Hermite decomposition has constant mass `1042` and odd flux
`-(1/4)(7875y + 22780y³ - 5488y⁵ + 15424y⁷ + 2304y⁹)`.  Clearing by
`15D²` gives the integral polynomial below.  The declarations in this section
are exact finite-D identities; the final analytic job is to majorize their
new summed remainder against the tapered head. -/

def hermiteDebtLeadingDensity (y : Q') : Q' :=
  Q'.ofNat 2304 * RingNormaliser.qpow y 10 +
    Q'.ofNat 10240 * RingNormaliser.qpow y 8 +
    -(Q'.ofNat 32480 * RingNormaliser.qpow y 6) +
    Q'.ofNat 29640 * RingNormaliser.qpow y 4 +
    -(Q'.ofNat 9210 * RingNormaliser.qpow y 2) +
    -(Q'.ofNat 15)

def hermiteDebtSecondFlux (y : Q') : Q' :=
  -(Q'.ofNat 15750 * y) +
    -(Q'.ofNat 45560 * RingNormaliser.qpow y 3) +
    Q'.ofNat 10976 * RingNormaliser.qpow y 5 +
    -(Q'.ofNat 30848 * RingNormaliser.qpow y 7) +
    -(Q'.ofNat 4608 * RingNormaliser.qpow y 9)

def hermiteDebtSecondFluxDerivative (y : Q') : Q' :=
  -(Q'.ofNat 15750) +
    -(Q'.ofNat 136680 * RingNormaliser.qpow y 2) +
    Q'.ofNat 54880 * RingNormaliser.qpow y 4 +
    -(Q'.ofNat 215936 * RingNormaliser.qpow y 6) +
    -(Q'.ofNat 41472 * RingNormaliser.qpow y 8)

private def pDebtLeadingDensity : PE :=
  let y : PE := .var 0
  .add (.add (.add (.add (.add
    (.mul (.const 2304) (.pow y 10))
    (.mul (.const 10240) (.pow y 8)))
    (.neg (.mul (.const 32480) (.pow y 6))))
    (.mul (.const 29640) (.pow y 4)))
    (.neg (.mul (.const 9210) (.pow y 2))))
    (.neg (.const 15))

private def pDebtSecondFlux : PE :=
  let y : PE := .var 0
  .add (.add (.add (.add
    (.neg (.mul (.const 15750) y))
    (.neg (.mul (.const 45560) (.pow y 3))))
    (.mul (.const 10976) (.pow y 5)))
    (.neg (.mul (.const 30848) (.pow y 7))))
    (.neg (.mul (.const 4608) (.pow y 9)))

private def pDebtSecondFluxDerivative : PE :=
  let y : PE := .var 0
  .add (.add (.add (.add
    (.neg (.const 15750))
    (.neg (.mul (.const 136680) (.pow y 2))))
    (.mul (.const 54880) (.pow y 4)))
    (.neg (.mul (.const 215936) (.pow y 6))))
    (.neg (.mul (.const 41472) (.pow y 8)))

private def pDebtSecondFluxL : PE :=
  .mul (.const 8) pDebtLeadingDensity

private def pDebtSecondFluxR : PE :=
  let y : PE := .var 0
  .add (.add (.const 15630) pDebtSecondFluxDerivative)
    (.neg (.mul (.mul (.const 4) y) pDebtSecondFlux))

private theorem pDebtSecondFlux_normal :
    RingNormaliser.normalize pDebtSecondFluxL =
      RingNormaliser.normalize pDebtSecondFluxR := by decide

/-- Exact Gaussian-Hermite identity selecting the second flux and its
constant mass `15630`. -/
theorem hermiteDebt_second_flux_identity (y : Q') :
    Q'.ofNat 8 * hermiteDebtLeadingDensity y ≈
      Q'.ofNat 15630 + hermiteDebtSecondFluxDerivative y +
        -(Q'.ofNat 4 * y * hermiteDebtSecondFlux y) := by
  simpa [pDebtSecondFluxL, pDebtSecondFluxR, pDebtLeadingDensity,
    pDebtSecondFlux, pDebtSecondFluxDerivative,
    hermiteDebtLeadingDensity, hermiteDebtSecondFlux,
    hermiteDebtSecondFluxDerivative, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pDebtSecondFluxL pDebtSecondFluxR pDebtSecondFlux_normal
      (fun _ => y))

def lowerSixHermiteSecondFluxPoly (D N : Q') : Q' :=
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let N3 := RingNormaliser.qpow N 3
  let N5 := RingNormaliser.qpow N 5
  let N7 := RingNormaliser.qpow N 7
  let N9p := RingNormaliser.qpow N 9
  (((-(Q'.ofNat 15750 * N * D4) +
      -(Q'.ofNat 45560 * N3 * D3)) +
      Q'.ofNat 10976 * N5 * D2) +
      -(Q'.ofNat 30848 * N7 * D)) +
      -(Q'.ofNat 4608 * N9p)

private def pSecondFluxAbsorptionCoreL : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  .mul (.const 4)
    (.add
      (.add
        (.mul (.const 45560) (.pow D 2))
        (.mul (.const 30848) (.pow N 4)))
      (.neg (.mul (.const 10976) (.mul (.pow N 2) D))))

private def pSecondFluxAbsorptionCoreR : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  let X : PE := .add (.mul (.const 2) (.pow N 2)) (.neg D)
  .add
    (.add
      (.mul (.const 10976) (.mul X X))
      (.mul (.const 79488) (.pow N 4)))
    (.mul (.const 171264) (.pow D 2))

private theorem pSecondFluxAbsorptionCore_normal :
    RingNormaliser.normalize pSecondFluxAbsorptionCoreL =
      RingNormaliser.normalize pSecondFluxAbsorptionCoreR := by decide

private theorem secondFluxAbsorptionCore_algebra (D N : Q') :
    Q'.ofNat 4 *
        ((Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
          Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
          -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D))) ≈
      (Q'.ofNat 10976 *
          ((Q'.ofNat 2 * RingNormaliser.qpow N 2 + -D) *
            (Q'.ofNat 2 * RingNormaliser.qpow N 2 + -D)) +
        Q'.ofNat 79488 * RingNormaliser.qpow N 4) +
        Q'.ofNat 171264 * RingNormaliser.qpow D 2 := by
  simpa only [pSecondFluxAbsorptionCoreL, pSecondFluxAbsorptionCoreR,
    RingNormaliser.eval,
    show Q'.ofInt 2 = Q'.ofNat 2 from rfl,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 10976 = Q'.ofNat 10976 from rfl,
    show Q'.ofInt 30848 = Q'.ofNat 30848 from rfl,
    show Q'.ofInt 45560 = Q'.ofNat 45560 from rfl,
    show Q'.ofInt 79488 = Q'.ofNat 79488 from rfl,
    show Q'.ofInt 171264 = Q'.ofNat 171264 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSecondFluxAbsorptionCoreL pSecondFluxAbsorptionCoreR
      pSecondFluxAbsorptionCore_normal
      (fun | 0 => D | _ => N))

set_option maxHeartbeats 1000000 in
private theorem secondFluxAbsorptionCore_nonnegative
    {D N : Q'} (hD : (0 : Q') ≤ D) (hN : (0 : Q') ≤ N) :
    (0 : Q') ≤
      (Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
        Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
        -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D)) := by
  let X := Q'.ofNat 2 * RingNormaliser.qpow N 2 + -D
  let B :=
    (Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
      Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
      -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D))
  have hD2 : (0 : Q') ≤ RingNormaliser.qpow D 2 :=
    ringQpow_nonnegative hD 2
  have hN4 : (0 : Q') ≤ RingNormaliser.qpow N 4 :=
    ringQpow_nonnegative hN 4
  have hX2 : (0 : Q') ≤ X * X :=
    SumOfSquares.q_mul_self_nonneg X
  have hcert : (0 : Q') ≤
      (Q'.ofNat 10976 * (X * X) +
        Q'.ofNat 79488 * RingNormaliser.qpow N 4) +
        Q'.ofNat 171264 * RingNormaliser.qpow D 2 := by
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hX2)
        (Q'.mul_nonneg _ _ (by decide) hN4))
      (Q'.mul_nonneg _ _ (by decide) hD2)
  have hscaled : (0 : Q') ≤ Q'.ofNat 4 * B := by
    dsimp only [X, B] at hcert ⊢
    exact Q'.le_trans' _ _ _ hcert
      (Q'.le_of_eqv
        (Q'.eqv_symm (secondFluxAbsorptionCore_algebra D N)))
  have hzero : Q'.ofNat 4 * (0 : Q') ≤ Q'.ofNat 4 * B :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 4))) hscaled
  exact Q'.le_of_mul_le_mul_left hzero (by decide)

private def pSecondFluxAbsorptionL : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  .add
    (.add
      (.mul (.const 45560) (.mul (.pow N 3) (.pow D 3)))
      (.mul (.const 30848) (.mul (.pow N 7) D)))
    (.neg (.mul (.const 10976) (.mul (.pow N 5) (.pow D 2))))

private def pSecondFluxAbsorptionR : PE :=
  let D : PE := .var 0
  let N : PE := .var 1
  .mul (.mul (.pow N 3) D)
    (.add
      (.add
        (.mul (.const 45560) (.pow D 2))
        (.mul (.const 30848) (.pow N 4)))
      (.neg (.mul (.const 10976) (.mul (.pow N 2) D))))

private theorem pSecondFluxAbsorption_normal :
    RingNormaliser.normalize pSecondFluxAbsorptionL =
      RingNormaliser.normalize pSecondFluxAbsorptionR := by decide

private theorem secondFluxAbsorption_algebra (D N : Q') :
    (Q'.ofNat 45560 *
          (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 3) +
        Q'.ofNat 30848 * (RingNormaliser.qpow N 7 * D)) +
        -(Q'.ofNat 10976 *
          (RingNormaliser.qpow N 5 * RingNormaliser.qpow D 2)) ≈
      (RingNormaliser.qpow N 3 * D) *
        ((Q'.ofNat 45560 * RingNormaliser.qpow D 2 +
          Q'.ofNat 30848 * RingNormaliser.qpow N 4) +
          -(Q'.ofNat 10976 * (RingNormaliser.qpow N 2 * D))) := by
  simpa only [pSecondFluxAbsorptionL, pSecondFluxAbsorptionR,
    RingNormaliser.eval,
    show Q'.ofInt 10976 = Q'.ofNat 10976 from rfl,
    show Q'.ofInt 30848 = Q'.ofNat 30848 from rfl,
    show Q'.ofInt 45560 = Q'.ofNat 45560 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSecondFluxAbsorptionL pSecondFluxAbsorptionR
      pSecondFluxAbsorption_normal
      (fun | 0 => D | _ => N))

/-- The odd second Hermite flux is nonpositive on the complete nonnegative
quadrant.  The only positive monomial is absorbed by its cubic and septic
neighbors through an explicit sum-of-squares certificate. -/
theorem lowerSixHermiteSecondFluxPoly_nonpositive
    {D N : Q'} (hD : (0 : Q') ≤ D) (hN : (0 : Q') ≤ N) :
    lowerSixHermiteSecondFluxPoly D N ≤ (0 : Q') := by
  let A :=
    (Q'.ofNat 45560 *
          (RingNormaliser.qpow N 3 * RingNormaliser.qpow D 3) +
        Q'.ofNat 30848 * (RingNormaliser.qpow N 7 * D)) +
        -(Q'.ofNat 10976 *
          (RingNormaliser.qpow N 5 * RingNormaliser.qpow D 2))
  have hfactor : (0 : Q') ≤ RingNormaliser.qpow N 3 * D :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hN 3) hD
  have hcore := secondFluxAbsorptionCore_nonnegative hD hN
  have hA : (0 : Q') ≤ A := by
    dsimp only [A]
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ hfactor hcore)
      (Q'.le_of_eqv (Q'.eqv_symm (secondFluxAbsorption_algebra D N)))
  have hfirst : (0 : Q') ≤
      Q'.ofNat 15750 * N * RingNormaliser.qpow D 4 := by
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) hN)
      (ringQpow_nonnegative hD 4)
  have hlast : (0 : Q') ≤
      Q'.ofNat 4608 * RingNormaliser.qpow N 9 :=
    Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hN 9)
  have hsum : (0 : Q') ≤
      (Q'.ofNat 15750 * N * RingNormaliser.qpow D 4 + A) +
        Q'.ofNat 4608 * RingNormaliser.qpow N 9 := by
    exact Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hfirst hA) hlast
  have hid : lowerSixHermiteSecondFluxPoly D N ≈
      -((Q'.ofNat 15750 * N * RingNormaliser.qpow D 4 + A) +
        Q'.ofNat 4608 * RingNormaliser.qpow N 9) := by
    unfold lowerSixHermiteSecondFluxPoly
    dsimp only [A]
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (Q'.nonpos_neg_of_nonneg hsum)

def lowerSixHermiteSecondFluxNumerator (k n : Nat) : Q' :=
  lowerSixModeWeight k n *
    lowerSixHermiteSecondFluxPoly
      (Q'.ofNat (k + 2)) (Q'.ofNat n)

theorem lowerSixHermiteSecondFluxNumerator_nonpositive (k n : Nat) :
    lowerSixHermiteSecondFluxNumerator k n ≤ (0 : Q') := by
  have hW : (0 : Q') ≤ lowerSixModeWeight k n := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hK : lowerSixHermiteSecondFluxPoly
      (Q'.ofNat (k + 2)) (Q'.ofNat n) ≤ (0 : Q') :=
    lowerSixHermiteSecondFluxPoly_nonpositive
      (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _)
  unfold lowerSixHermiteSecondFluxNumerator
  exact Q'.mul_nonpos_of_nonneg_nonpos hW hK

def lowerSixHermiteDebtCell (k n : Nat) : Q' :=
  -(Q'.ofNat 4 * lowerSixDiscreteHermiteRemainder k n)

def lowerSixHermiteSecondClearingScale (k : Nat) : Q' :=
  Q'.ofNat 15 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 2

def lowerSixHermiteSecondMassNumerator (k n : Nat) : Q' :=
  Q'.ofNat 15630 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
    lowerSixModeWeight k n

def lowerSixHermiteSecondRemainder (k n : Nat) : Q' :=
  lowerSixHermiteSecondClearingScale k * lowerSixHermiteDebtCell k n +
    -(lowerSixHermiteSecondFluxNumerator k (n + 1) +
      -lowerSixHermiteSecondFluxNumerator k n) +
    -lowerSixHermiteSecondMassNumerator k n

def lowerSixHermiteFirstRemainderBracket (k n : Nat) : Q' :=
  actualNetBracket k n +
    -(Q'.ofNat 6 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3)

def lowerSixHermiteSecondRemainderBracket (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let K := fun m => lowerSixHermiteSecondFluxPoly D (Q'.ofNat m)
  lowerSixHermiteSecondClearingScale k *
      (-(Q'.ofNat 4 * lowerSixHermiteFirstRemainderBracket k n)) +
    -(step * K (n + 1) + -K n) +
    -(Q'.ofNat 15630 * RingNormaliser.qpow D 4)

private def pFirstRemainderFactorL : PE :=
  -- `C*(W*T) - ((W*S)*Jp-W*Jn) - M*W`
  .add
    (.add
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.neg (.add
        (.mul (.mul (.var 1) (.var 3)) (.var 4))
        (.neg (.mul (.var 1) (.var 5))))))
    (.neg (.mul (.var 6) (.var 1)))

private def pFirstRemainderFactorR : PE :=
  .mul (.var 1)
    (.add
      (.add
        (.mul (.var 0) (.var 2))
        (.neg (.add (.mul (.var 3) (.var 4)) (.neg (.var 5)))))
      (.neg (.var 6)))

private theorem pFirstRemainderFactor_normal :
    RingNormaliser.normalize pFirstRemainderFactorL =
      RingNormaliser.normalize pFirstRemainderFactorR := by decide

private theorem firstRemainderFactor_algebra
    (C W T S Jp Jn M : Q') :
    C * (W * T) + -((W * S) * Jp + -(W * Jn)) + -(M * W) ≈
      W * (C * T + -(S * Jp + -Jn) + -M) := by
  simpa [pFirstRemainderFactorL, pFirstRemainderFactorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFirstRemainderFactorL pFirstRemainderFactorR
      pFirstRemainderFactor_normal
      (fun | 0 => C | 1 => W | 2 => T | 3 => S |
        4 => Jp | 5 => Jn | _ => M))

theorem lowerSixHermiteFirstRemainder_eqv_weight_mul_bracket (k n : Nat) :
    lowerSixDiscreteHermiteRemainder k n ≈
      lowerSixModeWeight k n * lowerSixHermiteFirstRemainderBracket k n := by
  let D := Q'.ofNat (k + 2)
  let W := lowerSixModeWeight k n
  let Ws := lowerSixModeWeight k (n + 1)
  let S := qpow (harmW k * harmW k) (2 * n + 1)
  let Jn := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n)
  let Jp := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1))
  let T := lowerSixQuadraticTaylorCarrier k n
  let C := Q'.ofNat 48 * RingNormaliser.qpow D 4
  let M := Q'.ofNat 6 * RingNormaliser.qpow D 3
  have hw : Ws ≈ W * S := by
    dsimp only [Ws, W, S]
    exact lowerSixModeWeight_succ_eqv k n
  have hflux : Ws * Jp + -(W * Jn) ≈
      (W * S) * Jp + -(W * Jn) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hw)
  unfold lowerSixDiscreteHermiteRemainder
    lowerSixQuadraticTaylorWeightedTerm
    lowerSixDiscreteHermiteFluxNumerator
    lowerSixDiscreteHermiteMassNumerator
    lowerSixHermiteFirstRemainderBracket actualNetBracket
  change C * (W * T) + -(Ws * Jp + -(W * Jn)) + -(M * W) ≈
    W * ((C * T + -(S * Jp + -Jn)) + -M)
  refine Q'.eqv_trans _
      (C * (W * T) + -((W * S) * Jp + -(W * Jn)) + -(M * W)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hflux))
  · exact firstRemainderFactor_algebra C W T S Jp Jn M

private def pSecondRemainderFactorL : PE :=
  .add
    (.add
      (.mul (.var 0) (.neg (.mul (.const 4) (.mul (.var 1) (.var 2)))))
      (.neg (.add
        (.mul (.mul (.var 1) (.var 3)) (.var 4))
        (.neg (.mul (.var 1) (.var 5))))))
    (.neg (.mul (.var 6) (.var 1)))

private def pSecondRemainderFactorR : PE :=
  .mul (.var 1)
    (.add
      (.add
        (.mul (.var 0) (.neg (.mul (.const 4) (.var 2))))
        (.neg (.add (.mul (.var 3) (.var 4)) (.neg (.var 5)))))
      (.neg (.var 6)))

private theorem pSecondRemainderFactor_normal :
    RingNormaliser.normalize pSecondRemainderFactorL =
      RingNormaliser.normalize pSecondRemainderFactorR := by decide

private theorem secondRemainderFactor_algebra
    (A W B S Kp Kn M : Q') :
    A * (-(Q'.ofNat 4 * (W * B))) +
        -((W * S) * Kp + -(W * Kn)) + -(M * W) ≈
      W * (A * (-(Q'.ofNat 4 * B)) +
        -(S * Kp + -Kn) + -M) := by
  simpa [pSecondRemainderFactorL, pSecondRemainderFactorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSecondRemainderFactorL pSecondRemainderFactorR
      pSecondRemainderFactor_normal
      (fun | 0 => A | 1 => W | 2 => B | 3 => S |
        4 => Kp | 5 => Kn | _ => M))

theorem lowerSixHermiteSecondRemainder_eqv_weight_mul_bracket (k n : Nat) :
    lowerSixHermiteSecondRemainder k n ≈
      lowerSixModeWeight k n * lowerSixHermiteSecondRemainderBracket k n := by
  let D := Q'.ofNat (k + 2)
  let A := lowerSixHermiteSecondClearingScale k
  let W := lowerSixModeWeight k n
  let Ws := lowerSixModeWeight k (n + 1)
  let B := lowerSixHermiteFirstRemainderBracket k n
  let S := qpow (harmW k * harmW k) (2 * n + 1)
  let Kn := lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)
  let Kp := lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1))
  let M := Q'.ofNat 15630 * RingNormaliser.qpow D 4
  have hw : Ws ≈ W * S := by
    dsimp only [Ws, W, S]
    exact lowerSixModeWeight_succ_eqv k n
  have hR := lowerSixHermiteFirstRemainder_eqv_weight_mul_bracket k n
  have hflux : Ws * Kp + -(W * Kn) ≈
      (W * S) * Kp + -(W * Kn) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hw)
  unfold lowerSixHermiteSecondRemainder lowerSixHermiteDebtCell
    lowerSixHermiteSecondFluxNumerator lowerSixHermiteSecondMassNumerator
    lowerSixHermiteSecondRemainderBracket
  change A * (-(Q'.ofNat 4 * lowerSixDiscreteHermiteRemainder k n)) +
      -(Ws * Kp + -(W * Kn)) + -(M * W) ≈
    W * (A * (-(Q'.ofNat 4 * B)) + -(S * Kp + -Kn) + -M)
  refine Q'.eqv_trans _
      (A * (-(Q'.ofNat 4 * (W * B))) +
        -((W * S) * Kp + -(W * Kn)) + -(M * W)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left A _ _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hR)))
        (Q'.neg_eqv_congr _ _ hflux))
      (Q'.eqv_refl _)
  · exact secondRemainderFactor_algebra A W B S Kp Kn M

private theorem nonpositive_of_eqv_nonnegative_mul
    {R W B : Q'}
    (hR : R ≈ W * B) (hW : (0 : Q') ≤ W) (hB : B ≤ (0 : Q')) :
    R ≤ (0 : Q') := by
  have hmul : W * B ≤ W * (0 : Q') :=
    Q'.mul_le_mul_of_nonneg_left B (0 : Q') W hB hW
  exact Q'.le_trans' R (W * B) (0 : Q') (Q'.le_of_eqv hR)
    (Q'.le_trans' (W * B) (W * (0 : Q')) (0 : Q') hmul
      (Q'.le_of_eqv (Q'.mul_zero_eqv W)))

theorem lowerSixHermiteSecondRemainder_nonpositive_of_bracket
    {k n : Nat}
    (hbracket : lowerSixHermiteSecondRemainderBracket k n ≤ (0 : Q')) :
    lowerSixHermiteSecondRemainder k n ≤ (0 : Q') := by
  have hW : (0 : Q') ≤ lowerSixModeWeight k n := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  exact nonpositive_of_eqv_nonnegative_mul
    (lowerSixHermiteSecondRemainder_eqv_weight_mul_bracket k n)
    hW hbracket

private def pSecondFluxReassembleL : PE := .var 0
private def pSecondFluxReassembleR : PE :=
  .add (.add (.var 1) (.var 2))
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))

private theorem pSecondFluxReassemble_normal :
    RingNormaliser.normalize pSecondFluxReassembleL =
      RingNormaliser.normalize pSecondFluxReassembleR := by decide

private theorem secondFlux_reassemble (A B C : Q') :
    A ≈ B + C + (A + -B + -C) := by
  simpa [pSecondFluxReassembleL, pSecondFluxReassembleR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSecondFluxReassembleL pSecondFluxReassembleR
      pSecondFluxReassemble_normal
      (fun | 0 => A | 1 => B | _ => C))

theorem lowerSixHermiteDebtCell_second_flux (k n : Nat) :
    lowerSixHermiteSecondClearingScale k * lowerSixHermiteDebtCell k n ≈
      (lowerSixHermiteSecondFluxNumerator k (n + 1) +
          -lowerSixHermiteSecondFluxNumerator k n) +
        lowerSixHermiteSecondMassNumerator k n +
        lowerSixHermiteSecondRemainder k n := by
  unfold lowerSixHermiteSecondRemainder
  exact secondFlux_reassemble _ _ _

private def pSecondFluxStepL : PE :=
  .add (.add (.var 0) (.neg (.var 1)))
    (.add (.var 2) (.neg (.var 0)))
private def pSecondFluxStepR : PE :=
  .add (.var 2) (.neg (.var 1))

private theorem pSecondFluxStep_normal :
    RingNormaliser.normalize pSecondFluxStepL =
      RingNormaliser.normalize pSecondFluxStepR := by decide

private theorem secondFlux_step (x a b : Q') :
    (x + -a) + (b + -x) ≈ b + -a := by
  simpa [pSecondFluxStepL, pSecondFluxStepR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSecondFluxStepL pSecondFluxStepR pSecondFluxStep_normal
      (fun | 0 => x | 1 => a | _ => b))

private theorem finSum_forwardDifference (F : Nat → Q') : ∀ N,
    finSum (fun j => F (j + 1) + -F j) N ≈ F N + -F 0
  | 0 => Q'.eqv_symm (Q'.add_neg_self_eqv (F 0))
  | N + 1 => by
      rw [finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (finSum_forwardDifference F N)) ?_
      exact secondFlux_step (F N) (F 0) (F (N + 1))

/-- Exact finite telescope for the cleared second flux. -/
theorem lowerSixHermiteDebtFinSum_second_flux (k N : Nat) :
    lowerSixHermiteSecondClearingScale k *
        finSum (fun j => lowerSixHermiteDebtCell k (j + 1)) N ≈
      (lowerSixHermiteSecondFluxNumerator k (N + 1) +
          -lowerSixHermiteSecondFluxNumerator k 1) +
        finSum
          (fun j => lowerSixHermiteSecondMassNumerator k (j + 1)) N +
        finSum
          (fun j => lowerSixHermiteSecondRemainder k (j + 1)) N := by
  let C := lowerSixHermiteSecondClearingScale k
  let dF := fun j => lowerSixHermiteSecondFluxNumerator k (j + 2) +
    -lowerSixHermiteSecondFluxNumerator k (j + 1)
  let M := fun j => lowerSixHermiteSecondMassNumerator k (j + 1)
  let R := fun j => lowerSixHermiteSecondRemainder k (j + 1)
  let T := fun j => lowerSixHermiteDebtCell k (j + 1)
  have hpoint : ∀ j, C * T j ≈ (dF j + M j) + R j := by
    intro j
    dsimp only [C, T, dF, M, R]
    simpa [Nat.add_assoc] using
      (lowerSixHermiteDebtCell_second_flux k (j + 1))
  have hsum : finSum (fun j => C * T j) N ≈
      finSum (fun j => (dF j + M j) + R j) N :=
    RationalTail.finSum_eqv_congr _ _ hpoint N
  have hflux : finSum dF N ≈
      lowerSixHermiteSecondFluxNumerator k (N + 1) +
        -lowerSixHermiteSecondFluxNumerator k 1 := by
    simpa [dF, Nat.add_assoc] using
      (finSum_forwardDifference
        (fun j => lowerSixHermiteSecondFluxNumerator k (j + 1)) N)
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum T C N) ?_
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add (fun j => dF j + M j) R N) ?_
  refine Q'.add_eqv_congr_right _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (RationalTail.finSum_add dF M N) ?_
  exact Q'.add_eqv_congr_right _ _ _ hflux

/-- The summed debt cells are exactly the production remainder debt. -/
theorem lowerSixHermiteDebtFinSum_eqv_remainderDebt (k : Nat) :
    finSum
        (fun j => lowerSixHermiteDebtCell k (j + 1))
        (growingAnchor k) ≈
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) := by
  let R := fun j => lowerSixDiscreteHermiteRemainder k (j + 1)
  have hterm : ∀ j, lowerSixHermiteDebtCell k (j + 1) ≈
      (-Q'.ofNat 4) * R j := by
    intro j
    unfold lowerSixHermiteDebtCell
    dsimp only [R]
    exact Q'.eqv_symm (Q'.neg_mul_eqv _ _)
  refine Q'.eqv_trans _
      (finSum (fun j => (-Q'.ofNat 4) * R j) (growingAnchor k)) _ ?_ ?_
  · exact RationalTail.finSum_eqv_congr _ _ hterm _
  refine Q'.eqv_trans _
      ((-Q'.ofNat 4) * finSum R (growingAnchor k)) _ ?_ ?_
  · exact Q'.eqv_symm
      (RationalTail.const_mul_finSum R (-Q'.ofNat 4) (growingAnchor k))
  · unfold lowerSixHermiteRemainderSum
    exact Q'.neg_mul_eqv _ _

def lowerSixHermiteDebtPrefix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixHermiteDebtCell k (j + 1))
    (thetaWindowLeft k)

def lowerSixHermiteSecondMassTail (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixHermiteSecondMassNumerator k
      (thetaWindowLeft k + j + 1))
    (growingAnchor k - thetaWindowLeft k)

def lowerSixHermiteSecondRemainderPrefix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixHermiteSecondRemainder k (j + 1))
    (thetaWindowLeft k)

def lowerSixHermiteSecondRemainderTail (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixHermiteSecondRemainder k
      (thetaWindowLeft k + j + 1))
    (growingAnchor k - thetaWindowLeft k)

/-- Gaussian blocks of length the square-root window center, starting at the
first mode beyond the retained prefix. -/
def lowerSixHermiteGaussianTailBlock (k i : Nat) : Q' :=
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  finSum (fun s => lowerSixModeWeight k (K + i * c + s)) c

/-- Constant adjacent-mode ratio used inside the first square-root block. -/
def lowerSixHermiteWithinBlockRate (k : Nat) : Q' :=
  let σ := harmW k * harmW k
  let K := thetaWindowLeft k + 1
  qpow σ (2 * K + 1)

private theorem ten_center_le_harmonicDen
    {k : Nat} (hk : 247 ≤ k) :
    10 * thetaWindowCenter k ≤ k + 2 := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h20c : 20 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 20 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  rcases Nat.le_total (10 * c) D with h | h
  · change 10 * c ≤ D
    exact h
  · rcases Nat.lt_or_eq_of_le h with hlt | heq
    · have hupper : 2 * D + 1 < 20 * c := by omega
      have hfalse : False := by omega
      exact False.elim hfalse
    · change 10 * c ≤ D
      omega

private theorem eight_withinBlockExponent_le_harmonicDen
    {k : Nat} (hk : 247 ≤ k) :
    8 * (2 * (thetaWindowLeft k + 1) + 1) ≤ k + 2 := by
  let c := thetaWindowCenter k
  let d := thetaWindowLeft k
  let D := k + 2
  have hc := ten_center_le_harmonicDen hk
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hd : 2 * d ≤ c := by
    dsimp only [d]
    unfold thetaWindowLeft
    omega
  dsimp only [c, d, D] at hc hc22 hd ⊢
  omega

private theorem lowerSixWithinBlockLinearSmall
    {k : Nat} (hk : 247 ≤ k) :
    Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
        ((1 : Q') + -(harmW k * harmW k)) ≤
      oneFourth := by
  let D := k + 2
  let m := 2 * (thetaWindowLeft k + 1) + 1
  have hDpos : 0 < D := by
    dsimp only [D]
    omega
  have hDDpos : 0 < D * D := Nat.mul_pos hDpos hDpos
  have hm : 8 * m ≤ D := by
    dsimp only [m, D]
    exact eight_withinBlockExponent_le_harmonicDen hk
  have hnat : 4 * m * (2 * D - 1) ≤ D * D := by
    have htwo : 2 * D - 1 ≤ 2 * D := by omega
    calc
      4 * m * (2 * D - 1) ≤ 4 * m * (2 * D) :=
        Nat.mul_le_mul_left (4 * m) htwo
      _ = (8 * m) * D := by
        calc
          4 * m * (2 * D) = (4 * 2) * (m * D) := by ac_rfl
          _ = 8 * (m * D) := by rw [show 4 * 2 = 8 by decide]
          _ = (8 * m) * D := by rw [Nat.mul_assoc]
      _ ≤ D * D := Nat.mul_le_mul_right D hm
  let u := (1 : Q') + -(harmW k * harmW k)
  let v := Q'.mkPos (((2 * D - 1 : Nat) : Int)) (D * D) hDDpos
  have huv : u ≈ v := by
    refine Q'.eqv_trans _
      (harmU k * ((1 : Q') + harmW k)) _ ?_ ?_
    · dsimp only [u]
      exact one_sub_harmW_square_eqv k
    · dsimp only [v, D]
      unfold harmW harmU oneSub unit
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
        Q'.mul_den_cast, Q'.neg_den, envelope_neg_num_cast,
        Q'.mkPos_num, Q'.mkPos_den,
        show (1 : Q').num = 1 from rfl,
        show ((1 : Q').den : Int) = 1 from rfl,
        Int.one_mul, Int.mul_one]
      push_cast [Int.natCast_sub (by omega : 1 ≤ 2 * (k + 2))]
      congr 1 <;> omega
  have hbound : Q'.ofNat m * v ≤ oneFourth := by
    unfold oneFourth
    dsimp only [v]
    show
      (Q'.ofNat m *
        Q'.mkPos (((2 * D - 1 : Nat) : Int)) (D * D) hDDpos).num *
          ((Q'.mkPos 1 4 (by decide)).den : Int) ≤
        (Q'.mkPos 1 4 (by decide)).num *
          (Q'.ofNat m *
            Q'.mkPos (((2 * D - 1 : Nat) : Int)) (D * D) hDDpos).den
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
      Int.one_mul]
    have hnat' : m * (2 * D - 1) * 4 ≤ D * D := by
      exact Nat.le_trans (Nat.le_of_eq (by ac_rfl)) hnat
    exact_mod_cast hnat'
  dsimp only [m, u] at huv ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ huv)) hbound

/-- The constant adjacent-mode ratio in the first tail block has a
quantitative decrement.  This is the sharp intra-block substitute for the
coarser seven-block contraction. -/
theorem lowerSixWithinBlockRate_decrement
    {k : Nat} (hk : 247 ≤ k) :
    fourFifths *
        (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
          ((1 : Q') + -(harmW k * harmW k))) ≤
      (1 : Q') + -lowerSixHermiteWithinBlockRate k := by
  have hσ0 : (0 : Q') ≤ harmW k * harmW k :=
    Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : harmW k * harmW k ≤ (1 : Q') := by
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  unfold lowerSixHermiteWithinBlockRate
  exact qpow_decrement_ge_fourFifths_linear hσ0 hσ1 _
    (lowerSixWithinBlockLinearSmall hk)

/-- Cleared geometric control of all constant-ratio steps in the first
square-root block. -/
theorem lowerSixWithinBlockRate_geomSum_cleared
    {k : Nat} (hk : 247 ≤ k) :
    (fourFifths *
        (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
          ((1 : Q') + -(harmW k * harmW k)))) *
        HeatKernelRGStep.geomSum (lowerSixHermiteWithinBlockRate k)
          (thetaWindowCenter k) ≤
      (1 : Q') := by
  let r := lowerSixHermiteWithinBlockRate k
  let a := fourFifths *
    (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
      ((1 : Q') + -(harmW k * harmW k)))
  let c := thetaWindowCenter k
  have hr0 : (0 : Q') ≤ r := by
    dsimp only [r, lowerSixHermiteWithinBlockRate]
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hgeom0 : (0 : Q') ≤ HeatKernelRGStep.geomSum r c :=
    HeatKernelRGStep.geomSum_nonneg hr0 c
  have hdec : a ≤ (1 : Q') + -r := by
    dsimp only [a, r]
    exact lowerSixWithinBlockRate_decrement hk
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _
    (HeatKernelRGStep.geomSum r c) hdec hgeom0
  have hfactor : ((1 : Q') + -r) *
      HeatKernelRGStep.geomSum r c ≈
      (1 : Q') + -(qpow r c) := by
    change ((1 : Q') - r) * HeatKernelRGStep.geomSum r c ≈
      (1 : Q') - qpow r c
    exact Q'.eqv_symm (HeatKernelRGStep.oneSub_pow_factor r c)
  have hpow0 : (0 : Q') ≤ qpow r c := qpow_nonneg _ hr0 _
  have hone : (1 : Q') + -(qpow r c) ≤ (1 : Q') := by
    have hneg := Q'.nonpos_neg_of_nonneg hpow0
    have hadd := Q'.add_le_add_left (1 : Q') _ _ hneg
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv 1))
  dsimp only [a, r, c] at hmul ⊢
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hone)

private theorem nat_le_self_mul_self : ∀ n : Nat, n ≤ n * n
  | 0 => by omega
  | n + 1 => by
      have h := Nat.mul_le_mul_left (n + 1)
        (show 1 ≤ n + 1 by omega)
      simpa only [Nat.mul_one] using h

/-- Every mode in the first square-root block is dominated by the first
weight times a constant-ratio geometric progression. -/
theorem lowerSixModeWeight_firstBlock_le_geometric
    (k s : Nat) :
    lowerSixModeWeight k (thetaWindowLeft k + 1 + s) ≤
      lowerSixModeWeight k (thetaWindowLeft k + 1) *
        qpow (lowerSixHermiteWithinBlockRate k) s := by
  let σ := harmW k * harmW k
  let K := thetaWindowLeft k + 1
  let m := 2 * K + 1
  let δ := 2 * K * s + s * s
  have hsq : s ≤ s * s := nat_le_self_mul_self s
  have hδ : s * m ≤ δ := by
    dsimp only [m, δ]
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm s (2 * K)]
    exact Nat.add_le_add_left hsq (2 * K * s)
  have hexp : (K + s) * (K + s) = K * K + δ := by
    dsimp only [δ]
    simp only [Nat.add_mul, Nat.mul_add]
    rw [show s * K = K * s from Nat.mul_comm s K]
    rw [show 2 * K = K + K by omega, Nat.add_mul]
    rw [Nat.add_mul K K s]
    ac_rfl
  have hsplit : lowerSixModeWeight k (K + s) ≈
      lowerSixModeWeight k K * qpow σ δ := by
    unfold lowerSixModeWeight
    dsimp only [σ]
    rw [hexp]
    exact HeatKernelRGStep.qpow_add _ _ _
  have hσ0 : (0 : Q') ≤ σ := by
    dsimp only [σ]
    exact Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)
  have hσ1 : σ ≤ (1 : Q') := by
    dsimp only [σ]
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hpow0 := HeatKernelRGStep.qpow_antitone hσ0 hσ1
    (s * m) δ hδ
  have hiter : qpow σ (s * m) ≈
      qpow (lowerSixHermiteWithinBlockRate k) s := by
    unfold lowerSixHermiteWithinBlockRate
    dsimp only [σ, K, m]
    rw [Nat.mul_comm s (2 * (thetaWindowLeft k + 1) + 1)]
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_qpow _ _ _)
  have hpow : qpow σ δ ≤
      qpow (lowerSixHermiteWithinBlockRate k) s :=
    Q'.le_trans' _ _ _ hpow0 (Q'.le_of_eqv hiter)
  have hW0 : (0 : Q') ≤ lowerSixModeWeight k K := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _ hσ0 _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (lowerSixModeWeight k K) hpow hW0
  dsimp only [K] at hsplit hmul ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hmul

private theorem finSum_qpow_eqv_geomSum (r : Q') : ∀ N,
    finSum (fun s => qpow r s) N ≈ HeatKernelRGStep.geomSum r N
  | 0 => Q'.eqv_refl _
  | N + 1 => by
      rw [finSum_succ, HeatKernelRGStep.geomSum_succ]
      exact Q'.add_eqv_congr_right _ _ _ (finSum_qpow_eqv_geomSum r N)

theorem lowerSixHermiteGaussianTailBlock_le_geometric (k : Nat) :
    lowerSixHermiteGaussianTailBlock k 0 ≤
      lowerSixModeWeight k (thetaWindowLeft k + 1) *
        HeatKernelRGStep.geomSum (lowerSixHermiteWithinBlockRate k)
          (thetaWindowCenter k) := by
  let W := lowerSixModeWeight k (thetaWindowLeft k + 1)
  let r := lowerSixHermiteWithinBlockRate k
  let c := thetaWindowCenter k
  let f := fun s => lowerSixModeWeight k (thetaWindowLeft k + 1 + s)
  let g := fun s => W * qpow r s
  have hterm : ∀ s, s < c → f s ≤ g s := by
    intro s _
    dsimp only [f, g, W, r]
    exact lowerSixModeWeight_firstBlock_le_geometric k s
  have hsum := YMGap.Constructive.finSum_le_lt f g c hterm
  have hclosed : finSum g c ≈
      W * HeatKernelRGStep.geomSum r c := by
    refine Q'.eqv_trans _ (W * finSum (fun s => qpow r s) c) _ ?_ ?_
    · exact Q'.eqv_symm
        (RationalTail.const_mul_finSum (fun s => qpow r s) W c)
    · exact Q'.mul_eqv_congr_left _ _ _
        (finSum_qpow_eqv_geomSum r c)
  unfold lowerSixHermiteGaussianTailBlock
  dsimp only [f, g, W, r, c] at hsum hclosed ⊢
  simpa only [Nat.zero_mul, Nat.add_zero] using
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hclosed))

/-- Division-free sharp first-block bound.  The reciprocal-Bernoulli
decrement times the complete Gaussian block is at most its first weight. -/
theorem lowerSixHermiteGaussianTailBlock_cleared
    {k : Nat} (hk : 247 ≤ k) :
    (fourFifths *
        (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
          ((1 : Q') + -(harmW k * harmW k)))) *
        lowerSixHermiteGaussianTailBlock k 0 ≤
      lowerSixModeWeight k (thetaWindowLeft k + 1) := by
  let a := fourFifths *
    (Q'.ofNat (2 * (thetaWindowLeft k + 1) + 1) *
      ((1 : Q') + -(harmW k * harmW k)))
  let W := lowerSixModeWeight k (thetaWindowLeft k + 1)
  let S := HeatKernelRGStep.geomSum (lowerSixHermiteWithinBlockRate k)
    (thetaWindowCenter k)
  have hu0 : (0 : Q') ≤ (1 : Q') + -(harmW k * harmW k) := by
    have hmul := Q'.mul_le_mul_of_nonneg
      (harmW_le_one k) (harmW_le_one k) (by decide) (harmW_nonneg k)
    have hσ1 := Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
    exact Q'.sub_nonneg_of_le hσ1
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact Q'.mul_nonneg _ _ (by
      unfold fourFifths
      decide) (Q'.mul_nonneg _ _
        (HeatKernelRGStep.zero_le_ofNat _) hu0)
  have hblock := lowerSixHermiteGaussianTailBlock_le_geometric k
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ a hblock ha0
  have hAS : a * S ≤ (1 : Q') := by
    dsimp only [a, S]
    exact lowerSixWithinBlockRate_geomSum_cleared hk
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hWAS := Q'.mul_le_mul_of_nonneg_left _ _ W hAS hW0
  have hreassoc : a * (W * S) ≈ W * (a * S) := by ring_qeqv
  dsimp only [a, W, S] at hscaled hWAS hreassoc ⊢
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc)
      (Q'.le_trans' _ _ _ hWAS (Q'.le_of_eqv (Q'.mul_one_eqv _))))

private theorem thetaWindowCenter_sq_ge_harmonicDen
    {k : Nat} (hk : 38 ≤ k) :
    k + 2 ≤ thetaWindowCenter k * thetaWindowCenter k := by
  let c := thetaWindowCenter k
  have hc9 : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine hk
  have hnext : 2 * (k + 2) + 1 < (c + 1) * (c + 1) := by
    rcases Nat.lt_or_ge (2 * (k + 2) + 1) ((c + 1) * (c + 1)) with h | h
    · exact h
    · have hbad : c + 1 ≤ c := by
        dsimp only [c, thetaWindowCenter, thetaWindowLength] at h ⊢
        exact ChebOrthoMidpointEst.isqrt_ge h
      omega
  have htwo : 2 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 2 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  have hsquare : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  rw [hsquare] at hnext
  dsimp only [c] at hc9 hnext htwo ⊢
  omega

/-- Advancing one square-root block cuts every harmonic Gaussian weight by
at least one half.  The proof uses only the already derived harmonic block
power `w^(k+2) ≤ 1/2`. -/
theorem lowerSixModeWeight_center_step_le_half
    {k : Nat} (hk : 38 ≤ k) (r : Nat) :
    lowerSixModeWeight k (r + thetaWindowCenter k) ≤
      HalfPow.half * lowerSixModeWeight k r := by
  let c := thetaWindowCenter k
  let w := harmW k
  let sigma := w * w
  let delta := 2 * r * c + c * c
  change lowerSixModeWeight k (r + c) ≤
    HalfPow.half * lowerSixModeWeight k r
  have hexp : (r + c) * (r + c) = r * r + delta := by
    dsimp only [delta]
    rw [Nat.add_mul, Nat.mul_add]
    rw [Nat.mul_add]
    rw [show c * r = r * c from Nat.mul_comm c r]
    have htwo : 2 * r * c = r * c + r * c := by
      rw [show 2 * r = r + r by omega, Nat.add_mul]
    rw [htwo]
    omega
  have hsplit : lowerSixModeWeight k (r + c) ≈
      lowerSixModeWeight k r * qpow sigma delta := by
    unfold lowerSixModeWeight
    dsimp only [sigma, w]
    rw [hexp]
    exact HeatKernelRGStep.qpow_add _ _ _
  have hdouble : qpow sigma delta ≈ qpow w (delta + delta) := by
    dsimp only [sigma]
    refine Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w delta) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add w delta delta)
  have hD : k + 2 ≤ delta + delta := by
    have hc := thetaWindowCenter_sq_ge_harmonicDen hk
    dsimp only [c, delta] at hc ⊢
    omega
  have hwGain : qpow w (delta + delta) ≤ qpow w (k + 2) :=
    HeatKernelRGStep.qpow_antitone (harmW_nonneg k) (harmW_le_one k)
      (k + 2) (delta + delta) hD
  have hgain : qpow sigma delta ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hdouble)
      (Q'.le_trans' _ _ _ hwGain (harmonic_block_power_le_half k))
  have hW0 : (0 : Q') ≤ lowerSixModeWeight k r := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hmul : lowerSixModeWeight k r * qpow sigma delta ≤
      lowerSixModeWeight k r * HalfPow.half :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgain hW0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-- Uniform inter-block rate on the physical tail range. -/
def lowerSixHermiteBlockRate : Q' := qpow HalfPow.half 7

/-- Geometric closure multiplier `1/(1-2^-7)`. -/
def lowerSixHermiteBlockClosure : Q' := Q'.mkPos 128 127 (by decide)

private theorem harmonic_seven_blocks_le_rate (k : Nat) :
    qpow (harmW k) ((k + 2) * 7) ≤ lowerSixHermiteBlockRate := by
  let p := qpow (harmW k) (k + 2)
  have hp0 : (0 : Q') ≤ p :=
    qpow_nonneg _ (harmW_nonneg k) _
  have hp : p ≤ HalfPow.half := by
    dsimp only [p]
    exact harmonic_block_power_le_half k
  have hmono := FusedAmplitudeDerivation.qpow_mono_base hp0 hp 7
  unfold lowerSixHermiteBlockRate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (HeatKernelRGStep.qpow_qpow (harmW k) (k + 2) 7))) hmono

private theorem seven_den_le_double_center_delta
    {k r : Nat} (hk : 247 ≤ k)
    (hr : thetaWindowLeft k + 1 ≤ r) :
    7 * (k + 2) ≤
      (2 * r * thetaWindowCenter k +
        thetaWindowCenter k * thetaWindowCenter k) +
      (2 * r * thetaWindowCenter k +
        thetaWindowCenter k * thetaWindowCenter k) := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hnext : 2 * D + 1 < (c + 1) * (c + 1) := by
    rcases Nat.lt_or_ge (2 * D + 1) ((c + 1) * (c + 1)) with h | h
    · exact h
    · have hbad : c + 1 ≤ c := by
        dsimp only [c, D, thetaWindowCenter, thetaWindowLength] at h ⊢
        exact ChebOrthoMidpointEst.isqrt_ge h
      omega
  have hsquare : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  rw [hsquare] at hnext
  have htwoD : 2 * D < c * c + 2 * c := by omega
  have hscaled : 7 * (2 * D) < 7 * (c * c + 2 * c) := by
    omega
  have hc14 : 14 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 14 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  have hupper : 7 * (c * c + 2 * c) ≤ 8 * (c * c) := by
    rw [Nat.mul_add]
    have hsevenTwo : 7 * (2 * c) = 14 * c := by omega
    rw [hsevenTwo]
    omega
  have hseven : 7 * D ≤ 4 * (c * c) := by
    omega
  have hcr : c ≤ 2 * r := by
    dsimp only [c]
    unfold thetaWindowLeft at hr
    omega
  have hmul : c * c ≤ (2 * r) * c :=
    Nat.mul_le_mul_right c hcr
  dsimp only [c, D] at hseven hmul ⊢
  omega

/-- On `k ≥ 247`, one square-root block suppresses every tail mode by
the derived rate `2^-7`. -/
theorem lowerSixModeWeight_center_step_le_rate
    {k r : Nat} (hk : 247 ≤ k)
    (hr : thetaWindowLeft k + 1 ≤ r) :
    lowerSixModeWeight k (r + thetaWindowCenter k) ≤
      lowerSixHermiteBlockRate * lowerSixModeWeight k r := by
  let c := thetaWindowCenter k
  let w := harmW k
  let sigma := w * w
  let delta := 2 * r * c + c * c
  change lowerSixModeWeight k (r + c) ≤
    lowerSixHermiteBlockRate * lowerSixModeWeight k r
  have hexp : (r + c) * (r + c) = r * r + delta := by
    dsimp only [delta]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    rw [show c * r = r * c from Nat.mul_comm c r]
    have htwo : 2 * r * c = r * c + r * c := by
      rw [show 2 * r = r + r by omega, Nat.add_mul]
    rw [htwo]
    omega
  have hsplit : lowerSixModeWeight k (r + c) ≈
      lowerSixModeWeight k r * qpow sigma delta := by
    unfold lowerSixModeWeight
    dsimp only [sigma, w]
    rw [hexp]
    exact HeatKernelRGStep.qpow_add _ _ _
  have hdouble : qpow sigma delta ≈ qpow w (delta + delta) := by
    dsimp only [sigma]
    refine Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w delta) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add w delta delta)
  have hD : (k + 2) * 7 ≤ delta + delta := by
    have h := seven_den_le_double_center_delta hk hr
    dsimp only [c, delta] at h ⊢
    simpa [Nat.mul_comm] using h
  have hwGain : qpow w (delta + delta) ≤ qpow w ((k + 2) * 7) :=
    HeatKernelRGStep.qpow_antitone (harmW_nonneg k) (harmW_le_one k)
      ((k + 2) * 7) (delta + delta) hD
  have hgain : qpow sigma delta ≤ lowerSixHermiteBlockRate :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hdouble)
      (Q'.le_trans' _ _ _ hwGain (harmonic_seven_blocks_le_rate k))
  have hW0 : (0 : Q') ≤ lowerSixModeWeight k r := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hmul : lowerSixModeWeight k r * qpow sigma delta ≤
      lowerSixModeWeight k r * lowerSixHermiteBlockRate :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgain hW0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

private theorem envelope_finSum_add_block (f : Nat → Q') (a : Nat) : ∀ t,
    finSum f (a + t) ≈ finSum f a + finSum (fun s => f (a + s)) t
  | 0 => Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | t + 1 => by
      rw [show a + (t + 1) = (a + t) + 1 by omega,
        finSum_succ, finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (envelope_finSum_add_block f a t)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem envelope_finSum_block (f : Nat → Q') (c : Nat) : ∀ P,
    finSum f (P * c) ≈
      finSum (fun i => finSum (fun s => f (i * c + s)) c) P
  | 0 => by rw [Nat.zero_mul]; exact Q'.eqv_refl 0
  | P + 1 => by
      rw [Nat.succ_mul, finSum_succ]
      refine Q'.eqv_trans _ _ _ (envelope_finSum_add_block f (P * c) c) ?_
      exact Q'.add_eqv_congr_right _ _ _ (envelope_finSum_block f c P)

theorem lowerSixHermiteGaussianTailBlock_nonnegative
    (k i : Nat) :
    (0 : Q') ≤ lowerSixHermiteGaussianTailBlock k i := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun s => lowerSixModeWeight k (K + i * c + s)
  have hf : ∀ s, (0 : Q') ≤ f s := by
    intro s
    dsimp only [f]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hsum := RationalTail.finSum_monotone_of_nonneg f hf
    0 c (Nat.zero_le c)
  unfold lowerSixHermiteGaussianTailBlock
  dsimp only [c, K, f] at hsum ⊢
  exact hsum

theorem lowerSixHermiteGaussianTailBlock_step
    {k : Nat} (hk : 38 ≤ k) (i : Nat) :
    lowerSixHermiteGaussianTailBlock k (i + 1) ≤
      HalfPow.half * lowerSixHermiteGaussianTailBlock k i := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun s => lowerSixModeWeight k (K + (i + 1) * c + s)
  let g := fun s => HalfPow.half *
    lowerSixModeWeight k (K + i * c + s)
  have hterm : ∀ s, s < c → f s ≤ g s := by
    intro s _
    have hidx : K + (i + 1) * c + s = (K + i * c + s) + c := by
      rw [Nat.add_mul]
      omega
    dsimp only [f, g]
    rw [hidx]
    exact lowerSixModeWeight_center_step_le_half hk _
  have hsum := YMGap.Constructive.finSum_le_lt f g c hterm
  have hpull : HalfPow.half * lowerSixHermiteGaussianTailBlock k i ≈
      finSum g c := by
    unfold lowerSixHermiteGaussianTailBlock
    dsimp only [c, K, g]
    exact RationalTail.const_mul_finSum
      (fun s => lowerSixModeWeight k
        (thetaWindowLeft k + 1 + i * thetaWindowCenter k + s))
      HalfPow.half (thetaWindowCenter k)
  unfold lowerSixHermiteGaussianTailBlock
  dsimp only [c, K, f] at hsum ⊢
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

theorem lowerSixHermiteGaussianTailBlock_step_rate
    {k : Nat} (hk : 247 ≤ k) (i : Nat) :
    lowerSixHermiteGaussianTailBlock k (i + 1) ≤
      lowerSixHermiteBlockRate * lowerSixHermiteGaussianTailBlock k i := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun s => lowerSixModeWeight k (K + (i + 1) * c + s)
  let g := fun s => lowerSixHermiteBlockRate *
    lowerSixModeWeight k (K + i * c + s)
  have hterm : ∀ s, s < c → f s ≤ g s := by
    intro s _
    let r := K + i * c + s
    have hr : thetaWindowLeft k + 1 ≤ r := by
      dsimp only [r, K]
      omega
    have hidx : K + (i + 1) * c + s = r + c := by
      dsimp only [r]
      rw [Nat.add_mul]
      omega
    dsimp only [f, g]
    rw [hidx]
    exact lowerSixModeWeight_center_step_le_rate hk hr
  have hsum := YMGap.Constructive.finSum_le_lt f g c hterm
  have hpull : lowerSixHermiteBlockRate *
      lowerSixHermiteGaussianTailBlock k i ≈ finSum g c := by
    unfold lowerSixHermiteGaussianTailBlock
    dsimp only [c, K, g]
    exact RationalTail.const_mul_finSum
      (fun s => lowerSixModeWeight k
        (thetaWindowLeft k + 1 + i * thetaWindowCenter k + s))
      lowerSixHermiteBlockRate (thetaWindowCenter k)
  unfold lowerSixHermiteGaussianTailBlock
  dsimp only [c, K, f] at hsum ⊢
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

theorem lowerSixHermiteGaussianTailBlock_zero_le_head
    (k : Nat) :
    lowerSixHermiteGaussianTailBlock k 0 ≤
      Q'.ofNat (thetaWindowCenter k) *
        lowerSixModeWeight k (thetaWindowLeft k + 1) := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun s => lowerSixModeWeight k (K + s)
  have hhead0 : (0 : Q') ≤ lowerSixModeWeight k K := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hterm : ∀ s, s < c → f s ≤ lowerSixModeWeight k K := by
    intro s _
    have hindex : K * K ≤ (K + s) * (K + s) :=
      Nat.mul_le_mul (Nat.le_add_right K s) (Nat.le_add_right K s)
    dsimp only [f]
    unfold lowerSixModeWeight
    exact HeatKernelRGStep.qpow_antitone
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k))
      (square_harmW_le_one k) _ _ hindex
  have hcount := BondMovingMoment.finSum_le_count_mul hhead0 f c hterm
  unfold lowerSixHermiteGaussianTailBlock
  dsimp only [c, K, f] at hcount ⊢
  simpa using hcount

/-- The block sequence has a uniform geometric sum. -/
theorem lowerSixHermiteGaussianTailBlocks_le
    {k : Nat} (hk : 38 ≤ k) (P : Nat) :
    finSum (lowerSixHermiteGaussianTailBlock k) P ≤
      Q'.ofNat 2 *
        (Q'.ofNat (thetaWindowCenter k) *
          lowerSixModeWeight k (thetaWindowLeft k + 1)) := by
  let F0 := Q'.ofNat (thetaWindowCenter k) *
    lowerSixModeWeight k (thetaWindowLeft k + 1)
  let H := Q'.ofNat 2 * F0
  have hF0 : (0 : Q') ≤ F0 := by
    dsimp only [F0]
    exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (by
        unfold lowerSixModeWeight
        exact qpow_nonneg _
          (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _)
  have hH : (0 : Q') ≤ H :=
    Q'.mul_nonneg _ _ (by decide) hF0
  have hrec : F0 + HalfPow.half * H ≤ H := by
    have hhalf : HalfPow.half * (Q'.ofNat 2 * F0) ≈ F0 := by
      refine Q'.eqv_trans _ ((HalfPow.half * Q'.ofNat 2) * F0) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * F0) _
        (Q'.mul_eqv_congr_right _ _ F0 (by decide)) ?_
      exact Q'.one_mul_eqv F0
    apply Q'.le_of_eqv
    refine Q'.eqv_trans _ (F0 + F0) _
      (Q'.add_eqv_congr_left F0 _ _ (by
        dsimp only [H]
        exact hhalf)) ?_
    dsimp only [H]
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ (((1 : Q') + (1 : Q')) * F0) _
      (Q'.mul_eqv_congr_right _ _ F0 (by decide)) ?_
    refine Q'.eqv_trans _ ((1 : Q') * F0 + (1 : Q') * F0) _
      (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv F0) (Q'.one_mul_eqv F0)
  have hgeom := CharacterTail.geom_series_le
    (lowerSixHermiteGaussianTailBlock k) F0 HalfPow.half H
    HalfPow.half_nonneg hH
    (by
      dsimp only [F0]
      exact lowerSixHermiteGaussianTailBlock_zero_le_head k)
    (lowerSixHermiteGaussianTailBlock_step hk) hrec P
  dsimp only [H, F0] at hgeom ⊢
  exact hgeom

/-- Sharper block sum: retain the entire first square-root block exactly,
then pay the later blocks by the derived half-ratio. -/
theorem lowerSixHermiteGaussianTailBlocks_le_two_first
    {k : Nat} (hk : 38 ≤ k) (P : Nat) :
    finSum (lowerSixHermiteGaussianTailBlock k) P ≤
      Q'.ofNat 2 * lowerSixHermiteGaussianTailBlock k 0 := by
  let F0 := lowerSixHermiteGaussianTailBlock k 0
  let H := Q'.ofNat 2 * F0
  have hF0 : (0 : Q') ≤ F0 := by
    dsimp only [F0]
    exact lowerSixHermiteGaussianTailBlock_nonnegative k 0
  have hH : (0 : Q') ≤ H :=
    Q'.mul_nonneg _ _ (by decide) hF0
  have hrec : F0 + HalfPow.half * H ≤ H := by
    have hhalf : HalfPow.half * (Q'.ofNat 2 * F0) ≈ F0 := by
      refine Q'.eqv_trans _ ((HalfPow.half * Q'.ofNat 2) * F0) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * F0) _
        (Q'.mul_eqv_congr_right _ _ F0 (by decide)) ?_
      exact Q'.one_mul_eqv F0
    apply Q'.le_of_eqv
    refine Q'.eqv_trans _ (F0 + F0) _
      (Q'.add_eqv_congr_left F0 _ _ (by
        dsimp only [H]
        exact hhalf)) ?_
    dsimp only [H]
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ (((1 : Q') + (1 : Q')) * F0) _
      (Q'.mul_eqv_congr_right _ _ F0 (by decide)) ?_
    refine Q'.eqv_trans _ ((1 : Q') * F0 + (1 : Q') * F0) _
      (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv F0) (Q'.one_mul_eqv F0)
  have hgeom := CharacterTail.geom_series_le
    (lowerSixHermiteGaussianTailBlock k) F0 HalfPow.half H
    HalfPow.half_nonneg hH (Q'.le_refl' F0)
    (lowerSixHermiteGaussianTailBlock_step hk) hrec P
  dsimp only [H, F0] at hgeom ⊢
  exact hgeom

/-- Sharp geometric sum on the physical tail range. -/
theorem lowerSixHermiteGaussianTailBlocks_le_closure
    {k : Nat} (hk : 247 ≤ k) (P : Nat) :
    finSum (lowerSixHermiteGaussianTailBlock k) P ≤
      lowerSixHermiteBlockClosure *
        lowerSixHermiteGaussianTailBlock k 0 := by
  let F0 := lowerSixHermiteGaussianTailBlock k 0
  let H := lowerSixHermiteBlockClosure * F0
  have hF0 : (0 : Q') ≤ F0 := by
    dsimp only [F0]
    exact lowerSixHermiteGaussianTailBlock_nonnegative k 0
  have hrate : (0 : Q') ≤ lowerSixHermiteBlockRate := by
    unfold lowerSixHermiteBlockRate
    exact qpow_nonneg _ HalfPow.half_nonneg _
  have hclosure : (0 : Q') ≤ lowerSixHermiteBlockClosure := by
    unfold lowerSixHermiteBlockClosure
    decide
  have hH : (0 : Q') ≤ H :=
    Q'.mul_nonneg _ _ hclosure hF0
  have hcoef : (1 : Q') +
      lowerSixHermiteBlockRate * lowerSixHermiteBlockClosure ≈
        lowerSixHermiteBlockClosure := by
    unfold lowerSixHermiteBlockRate lowerSixHermiteBlockClosure
      HalfPow.half qpow
    decide
  have hrec : F0 + lowerSixHermiteBlockRate * H ≤ H := by
    apply Q'.le_of_eqv
    refine Q'.eqv_trans _
      (((1 : Q') + lowerSixHermiteBlockRate *
        lowerSixHermiteBlockClosure) * F0) _ ?_ ?_
    · dsimp only [H]
      envelope_ring
    · exact Q'.mul_eqv_congr_right _ _ F0 hcoef
  have hgeom := CharacterTail.geom_series_le
    (lowerSixHermiteGaussianTailBlock k) F0
    lowerSixHermiteBlockRate H hrate hH (Q'.le_refl' F0)
    (lowerSixHermiteGaussianTailBlock_step_rate hk) hrec P
  dsimp only [H, F0] at hgeom ⊢
  exact hgeom

/-- A square-root-block Gaussian upper bound valid for every finite tail
window.  Unlike a one-step geometric estimate, this has the correct
`O(thetaWindowCenter)` scale at the active cutoff. -/
theorem lowerSixHermiteWeightTail_le_blockEnvelope
    {k : Nat} (hk : 38 ≤ k) (M : Nat) :
    finSum
        (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)) M ≤
      Q'.ofNat 2 * lowerSixHermiteGaussianTailBlock k 0 := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun j => lowerSixModeWeight k (K + j)
  have hcpos : 0 < c := by
    dsimp only [c]
    exact ChebOrthoMidpointEst.isqrt_pos (by
      unfold thetaWindowLength
      omega)
  have hM : M ≤ (M + 1) * c := by
    have hmul : M * 1 ≤ M * c :=
      Nat.mul_le_mul_left M (show 1 ≤ c by omega)
    have hsucc : M * c ≤ (M + 1) * c :=
      Nat.mul_le_mul_right c (Nat.le_succ M)
    exact Nat.le_trans (by simpa using hmul) hsucc
  have hf0 : ∀ j, (0 : Q') ≤ f j := by
    intro j
    dsimp only [f]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hpad := RationalTail.finSum_monotone_of_nonneg f hf0
    M ((M + 1) * c) hM
  have hblocks : finSum f ((M + 1) * c) ≈
      finSum (lowerSixHermiteGaussianTailBlock k) (M + 1) := by
    refine Q'.eqv_trans _ _ _ (envelope_finSum_block f c (M + 1)) ?_
    apply RationalTail.finSum_eqv_congr
    intro i
    unfold lowerSixHermiteGaussianTailBlock
    dsimp only [f, c, K]
    apply RationalTail.finSum_eqv_congr
    intro s
    have hidx : thetaWindowLeft k + 1 +
        (i * thetaWindowCenter k + s) =
        thetaWindowLeft k + 1 + i * thetaWindowCenter k + s := by omega
    rw [hidx]
    exact Q'.eqv_refl _
  have hgeom := lowerSixHermiteGaussianTailBlocks_le_two_first hk (M + 1)
  have hstart : finSum
      (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)) M ≈
      finSum f M := by
    apply RationalTail.finSum_eqv_congr
    intro j
    dsimp only [f, K]
    rw [show thetaWindowLeft k + j + 1 =
      thetaWindowLeft k + 1 + j by omega]
    exact Q'.eqv_refl _
  dsimp only [f, K, c] at hpad hblocks hgeom ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
    (Q'.le_trans' _ _ _ hpad
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hblocks) hgeom))

/-- Sharp finite-tail bound used by the physical `k ≥ 247` envelope. -/
theorem lowerSixHermiteWeightTail_le_sharpBlockEnvelope
    {k : Nat} (hk : 247 ≤ k) (M : Nat) :
    finSum
        (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)) M ≤
      lowerSixHermiteBlockClosure *
        lowerSixHermiteGaussianTailBlock k 0 := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun j => lowerSixModeWeight k (K + j)
  have hcpos : 0 < c := by
    dsimp only [c]
    exact ChebOrthoMidpointEst.isqrt_pos (by
      unfold thetaWindowLength
      omega)
  have hM : M ≤ (M + 1) * c := by
    have hmul : M * 1 ≤ M * c :=
      Nat.mul_le_mul_left M (show 1 ≤ c by omega)
    have hsucc : M * c ≤ (M + 1) * c :=
      Nat.mul_le_mul_right c (Nat.le_succ M)
    exact Nat.le_trans (by simpa using hmul) hsucc
  have hf0 : ∀ j, (0 : Q') ≤ f j := by
    intro j
    dsimp only [f]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hpad := RationalTail.finSum_monotone_of_nonneg f hf0
    M ((M + 1) * c) hM
  have hblocks : finSum f ((M + 1) * c) ≈
      finSum (lowerSixHermiteGaussianTailBlock k) (M + 1) := by
    refine Q'.eqv_trans _ _ _ (envelope_finSum_block f c (M + 1)) ?_
    apply RationalTail.finSum_eqv_congr
    intro i
    unfold lowerSixHermiteGaussianTailBlock
    dsimp only [f, c, K]
    apply RationalTail.finSum_eqv_congr
    intro s
    have hidx : thetaWindowLeft k + 1 +
        (i * thetaWindowCenter k + s) =
        thetaWindowLeft k + 1 + i * thetaWindowCenter k + s := by omega
    rw [hidx]
    exact Q'.eqv_refl _
  have hgeom := lowerSixHermiteGaussianTailBlocks_le_closure hk (M + 1)
  have hstart : finSum
      (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)) M ≈
      finSum f M := by
    apply RationalTail.finSum_eqv_congr
    intro j
    dsimp only [f, K]
    rw [show thetaWindowLeft k + j + 1 =
      thetaWindowLeft k + 1 + j by omega]
    exact Q'.eqv_refl _
  dsimp only [f, K, c] at hpad hblocks hgeom ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
    (Q'.le_trans' _ _ _ hpad
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hblocks) hgeom))

/-- Closed square-root-window replacement for the long second-mass tail. -/
def lowerSixHermiteSecondMassTailBlockBound (k : Nat) : Q' :=
  (Q'.ofNat 15630 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) *
    (lowerSixHermiteBlockClosure * lowerSixHermiteGaussianTailBlock k 0)

theorem lowerSixHermiteSecondMassTail_le_blockBound
    {k : Nat} (hk : 247 ≤ k) :
    lowerSixHermiteSecondMassTail k ≤
      lowerSixHermiteSecondMassTailBlockBound k := by
  let C := Q'.ofNat 15630 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  let M := growingAnchor k - thetaWindowLeft k
  let W := fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)
  have htail : finSum W M ≤
      lowerSixHermiteBlockClosure * lowerSixHermiteGaussianTailBlock k 0 := by
    dsimp only [W, M]
    exact lowerSixHermiteWeightTail_le_sharpBlockEnvelope hk _
  have hD : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC : (0 : Q') ≤ C := by
    dsimp only [C]
    exact Q'.mul_nonneg _ _ (by decide) (ringQpow_nonnegative hD 4)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C htail hC
  have hmass : C * finSum W M ≈ lowerSixHermiteSecondMassTail k := by
    unfold lowerSixHermiteSecondMassTail
      lowerSixHermiteSecondMassNumerator
    dsimp only [C, W, M]
    exact RationalTail.const_mul_finSum
      (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1))
      (Q'.ofNat 15630 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 4)
      (growingAnchor k - thetaWindowLeft k)
  unfold lowerSixHermiteSecondMassTailBlockBound
  dsimp only [C] at hscaled
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hmass) hscaled

/-- The prefix-retaining second-flux envelope.  Unlike the crude bound that
drops the entire negative second remainder, this keeps exactly the low-mode
reserve needed at the induction anchor. -/
def lowerSixHermiteSecondTailEnvelope (k : Nat) : Q' :=
  (lowerSixHermiteSecondClearingScale k * lowerSixHermiteDebtPrefix k +
    (lowerSixHermiteSecondFluxNumerator k (growingAnchor k + 1) +
      -lowerSixHermiteSecondFluxNumerator k (thetaWindowLeft k + 1))) +
    lowerSixHermiteSecondMassTail k

/-- The fully finite symbolic envelope: it retains the debt prefix and one
square-root Gaussian block, but contains no long tail sum. -/
def lowerSixHermiteSecondWindowEnvelope (k : Nat) : Q' :=
  (lowerSixHermiteSecondClearingScale k * lowerSixHermiteDebtPrefix k +
    (lowerSixHermiteSecondFluxNumerator k (growingAnchor k + 1) +
      -lowerSixHermiteSecondFluxNumerator k (thetaWindowLeft k + 1))) +
    lowerSixHermiteSecondMassTailBlockBound k

/-- The remote upper endpoint is always nonpositive and can be deleted from
the symbolic window. -/
def lowerSixHermiteSecondWindowEnvelopeNoUpper (k : Nat) : Q' :=
  (lowerSixHermiteSecondClearingScale k * lowerSixHermiteDebtPrefix k +
    -lowerSixHermiteSecondFluxNumerator k (thetaWindowLeft k + 1)) +
    lowerSixHermiteSecondMassTailBlockBound k

theorem lowerSixHermiteSecondWindowEnvelope_le_noUpper (k : Nat) :
    lowerSixHermiteSecondWindowEnvelope k ≤
      lowerSixHermiteSecondWindowEnvelopeNoUpper k := by
  let P := lowerSixHermiteSecondClearingScale k *
    lowerSixHermiteDebtPrefix k
  let F := lowerSixHermiteSecondFluxNumerator k (growingAnchor k + 1)
  let L := lowerSixHermiteSecondFluxNumerator k (thetaWindowLeft k + 1)
  let M := lowerSixHermiteSecondMassTailBlockBound k
  have hF : F ≤ (0 : Q') := by
    dsimp only [F]
    exact lowerSixHermiteSecondFluxNumerator_nonpositive _ _
  have hdrop0 := Q'.add_le_add_right F (0 : Q') (-L) hF
  have hdrop : F + -L ≤ -L :=
    Q'.le_trans' _ _ _ hdrop0
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-L))))
  have hprefix := Q'.add_le_add_left P _ _ hdrop
  have hmass := Q'.add_le_add_right _ _ M hprefix
  unfold lowerSixHermiteSecondWindowEnvelope
    lowerSixHermiteSecondWindowEnvelopeNoUpper
  dsimp only [P, F, L, M] at hmass ⊢
  exact hmass

theorem lowerSixHermiteSecondTailEnvelope_le_windowEnvelope
    {k : Nat} (hk : 247 ≤ k) :
    lowerSixHermiteSecondTailEnvelope k ≤
      lowerSixHermiteSecondWindowEnvelope k := by
  unfold lowerSixHermiteSecondTailEnvelope
    lowerSixHermiteSecondWindowEnvelope
  exact Q'.add_le_add_left _ _ _
    (lowerSixHermiteSecondMassTail_le_blockBound hk)

private theorem thetaWindowLeft_le_anchor_for_second
    {k : Nat} (hk : 38 ≤ k) :
    thetaWindowLeft k ≤ growingAnchor k := by
  have hc := thetaWindowCenter_le_harmonicDen hk
  unfold thetaWindowLeft growingAnchor
  have hdiv := Nat.div_le_self (thetaWindowCenter k) 2
  omega

theorem lowerSixHermiteSecondMassSum_split
    {k : Nat} (hk : 38 ≤ k) :
    finSum
        (fun j => lowerSixHermiteSecondMassNumerator k (j + 1))
        (growingAnchor k) ≈
      finSum
          (fun j => lowerSixHermiteSecondMassNumerator k (j + 1))
          (thetaWindowLeft k) +
        lowerSixHermiteSecondMassTail k := by
  have hle := thetaWindowLeft_le_anchor_for_second hk
  have hlen : thetaWindowLeft k +
      (growingAnchor k - thetaWindowLeft k) = growingAnchor k := by omega
  unfold lowerSixHermiteSecondMassTail
  simpa only [hlen] using (YMGap.Constructive.finSum_split
    (fun j => lowerSixHermiteSecondMassNumerator k (j + 1))
    (thetaWindowLeft k)
    (growingAnchor k - thetaWindowLeft k))

theorem lowerSixHermiteSecondRemainderSum_split
    {k : Nat} (hk : 38 ≤ k) :
    finSum
        (fun j => lowerSixHermiteSecondRemainder k (j + 1))
        (growingAnchor k) ≈
      lowerSixHermiteSecondRemainderPrefix k +
        lowerSixHermiteSecondRemainderTail k := by
  have hle := thetaWindowLeft_le_anchor_for_second hk
  have hlen : thetaWindowLeft k +
      (growingAnchor k - thetaWindowLeft k) = growingAnchor k := by omega
  unfold lowerSixHermiteSecondRemainderPrefix
    lowerSixHermiteSecondRemainderTail
  simpa only [hlen] using (YMGap.Constructive.finSum_split
    (fun j => lowerSixHermiteSecondRemainder k (j + 1))
    (thetaWindowLeft k)
    (growingAnchor k - thetaWindowLeft k))

/-- Once the weight-free second bracket is nonpositive on the retained tail,
the entire second-remainder tail is nonpositive.  This is the pointwise-to-
summed sign bridge used by the prefix-retaining telescope. -/
theorem lowerSixHermiteSecondRemainderTail_nonpositive_of_brackets
    {k : Nat}
    (hbracket : ∀ j, j < growingAnchor k - thetaWindowLeft k →
      lowerSixHermiteSecondRemainderBracket k
        (thetaWindowLeft k + j + 1) ≤ (0 : Q')) :
    lowerSixHermiteSecondRemainderTail k ≤ (0 : Q') := by
  let f := fun j => lowerSixHermiteSecondRemainder k
    (thetaWindowLeft k + j + 1)
  let z := fun _ : Nat => (0 : Q')
  have hterm : ∀ j, j < growingAnchor k - thetaWindowLeft k →
      f j ≤ z j := by
    intro j hj
    dsimp only [f, z]
    exact lowerSixHermiteSecondRemainder_nonpositive_of_bracket
      (hbracket j hj)
  have hsum := YMGap.Constructive.finSum_le_lt f z
    (growingAnchor k - thetaWindowLeft k) hterm
  unfold lowerSixHermiteSecondRemainderTail
  exact Q'.le_trans' _ _ _ hsum
    (RationalTail.zero_eta_bound
      (growingAnchor k - thetaWindowLeft k))

private def pSecondPrefixCollapseL : PE :=
  -- `(FN-F1) + (MP+MT) + (RP+RT)`
  .add
    (.add
      (.add (.var 0) (.neg (.var 1)))
      (.add (.var 3) (.var 4)))
    (.add (.var 5) (.var 6))

private def pSecondPrefixCollapseR : PE :=
  -- `((AP + (FN-FD)) + MT) + RT`, with
  -- `AP = (FD-F1)+MP+RP`.
  .add
    (.add
      (.add
        (.add
          (.add (.var 2) (.neg (.var 1)))
          (.var 3))
        (.var 5))
      (.add (.var 0) (.neg (.var 2))))
    (.add (.var 4) (.var 6))

private theorem pSecondPrefixCollapse_normal :
    RingNormaliser.normalize pSecondPrefixCollapseL =
      RingNormaliser.normalize pSecondPrefixCollapseR := by decide

private theorem secondPrefixCollapse_algebra
    (FN F1 FD MP MT RP RT : Q') :
    ((FN + -F1) + (MP + MT)) + (RP + RT) ≈
      ((((FD + -F1) + MP) + RP) + (FN + -FD)) + (MT + RT) := by
  simpa [pSecondPrefixCollapseL, pSecondPrefixCollapseR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSecondPrefixCollapseL pSecondPrefixCollapseR
      pSecondPrefixCollapse_normal
      (fun | 0 => FN | 1 => F1 | 2 => FD | 3 => MP |
        4 => MT | 5 => RP | _ => RT))

/-- Exact prefix-retaining second-flux normal form. -/
theorem lowerSixHermiteDebtFinSum_second_flux_prefix_retaining
    {k : Nat} (hk : 38 ≤ k) :
    lowerSixHermiteSecondClearingScale k *
        finSum
          (fun j => lowerSixHermiteDebtCell k (j + 1))
          (growingAnchor k) ≈
      lowerSixHermiteSecondTailEnvelope k +
        lowerSixHermiteSecondRemainderTail k := by
  let A := lowerSixHermiteSecondClearingScale k
  let FN := lowerSixHermiteSecondFluxNumerator k (growingAnchor k + 1)
  let F1 := lowerSixHermiteSecondFluxNumerator k 1
  let FD := lowerSixHermiteSecondFluxNumerator k (thetaWindowLeft k + 1)
  let MP := finSum
    (fun j => lowerSixHermiteSecondMassNumerator k (j + 1))
    (thetaWindowLeft k)
  let MT := lowerSixHermiteSecondMassTail k
  let RP := lowerSixHermiteSecondRemainderPrefix k
  let RT := lowerSixHermiteSecondRemainderTail k
  let DP := lowerSixHermiteDebtPrefix k
  let DS := finSum
    (fun j => lowerSixHermiteDebtCell k (j + 1)) (growingAnchor k)
  let MS := finSum
    (fun j => lowerSixHermiteSecondMassNumerator k (j + 1))
    (growingAnchor k)
  let RS := finSum
    (fun j => lowerSixHermiteSecondRemainder k (j + 1))
    (growingAnchor k)
  have hfull : A * DS ≈ ((FN + -F1) + MS) + RS := by
    dsimp only [A, DS, FN, F1, MS, RS]
    exact lowerSixHermiteDebtFinSum_second_flux k (growingAnchor k)
  have hmass : MS ≈ MP + MT := by
    dsimp only [MS, MP, MT]
    exact lowerSixHermiteSecondMassSum_split hk
  have hrem : RS ≈ RP + RT := by
    dsimp only [RS, RP, RT]
    exact lowerSixHermiteSecondRemainderSum_split hk
  have hpref' : A * DP ≈ ((FD + -F1) + MP) + RP := by
    dsimp only [A, DP, FD, F1, MP, RP,
      lowerSixHermiteDebtPrefix, lowerSixHermiteSecondRemainderPrefix]
    exact lowerSixHermiteDebtFinSum_second_flux k (thetaWindowLeft k)
  change A * DS ≈ (((A * DP + (FN + -FD)) + MT) + RT)
  refine Q'.eqv_trans _
      (((FN + -F1) + (MP + MT)) + (RP + RT)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _ hfull ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left _ _ _ hmass) hrem
  refine Q'.eqv_trans _
      (((((FD + -F1) + MP) + RP) + (FN + -FD)) + (MT + RT)) _
      (secondPrefixCollapse_algebra FN F1 FD MP MT RP RT) ?_
  refine Q'.eqv_trans _
      (((A * DP) + (FN + -FD)) + (MT + RT)) _ ?_ ?_
  · have hinner :
        ((((FD + -F1) + MP) + RP) + (FN + -FD)) ≈
          (A * DP) + (FN + -FD) :=
      Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hpref')
    exact Q'.add_eqv_congr_right _ _ _ hinner
  · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

theorem lowerSixHermiteSecondClearingScale_pos (k : Nat) :
    (0 : Q') < lowerSixHermiteSecondClearingScale k := by
  have hD : (0 : Q') < Q'.ofNat (k + 2) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Q'.ofNat_succ_pos (k + 1))
  have hpow : (0 : Q') <
      RingNormaliser.qpow (Q'.ofNat (k + 2)) 2 :=
    ringQpow_positive hD 2
  unfold lowerSixHermiteSecondClearingScale
  exact Q'.mul_pos (by decide) hpow

/-- Production-facing reduction furnished by the prefix-retaining telescope.
The two residuals are now separated cleanly: a tail sign theorem for the
second remainder, and one explicit envelope comparison. -/
theorem remainderDebt_le_linearHead_of_secondFlux
    {k : Nat} (hk : 48 ≤ k)
    (htail : lowerSixHermiteSecondRemainderTail k ≤ (0 : Q'))
    (henvelope : lowerSixHermiteSecondTailEnvelope k ≤
      lowerSixHermiteSecondClearingScale k *
        lowerSixHermiteLinearHeadMassFloor k) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
      lowerSixHermiteLinearHeadMassFloor k := by
  let A := lowerSixHermiteSecondClearingScale k
  let DS := finSum
    (fun j => lowerSixHermiteDebtCell k (j + 1)) (growingAnchor k)
  let E := lowerSixHermiteSecondTailEnvelope k
  let RT := lowerSixHermiteSecondRemainderTail k
  let H := lowerSixHermiteLinearHeadMassFloor k
  let Debt := -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k)
  have hnormal : A * DS ≈ E + RT := by
    dsimp only [A, DS, E, RT]
    exact lowerSixHermiteDebtFinSum_second_flux_prefix_retaining (by omega)
  have hdrop : E + RT ≤ E := by
    have hadd := Q'.add_le_add_left E RT 0 htail
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv E))
  have hscaledDS : A * DS ≤ A * H := by
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormal) hdrop)
      henvelope
  have hbridge : DS ≈ Debt := by
    dsimp only [DS, Debt]
    exact lowerSixHermiteDebtFinSum_eqv_remainderDebt k
  have hscaledDebt : A * Debt ≤ A * H :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_eqv_congr_left A _ _ hbridge))) hscaledDS
  exact Q'.le_of_mul_le_mul_left hscaledDebt
    (lowerSixHermiteSecondClearingScale_pos k)

/-- Closed-window consumer.  The long Gaussian mass tail and summed
second-remainder sign have both been discharged; the remaining hypotheses
are one finite bracket window and one finite symbolic envelope comparison. -/
theorem remainderDebt_le_linearHead_of_secondWindow
    {k : Nat} (hk : 247 ≤ k)
    (hbracket : ∀ j, j < growingAnchor k - thetaWindowLeft k →
      lowerSixHermiteSecondRemainderBracket k
        (thetaWindowLeft k + j + 1) ≤ (0 : Q'))
    (hwindow : lowerSixHermiteSecondWindowEnvelope k ≤
      lowerSixHermiteSecondClearingScale k *
        lowerSixHermiteLinearHeadMassFloor k) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
      lowerSixHermiteLinearHeadMassFloor k := by
  apply remainderDebt_le_linearHead_of_secondFlux (by omega)
  · exact lowerSixHermiteSecondRemainderTail_nonpositive_of_brackets hbracket
  · exact Q'.le_trans' _ _ _
      (lowerSixHermiteSecondTailEnvelope_le_windowEnvelope (by omega))
      hwindow

def negativeNetModes (k : Nat) : List Nat :=
  (List.range (growingAnchor k)).map (fun j => j + 1) |>.filter
    (fun n => decide (¬ ((0 : Q') ≤ netBracket k n)))

/-- Stronger exact fence: even after adding the positive mass, the finite-D
cell is negative at mode twenty.  B cannot be proved termwise. -/
theorem mass_plus_remainder_pointwise_nonnegative_fails_k247_n20 :
    ¬ ((0 : Q') ≤
      lowerSixDiscreteHermiteMassNumerator 247 20 +
        lowerSixDiscreteHermiteRemainder 247 20) := by
  unfold lowerSixDiscreteHermiteRemainder
    lowerSixDiscreteHermiteMassNumerator
    lowerSixDiscreteHermiteFluxNumerator lowerSixDiscreteHermiteFluxPoly
    lowerSixQuadraticTaylorWeightedTerm lowerSixQuadraticTaylorCarrier
    lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff
    lowerSixDriftExcess lowerSixModeWeight lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope driftDen harmW harmU
    oneSub unit RingNormaliser.qpow qpow
  decide

#print axioms mass_add_remainder_eqv_weight_mul_netBracket
#print axioms massSum_add_remainderSum_eqv_weightedNetBracketSum
#print axioms one_add_lowerSixHermiteWeightSum_eqv_thetaCentered0
#print axioms lowerSixHermiteMassSum_eqv_scaledWeightSum
#print axioms lowerSixHermiteMassSum_ge_half_head
#print axioms lowerSixHermiteMassSum_ge_dynamic_head
#print axioms lowerSixHermiteLinearHeadCell_nonnegative
#print axioms lowerSixHermiteLinearHeadSum_nonnegative
#print axioms lowerSixHermiteLinearHeadSum_eqv_closed
#print axioms lowerSixHermiteLinearHeadMassFloor_le_mass
#print axioms lowerSixHermiteMassSum_nonnegative
#print axioms mass_add_remainderSum_nonnegative_of_quarter_envelope
#print axioms mass_add_remainderSum_nonnegative_of_linearHead_payment
#print axioms hermiteDebt_second_flux_identity
#print axioms lowerSixHermiteDebtCell_second_flux
#print axioms lowerSixHermiteDebtFinSum_second_flux
#print axioms lowerSixHermiteDebtFinSum_eqv_remainderDebt
#print axioms mass_plus_remainder_pointwise_nonnegative_fails_k247_n20
#print axioms lowerSixHermiteFirstRemainder_eqv_weight_mul_bracket
#print axioms lowerSixHermiteSecondRemainder_eqv_weight_mul_bracket
#print axioms lowerSixHermiteSecondRemainder_nonpositive_of_bracket
#print axioms lowerSixModeWeight_center_step_le_rate
#print axioms lowerSixHermiteGaussianTailBlock_step_rate
#print axioms lowerSixHermiteGaussianTailBlocks_le_closure
#print axioms lowerSixHermiteWeightTail_le_sharpBlockEnvelope
#print axioms lowerSixHermiteSecondMassTail_le_blockBound
#print axioms lowerSixHermiteSecondTailEnvelope_le_windowEnvelope
#print axioms lowerSixHermiteSecondRemainderTail_nonpositive_of_brackets
#print axioms lowerSixHermiteDebtFinSum_second_flux_prefix_retaining
#print axioms lowerSixHermiteSecondClearingScale_pos
#print axioms remainderDebt_le_linearHead_of_secondFlux
#print axioms remainderDebt_le_linearHead_of_secondWindow
#print axioms lowerSixHermiteSecondFluxPoly_nonpositive
#print axioms lowerSixHermiteSecondFluxNumerator_nonpositive
#print axioms lowerSixHermiteSecondWindowEnvelope_le_noUpper
#print axioms lowerSixWithinBlockRate_decrement
#print axioms lowerSixWithinBlockRate_geomSum_cleared
#print axioms lowerSixModeWeight_firstBlock_le_geometric
#print axioms lowerSixHermiteGaussianTailBlock_le_geometric
#print axioms lowerSixHermiteGaussianTailBlock_cleared

end YMGap.Continuum.ScratchHermiteSummedEnvelope
