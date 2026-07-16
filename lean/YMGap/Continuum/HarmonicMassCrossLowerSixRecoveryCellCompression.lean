/-
Exact compression of the lower-six cumulative recovery slack.

The window prefix ends at `R = thetaWindowRight k`, while the recovery
reserve begins at `R+1` and ends at `2c`, where
`c = thetaWindowCenter k`.  Their sum therefore forgets the auxiliary
window edge completely: it is the left endpoint contribution plus the
unbroken Dirichlet block through mode `2c`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- The exact recovery payment slack.  Its nonnegativity is equivalent to
`-lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k`. -/
def lowerSixRecoverySlack (k : Nat) : Q' :=
  lowerSixWindowPrefix k + lowerSixRecoveryReserve k

/-- The same slack after removing the artificial right-window split. -/
def lowerSixCenterSlack (k : Nat) : Q' :=
  Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
    finSum (fun j => lowerSixDirichletIncrement k (j + 1))
      (2 * thetaWindowCenter k)

/-- The same expression with the square-root center exposed as an independent
parameter.  This is the coordinate used for finite differences inside one
fixed-center cell. -/
def lowerSixFixedCenterSlack (k c : Nat) : Q' :=
  Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
    finSum (fun j => lowerSixDirichletIncrement k (j + 1)) (2 * c)

theorem lowerSixCenterSlack_eqv_fixed (k : Nat) :
    lowerSixCenterSlack k ≈
      lowerSixFixedCenterSlack k (thetaWindowCenter k) := by
  exact Q'.eqv_refl _

private theorem thetaWindowRight_le_twice_center (k : Nat) :
    thetaWindowRight k ≤ 2 * thetaWindowCenter k := by
  unfold thetaWindowRight
  have h := Nat.div_le_self (thetaWindowCenter k) 4
  omega

/-- The exact payment slack is the endpoint plus every Dirichlet cell from
mode one through mode `2 * thetaWindowCenter k`.  In particular all
dependence on `thetaWindowRight` and its division by four cancels. -/
theorem lowerSixRecoverySlack_eqv_centerSlack (k : Nat) :
    lowerSixRecoverySlack k ≈ lowerSixCenterSlack k := by
  let R := thetaWindowRight k
  let C := 2 * thetaWindowCenter k
  let f := fun j => lowerSixDirichletIncrement k (j + 1)
  have hRC : R ≤ C := by
    dsimp only [R, C]
    exact thetaWindowRight_le_twice_center k
  have hcount : C = R + (C - R) := by omega
  have hsplit := finSum_split f R (C - R)
  rw [← hcount] at hsplit
  have htail :
      finSum
          (fun j => lowerSixDirichletIncrement k (R + 1 + j))
          (C - R) ≈
        finSum (fun j => f (R + j)) (C - R) := by
    exact finSum_eqv_congr _ _ (fun j => by
      dsimp only [f]
      have hidx : R + 1 + j = R + j + 1 := by omega
      rw [hidx]
      exact Q'.eqv_refl _) _
  unfold lowerSixRecoverySlack lowerSixCenterSlack
    lowerSixWindowPrefix lowerSixRecoveryReserve lowerSixRecoveryCount
  dsimp only [R, C, f] at hsplit htail ⊢
  let endpoint := Q'.ofNat 4 * integerThetaTerm (harmW k) 1
  let head :=
    finSum (fun j => lowerSixDirichletIncrement k (j + 1))
      (thetaWindowRight k)
  let tail :=
    finSum
      (fun j => lowerSixDirichletIncrement k
        (thetaWindowRight k + 1 + j))
      (2 * thetaWindowCenter k - thetaWindowRight k)
  let shifted :=
    finSum
      (fun j => lowerSixDirichletIncrement k
        (thetaWindowRight k + j + 1))
      (2 * thetaWindowCenter k - thetaWindowRight k)
  let full :=
    finSum (fun j => lowerSixDirichletIncrement k (j + 1))
      (2 * thetaWindowCenter k)
  change (endpoint + head) + tail ≈ endpoint + full
  have htail' : tail ≈ shifted := by
    exact htail
  have hsplit' : full ≈ head + shifted := by
    exact hsplit
  refine Q'.eqv_trans _ (endpoint + (head + tail)) _
    (Q'.add_assoc_eqv endpoint head tail) ?_
  refine Q'.eqv_trans _ (endpoint + (head + shifted)) _
    (Q'.add_eqv_congr_left endpoint _ _
      (Q'.add_eqv_congr_left head _ _ htail')) ?_
  exact Q'.add_eqv_congr_left endpoint _ _ (Q'.eqv_symm hsplit')

/-- The first center transition is an exact fence against a universal
"center jumps are nonnegative" argument: the center moves from ten to eleven
between scales 57 and 58, but the compressed slack strictly decreases. -/
theorem lowerSixCenterSlack_crossing_nonnegative_fails_57_58 :
    (thetaWindowCenter 57 = 10 ∧ thetaWindowCenter 58 = 11) ∧
      ¬ (lowerSixCenterSlack 57 ≤ lowerSixCenterSlack 58) := by
  unfold lowerSixCenterSlack lowerSixDirichletIncrement
    lowerSixDirichletProfile thetaDirichletCell thetaRootTerm
    integerThetaTerm thetaWindowCenter thetaWindowLength harmW harmU
    oneSub unit qpow
  decide

#print axioms lowerSixCenterSlack_eqv_fixed
#print axioms lowerSixRecoverySlack_eqv_centerSlack
#print axioms lowerSixCenterSlack_crossing_nonnegative_fails_57_58

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryCellCompression
