/-
# Exact shell commutator for the ordered Racah outer shifts

The two physical `N-2` channel families reconstruct every parent factorial
carrier.  Their correction coefficients, however, are shifted.  This file
performs the resulting algebra exactly: four shifted shell equations reduce
the parent shell residual to an exchange-operator commutator plus the explicit
coefficient commutator.  No vanishing of either commutator is assumed here.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftCoefficientRemainder

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftShellCommutator

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftTransport
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem split_difference (X Y Z : Q') :
    X + -Z ≈ (X + -Y) + (Y + -Z) := by
  refine Q'.eqv_symm (Q'.eqv_trans _
    ((X + -Z) + ((-Y) + Y)) _ (by ring_qeqv) ?_)
  refine Q'.eqv_trans _ ((X + -Z) + 0) _
    (Q'.add_eqv_congr_left (X + -Z) _ _ (Q'.neg_add_self_eqv Y)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (X + -Z))

/-- A scalar three-carrier correction row. -/
def correctionCarrierRow
    (L D U xm x xp : Q') : Q' :=
  L * xm + D * x + U * xp

/-- The correction row at one physical shell coordinate. -/
def shellCorrectionRHS {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  correctionCarrierRow
    (omegaCorrectionLowerCoefficient a b c d q.p)
    (omegaCorrectionDiagonalCoefficient a b c d q.p)
    (omegaCorrectionUpperCoefficient a b c d q.p)
    (rightShellFactorialCoefficient qm i j l)
    (rightShellFactorialCoefficient q i j l)
    (rightShellFactorialCoefficient qp i j l)

/-- The exchange side of one shell correction row. -/
def shellCorrectionLHS {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) : Q' :=
  omegaExchangeCorrection a b c
    (fun u v w => rightShellFactorialCoefficient
      (reducePositiveInnerRightChannel q hp) u v w) i j l

/-- Four-direction Euler reconstruction applied to the two shifted correction
rows. -/
def outerShiftShellRHS {a b c d : Nat}
    (qms qs qps : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qmt qt qpt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (i j l : Nat) : Q' :=
  Q'.ofNat i *
      (Q'.ofNat (b - j) * shellCorrectionRHS qms qs qps (i - 1) j l +
        Q'.ofNat (c - l) * shellCorrectionRHS qmt qt qpt (i - 1) j l) +
    -(Q'.ofNat (a - i) *
      (Q'.ofNat j * shellCorrectionRHS qms qs qps i (j - 1) l +
        Q'.ofNat l * shellCorrectionRHS qmt qt qpt i j (l - 1)))

/-- The same four-direction reconstruction applied to the exchange sides of
the shifted shell equations. -/
def outerShiftShellLHS {a b c d : Nat}
    (qs : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (hps : 0 < qs.p) (hpt : 0 < qt.p)
    (i j l : Nat) : Q' :=
  Q'.ofNat i *
      (Q'.ofNat (b - j) * shellCorrectionLHS qs hps (i - 1) j l +
        Q'.ofNat (c - l) * shellCorrectionLHS qt hpt (i - 1) j l) +
    -(Q'.ofNat (a - i) *
      (Q'.ofNat j * shellCorrectionLHS qs hps i (j - 1) l +
        Q'.ofNat l * shellCorrectionLHS qt hpt i j (l - 1)))

/-- Four shifted shell equations reconstruct their four weighted correction
rows. -/
theorem outerShiftShellLHS_eq_rhs_of_four
    {a b c d : Nat}
    (qms qs qps : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qmt qt qpt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (hps : 0 < qs.p) (hpt : 0 < qt.p)
    (i j l : Nat)
    (hs0 : OmegaCorrectionShellAt qms qs qps hps (i - 1) j l)
    (ht0 : OmegaCorrectionShellAt qmt qt qpt hpt (i - 1) j l)
    (hs1 : OmegaCorrectionShellAt qms qs qps hps i (j - 1) l)
    (ht1 : OmegaCorrectionShellAt qmt qt qpt hpt i j (l - 1)) :
    outerShiftShellLHS qs qt hps hpt i j l ≈
      outerShiftShellRHS qms qs qps qmt qt qpt i j l := by
  have hs0' : shellCorrectionLHS qs hps (i - 1) j l ≈
      shellCorrectionRHS qms qs qps (i - 1) j l := by
    simpa only [shellCorrectionLHS, shellCorrectionRHS,
      correctionCarrierRow] using hs0
  have ht0' : shellCorrectionLHS qt hpt (i - 1) j l ≈
      shellCorrectionRHS qmt qt qpt (i - 1) j l := by
    simpa only [shellCorrectionLHS, shellCorrectionRHS,
      correctionCarrierRow] using ht0
  have hs1' : shellCorrectionLHS qs hps i (j - 1) l ≈
      shellCorrectionRHS qms qs qps i (j - 1) l := by
    simpa only [shellCorrectionLHS, shellCorrectionRHS,
      correctionCarrierRow] using hs1
  have ht1' : shellCorrectionLHS qt hpt i j (l - 1) ≈
      shellCorrectionRHS qmt qt qpt i j (l - 1) := by
    simpa only [shellCorrectionLHS, shellCorrectionRHS,
      correctionCarrierRow] using ht1
  unfold outerShiftShellLHS outerShiftShellRHS
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hs0')
        (Q'.mul_eqv_congr_left _ _ _ ht0')))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ hs1')
          (Q'.mul_eqv_congr_left _ _ _ ht1'))))

/-- The parent correction row with each of its three carriers replaced by
the exact two-direction reconstruction. -/
def parentReconstructedShellRHS {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (qms qs qps : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qmt qt qpt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (i j l : Nat) : Q' :=
  correctionCarrierRow
    (omegaCorrectionLowerCoefficient a b c d q.p)
    (omegaCorrectionDiagonalCoefficient a b c d q.p)
    (omegaCorrectionUpperCoefficient a b c d q.p)
    (outerShiftReconstruction qms qmt i j l)
    (outerShiftReconstruction qs qt i j l)
    (outerShiftReconstruction qps qpt i j l)

/-- One shifted correction row minus the parent coefficient row, evaluated
on the same three shifted carriers. -/
def coefficientMismatchRow
    (L D U Ls Ds Us xm x xp : Q') : Q' :=
  (Ls + -L) * xm + (Ds + -D) * x + (Us + -U) * xp

/-- The explicit coefficient commutator left by the four Euler directions.
All nine coefficient differences in this expression have exact
denominator-cleared formulas in the imported coefficient module. -/
def outerShiftCoefficientCommutator {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (qms qs qps : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qmt qt qpt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (i j l : Nat) : Q' :=
  let L := omegaCorrectionLowerCoefficient a b c d q.p
  let D := omegaCorrectionDiagonalCoefficient a b c d q.p
  let U := omegaCorrectionUpperCoefficient a b c d q.p
  let Ls := omegaCorrectionLowerCoefficient (a - 1) (b - 1) c d qs.p
  let Ds := omegaCorrectionDiagonalCoefficient (a - 1) (b - 1) c d qs.p
  let Us := omegaCorrectionUpperCoefficient (a - 1) (b - 1) c d qs.p
  let Lt := omegaCorrectionLowerCoefficient (a - 1) b (c - 1) d qt.p
  let Dt := omegaCorrectionDiagonalCoefficient (a - 1) b (c - 1) d qt.p
  let Ut := omegaCorrectionUpperCoefficient (a - 1) b (c - 1) d qt.p
  Q'.ofNat i *
      (Q'.ofNat (b - j) *
          coefficientMismatchRow L D U Ls Ds Us
            (rightShellFactorialCoefficient qms (i - 1) j l)
            (rightShellFactorialCoefficient qs (i - 1) j l)
            (rightShellFactorialCoefficient qps (i - 1) j l) +
        Q'.ofNat (c - l) *
          coefficientMismatchRow L D U Lt Dt Ut
            (rightShellFactorialCoefficient qmt (i - 1) j l)
            (rightShellFactorialCoefficient qt (i - 1) j l)
            (rightShellFactorialCoefficient qpt (i - 1) j l)) +
    -(Q'.ofNat (a - i) *
      (Q'.ofNat j *
          coefficientMismatchRow L D U Ls Ds Us
            (rightShellFactorialCoefficient qms i (j - 1) l)
            (rightShellFactorialCoefficient qs i (j - 1) l)
            (rightShellFactorialCoefficient qps i (j - 1) l) +
        Q'.ofNat l *
          coefficientMismatchRow L D U Lt Dt Ut
            (rightShellFactorialCoefficient qmt i j (l - 1))
            (rightShellFactorialCoefficient qt i j (l - 1))
            (rightShellFactorialCoefficient qpt i j (l - 1))))

/-- Exact algebraic extraction of the coefficient commutator. -/
theorem outerShiftShellRHS_sub_parentReconstructed_eq_coefficientCommutator
    {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (qms qs qps : FixedRightCGChannel (a - 1) (b - 1) c d)
    (qmt qt qpt : FixedRightCGChannel (a - 1) b (c - 1) d)
    (i j l : Nat)
    (hps : qs.p = q.p) (hpt : qt.p = q.p) :
    outerShiftShellRHS qms qs qps qmt qt qpt i j l +
        -(parentReconstructedShellRHS
          q qms qs qps qmt qt qpt i j l) ≈
      outerShiftCoefficientCommutator q qms qs qps qmt qt qpt i j l := by
  unfold outerShiftShellRHS parentReconstructedShellRHS
    shellCorrectionRHS correctionCarrierRow outerShiftReconstruction
    outerShiftCoefficientCommutator coefficientMismatchRow
  simp only [hps, hpt]
  ring_qeqv

/-- The three parent carriers in the reconstructed row are the actual parent
carriers, uniformly in the adjacent inner channel. -/
theorem parentReconstructedShellRHS_eq_shellCorrectionRHS
    {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmb : qm.p < b) (hmc : qm.p < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hpb : qp.p < b) (hpc : qp.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) (hrp : 0 < qp.r)
    (i j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hjb : j < b) (hlc : l < c)
    (hhm : qm.p < j + l) (hhq : q.p < j + l)
    (hhp : qp.p < j + l)
    (hdm : j + l + qm.p ≤ b + c)
    (hdq : j + l + q.p ≤ b + c)
    (hdp : j + l + qp.p ≤ b + c) :
    parentReconstructedShellRHS q
        (reduceFirstSecondRightChannel qm ha hb hmb hrm)
        (reduceFirstSecondRightChannel q ha hb hqb hr)
        (reduceFirstSecondRightChannel qp ha hb hpb hrp)
        (reduceFirstThirdRightChannel qm ha hc hmc hrm)
        (reduceFirstThirdRightChannel q ha hc hqc hr)
        (reduceFirstThirdRightChannel qp ha hc hpc hrp)
        i j l ≈
      shellCorrectionRHS qm q qp i j l := by
  have hm := rightShellFactorialCoefficient_outerShift_transport
    qm ha hb hc hmb hmc hrm i j l hj hl hjb hlc hhm hdm
  have hq := rightShellFactorialCoefficient_outerShift_transport
    q ha hb hc hqb hqc hr i j l hj hl hjb hlc hhq hdq
  have hp := rightShellFactorialCoefficient_outerShift_transport
    qp ha hb hc hpb hpc hrp i j l hj hl hjb hlc hhp hdp
  unfold parentReconstructedShellRHS shellCorrectionRHS correctionCarrierRow
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hm)
      (Q'.mul_eqv_congr_left _ _ _ hq))
    (Q'.mul_eqv_congr_left _ _ _ hp)

/-- The parent shell residual in subtraction form. -/
def shellCorrectionResidual {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) : Q' :=
  shellCorrectionLHS q hp i j l + -shellCorrectionRHS qm q qp i j l

/-- The four lower-label shell equations used by one outer-shift induction
step.  They occur at exactly the four Euler predecessor coordinates. -/
def OmegaCorrectionOuterShiftFourShellAt
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmb : qm.p < b) (hmc : qm.p < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hpb : qp.p < b) (hpc : qp.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) (hrp : 0 < qp.r)
    (i j l : Nat) : Prop :=
  let qms := reduceFirstSecondRightChannel qm ha hb hmb hrm
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qps := reduceFirstSecondRightChannel qp ha hb hpb hrp
  let qmt := reduceFirstThirdRightChannel qm ha hc hmc hrm
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  let qpt := reduceFirstThirdRightChannel qp ha hc hpc hrp
  let hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  let hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  OmegaCorrectionShellAt qms qs qps hps (i - 1) j l ∧
    OmegaCorrectionShellAt qmt qt qpt hpt (i - 1) j l ∧
    OmegaCorrectionShellAt qms qs qps hps i (j - 1) l ∧
    OmegaCorrectionShellAt qmt qt qpt hpt i j (l - 1)

/-- The difference between the parent exchange row and the Euler combination
of the two shifted exchange rows. -/
def outerShiftExchangeCommutator
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hqb : q.p < b) (hqc : q.p < c) (hr : 0 < q.r)
    (i j l : Nat) : Q' :=
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  let hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  let hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  shellCorrectionLHS q hp i j l +
    -outerShiftShellLHS qs qt hps hpt i j l

/-- The explicit coefficient defect specialized to the physical shifted
channel maps. -/
def physicalOuterShiftCoefficientCommutator
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmb : qm.p < b) (hmc : qm.p < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hpb : qp.p < b) (hpc : qp.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) (hrp : 0 < qp.r)
    (i j l : Nat) : Q' :=
  outerShiftCoefficientCommutator q
    (reduceFirstSecondRightChannel qm ha hb hmb hrm)
    (reduceFirstSecondRightChannel q ha hb hqb hr)
    (reduceFirstSecondRightChannel qp ha hb hpb hrp)
    (reduceFirstThirdRightChannel qm ha hc hmc hrm)
    (reduceFirstThirdRightChannel q ha hc hqc hr)
    (reduceFirstThirdRightChannel qp ha hc hpc hrp)
    i j l

/-- Exact outer-shift induction step.  Once the four smaller-label shell
equations are supplied, the parent residual is neither assumed nor restated:
it is reduced to the sum of the exchange commutator and the explicit
coefficient commutator. -/
theorem shellCorrectionResidual_eq_outerShift_commutators
    {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmb : qm.p < b) (hmc : qm.p < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hpb : qp.p < b) (hpc : qp.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) (hrp : 0 < qp.r)
    (i j l : Nat) (hj : 0 < j) (hl : 0 < l)
    (hjb : j < b) (hlc : l < c)
    (hhm : qm.p < j + l) (hhq : q.p < j + l)
    (hhp : qp.p < j + l)
    (hdm : j + l + qm.p ≤ b + c)
    (hdq : j + l + q.p ≤ b + c)
    (hdp : j + l + qp.p ≤ b + c)
    (hfour : OmegaCorrectionOuterShiftFourShellAt qm q qp hp
      ha hb hc hmb hmc hqb hqc hpb hpc hrm hr hrp i j l) :
    shellCorrectionResidual qm q qp hp i j l ≈
      outerShiftExchangeCommutator q hp ha hb hc hqb hqc hr i j l +
        physicalOuterShiftCoefficientCommutator qm q qp
          ha hb hc hmb hmc hqb hqc hpb hpc hrm hr hrp i j l := by
  let qms := reduceFirstSecondRightChannel qm ha hb hmb hrm
  let qs := reduceFirstSecondRightChannel q ha hb hqb hr
  let qps := reduceFirstSecondRightChannel qp ha hb hpb hrp
  let qmt := reduceFirstThirdRightChannel qm ha hc hmc hrm
  let qt := reduceFirstThirdRightChannel q ha hc hqc hr
  let qpt := reduceFirstThirdRightChannel qp ha hc hpc hrp
  have hps : 0 < qs.p := by
    dsimp only [qs, reduceFirstSecondRightChannel]
    exact hp
  have hpt : 0 < qt.p := by
    dsimp only [qt, reduceFirstThirdRightChannel]
    exact hp
  have hfour' := hfour
  unfold OmegaCorrectionOuterShiftFourShellAt at hfour'
  dsimp only at hfour'
  have hshift : outerShiftShellLHS qs qt hps hpt i j l ≈
      outerShiftShellRHS qms qs qps qmt qt qpt i j l := by
    apply outerShiftShellLHS_eq_rhs_of_four
    · simpa only [qms, qs, qps] using hfour'.1
    · simpa only [qmt, qt, qpt] using hfour'.2.1
    · simpa only [qms, qs, qps] using hfour'.2.2.1
    · simpa only [qmt, qt, qpt] using hfour'.2.2.2
  have hcoeff :
      outerShiftShellRHS qms qs qps qmt qt qpt i j l +
          -(parentReconstructedShellRHS q qms qs qps qmt qt qpt i j l) ≈
        outerShiftCoefficientCommutator q qms qs qps qmt qt qpt i j l := by
    apply outerShiftShellRHS_sub_parentReconstructed_eq_coefficientCommutator
    · rfl
    · rfl
  have hparent :
      parentReconstructedShellRHS q qms qs qps qmt qt qpt i j l ≈
        shellCorrectionRHS qm q qp i j l := by
    simpa only [qms, qs, qps, qmt, qt, qpt] using
      parentReconstructedShellRHS_eq_shellCorrectionRHS
        qm q qp ha hb hc hmb hmc hqb hqc hpb hpc hrm hr hrp
        i j l hj hl hjb hlc hhm hhq hhp hdm hdq hdp
  let CL := shellCorrectionLHS q hp i j l
  let SL := outerShiftShellLHS qs qt hps hpt i j l
  let SR := outerShiftShellRHS qms qs qps qmt qt qpt i j l
  let IR := parentReconstructedShellRHS q qms qs qps qmt qt qpt i j l
  let CR := shellCorrectionRHS qm q qp i j l
  let CC := outerShiftCoefficientCommutator q qms qs qps qmt qt qpt i j l
  have hshift' : SL ≈ SR := hshift
  have hparent' : IR ≈ CR := hparent
  have hcoeff' : SR + -IR ≈ CC := hcoeff
  change CL + -CR ≈ (CL + -SL) + CC
  refine Q'.eqv_trans _ ((CL + -SL) + (SL + -CR)) _
    (split_difference CL SL CR) ?_
  refine Q'.eqv_trans _ ((CL + -SL) + (SR + -IR)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' hshift'
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hparent')))
  · exact Q'.add_eqv_congr_left (CL + -SL) _ _ hcoeff'

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftShellCommutator

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftShellCommutator.outerShiftShellLHS_eq_rhs_of_four
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftShellCommutator.outerShiftShellRHS_sub_parentReconstructed_eq_coefficientCommutator
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftShellCommutator.parentReconstructedShellRHS_eq_shellCorrectionRHS
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionOuterShiftShellCommutator.shellCorrectionResidual_eq_outerShift_commutators
