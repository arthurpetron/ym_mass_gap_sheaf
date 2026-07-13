/-
Constructive Horner translation from the centered even endpoint to its
manifestly positive `M=m-5` certificate.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointSubstitution

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointEvenShift

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointSubstitution

local infix:50 " ≈ " => Q'.eqv

private def intCoeffs (cs : List Int) : QPoly.Poly := cs.map Q'.ofInt

private theorem qIntPoly_eq_eval (x : Q') : ∀ cs,
    qIntPoly x cs = QPoly.eval (intCoeffs cs) x
  | [] => rfl
  | _ :: cs => by
      simp only [qIntPoly, intCoeffs, List.map_cons, QPoly.eval]
      rw [qIntPoly_eq_eval x cs]
      rfl

/-- Polynomial translation `p(X+c)`, computed by Horner recursion. -/
private def shiftPoly (c : Q') : QPoly.Poly → QPoly.Poly
  | [] => []
  | a :: as => QPoly.padd [a]
      (QPoly.pmul [c, (1 : Q')] (shiftPoly c as))

private theorem eval_single (a x : Q') : QPoly.eval [a] x ≈ a := by
  show a + x * (0 : Q') ≈ a
  have hz : x * (0 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv x 0)
      (RingNormaliser.q_zero_mul x)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ hz)
    (QPoly.q_add_zero_eqv a)

private theorem eval_linear (c x : Q') :
    QPoly.eval [c, (1 : Q')] x ≈ x + c := by
  show c + x * ((1 : Q') + x * (0 : Q')) ≈ x + c
  have hz : x * (0 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv x 0)
      (RingNormaliser.q_zero_mul x)
  have hone : (1 : Q') + x * (0 : Q') ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ hz)
      (QPoly.q_add_zero_eqv 1)
  have hx : x * ((1 : Q') + x * (0 : Q')) ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hone)
      (Q'.mul_one_eqv x)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left c _ _ hx)
    (Q'.add_comm_eqv c x)

private theorem eval_shiftPoly (c x : Q') : ∀ p,
    QPoly.eval (shiftPoly c p) x ≈ QPoly.eval p (x + c)
  | [] => Q'.eqv_refl 0
  | a :: as => by
      have hadd := QPoly.eval_padd [a]
        (QPoly.pmul [c, (1 : Q')] (shiftPoly c as)) x
      have hmul := QPoly.eval_pmul [c, (1 : Q')] (shiftPoly c as) x
      have ha := eval_single a x
      have hl := eval_linear c x
      have ih := eval_shiftPoly c x as
      refine Q'.eqv_trans _ _ _ hadd ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' ha hmul) ?_
      exact Q'.add_eqv_congr_left a _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hl)
          (Q'.mul_eqv_congr_left (x + c) _ _ ih))

private theorem qIntPoly_eqv_congr {x y : Q'} (h : x ≈ y) : ∀ cs,
    qIntPoly x cs ≈ qIntPoly y cs
  | [] => Q'.eqv_refl 0
  | _ :: cs =>
      Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ h)
          (Q'.mul_eqv_congr_left y _ _ (qIntPoly_eqv_congr h cs)))

private theorem shifted_int_poly (source target : List Int)
    (hzero : QPoly.allZero
      (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs source))
        (intCoeffs target))) (M : Q') :
    qIntPoly (M + Q'.ofNat 5) source ≈ qIntPoly M target := by
  have hc : M + Q'.ofNat 5 ≈ M + Q'.ofInt 5 :=
    Q'.add_eqv_congr_left M _ _ (by decide)
  have hbase := qIntPoly_eqv_congr hc source
  rw [qIntPoly_eq_eval, qIntPoly_eq_eval] at hbase ⊢
  refine Q'.eqv_trans _ _ _ hbase ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (eval_shiftPoly (Q'.ofInt 5) M (intCoeffs source))) ?_
  exact QPoly.poly_eqv _ _ M hzero

private def evenMid6 : List Int := [-840, -840]
private def evenMid5 : List Int := [1680, 10220, 12180, 3640]
private def evenMid4 : List Int := [-840, -15953, -43995, 4690, 99540, 65968]
private def evenMid3 : List Int :=
  [0, 7371, 58905, 60746, -175140, -222096, 210000, 247744]
private def evenMid2 : List Int :=
  [0, -216, -23100, -87234, 93870, 475944, 23940, -642776,
    47040, 396032]
private def evenMid1 : List Int :=
  [0, -240, 840, 31896, 33600, -248388, -233100, 694808,
    655200, -573472, -282240, 269696]
private def evenMid0 : List Int :=
  [0, 8, 420, -1460, -15960, 18708, 114660, -104112, -357000,
    227056, 571200, -100608, -221760, 51968]

private def evenOut6 : List Int := [-5040, -840]
private def evenOut5 : List Int := [812280, 405020, 66780, 3640]
private def evenOut4 : List Int :=
  [267768270, 255815847, 97417355, 18487490, 1748740, 65968]
private def evenOut3 : List Int :=
  [21841840230, 30258032371, 17924029095, 5885433946,
    1156902460, 136143504, 8881040, 247744]
private def evenOut2 : List Int :=
  [743566698420, 1353372736234, 1093069941390, 514143901166,
    155204424970, 31180536744, 4168790780, 357667624,
    17868480, 396032]
private def evenOut1 : List Int :=
  [9598263481800, 21923004487860, 22726866496780, 14113282781896,
    5832806596400, 1684387012812, 346790869180, 50901978008,
    5219808960, 356146528, 14551040, 269696]
private def evenOut0 : List Int :=
  [10260221753040, 35914681752208, 54703546057020, 48961549556340,
    29046947509240, 12143586459708, 3697147858740, 832543566288,
    138979220520, 17015251056, 1486989760, 87931392, 3156160, 51968]

private theorem shift6_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid6))
      (intCoeffs evenOut6)) := by decide
private theorem shift5_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid5))
      (intCoeffs evenOut5)) := by decide
private theorem shift4_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid4))
      (intCoeffs evenOut4)) := by decide
private theorem shift3_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid3))
      (intCoeffs evenOut3)) := by decide
private theorem shift2_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid2))
      (intCoeffs evenOut2)) := by decide
private theorem shift1_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid1))
      (intCoeffs evenOut1)) := by decide
private theorem shift0_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs evenMid0))
      (intCoeffs evenOut0)) := by decide

def thetaCubicEvenCenteredFormula (m r : Q') : Q' :=
  RingNormaliser.qpow r 6 * qIntPoly m evenMid6 +
    (RingNormaliser.qpow r 5 * qIntPoly m evenMid5 +
      (RingNormaliser.qpow r 4 * qIntPoly m evenMid4 +
        (RingNormaliser.qpow r 3 * qIntPoly m evenMid3 +
          (RingNormaliser.qpow r 2 * qIntPoly m evenMid2 +
            (r * qIntPoly m evenMid1 + qIntPoly m evenMid0)))))

def thetaCubicEvenExpandedCertificate (M r : Q') : Q' :=
  RingNormaliser.qpow r 6 * qIntPoly M evenOut6 +
    (RingNormaliser.qpow r 5 * qIntPoly M evenOut5 +
      (RingNormaliser.qpow r 4 * qIntPoly M evenOut4 +
        (RingNormaliser.qpow r 3 * qIntPoly M evenOut3 +
          (RingNormaliser.qpow r 2 * qIntPoly M evenOut2 +
            (r * qIntPoly M evenOut1 + qIntPoly M evenOut0)))))

private theorem centered_eq_formula (m r : Q') :
    thetaCubicEvenCenteredPolynomial m r ≈
      thetaCubicEvenCenteredFormula m r := by
  unfold thetaCubicEvenCenteredPolynomial thetaCubicEvenCenteredFormula
  exact Q'.eqv_refl _

theorem thetaCubicEvenCentered_shift (M r : Q') :
    thetaCubicEvenCenteredPolynomial (M + Q'.ofNat 5) r ≈
      thetaCubicEvenExpandedCertificate M r := by
  have h6 := shifted_int_poly evenMid6 evenOut6 shift6_zero M
  have h5 := shifted_int_poly evenMid5 evenOut5 shift5_zero M
  have h4 := shifted_int_poly evenMid4 evenOut4 shift4_zero M
  have h3 := shifted_int_poly evenMid3 evenOut3 shift3_zero M
  have h2 := shifted_int_poly evenMid2 evenOut2 shift2_zero M
  have h1 := shifted_int_poly evenMid1 evenOut1 shift1_zero M
  have h0 := shifted_int_poly evenMid0 evenOut0 shift0_zero M
  refine Q'.eqv_trans _ _ _ (centered_eq_formula (M + Q'.ofNat 5) r) ?_
  unfold thetaCubicEvenCenteredFormula thetaCubicEvenExpandedCertificate
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ h6)
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ h5)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ h4)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ h3)
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ h2)
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left r _ _ h1) h0)))))

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def psub (a b : PE) : PE := padd a (pneg b)
private def ppow (a : PE) (n : Nat) : PE := .pow a n
private def pNatPoly (x : PE) : List Nat → PE
  | [] => pc 0
  | a :: as => padd (pc (Int.ofNat a)) (pmul x (pNatPoly x as))
private def pIntPoly (x : PE) : List Int → PE
  | [] => pc 0
  | a :: as => padd (pc a) (pmul x (pIntPoly x as))

private def pEvenB5 (M : PE) : PE := pNatPoly M [967, 321, 26]
private def pEvenB4 (M : PE) : PE :=
  pNatPoly M [6375435, 5028281, 1481414, 193276, 9424]
private def pEvenB3 (M : PE) : PE :=
  pNatPoly M [104008763, 105949322, 43037476, 8713824, 879408, 35392]
private def pEvenB2 (M : PE) : PE :=
  pNatPoly M [12392778307, 18012193558, 11200268775, 3861893350,
    797370562, 98576628, 6756064, 198016]
private def pEvenB1 (M : PE) : PE :=
  pNatPoly M [79985529015, 153363676760, 130491021694, 64651859336,
    20551339157, 4346005438, 611343944, 55156856, 2896096, 67424]
private def pEvenB0 (M : PE) : PE :=
  pNatPoly M [85501847942, 267938337023, 354768765302, 268999754458,
    131599027099, 43976918746, 10298061046, 1696010044, 193021120,
    14485680, 646128, 12992]

private def pGroupedCertificate (M r : PE) : PE :=
  padd
    (padd
      (padd
        (padd
          (padd
            (pmul (ppow r 5) (pmul (padd M (pc 6))
              (psub (pmul (pc 140) (pEvenB5 M)) (pmul (pc 840) r))))
            (pmul (ppow r 4)
              (pmul (pmul (pc 7) (padd M (pc 6))) (pEvenB4 M))))
          (pmul (ppow r 3)
            (pmul (pmul (pmul (pc 7) (padd M (pc 5)))
              (padd M (pc 6))) (pEvenB3 M))))
        (pmul (ppow r 2)
          (pmul (pmul (pmul (pc 2) (padd M (pc 5)))
            (padd M (pc 6))) (pEvenB2 M))))
      (pmul r (pmul (pmul (pmul (pc 4) (padd M (pc 5)))
        (padd M (pc 6))) (pEvenB1 M))))
    (pmul (pmul (pmul (pc 4) (padd M (pc 5)))
      (padd M (pc 6))) (pEvenB0 M))

private def pExpandedCertificate (M r : PE) : PE :=
  padd (pmul (ppow r 6) (pIntPoly M evenOut6)) <|
  padd (pmul (ppow r 5) (pIntPoly M evenOut5)) <|
  padd (pmul (ppow r 4) (pIntPoly M evenOut4)) <|
  padd (pmul (ppow r 3) (pIntPoly M evenOut3)) <|
  padd (pmul (ppow r 2) (pIntPoly M evenOut2))
    (padd (pmul r (pIntPoly M evenOut1)) (pIntPoly M evenOut0))

private theorem grouped_expanded_normal :
    RingNormaliser.normalize (pGroupedCertificate (.var 0) (.var 1)) =
      RingNormaliser.normalize (pExpandedCertificate (.var 0) (.var 1)) := by
  decide

private theorem qmul_eqv_congr {a b c d : Q'} (ha : a ≈ b) (hc : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left b _ _ hc)

private theorem qNatPoly_eq_pNatPoly (x : Q') : ∀ cs,
    qNatPoly x cs ≈
      RingNormaliser.eval (fun | 0 => x | _ => 0)
        (pNatPoly (.var 0) cs)
  | [] => Q'.eqv_refl _
  | a :: as => by
      simp only [qNatPoly, pNatPoly, padd, pmul, pc, RingNormaliser.eval]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (qmul_eqv_congr (Q'.eqv_refl x) (qNatPoly_eq_pNatPoly x as))

private theorem grouped_eq_local (M r : Q') :
    thetaCubicEvenEndpointCertificate M r ≈
      RingNormaliser.eval (fun | 0 => M | _ => r)
        (pGroupedCertificate (.var 0) (.var 1)) := by
  have h5 := qNatPoly_eq_pNatPoly M [967, 321, 26]
  have h4 := qNatPoly_eq_pNatPoly M
    [6375435, 5028281, 1481414, 193276, 9424]
  have h3 := qNatPoly_eq_pNatPoly M
    [104008763, 105949322, 43037476, 8713824, 879408, 35392]
  have h2 := qNatPoly_eq_pNatPoly M
    [12392778307, 18012193558, 11200268775, 3861893350,
      797370562, 98576628, 6756064, 198016]
  have h1 := qNatPoly_eq_pNatPoly M
    [79985529015, 153363676760, 130491021694, 64651859336,
      20551339157, 4346005438, 611343944, 55156856, 2896096, 67424]
  have h0 := qNatPoly_eq_pNatPoly M
    [85501847942, 267938337023, 354768765302, 268999754458,
      131599027099, 43976918746, 10298061046, 1696010044, 193021120,
      14485680, 646128, 12992]
  have hM5 : M + Q'.ofNat 5 ≈ M + Q'.ofInt 5 :=
    Q'.add_eqv_congr_left M _ _ (by decide)
  have hM6 : M + Q'.ofNat 6 ≈ M + Q'.ofInt 6 :=
    Q'.add_eqv_congr_left M _ _ (by decide)
  have ht5 :
      RingNormaliser.qpow r 5 * ((M + Q'.ofNat 6) *
        (Q'.ofNat 140 * qNatPoly M [967, 321, 26] +
          -(Q'.ofNat 840 * r))) ≈
      RingNormaliser.qpow r 5 * ((M + Q'.ofInt 6) *
        (Q'.ofInt 140 * RingNormaliser.eval (fun | 0 => M | _ => 0)
            (pEvenB5 (.var 0)) + -(Q'.ofInt 840 * r))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    apply qmul_eqv_congr hM6
    exact Q'.add_eqv_congr'
      (qmul_eqv_congr (by decide) h5)
      (Q'.neg_eqv_congr _ _ (qmul_eqv_congr (by decide) (Q'.eqv_refl r)))
  have ht4 :
      RingNormaliser.qpow r 4 *
          (Q'.ofNat 7 * (M + Q'.ofNat 6) *
            qNatPoly M [6375435, 5028281, 1481414, 193276, 9424]) ≈
      RingNormaliser.qpow r 4 *
          (Q'.ofInt 7 * (M + Q'.ofInt 6) *
            RingNormaliser.eval (fun | 0 => M | _ => 0)
              (pEvenB4 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    exact qmul_eqv_congr
      (qmul_eqv_congr (by decide) hM6) h4
  have ht3 :
      RingNormaliser.qpow r 3 *
          (Q'.ofNat 7 * (M + Q'.ofNat 5) * (M + Q'.ofNat 6) *
            qNatPoly M [104008763, 105949322, 43037476, 8713824,
              879408, 35392]) ≈
      RingNormaliser.qpow r 3 *
          (Q'.ofInt 7 * (M + Q'.ofInt 5) * (M + Q'.ofInt 6) *
            RingNormaliser.eval (fun | 0 => M | _ => 0)
              (pEvenB3 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    exact qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM5) hM6) h3
  have ht2 :
      RingNormaliser.qpow r 2 *
          (Q'.ofNat 2 * (M + Q'.ofNat 5) * (M + Q'.ofNat 6) *
            qNatPoly M [12392778307, 18012193558, 11200268775,
              3861893350, 797370562, 98576628, 6756064, 198016]) ≈
      RingNormaliser.qpow r 2 *
          (Q'.ofInt 2 * (M + Q'.ofInt 5) * (M + Q'.ofInt 6) *
            RingNormaliser.eval (fun | 0 => M | _ => 0)
              (pEvenB2 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    exact qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM5) hM6) h2
  have ht1 :
      r * (Q'.ofNat 4 * (M + Q'.ofNat 5) * (M + Q'.ofNat 6) *
        qNatPoly M [79985529015, 153363676760, 130491021694,
          64651859336, 20551339157, 4346005438, 611343944,
          55156856, 2896096, 67424]) ≈
      r * (Q'.ofInt 4 * (M + Q'.ofInt 5) * (M + Q'.ofInt 6) *
        RingNormaliser.eval (fun | 0 => M | _ => 0)
          (pEvenB1 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl r)
    exact qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM5) hM6) h1
  have ht0 :
      Q'.ofNat 4 * (M + Q'.ofNat 5) * (M + Q'.ofNat 6) *
        qNatPoly M [85501847942, 267938337023, 354768765302,
          268999754458, 131599027099, 43976918746, 10298061046,
          1696010044, 193021120, 14485680, 646128, 12992] ≈
      Q'.ofInt 4 * (M + Q'.ofInt 5) * (M + Q'.ofInt 6) *
        RingNormaliser.eval (fun | 0 => M | _ => 0)
          (pEvenB0 (.var 0)) :=
    qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM5) hM6) h0
  unfold thetaCubicEvenEndpointCertificate
  simp only [pGroupedCertificate, pEvenB5, pEvenB4, pEvenB3, pEvenB2,
    pEvenB1, pEvenB0, padd, pmul, pneg, psub, ppow, pc,
    RingNormaliser.eval]
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' ht5 ht4) ht3) ht2) ht1) ht0

private theorem expanded_eq_local (M r : Q') :
    thetaCubicEvenExpandedCertificate M r ≈
      RingNormaliser.eval (fun | 0 => M | _ => r)
        (pExpandedCertificate (.var 0) (.var 1)) := by
  unfold thetaCubicEvenExpandedCertificate
  exact Q'.eqv_refl _

theorem thetaCubicEvenExpandedCertificate_eq_grouped (M r : Q') :
    thetaCubicEvenExpandedCertificate M r ≈
      thetaCubicEvenEndpointCertificate M r := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    (pGroupedCertificate (.var 0) (.var 1))
    (pExpandedCertificate (.var 0) (.var 1)) grouped_expanded_normal
    (fun | 0 => M | _ => r)
  exact Q'.eqv_trans _ _ _ (expanded_eq_local M r)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) (Q'.eqv_symm (grouped_eq_local M r)))

/-- Final even shift bridge. -/
theorem thetaCubicEvenCentered_eq_certificate (M r : Q') :
    thetaCubicEvenCenteredPolynomial (M + Q'.ofNat 5) r ≈
      thetaCubicEvenEndpointCertificate M r :=
  Q'.eqv_trans _ _ _ (thetaCubicEvenCentered_shift M r)
    (thetaCubicEvenExpandedCertificate_eq_grouped M r)

#print axioms thetaCubicEvenCenteredFormula
#print axioms thetaCubicEvenExpandedCertificate
#print axioms thetaCubicEvenCentered_shift
#print axioms thetaCubicEvenExpandedCertificate_eq_grouped
#print axioms thetaCubicEvenCentered_eq_certificate

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointEvenShift
