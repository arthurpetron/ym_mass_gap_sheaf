/-
Constructive Horner translation from the centered odd endpoint to its
manifestly positive `M=m-5` certificate.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddSubstitution

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddShift

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddSubstitution

local infix:50 " ≈ " => Q'.eqv

private def intCoeffs (cs : List Int) : QPoly.Poly := cs.map Q'.ofInt

private theorem qIntPoly_eq_eval (x : Q') : ∀ cs,
    qIntPoly x cs = QPoly.eval (intCoeffs cs) x
  | [] => rfl
  | _ :: cs => by
      simp only [qIntPoly, intCoeffs, List.map_cons, QPoly.eval]
      rw [qIntPoly_eq_eval x cs]
      rfl

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
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha hmul) ?_
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

private def oddMid6 : List Int := [-1680, -840]
private def oddMid5 : List Int := [14280, 23660, 15540, 3640]
private def oddMid4 : List Int :=
  [-40950, -50393, 134645, 344890, 266980, 65968]
private def oddMid3 : List Int :=
  [64050, 60291, -368599, -540974, 564620, 1606864, 1114064, 247744]
private def oddMid2 : List Int :=
  [-50400, 14484, 633906, 777084, -1026494, -1927296, 733124,
    2953096, 1923264, 396032]
private def oddMid1 : List Int :=
  [20160, -27120, -299904, 157308, 2366588, 3098284, -579964,
    -3344024, -980928, 1673696, 1301888, 269696]
private def oddMid0 : List Int :=
  [-3360, 6728, 50340, -93044, -427440, 468724, 3121412,
    3878104, 506328, -2612400, -2074752, -371200, 156352, 51968]

private def oddOut6 : List Int := [-5880, -840]
private def oddOut5 : List Int := [976080, 452060, 70140, 3640]
private def oddOut4 : List Int :=
  [419196960, 366802807, 127814995, 22176490, 1916180, 65968]
private def oddOut3 : List Int :=
  [42060116280, 53245261251, 28787339791, 8617027426,
    1542390220, 165094384, 9785104, 247744]
private def oddOut2 : List Int :=
  [1760389333920, 2924609537844, 2153387158566, 922293408204,
    253225907606, 46220809824, 5608712284, 436312456,
    19744704, 396032]
private def oddOut1 : List Int :=
  [28509121992960, 59304004753440, 55913455165416, 31539235225068,
    11826254432188, 3095271950764, 577015937596, 76616865256,
    7101439392, 437600096, 16135168, 269696]
private def oddOut0 : List Int :=
  [58671501833280, 167768674924328, 215511927756180, 165704277994156,
    85438512875160, 31286860711684, 8389123884652, 1670354891224,
    247273052328, 26906130000, 2093346048, 110347520, 3534272, 51968]

private theorem shift6_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid6))
      (intCoeffs oddOut6)) := by decide
private theorem shift5_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid5))
      (intCoeffs oddOut5)) := by decide
private theorem shift4_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid4))
      (intCoeffs oddOut4)) := by decide
private theorem shift3_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid3))
      (intCoeffs oddOut3)) := by decide
private theorem shift2_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid2))
      (intCoeffs oddOut2)) := by decide
private theorem shift1_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid1))
      (intCoeffs oddOut1)) := by decide
private theorem shift0_zero : QPoly.allZero
    (QPoly.psub (shiftPoly (Q'.ofInt 5) (intCoeffs oddMid0))
      (intCoeffs oddOut0)) := by decide

def thetaCubicOddCenteredFormula (m r : Q') : Q' :=
  RingNormaliser.qpow r 6 * qIntPoly m oddMid6 +
    (RingNormaliser.qpow r 5 * qIntPoly m oddMid5 +
      (RingNormaliser.qpow r 4 * qIntPoly m oddMid4 +
        (RingNormaliser.qpow r 3 * qIntPoly m oddMid3 +
          (RingNormaliser.qpow r 2 * qIntPoly m oddMid2 +
            (r * qIntPoly m oddMid1 + qIntPoly m oddMid0)))))

def thetaCubicOddExpandedCertificate (M r : Q') : Q' :=
  RingNormaliser.qpow r 6 * qIntPoly M oddOut6 +
    (RingNormaliser.qpow r 5 * qIntPoly M oddOut5 +
      (RingNormaliser.qpow r 4 * qIntPoly M oddOut4 +
        (RingNormaliser.qpow r 3 * qIntPoly M oddOut3 +
          (RingNormaliser.qpow r 2 * qIntPoly M oddOut2 +
            (r * qIntPoly M oddOut1 + qIntPoly M oddOut0)))))

private theorem centered_eq_formula (m r : Q') :
    thetaCubicOddCenteredPolynomial m r ≈
      thetaCubicOddCenteredFormula m r := by
  unfold thetaCubicOddCenteredPolynomial thetaCubicOddCenteredFormula
  exact Q'.eqv_refl _

theorem thetaCubicOddCentered_shift (M r : Q') :
    thetaCubicOddCenteredPolynomial (M + Q'.ofNat 5) r ≈
      thetaCubicOddExpandedCertificate M r := by
  have h6 := shifted_int_poly oddMid6 oddOut6 shift6_zero M
  have h5 := shifted_int_poly oddMid5 oddOut5 shift5_zero M
  have h4 := shifted_int_poly oddMid4 oddOut4 shift4_zero M
  have h3 := shifted_int_poly oddMid3 oddOut3 shift3_zero M
  have h2 := shifted_int_poly oddMid2 oddOut2 shift2_zero M
  have h1 := shifted_int_poly oddMid1 oddOut1 shift1_zero M
  have h0 := shifted_int_poly oddMid0 oddOut0 shift0_zero M
  refine Q'.eqv_trans _ _ _ (centered_eq_formula (M + Q'.ofNat 5) r) ?_
  unfold thetaCubicOddCenteredFormula thetaCubicOddExpandedCertificate
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

private def pOddB5 (M : PE) : PE := pNatPoly M [996, 319, 26]
private def pOddB4 (M : PE) : PE :=
  pNatPoly M [8555040, 6263623, 1713666, 207772, 9424]
private def pOddB3 (M : PE) : PE :=
  pNatPoly M [858369720, 964013739, 449780482, 111603348,
    15534016, 1150128, 35392]
private def pOddB2 (M : PE) : PE :=
  pNatPoly M [20957015880, 28330084821, 16367749065, 5238949558,
    1003306202, 114963684, 7298144, 198016]
private def pOddB1 (M : PE) : PE :=
  pNatPoly M [169697154720, 300474718500, 235773697527, 107601809998,
    31475390013, 6119907322, 790947600, 65523576, 3157280, 67424]
private def pOddB0 (M : PE) : PE :=
  pNatPoly M [349235129960, 890526477181, 998854823946, 655962626430,
    281744267887, 83406596880, 17410736758, 2567679716, 262564048,
    17750480, 714672, 12992]

private def pGroupedCertificate (M r : PE) : PE :=
  padd
    (padd
      (padd
        (padd
          (padd
            (pmul (ppow r 5) (pmul (padd M (pc 7))
              (psub (pmul (pc 140) (pOddB5 M)) (pmul (pc 840) r))))
            (pmul (ppow r 4)
              (pmul (pmul (pc 7) (padd M (pc 7))) (pOddB4 M))))
          (pmul (ppow r 3)
            (pmul (pmul (pc 7) (padd M (pc 7))) (pOddB3 M))))
        (pmul (ppow r 2)
          (pmul (pmul (pmul (pc 2) (padd M (pc 6)))
            (padd M (pc 7))) (pOddB2 M))))
      (pmul r (pmul (pmul (pmul (pc 4) (padd M (pc 6)))
        (padd M (pc 7))) (pOddB1 M))))
    (pmul (pmul (pmul (pc 4) (padd M (pc 6)))
      (padd M (pc 7))) (pOddB0 M))

private def pExpandedCertificate (M r : PE) : PE :=
  padd (pmul (ppow r 6) (pIntPoly M oddOut6)) <|
  padd (pmul (ppow r 5) (pIntPoly M oddOut5)) <|
  padd (pmul (ppow r 4) (pIntPoly M oddOut4)) <|
  padd (pmul (ppow r 3) (pIntPoly M oddOut3)) <|
  padd (pmul (ppow r 2) (pIntPoly M oddOut2))
    (padd (pmul r (pIntPoly M oddOut1)) (pIntPoly M oddOut0))

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
    thetaCubicOddEndpointCertificate M r ≈
      RingNormaliser.eval (fun | 0 => M | _ => r)
        (pGroupedCertificate (.var 0) (.var 1)) := by
  have h5 := qNatPoly_eq_pNatPoly M [996, 319, 26]
  have h4 := qNatPoly_eq_pNatPoly M
    [8555040, 6263623, 1713666, 207772, 9424]
  have h3 := qNatPoly_eq_pNatPoly M
    [858369720, 964013739, 449780482, 111603348,
      15534016, 1150128, 35392]
  have h2 := qNatPoly_eq_pNatPoly M
    [20957015880, 28330084821, 16367749065, 5238949558,
      1003306202, 114963684, 7298144, 198016]
  have h1 := qNatPoly_eq_pNatPoly M
    [169697154720, 300474718500, 235773697527, 107601809998,
      31475390013, 6119907322, 790947600, 65523576, 3157280, 67424]
  have h0 := qNatPoly_eq_pNatPoly M
    [349235129960, 890526477181, 998854823946, 655962626430,
      281744267887, 83406596880, 17410736758, 2567679716, 262564048,
      17750480, 714672, 12992]
  have hM6 : M + Q'.ofNat 6 ≈ M + Q'.ofInt 6 :=
    Q'.add_eqv_congr_left M _ _ (by decide)
  have hM7 : M + Q'.ofNat 7 ≈ M + Q'.ofInt 7 :=
    Q'.add_eqv_congr_left M _ _ (by decide)
  have ht5 :
      RingNormaliser.qpow r 5 * ((M + Q'.ofNat 7) *
        (Q'.ofNat 140 * qNatPoly M [996, 319, 26] +
          -(Q'.ofNat 840 * r))) ≈
      RingNormaliser.qpow r 5 * ((M + Q'.ofInt 7) *
        (Q'.ofInt 140 * RingNormaliser.eval (fun | 0 => M | _ => 0)
            (pOddB5 (.var 0)) + -(Q'.ofInt 840 * r))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    apply qmul_eqv_congr hM7
    exact Q'.add_eqv_congr'
      (qmul_eqv_congr (by decide) h5)
      (Q'.neg_eqv_congr _ _ (qmul_eqv_congr (by decide) (Q'.eqv_refl r)))
  have ht4 :
      RingNormaliser.qpow r 4 *
          (Q'.ofNat 7 * (M + Q'.ofNat 7) *
            qNatPoly M [8555040, 6263623, 1713666, 207772, 9424]) ≈
      RingNormaliser.qpow r 4 *
          (Q'.ofInt 7 * (M + Q'.ofInt 7) *
            RingNormaliser.eval (fun | 0 => M | _ => 0)
              (pOddB4 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    exact qmul_eqv_congr (qmul_eqv_congr (by decide) hM7) h4
  have ht3 :
      RingNormaliser.qpow r 3 *
          (Q'.ofNat 7 * (M + Q'.ofNat 7) *
            qNatPoly M [858369720, 964013739, 449780482, 111603348,
              15534016, 1150128, 35392]) ≈
      RingNormaliser.qpow r 3 *
          (Q'.ofInt 7 * (M + Q'.ofInt 7) *
            RingNormaliser.eval (fun | 0 => M | _ => 0)
              (pOddB3 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    exact qmul_eqv_congr (qmul_eqv_congr (by decide) hM7) h3
  have ht2 :
      RingNormaliser.qpow r 2 *
          (Q'.ofNat 2 * (M + Q'.ofNat 6) * (M + Q'.ofNat 7) *
            qNatPoly M [20957015880, 28330084821, 16367749065,
              5238949558, 1003306202, 114963684, 7298144, 198016]) ≈
      RingNormaliser.qpow r 2 *
          (Q'.ofInt 2 * (M + Q'.ofInt 6) * (M + Q'.ofInt 7) *
            RingNormaliser.eval (fun | 0 => M | _ => 0)
              (pOddB2 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl _)
    exact qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM6) hM7) h2
  have ht1 :
      r * (Q'.ofNat 4 * (M + Q'.ofNat 6) * (M + Q'.ofNat 7) *
        qNatPoly M [169697154720, 300474718500, 235773697527,
          107601809998, 31475390013, 6119907322, 790947600,
          65523576, 3157280, 67424]) ≈
      r * (Q'.ofInt 4 * (M + Q'.ofInt 6) * (M + Q'.ofInt 7) *
        RingNormaliser.eval (fun | 0 => M | _ => 0)
          (pOddB1 (.var 0))) := by
    apply qmul_eqv_congr (Q'.eqv_refl r)
    exact qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM6) hM7) h1
  have ht0 :
      Q'.ofNat 4 * (M + Q'.ofNat 6) * (M + Q'.ofNat 7) *
        qNatPoly M [349235129960, 890526477181, 998854823946,
          655962626430, 281744267887, 83406596880, 17410736758,
          2567679716, 262564048, 17750480, 714672, 12992] ≈
      Q'.ofInt 4 * (M + Q'.ofInt 6) * (M + Q'.ofInt 7) *
        RingNormaliser.eval (fun | 0 => M | _ => 0)
          (pOddB0 (.var 0)) :=
    qmul_eqv_congr
      (qmul_eqv_congr (qmul_eqv_congr (by decide) hM6) hM7) h0
  unfold thetaCubicOddEndpointCertificate
  simp only [pGroupedCertificate, pOddB5, pOddB4, pOddB3, pOddB2,
    pOddB1, pOddB0, padd, pmul, pneg, psub, ppow, pc,
    RingNormaliser.eval]
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' ht5 ht4) ht3) ht2) ht1) ht0

private theorem expanded_eq_local (M r : Q') :
    thetaCubicOddExpandedCertificate M r ≈
      RingNormaliser.eval (fun | 0 => M | _ => r)
        (pExpandedCertificate (.var 0) (.var 1)) := by
  unfold thetaCubicOddExpandedCertificate
  exact Q'.eqv_refl _

theorem thetaCubicOddExpandedCertificate_eq_grouped (M r : Q') :
    thetaCubicOddExpandedCertificate M r ≈
      thetaCubicOddEndpointCertificate M r := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    (pGroupedCertificate (.var 0) (.var 1))
    (pExpandedCertificate (.var 0) (.var 1)) grouped_expanded_normal
    (fun | 0 => M | _ => r)
  exact Q'.eqv_trans _ _ _ (expanded_eq_local M r)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm h) (Q'.eqv_symm (grouped_eq_local M r)))

theorem thetaCubicOddCentered_eq_certificate (M r : Q') :
    thetaCubicOddCenteredPolynomial (M + Q'.ofNat 5) r ≈
      thetaCubicOddEndpointCertificate M r :=
  Q'.eqv_trans _ _ _ (thetaCubicOddCentered_shift M r)
    (thetaCubicOddExpandedCertificate_eq_grouped M r)

#print axioms thetaCubicOddCenteredFormula
#print axioms thetaCubicOddExpandedCertificate
#print axioms thetaCubicOddCentered_shift
#print axioms thetaCubicOddExpandedCertificate_eq_grouped
#print axioms thetaCubicOddCentered_eq_certificate

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddShift
