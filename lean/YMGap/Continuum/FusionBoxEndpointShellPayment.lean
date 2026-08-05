/-
`FusionBoxEndpointShellPayment` -- direct endpoint payment of the complete
outer product by the selected positive middle-square shells.

The even channel spends four central cells.  The odd channel uses the sharper
two-shell scalar inequality and spends only the central cell plus the four
first displaced/displaced cells.  These endpoint inequalities are downstream
of the stable cleared-ledger scale bridge in `FusionBoxFirstShellReserve`.
-/

import YMGap.Continuum.FusionBoxFirstShellReserve

namespace YMGap.Continuum.FusionBoxEndpointShellPayment

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionBoxPrefixReserve
open YMGap.Continuum.FusionBoxStrandCeilings
open YMGap.Continuum.FusionBoxFirstShellReserve

private abbrev halfW : Q' := wH

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, Q'.mkPos_num, Q'.mkPos_den, neg_num_cast_local,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem rgQpow_add_local (x : Q') (a : Nat) : forall b : Nat,
    (RGTransport.qpow x (a + b)).eqv
      (RGTransport.qpow x a * RGTransport.qpow x b)
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (RGTransport.qpow x a))
  | b + 1 => by
      have ih := rgQpow_add_local x a b
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      rw [hab]
      show (RGTransport.qpow x (a + b) * x).eqv
        (RGTransport.qpow x a * (RGTransport.qpow x b * x))
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x ih)
        (Q'.mul_assoc_eqv (RGTransport.qpow x a)
          (RGTransport.qpow x b) x)

/-- The two even strand ceilings spend at most three of the four central
middle-square cells.  The fourth cell is the uniform strict reserve. -/
theorem evenOuterProduct_le_fourCentral
    (N m : Nat) :
    boxSum halfW N (2 * m) * boxSum halfW N (2 * m + 2) <=
      Q'.ofNat 4 *
        ((coeffW halfW m * coeffW halfW m) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1))) := by
  have hright :
      boxSum halfW N (2 * m + 2) <= Q'.mkPos 13 8 (by decide) *
        (coeffW halfW (m + 1) * coeffW halfW (m + 1)) := by
    have hindex : 2 * (m + 1) = 2 * m + 2 := by omega
    simpa only [hindex] using boxSum_even_ceiling N (m + 1)
  have houter := even_first_shell_dominates_negative N m
    (boxSum_even_ceiling N m) hright
  have hcell0 : (0 : Q') <=
      (coeffW halfW m * coeffW halfW m) *
        (coeffW halfW (m + 1) * coeffW halfW (m + 1)) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) m)
        (coeffW_nonneg (by decide) m))
      (Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) (m + 1))
        (coeffW_nonneg (by decide) (m + 1)))
  exact Q'.le_trans' _ _ _ houter
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hcell0)

/-- Exact endpoint ratio between the displaced odd middle-box cell and its
central cell.  The factor four is precisely `wH^(-2)`; the remaining factor
is the dimension ratio `oddPeakRatio`. -/
theorem fourOddDisplaced_eqv_peakRatioCentral (m : Nat) :
    (Q'.ofNat 4 *
      (coeffW halfW m * coeffW halfW (m + 2))).eqv
      (oddPeakRatio m *
        (coeffW halfW (m + 1) * coeffW halfW (m + 1))) := by
  let p0 := RGTransport.qpow halfW (c4 m)
  let p1 := RGTransport.qpow halfW (c4 (m + 1))
  let p2 := RGTransport.qpow halfW (c4 (m + 2))
  have hcasimir :
      c4 m + c4 (m + 2) = c4 (m + 1) + c4 (m + 1) + 2 := by
    unfold c4
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hpowers :
      (p0 * p2).eqv ((p1 * p1) * RGTransport.qpow halfW 2) := by
    refine Q'.eqv_trans _
      (RGTransport.qpow halfW (c4 m + c4 (m + 2))) _
      (Q'.eqv_symm (rgQpow_add_local halfW (c4 m) (c4 (m + 2)))) ?_
    rw [hcasimir]
    refine Q'.eqv_trans _
      (RGTransport.qpow halfW (c4 (m + 1) + c4 (m + 1)) *
        RGTransport.qpow halfW 2) _
      (rgQpow_add_local halfW (c4 (m + 1) + c4 (m + 1)) 2) ?_
    exact Q'.mul_eqv_congr_right _ _ (RGTransport.qpow halfW 2)
      (rgQpow_add_local halfW (c4 (m + 1)) (c4 (m + 1)))
  have hhalfSquare :
      (Q'.ofNat 4 * RGTransport.qpow halfW 2).eqv (1 : Q') := by decide
  have hfourPowers :
      (Q'.ofNat 4 * (p0 * p2)).eqv (p1 * p1) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 4 * ((p1 * p1) * RGTransport.qpow halfW 2)) _
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hpowers) ?_
    refine Q'.eqv_trans _
      ((p1 * p1) * (Q'.ofNat 4 * RGTransport.qpow halfW 2)) _
      (by ring_qeqv) ?_
    exact Q'.eqv_trans _ ((p1 * p1) * (1 : Q')) _
      (Q'.mul_eqv_congr_left (p1 * p1) _ _ hhalfSquare)
      (Q'.mul_one_eqv (p1 * p1))
  have hdimensions :
      (Q'.ofNat (m + 1) * Q'.ofNat (m + 3)).eqv
        (oddPeakRatio m *
          (Q'.ofNat (m + 2) * Q'.ofNat (m + 2))) := by
    have hleft :
        (Q'.ofNat (m + 1) * Q'.ofNat (m + 3)).eqv
          (Q'.ofNat ((m + 1) * (m + 3))) :=
      Q'.eqv_symm (ofNat_mul_eqv (m + 1) (m + 3))
    have hcancel :
        (oddPeakRatio m * Q'.ofNat ((m + 2) * (m + 2))).eqv
          (Q'.ofNat ((m + 1) * (m + 3))) := by
      unfold oddPeakRatio
      show ((Q'.mkPos ((m + 1) * (m + 3)) ((m + 2) * (m + 2))
          (Nat.mul_pos (by omega) (by omega)) *
          Q'.ofNat ((m + 2) * (m + 2))).num) *
            (((Q'.ofNat ((m + 1) * (m + 3))).den : Int)) =
        (Q'.ofNat ((m + 1) * (m + 3))).num *
          (((Q'.mkPos ((m + 1) * (m + 3)) ((m + 2) * (m + 2))
            (Nat.mul_pos (by omega) (by omega)) *
            Q'.ofNat ((m + 2) * (m + 2))).den : Int))
      simp only [Q'.mul_num_cast, Q'.mul_den_cast,
        Q'.mkPos_num, Q'.mkPos_den,
        Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one,
        Int.natCast_mul, Int.natCast_add, Int.natCast_one,
        show ((2 : Nat) : Int) = 2 from rfl,
        show ((3 : Nat) : Int) = 3 from rfl]
    have hright :
        (oddPeakRatio m *
          (Q'.ofNat (m + 2) * Q'.ofNat (m + 2))).eqv
          (Q'.ofNat ((m + 1) * (m + 3))) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (oddPeakRatio m) _ _
          (Q'.eqv_symm (ofNat_mul_eqv (m + 2) (m + 2))))
        hcancel
    exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)
  have hm2 : m + 1 + 1 = m + 2 := by omega
  have hm3 : m + 2 + 1 = m + 3 := by omega
  unfold coeffW dimQ
  rw [hm2, hm3]
  change (Q'.ofNat 4 *
      ((Q'.ofNat (m + 1) * p0) * (Q'.ofNat (m + 3) * p2))).eqv
    (oddPeakRatio m *
      ((Q'.ofNat (m + 2) * p1) * (Q'.ofNat (m + 2) * p1)))
  refine Q'.eqv_trans _
    ((Q'.ofNat (m + 1) * Q'.ofNat (m + 3)) *
      (Q'.ofNat 4 * (p0 * p2))) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (m + 1) * Q'.ofNat (m + 3)) * (p1 * p1)) _
    (Q'.mul_eqv_congr_left _ _ _ hfourPowers) ?_
  refine Q'.eqv_trans _
    ((oddPeakRatio m *
      (Q'.ofNat (m + 2) * Q'.ofNat (m + 2))) * (p1 * p1)) _
    (Q'.mul_eqv_congr_right _ _ (p1 * p1) hdimensions) ?_
  ring_qeqv

/-- The sharper odd scalar payment: the complete outer product is paid by
the one central middle-square cell and the four first displaced/displaced
cells.  Mixed central/displaced cells are not spent. -/
theorem oddOuterProduct_le_central_add_fourDisplaced
    (N m : Nat) :
    boxSum halfW N (2 * m + 1) * boxSum halfW N (2 * m + 3) <=
      (coeffW halfW (m + 1) * coeffW halfW (m + 1)) *
          (coeffW halfW (m + 1) * coeffW halfW (m + 1)) +
        Q'.ofNat 4 *
          ((coeffW halfW m * coeffW halfW (m + 2)) *
            (coeffW halfW m * coeffW halfW (m + 2))) := by
  let A := coeffW halfW m * coeffW halfW (m + 1)
  let B := coeffW halfW (m + 1) * coeffW halfW (m + 2)
  let C := coeffW halfW (m + 1) * coeffW halfW (m + 1)
  let D := coeffW halfW m * coeffW halfW (m + 2)
  let q := Q'.mkPos 35 32 (by decide)
  let x := oddPeakRatio m
  have hA0 : (0 : Q') <= A := Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) m)
    (coeffW_nonneg (by decide) (m + 1))
  have hleft : boxSum halfW N (2 * m + 1) <= q * (Q'.ofNat 2 * A) := by
    simpa only [q, A] using boxSum_odd_ceiling N m
  have hright : boxSum halfW N (2 * m + 3) <= q * (Q'.ofNat 2 * B) := by
    have hindex : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    have hcoeff : m + 1 + 1 = m + 2 := by omega
    simpa only [q, B, hindex, hcoeff] using boxSum_odd_ceiling N (m + 1)
  have hright0 : (0 : Q') <= boxSum halfW N (2 * m + 3) :=
    YMGap.Continuum.FusionCoreInduction.boxSum_nonneg (by decide) _ _
  have hleftBound0 : (0 : Q') <= q * (Q'.ofNat 2 * A) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (by decide) hA0)
  have hceil :
      boxSum halfW N (2 * m + 1) * boxSum halfW N (2 * m + 3) <=
        (q * (Q'.ofNat 2 * A)) * (q * (Q'.ofNat 2 * B)) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftBound0)
  have hC0 : (0 : Q') <= C := Q'.mul_nonneg _ _
    (coeffW_nonneg (by decide) (m + 1))
    (coeffW_nonneg (by decide) (m + 1))
  have hCC0 : (0 : Q') <= C * C := Q'.mul_nonneg _ _ hC0 hC0
  have hscalar := odd_two_shell_scalar
    (oddPeakRatio_nonneg m) (oddPeakRatio_le_one m)
  have hscaled :
      ((q * q) * x) * (C * C) <=
        ((1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x)) * (C * C) := by
    simpa only [q, x] using
      Q'.mul_le_mul_of_nonneg_right _ _ (C * C) hscalar hCC0
  have hABCD : (A * B).eqv (C * D) := by
    unfold A B C D
    ring_qeqv
  have hratio : (Q'.ofNat 4 * D).eqv (x * C) := by
    simpa only [D, x, C] using fourOddDisplaced_eqv_peakRatioCentral m
  have hupper :
      ((q * (Q'.ofNat 2 * A)) * (q * (Q'.ofNat 2 * B))).eqv
        (((q * q) * x) * (C * C)) := by
    refine Q'.eqv_trans _ ((q * q) * (Q'.ofNat 4 * (A * B))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ ((q * q) * (Q'.ofNat 4 * (C * D))) _
      (Q'.mul_eqv_congr_left (q * q) _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hABCD)) ?_
    refine Q'.eqv_trans _ ((q * q) * (C * (Q'.ofNat 4 * D))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _ ((q * q) * (C * (x * C))) _
      (Q'.mul_eqv_congr_left (q * q) _ _
        (Q'.mul_eqv_congr_left C _ _ hratio)) ?_
    ring_qeqv
  have hratioSquare :
      ((Q'.ofNat 4 * D) * (Q'.ofNat 4 * D)).eqv
        ((x * C) * (x * C)) :=
    Q'.eqv_trans _ ((x * C) * (Q'.ofNat 4 * D)) _
      (Q'.mul_eqv_congr_right _ _ _ hratio)
      (Q'.mul_eqv_congr_left (x * C) _ _ hratio)
  have hquarterSquare :
      (Q'.mkPos 1 4 (by decide) * ((x * x) * (C * C))).eqv
        (Q'.ofNat 4 * (D * D)) := by
    refine Q'.eqv_trans _
      (Q'.mkPos 1 4 (by decide) * ((x * C) * (x * C))) _
      (by ring_qeqv) ?_
    refine Q'.eqv_trans _
      (Q'.mkPos 1 4 (by decide) *
        ((Q'.ofNat 4 * D) * (Q'.ofNat 4 * D))) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hratioSquare)) ?_
    ring_qeqv
  have hselected :
      (((1 : Q') + Q'.mkPos 1 4 (by decide) * (x * x)) * (C * C)).eqv
        (C * C + Q'.ofNat 4 * (D * D)) := by
    refine Q'.eqv_trans _
      (C * C + Q'.mkPos 1 4 (by decide) * ((x * x) * (C * C))) _
      (by ring_qeqv) ?_
    exact Q'.add_eqv_congr_left (C * C) _ _ hquarterSquare
  exact Q'.le_trans' _ _ _ hceil
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hupper)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (by simpa only [C, D] using hselected))))

#print axioms YMGap.Continuum.FusionBoxEndpointShellPayment.evenOuterProduct_le_fourCentral
#print axioms YMGap.Continuum.FusionBoxEndpointShellPayment.fourOddDisplaced_eqv_peakRatioCentral
#print axioms YMGap.Continuum.FusionBoxEndpointShellPayment.oddOuterProduct_le_central_add_fourDisplaced

end YMGap.Continuum.FusionBoxEndpointShellPayment
