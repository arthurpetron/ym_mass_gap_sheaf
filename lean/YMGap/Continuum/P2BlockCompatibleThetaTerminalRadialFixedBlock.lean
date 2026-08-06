/-
Track 11.7-fusion / R3v -- physical fixed-block transport for the radial moment.

The finite certificates in the preceding module are transported here to the
physical block-compatible schedule.  For `k>=8`, write

    H = 2^(k-8),   L = 1280 H.

Bernoulli and reciprocal Bernoulli trap `w_k^(H^2)` between the two fixed
rational bases used by the tables.  Blockwise endpoint bounds then compare
the physical second and fourth theta moments with the fixed tables.  The
first scale `k=7` is checked by its separate exact 640-entry table.

No classical choice, native evaluation, custom axiom, or proof hole is used.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedPoint

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedBlock

set_option maxHeartbeats 8000000
set_option maxRecDepth 60000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedPoint
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialMoment
open YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Flatten a fixed number of consecutive blocks without evaluating their
product length. -/
private theorem fsum_blocks_eq (f : Nat -> Q') (H : Nat) : forall B,
    fsum f (B * H) ≈
      fsum (fun b => fsum (fun r => f (b * H + r)) H) B
  | 0 => by
      simp only [Nat.zero_mul, fsum_zero]
      exact Q'.eqv_refl 0
  | B + 1 => by
      have ih := fsum_blocks_eq f H B
      rw [Nat.succ_mul]
      change fsum f (B * H + H) ≈
        fsum (fun b => fsum (fun r => f (b * H + r)) H) B +
          fsum (fun r => f (B * H + r)) H
      refine Q'.eqv_trans _ _ _
        (FusionCoreStepRoundH.fsum_split_at f (B * H) H) ?_
      exact Q'.add_eqv_congr' ih (Q'.eqv_refl _)

/-- Replace the squared theta base by twice the exponent of the heat weight. -/
private theorem thetaPower_eq_double (w : Q') (n : Nat) :
    qpow (w * w) (n * n) ≈ qpow w (2 * (n * n)) := by
  have hsquare := FusionQuotientCollapse.qpow_mul_self w (n * n)
  have hadd := HeatKernelRGStep.qpow_add w (n * n) (n * n)
  refine Q'.eqv_trans _ (qpow w (n * n) * qpow w (n * n)) _
    hsquare ?_
  refine Q'.eqv_trans _ (qpow w (n * n + n * n)) _
    (Q'.eqv_symm hadd) ?_
  rw [show n * n + n * n = 2 * (n * n) by omega]
  exact Q'.eqv_refl _

/-- Powers at dyadically scaled block endpoints are powers of one scaled
base. -/
private theorem scaledEndpointPower_eqv
    (w : Q') (H x : Nat) :
    qpow w (2 * (((x * H) * (x * H)))) ≈
      qpow (qpow w (H * H)) (2 * (x * x)) := by
  have hiter := HeatKernelRGStep.qpow_qpow w (H * H) (2 * (x * x))
  have hexp : (H * H) * (2 * (x * x)) =
      2 * ((x * H) * (x * H)) := by ac_rfl
  exact Q'.eqv_trans _ _ _ (by
      rw [hexp]
      exact Q'.eqv_refl _)
    (Q'.eqv_symm hiter)

private theorem tailMargin_mul_square_eqv
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    blockMargin k * Q'.ofNat (H * H) ≈
      Q'.mkPos 1 786432 (by decide) := by
  have h := fineMargin_mul_dyadicSquare_eqv
    (k := k - 1) (by omega : 7 <= k - 1)
  have hidx : k - 1 + 1 = k := by omega
  have hsub : k - 1 - 7 = k - 8 := by omega
  rw [hidx, hsub] at h
  exact h

/-- Uniform Bernoulli lower base for every physical `k>=8`. -/
theorem radialTailLowerQ_le_scaledBase
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    radialTailLowerQ <= qpow (blockWeight k) (H * H) := by
  let H := 2 ^ (k - 8)
  let u := blockMargin k
  have hmargin : u * Q'.ofNat (H * H) ≈
      Q'.mkPos 1 786432 (by decide) := by
    simpa only [H, u] using tailMargin_mul_square_eqv hk
  have hone : (1 : Q') - blockWeight k ≈ u := by
    simpa only [u] using one_sub_blockWeight_eqv_margin k
  have hprod : Q'.ofNat (H * H) * ((1 : Q') - blockWeight k) ≈
      Q'.mkPos 1 786432 (by decide) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (H * H) * u) _
      (Q'.mul_eqv_congr_left _ _ _ hone) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hmargin
  have hleft : (1 : Q') -
        Q'.ofNat (H * H) * ((1 : Q') - blockWeight k) ≈
      radialTailLowerQ := by
    refine Q'.eqv_trans _
      ((1 : Q') - Q'.mkPos 1 786432 (by decide)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left 1 _ _
        (Q'.neg_eqv_congr _ _ hprod)
    · unfold radialTailLowerQ
      decide
  have hbern := qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) (H * H)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hbern

private theorem tailBernDen_eqv
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    bernDen (blockMargin k) (H * H) ≈
      Q'.mkPos 786433 786432 (by decide) := by
  let H := 2 ^ (k - 8)
  unfold bernDen
  have hm := tailMargin_mul_square_eqv hk
  have hp : Q'.ofNat (H * H) * blockMargin k ≈
      Q'.mkPos 1 786432 (by decide) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (by simpa only [H] using hm)
  refine Q'.eqv_trans _
    ((1 : Q') + Q'.mkPos 1 786432 (by decide)) _
    (Q'.add_eqv_congr_left 1 _ _ hp) ?_
  decide

/-- Uniform reciprocal-Bernoulli upper base for every physical `k>=8`. -/
theorem scaledBase_le_radialTailUpperQ
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    qpow (blockWeight k) (H * H) <= radialTailUpperQ := by
  let H := 2 ^ (k - 8)
  let u := blockMargin k
  let D := Q'.mkPos 786433 786432 (by decide)
  have hu0 : (0 : Q') <= u := blockMargin_nonneg k
  have hu1 : u <= (1 : Q') := blockMargin_le_one k
  have hbern := oneSub_pow_mul_bernDen_le hu0 hu1 (H * H)
  have hden : bernDen u (H * H) ≈ D := by
    simpa only [H, u, D] using tailBernDen_eqv hk
  have hprod : qpow (blockWeight k) (H * H) * D <= (1 : Q') := by
    have hleft : qpow (blockWeight k) (H * H) * bernDen u (H * H) ≈
        qpow (blockWeight k) (H * H) * D :=
      Q'.mul_eqv_congr_left _ _ _ hden
    have hweight : blockWeight k = oneSub u := rfl
    rw [hweight]
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hbern
  have hDpos : (0 : Q') < D := by unfold D; decide
  have hdiv : Q'.divPos (1 : Q') D hDpos <= radialTailUpperQ := by
    apply Q'.divPos_le_of_le_mul
    unfold D radialTailUpperQ
    decide
  exact Q'.le_trans' _ _ _
    (Q'.le_divPos_of_mul_le (1 : Q') D hDpos hprod) hdiv

private theorem radialTailLowerTable_generated :
    radialTailLowerTable ≈
      fsum (fun b =>
        Q'.ofNat (4 * (b * b * b * b)) *
          fixedPointVal radialTailLowerScale radialTailLowerScale_pos
            (floorPow radialTailLowerScale radialTailLowerBase
              (2 * ((b + 1) * (b + 1))))) radialTailBlocks := by
  have h := radialTailLowerGenerated_eqv radialTailBlocks
  rw [radialTailLowerTableNum_eq] at h
  simpa only [radialTailLowerTable] using h

private theorem radialTailUpperTable_generated :
    radialTailUpperTable ≈
      fsum (fun b =>
        Q'.ofNat ((b + 1) * (b + 1)) *
          fixedPointVal radialTailUpperScale radialTailUpperScale_pos
            (ceilPow radialTailUpperScale radialTailUpperBase
              (2 * (b * b)))) radialTailBlocks := by
  have h := radialTailUpperGenerated_eqv radialTailBlocks
  rw [radialTailUpperTableNum_eq] at h
  simpa only [radialTailUpperTable] using h

private theorem tailCutoffLength_eq
    {k : Nat} (hk : 8 <= k) :
    blockNcut k + 1 = radialTailBlocks * 2 ^ (k - 8) := by
  have hdecomp : k = 8 + (k - 8) := by omega
  rw [blockNcut_closed, hdecomp, Nat.pow_add]
  rw [show 2 ^ 8 = 256 by decide,
    show 8 + (k - 8) - 8 = k - 8 by omega]
  unfold radialTailBlocks
  omega

private theorem tailFloorPower_le_physical
    {k : Nat} (hk : 8 <= k) (b r : Nat)
    (hr : r < 2 ^ (k - 8)) :
    let H := 2 ^ (k - 8)
    let n := b * H + r + 1
    fixedPointVal radialTailLowerScale radialTailLowerScale_pos
        (floorPow radialTailLowerScale radialTailLowerBase
          (2 * ((b + 1) * (b + 1)))) <=
      qpow (blockWeight k * blockWeight k) (n * n) := by
  let H := 2 ^ (k - 8)
  let n := b * H + r + 1
  let w := blockWeight k
  let scaled := qpow w (H * H)
  let e := 2 * ((b + 1) * (b + 1))
  have hfloor := radialTailFloorPow_le e
  have hbase : radialTailLowerQ <= scaled := by
    simpa only [H, w, scaled] using radialTailLowerQ_le_scaledBase hk
  have hlo0 : (0 : Q') <= radialTailLowerQ := by
    unfold radialTailLowerQ
    decide
  have hmono := HeatKernelGap.qpow_mono hlo0 hbase e
  have hendpoint : qpow scaled e ≈
      qpow w (2 * (((b + 1) * H) * ((b + 1) * H))) := by
    simpa only [scaled, e] using
      Q'.eqv_symm (scaledEndpointPower_eqv w H (b + 1))
  have hnle : n <= (b + 1) * H := by
    dsimp only [n, H]
    rw [Nat.add_mul]
    omega
  have hexp : 2 * (n * n) <=
      2 * (((b + 1) * H) * ((b + 1) * H)) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hnle hnle)
  have hanti := HeatKernelRGStep.qpow_antitone
    (blockWeight_nonneg k) (blockWeight_le_one k)
    (2 * (n * n))
    (2 * (((b + 1) * H) * ((b + 1) * H))) hexp
  have htheta := thetaPower_eq_double w n
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hendpoint)
        (Q'.le_trans' _ _ _ hanti (Q'.ge_of_eqv htheta))))

private theorem physical_le_tailCeilPower
    {k : Nat} (hk : 8 <= k) (b r : Nat)
    (hr : r < 2 ^ (k - 8)) :
    let H := 2 ^ (k - 8)
    let n := b * H + r + 1
    qpow (blockWeight k * blockWeight k) (n * n) <=
      fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        (ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b))) := by
  let H := 2 ^ (k - 8)
  let n := b * H + r + 1
  let w := blockWeight k
  let scaled := qpow w (H * H)
  let e := 2 * (b * b)
  have hnlo : b * H <= n := by dsimp only [n]; omega
  have hexp : 2 * ((b * H) * (b * H)) <= 2 * (n * n) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hnlo hnlo)
  have hanti := HeatKernelRGStep.qpow_antitone
    (blockWeight_nonneg k) (blockWeight_le_one k)
    (2 * ((b * H) * (b * H))) (2 * (n * n)) hexp
  have htheta := thetaPower_eq_double w n
  have hscaled : qpow w (2 * ((b * H) * (b * H))) ≈
      qpow scaled e := by
    simpa only [scaled, e] using scaledEndpointPower_eqv w H b
  have hbase : scaled <= radialTailUpperQ := by
    simpa only [H, w, scaled] using scaledBase_le_radialTailUpperQ hk
  have hscaled0 : (0 : Q') <= scaled :=
    qpow_nonneg _ (blockWeight_nonneg k) (H * H)
  have hmono := HeatKernelGap.qpow_mono hscaled0 hbase e
  have hceil := radialTailPow_le_ceil e
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htheta)
    (Q'.le_trans' _ _ _ hanti
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled)
        (Q'.le_trans' _ _ _ hmono hceil)))

private theorem tailLowerTerm_le_fourthTerm
    {k : Nat} (hk : 8 <= k) (b r : Nat)
    (hr : r < 2 ^ (k - 8)) :
    let H := 2 ^ (k - 8)
    let n := b * H + r + 1
    Q'.ofNat (4 * (b * b * b * b) *
          (H * H * H * H)) *
        fixedPointVal radialTailLowerScale radialTailLowerScale_pos
          (floorPow radialTailLowerScale radialTailLowerBase
            (2 * ((b + 1) * (b + 1)))) <=
      Q'.ofNat (4 * (n * n)) * integerThetaTerm (blockWeight k) n := by
  let H := 2 ^ (k - 8)
  let n := b * H + r + 1
  let floor := fixedPointVal radialTailLowerScale radialTailLowerScale_pos
    (floorPow radialTailLowerScale radialTailLowerBase
      (2 * ((b + 1) * (b + 1))))
  let power := qpow (blockWeight k * blockWeight k) (n * n)
  have hnlo : b * H <= n := by dsimp only [n]; omega
  have hsq : (b * H) * (b * H) <= n * n :=
    Nat.mul_le_mul hnlo hnlo
  have hfour : ((b * H) * (b * H)) * ((b * H) * (b * H)) <=
      (n * n) * (n * n) := Nat.mul_le_mul hsq hsq
  have hcoeffNat : 4 * (b * b * b * b) * (H * H * H * H) <=
      (4 * (n * n)) * (n * n) := by
    have hreorder : (b * b * b * b) * (H * H * H * H) =
        ((b * H) * (b * H)) * ((b * H) * (b * H)) := by ac_rfl
    calc
      4 * (b * b * b * b) * (H * H * H * H) =
          4 * ((b * b * b * b) * (H * H * H * H)) := by ac_rfl
      _ = 4 * (((b * H) * (b * H)) * ((b * H) * (b * H))) := by
        rw [hreorder]
      _ <= 4 * ((n * n) * (n * n)) := Nat.mul_le_mul_left 4 hfour
      _ = (4 * (n * n)) * (n * n) := by ac_rfl
  have hcoeff := Q'.ofNat_le_ofNat hcoeffNat
  have hpower : floor <= power := by
    simpa only [H, n, floor, power] using
      tailFloorPower_le_physical hk b r hr
  have hfloor0 : (0 : Q') <= floor :=
    fixedPointVal_nonneg _ _ _
  have hactual0 : (0 : Q') <= Q'.ofNat ((4 * (n * n)) * (n * n)) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg hcoeff hpower hactual0 hfloor0
  have hrhs : Q'.ofNat ((4 * (n * n)) * (n * n)) * power ≈
      Q'.ofNat (4 * (n * n)) *
        (Q'.ofNat (n * n) * power) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat (4 * (n * n)) * Q'.ofNat (n * n)) * power) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ power
        (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv _ _))
    · exact Q'.mul_assoc_eqv _ _ _
  unfold integerThetaTerm
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hrhs)

private theorem thetaTerm_le_tailUpperTerm
    {k : Nat} (hk : 8 <= k) (b r : Nat)
    (hr : r < 2 ^ (k - 8)) :
    let H := 2 ^ (k - 8)
    let n := b * H + r + 1
    integerThetaTerm (blockWeight k) n <=
      Q'.ofNat (((b + 1) * (b + 1)) * (H * H)) *
        fixedPointVal radialTailUpperScale radialTailUpperScale_pos
          (ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b))) := by
  let H := 2 ^ (k - 8)
  let n := b * H + r + 1
  let power := qpow (blockWeight k * blockWeight k) (n * n)
  let ceil := fixedPointVal radialTailUpperScale radialTailUpperScale_pos
    (ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b)))
  have hnhi : n <= (b + 1) * H := by
    dsimp only [n, H]
    rw [Nat.add_mul]
    omega
  have hcoeffNat : n * n <= ((b + 1) * (b + 1)) * (H * H) := by
    have h := Nat.mul_le_mul hnhi hnhi
    have hreorder : ((b + 1) * H) * ((b + 1) * H) =
        ((b + 1) * (b + 1)) * (H * H) := by ac_rfl
    rw [hreorder] at h
    exact h
  have hcoeff := Q'.ofNat_le_ofNat hcoeffNat
  have hpower : power <= ceil := by
    simpa only [H, n, power, ceil] using
      physical_le_tailCeilPower hk b r hr
  have hupperCoeff0 : (0 : Q') <=
      Q'.ofNat (((b + 1) * (b + 1)) * (H * H)) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hpower0 : (0 : Q') <= power :=
    qpow_nonneg _
      (Q'.mul_nonneg _ _ (blockWeight_nonneg k) (blockWeight_nonneg k)) _
  have hcoeff0 : (0 : Q') <= Q'.ofNat (n * n) :=
    HeatKernelRGStep.zero_le_ofNat _
  unfold integerThetaTerm
  exact Q'.mul_le_mul_of_nonneg hcoeff hpower hupperCoeff0 hpower0

private theorem tailLowerBlock_le_fourthBlock
    {k : Nat} (hk : 8 <= k) (b : Nat) :
    let H := 2 ^ (k - 8)
    Q'.ofNat H *
        (Q'.ofNat (4 * (b * b * b * b) * (H * H * H * H)) *
          fixedPointVal radialTailLowerScale radialTailLowerScale_pos
            (floorPow radialTailLowerScale radialTailLowerBase
              (2 * ((b + 1) * (b + 1))))) <=
      fsum (fun r =>
        let n := b * H + r + 1
        Q'.ofNat (4 * (n * n)) * integerThetaTerm (blockWeight k) n) H := by
  let H := 2 ^ (k - 8)
  let c := Q'.ofNat (4 * (b * b * b * b) * (H * H * H * H)) *
    fixedPointVal radialTailLowerScale radialTailLowerScale_pos
      (floorPow radialTailLowerScale radialTailLowerBase
        (2 * ((b + 1) * (b + 1))))
  have hsum : fsum (fun _ => c) H <=
      fsum (fun r =>
        let n := b * H + r + 1
        Q'.ofNat (4 * (n * n)) * integerThetaTerm (blockWeight k) n) H := by
    apply CubeRatioBounds.fsum_mono_lt
    intro r hr
    simpa only [H, c] using tailLowerTerm_le_fourthTerm hk b r hr
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (JacobiModularCReal.fsum_const_val c H)) hsum

private theorem thetaBlock_le_tailUpperBlock
    {k : Nat} (hk : 8 <= k) (b : Nat) :
    let H := 2 ^ (k - 8)
    fsum (fun r =>
        integerThetaTerm (blockWeight k) (b * H + r + 1)) H <=
      Q'.ofNat H *
        (Q'.ofNat (((b + 1) * (b + 1)) * (H * H)) *
          fixedPointVal radialTailUpperScale radialTailUpperScale_pos
            (ceilPow radialTailUpperScale radialTailUpperBase
              (2 * (b * b)))) := by
  let H := 2 ^ (k - 8)
  let c := Q'.ofNat (((b + 1) * (b + 1)) * (H * H)) *
    fixedPointVal radialTailUpperScale radialTailUpperScale_pos
      (ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b)))
  have hsum : fsum (fun r =>
      integerThetaTerm (blockWeight k) (b * H + r + 1)) H <=
      fsum (fun _ => c) H := by
    apply CubeRatioBounds.fsum_mono_lt
    intro r hr
    simpa only [H, c] using thetaTerm_le_tailUpperTerm hk b r hr
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (JacobiModularCReal.fsum_const_val c H))

private theorem lowerScaleTerm_eqv (H b : Nat) (x : Q') :
    Q'.ofNat H *
        (Q'.ofNat (4 * (b * b * b * b) * (H * H * H * H)) * x) ≈
      Q'.ofNat (H * H * H * H * H) *
        (Q'.ofNat (4 * (b * b * b * b)) * x) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.one_mul, Int.mul_one]
  ac_rfl

private theorem upperScaleTerm_eqv (H b : Nat) (x : Q') :
    Q'.ofNat H *
        (Q'.ofNat (((b + 1) * (b + 1)) * (H * H)) * x) ≈
      Q'.ofNat (H * H * H) *
        (Q'.ofNat ((b + 1) * (b + 1)) * x) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.natCast_add, Int.one_mul, Int.mul_one]
  ac_rfl

/-- The fixed lower table, scaled by `H^5`, is below the physical fourfold
fourth moment. -/
theorem scaledRadialTailLowerTable_le_fourthMoment
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    Q'.ofNat (H * H * H * H * H) * radialTailLowerTable <=
      fixedCutoffTerminalIntegerFourFourthSum
        (blockWeight k) (blockNcut k) := by
  let H := 2 ^ (k - 8)
  let c := Q'.ofNat (H * H * H * H * H)
  let tableTerm := fun b =>
    Q'.ofNat (4 * (b * b * b * b)) *
      fixedPointVal radialTailLowerScale radialTailLowerScale_pos
        (floorPow radialTailLowerScale radialTailLowerBase
          (2 * ((b + 1) * (b + 1))))
  let blockTerm := fun b =>
    Q'.ofNat H *
      (Q'.ofNat (4 * (b * b * b * b) * (H * H * H * H)) *
        fixedPointVal radialTailLowerScale radialTailLowerScale_pos
          (floorPow radialTailLowerScale radialTailLowerBase
            (2 * ((b + 1) * (b + 1)))))
  have hscaled : c * radialTailLowerTable ≈
      fsum (fun b => c * tableTerm b) radialTailBlocks := by
    refine Q'.eqv_trans _ (c * fsum tableTerm radialTailBlocks) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left c _ _ radialTailLowerTable_generated
    · exact CubeRatioBounds.fsum_const_mul c tableTerm radialTailBlocks
  have hterms : fsum (fun b => c * tableTerm b) radialTailBlocks ≈
      fsum blockTerm radialTailBlocks :=
    CubeRatioBounds.fsum_eqv_congr _ _ (fun b => by
      simpa only [c, tableTerm, blockTerm, H] using
        Q'.eqv_symm (lowerScaleTerm_eqv H b
          (fixedPointVal radialTailLowerScale radialTailLowerScale_pos
            (floorPow radialTailLowerScale radialTailLowerBase
              (2 * ((b + 1) * (b + 1))))))) _
  have htoBlocks : c * radialTailLowerTable ≈
      fsum blockTerm radialTailBlocks :=
    Q'.eqv_trans (c * radialTailLowerTable)
      (fsum (fun b => c * tableTerm b) radialTailBlocks)
      (fsum blockTerm radialTailBlocks) hscaled hterms
  let f := fun j =>
    Q'.ofNat (4 * ((j + 1) * (j + 1))) *
      integerThetaTerm (blockWeight k) (j + 1)
  have hblocks : fsum blockTerm radialTailBlocks <=
      fsum (fun b => fsum (fun r => f (b * H + r)) H)
        radialTailBlocks := by
    apply CubeRatioBounds.fsum_mono_lt
    intro b _
    simpa only [blockTerm, f, H] using tailLowerBlock_le_fourthBlock hk b
  have hflat := fsum_blocks_eq f H radialTailBlocks
  have hlen := tailCutoffLength_eq hk
  have hstart : c * radialTailLowerTable <=
      fsum blockTerm radialTailBlocks := Q'.le_of_eqv htoBlocks
  have hend : fsum (fun b => fsum (fun r => f (b * H + r)) H)
        radialTailBlocks <= fsum f (radialTailBlocks * H) :=
    Q'.ge_of_eqv hflat
  unfold fixedCutoffTerminalIntegerFourFourthSum
  rw [hlen]
  change c * radialTailLowerTable <= _
  exact Q'.le_trans' _ _ _ hstart
    (Q'.le_trans' _ _ _ hblocks hend)

/-- The physical integer-theta second moment is below the fixed upper table
times `H^3`. -/
theorem integerThetaSum_le_scaledRadialTailUpperTable
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    integerThetaSum (blockWeight k) (blockNcut k) <=
      Q'.ofNat (H * H * H) * radialTailUpperTable := by
  let H := 2 ^ (k - 8)
  let c := Q'.ofNat (H * H * H)
  let tableTerm := fun b =>
    Q'.ofNat ((b + 1) * (b + 1)) *
      fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        (ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b)))
  let blockTerm := fun b =>
    Q'.ofNat H *
      (Q'.ofNat (((b + 1) * (b + 1)) * (H * H)) *
        fixedPointVal radialTailUpperScale radialTailUpperScale_pos
          (ceilPow radialTailUpperScale radialTailUpperBase (2 * (b * b))))
  have hscaled : c * radialTailUpperTable ≈
      fsum (fun b => c * tableTerm b) radialTailBlocks := by
    refine Q'.eqv_trans _ (c * fsum tableTerm radialTailBlocks) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left c _ _ radialTailUpperTable_generated
    · exact CubeRatioBounds.fsum_const_mul c tableTerm radialTailBlocks
  have hterms : fsum blockTerm radialTailBlocks ≈
      fsum (fun b => c * tableTerm b) radialTailBlocks :=
    CubeRatioBounds.fsum_eqv_congr _ _ (fun b => by
      simpa only [c, tableTerm, blockTerm, H] using
        upperScaleTerm_eqv H b
          (fixedPointVal radialTailUpperScale radialTailUpperScale_pos
            (ceilPow radialTailUpperScale radialTailUpperBase
              (2 * (b * b))))) _
  have hfromBlocks : fsum blockTerm radialTailBlocks ≈
      c * radialTailUpperTable :=
    Q'.eqv_trans (fsum blockTerm radialTailBlocks)
      (fsum (fun b => c * tableTerm b) radialTailBlocks)
      (c * radialTailUpperTable) hterms (Q'.eqv_symm hscaled)
  let f := fun j => integerThetaTerm (blockWeight k) (j + 1)
  have hblocks : fsum (fun b => fsum (fun r => f (b * H + r)) H)
        radialTailBlocks <= fsum blockTerm radialTailBlocks := by
    apply CubeRatioBounds.fsum_mono_lt
    intro b _
    simpa only [blockTerm, f, H] using thetaBlock_le_tailUpperBlock hk b
  have hflat := fsum_blocks_eq f H radialTailBlocks
  have hlen := tailCutoffLength_eq hk
  unfold integerThetaSum
  rw [← MovingCutoff.fsum_eq_finSum, hlen]
  change _ <= c * radialTailUpperTable
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hflat)
    (Q'.le_trans' _ _ _ hblocks
      (Q'.le_of_eqv hfromBlocks))

private theorem add_le_add_local {a b c d : Q'}
    (h1 : a <= b) (h2 : c <= d) : a + c <= b + d :=
  Q'.le_trans' _ (b + c) _
    (Q'.add_le_add_right _ _ c h1)
    (Q'.add_le_add_left b _ _ h2)

private theorem tailTerminalPower_le
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    let L := radialTailBlocks * H
    qpow (blockWeight k * blockWeight k) (L * L) <=
      radialTailTerminalUpper := by
  let H := 2 ^ (k - 8)
  let L := radialTailBlocks * H
  let w := blockWeight k
  let scaled := qpow w (H * H)
  let e := 2 * (radialTailBlocks * radialTailBlocks)
  have htheta := thetaPower_eq_double w L
  have hscaled : qpow w (2 * (L * L)) ≈ qpow scaled e := by
    simpa only [L, scaled, e] using
      scaledEndpointPower_eqv w H radialTailBlocks
  have hbase : scaled <= radialTailUpperQ := by
    simpa only [H, w, scaled] using scaledBase_le_radialTailUpperQ hk
  have hscaled0 : (0 : Q') <= scaled :=
    qpow_nonneg _ (blockWeight_nonneg k) (H * H)
  have hmono := HeatKernelGap.qpow_mono hscaled0 hbase e
  have hceil := radialTailPow_le_ceil e
  have hwitness : fixedPointVal radialTailUpperScale radialTailUpperScale_pos
        (ceilPow radialTailUpperScale radialTailUpperBase e) ≈
      radialTailTerminalUpper := by
    rw [radialTailTerminalPow_eq]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htheta)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled)
      (Q'.le_trans' _ _ _ hmono
        (Q'.le_trans' _ _ _ hceil (Q'.le_of_eqv hwitness))))

private theorem tailTerminalCoeff_le
    (H : Nat) (hH : 0 < H) :
    let B := radialTailBlocks
    let L := B * H
    (2 * L + 1) * (L * L) <=
      (2 * (B * B * B) + B * B) * (H * H * H * H * H) := by
  let B := radialTailBlocks
  let L := B * H
  have hH2 : 1 <= H * H := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.ne_of_gt hH) (Nat.ne_of_gt hH))
  have hH3 : H * H * H <= H * H * H * H * H := by
    calc
      H * H * H = (H * H * H) * 1 := by rw [Nat.mul_one]
      _ <= (H * H * H) * (H * H) := Nat.mul_le_mul_left _ hH2
      _ = H * H * H * H * H := by ac_rfl
  have hH2to5 : H * H <= H * H * H * H * H := by
    have hH3one : 1 <= H * H * H :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.mul_ne_zero
          (Nat.ne_of_gt hH) (Nat.ne_of_gt hH)) (Nat.ne_of_gt hH))
    calc
      H * H = (H * H) * 1 := by rw [Nat.mul_one]
      _ <= (H * H) * (H * H * H) := Nat.mul_le_mul_left _ hH3one
      _ = H * H * H * H * H := by ac_rfl
  dsimp only [B, L]
  calc
    (2 * (radialTailBlocks * H) + 1) *
        ((radialTailBlocks * H) * (radialTailBlocks * H)) =
      2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) *
          (H * H * H) +
        (radialTailBlocks * radialTailBlocks) * (H * H) := by
          rw [Nat.add_mul, Nat.one_mul]
          congr 1 <;> ac_rfl
    _ <= 2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) *
          (H * H * H * H * H) +
        (radialTailBlocks * radialTailBlocks) *
          (H * H * H * H * H) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ hH3) (Nat.mul_le_mul_left _ hH2to5)
    _ = (2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) +
          radialTailBlocks * radialTailBlocks) *
        (H * H * H * H * H) := by rw [Nat.add_mul]

theorem terminalIntegerTheta_le_scaledTailTerminal
    {k : Nat} (hk : 8 <= k) :
    let H := 2 ^ (k - 8)
    let L := radialTailBlocks * H
    Q'.ofNat (2 * L + 1) * integerThetaTerm (blockWeight k) L <=
      Q'.ofNat (H * H * H * H * H) *
        (Q'.ofNat
          (2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) +
            radialTailBlocks * radialTailBlocks) *
          radialTailTerminalUpper) := by
  let H := 2 ^ (k - 8)
  let L := radialTailBlocks * H
  let power := qpow (blockWeight k * blockWeight k) (L * L)
  have hH : 0 < H := Nat.pow_pos (by decide)
  have hcoeffNat := tailTerminalCoeff_le H hH
  have hcoeff := Q'.ofNat_le_ofNat hcoeffNat
  have hpower : power <= radialTailTerminalUpper := by
    simpa only [H, L, power] using tailTerminalPower_le hk
  have hupper0 : (0 : Q') <= Q'.ofNat
      ((2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) +
        radialTailBlocks * radialTailBlocks) *
          (H * H * H * H * H)) := HeatKernelRGStep.zero_le_ofNat _
  have hpower0 : (0 : Q') <= power :=
    qpow_nonneg _ (Q'.mul_nonneg _ _
      (blockWeight_nonneg k) (blockWeight_nonneg k)) _
  have hmul := Q'.mul_le_mul_of_nonneg hcoeff hpower hupper0 hpower0
  unfold integerThetaTerm
  have hleft : Q'.ofNat (2 * L + 1) *
      (Q'.ofNat (L * L) * power) ≈
      Q'.ofNat ((2 * L + 1) * (L * L)) * power := by
    refine Q'.eqv_trans _
      ((Q'.ofNat (2 * L + 1) * Q'.ofNat (L * L)) * power) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ power
      (HeatKernelRGStep.ofNat_mul_eqv _ _)
  have hright : Q'.ofNat
        ((2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) +
          radialTailBlocks * radialTailBlocks) *
            (H * H * H * H * H)) * radialTailTerminalUpper ≈
      Q'.ofNat (H * H * H * H * H) *
        (Q'.ofNat
          (2 * (radialTailBlocks * radialTailBlocks * radialTailBlocks) +
            radialTailBlocks * radialTailBlocks) *
          radialTailTerminalUpper) := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Int.natCast_mul, Int.natCast_add, Int.one_mul]
    ac_rfl
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

private theorem secondMomentScale_eqv
    (H B : Nat) (alpha upper : Q') :
    alpha *
        ((Q'.ofNat (B * H) * Q'.ofNat (B * H)) *
          (Q'.ofNat (H * H * H) * upper)) ≈
      Q'.ofNat (H * H * H * H * H) *
        (alpha * (Q'.ofNat (B * B) * upper)) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.one_mul]
  ac_rfl

/-- The uniform `k>=8` table proves the physical integer-theta fourth-moment
field. -/
theorem terminalIntegerFourth_fromEight
    (k : Nat) (hk : 8 <= k) :
    let w := blockWeight k
    let N := blockNcut k
    let L := Q'.ofNat (N + 1)
    let Theta := integerThetaSum w N
    terminalRadialMomentCoeff * ((L * L) * Theta) +
        Q'.ofNat (2 * (N + 1) + 1) * integerThetaTerm w (N + 1) <=
      fixedCutoffTerminalIntegerFourFourthSum w N +
        Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
          integerThetaTerm w 1 + Q'.ofNat 2 * Theta := by
  let H := 2 ^ (k - 8)
  let B := radialTailBlocks
  let nL := B * H
  let w := blockWeight k
  let N := blockNcut k
  let L := Q'.ofNat nL
  let Theta := integerThetaSum w N
  let M4 := fixedCutoffTerminalIntegerFourFourthSum w N
  let c := Q'.ofNat (H * H * H * H * H)
  let A := terminalRadialMomentCoeff *
    (Q'.ofNat (B * B) * radialTailUpperTable)
  let T := Q'.ofNat (2 * (B * B * B) + B * B) *
    radialTailTerminalUpper
  have hlen := tailCutoffLength_eq hk
  have htheta : Theta <= Q'.ofNat (H * H * H) * radialTailUpperTable := by
    simpa only [H, w, N, Theta] using
      integerThetaSum_le_scaledRadialTailUpperTable hk
  have hL0 : (0 : Q') <= L * L :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _)
  have halpha0 : (0 : Q') <= terminalRadialMomentCoeff := by
    unfold terminalRadialMomentCoeff
    decide
  have hsecondRaw := Q'.mul_le_mul_of_nonneg_left _ _ (L * L)
    htheta hL0
  have hsecondRaw' := Q'.mul_le_mul_of_nonneg_left _ _
    terminalRadialMomentCoeff hsecondRaw halpha0
  have hscaleSecond : terminalRadialMomentCoeff *
        ((L * L) * (Q'.ofNat (H * H * H) * radialTailUpperTable)) ≈
      c * A := by
    simpa only [L, nL, B, c, A] using
      secondMomentScale_eqv H B terminalRadialMomentCoeff radialTailUpperTable
  have hsecond : terminalRadialMomentCoeff * ((L * L) * Theta) <= c * A :=
    Q'.le_trans' _ _ _ hsecondRaw' (Q'.le_of_eqv hscaleSecond)
  have hterminal : Q'.ofNat (2 * nL + 1) *
      integerThetaTerm w nL <= c * T := by
    simpa only [H, B, nL, w, c, T] using
      terminalIntegerTheta_le_scaledTailTerminal hk
  have hsum : terminalRadialMomentCoeff * ((L * L) * Theta) +
      Q'.ofNat (2 * nL + 1) * integerThetaTerm w nL <=
        c * A + c * T := add_le_add_local hsecond hterminal
  have hfactor : c * A + c * T ≈ c * (A + T) :=
    Q'.eqv_symm (Q'.mul_add_eqv c A T)
  have hbalance : c * (A + T) <= c * radialTailLowerTable :=
    Q'.mul_le_mul_of_nonneg_left _ _ c (by
      simpa only [A, T, B] using radialTailFixedBalance)
      (HeatKernelRGStep.zero_le_ofNat _)
  have hlower : c * radialTailLowerTable <= M4 := by
    simpa only [H, w, N, c, M4] using
      scaledRadialTailLowerTable_le_fourthMoment hk
  have hstrong : terminalRadialMomentCoeff * ((L * L) * Theta) +
      Q'.ofNat (2 * nL + 1) * integerThetaTerm w nL <= M4 :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
        (Q'.le_trans' _ _ _ hbalance hlower))
  have htermOne0 : (0 : Q') <= integerThetaTerm w 1 := by
    unfold integerThetaTerm
    exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (qpow_nonneg _ (Q'.mul_nonneg _ _
        (blockWeight_nonneg k) (blockWeight_nonneg k)) _)
  have hhead0 : (0 : Q') <=
      Q'.ofNat (2 * (nL * nL) - 1) * integerThetaTerm w 1 :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) htermOne0
  have htheta0 : (0 : Q') <= Theta := by
    unfold Theta integerThetaSum
    rw [← MovingCutoff.fsum_eq_finSum]
    exact BondMovingStep.fsum_nonneg (fun j => by
      unfold integerThetaTerm
      exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (qpow_nonneg _ (Q'.mul_nonneg _ _
          (blockWeight_nonneg k) (blockWeight_nonneg k)) _)) _
  have htwoTheta0 : (0 : Q') <= Q'.ofNat 2 * Theta :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) htheta0
  have hweaken : M4 <= M4 +
      Q'.ofNat (2 * (nL * nL) - 1) * integerThetaTerm w 1 +
        Q'.ofNat 2 * Theta :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hhead0)
      (Q'.add_le_self_of_nonneg _ _ htwoTheta0)
  have hfinal := Q'.le_trans' _ _ _ hstrong hweaken
  dsimp only
  rw [hlen]
  simpa only [w, N, L, Theta, M4, nL] using hfinal

/-! ## Exact first physical scale -/

private theorem radialSevenQ_eqv_weight :
    radialSevenQ ≈ blockWeight 7 := by
  unfold radialSevenQ blockWeight blockMargin
    SpectralLocalizationCrux.q112 blockQuarter
  decide

private theorem sevenFloorPower_le_physical (n : Nat) :
    fixedPointVal radialSevenScale radialSevenScale_pos
        (floorPow radialSevenScale radialSevenBase (2 * (n * n))) <=
      qpow (blockWeight 7 * blockWeight 7) (n * n) := by
  have hfloor := radialSevenFloorPow_le (2 * (n * n))
  have hbase := BondMovingRelResidual.qpow_eqv_congr_base
    radialSevenQ_eqv_weight (2 * (n * n))
  have htheta := thetaPower_eq_double (blockWeight 7) n
  exact Q'.le_trans' _ _ _ hfloor
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hbase)
      (Q'.ge_of_eqv htheta))

private theorem sevenPhysical_le_ceilPower (n : Nat) :
    qpow (blockWeight 7 * blockWeight 7) (n * n) <=
      fixedPointVal radialSevenScale radialSevenScale_pos
        (ceilPow radialSevenScale radialSevenBase (2 * (n * n))) := by
  have htheta := thetaPower_eq_double (blockWeight 7) n
  have hbase := BondMovingRelResidual.qpow_eqv_congr_base
    radialSevenQ_eqv_weight (2 * (n * n))
  have hceil := radialSevenPow_le_ceil (2 * (n * n))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htheta)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hbase) hceil)

private theorem radialSevenLowerTable_generated :
    radialSevenLowerTable ≈
      fsum (fun b =>
        Q'.ofNat
            (4 * ((b + 1) * (b + 1) * (b + 1) * (b + 1))) *
          fixedPointVal radialSevenScale radialSevenScale_pos
            (floorPow radialSevenScale radialSevenBase
              (2 * ((b + 1) * (b + 1))))) radialSevenBlocks := by
  have h := radialSevenLowerGenerated_eqv radialSevenBlocks
  rw [radialSevenLowerTableNum_eq] at h
  simpa only [radialSevenLowerTable] using h

private theorem radialSevenUpperTable_generated :
    radialSevenUpperTable ≈
      fsum (fun b =>
        Q'.ofNat ((b + 1) * (b + 1)) *
          fixedPointVal radialSevenScale radialSevenScale_pos
            (ceilPow radialSevenScale radialSevenBase
              (2 * ((b + 1) * (b + 1))))) radialSevenBlocks := by
  have h := radialSevenUpperGenerated_eqv radialSevenBlocks
  rw [radialSevenUpperTableNum_eq] at h
  simpa only [radialSevenUpperTable] using h

theorem radialSevenLowerTable_le_fourthMoment :
    radialSevenLowerTable <=
      fixedCutoffTerminalIntegerFourFourthSum
        (blockWeight 7) (blockNcut 7) := by
  let lowerTerm := fun b =>
    Q'.ofNat (4 * ((b + 1) * (b + 1) * (b + 1) * (b + 1))) *
      fixedPointVal radialSevenScale radialSevenScale_pos
        (floorPow radialSevenScale radialSevenBase
          (2 * ((b + 1) * (b + 1))))
  let physicalTerm := fun b =>
    Q'.ofNat (4 * ((b + 1) * (b + 1))) *
      integerThetaTerm (blockWeight 7) (b + 1)
  have hterms : fsum lowerTerm radialSevenBlocks <=
      fsum physicalTerm radialSevenBlocks := by
    apply CubeRatioBounds.fsum_mono_lt
    intro b _
    dsimp only [lowerTerm, physicalTerm]
    let n := b + 1
    let floor := fixedPointVal radialSevenScale radialSevenScale_pos
      (floorPow radialSevenScale radialSevenBase (2 * (n * n)))
    let power := qpow (blockWeight 7 * blockWeight 7) (n * n)
    have hp : floor <= power := by
      simpa only [n, floor, power] using sevenFloorPower_le_physical n
    have hc : Q'.ofNat (4 * (n * n * n * n)) * floor ≈
        Q'.ofNat (4 * (n * n)) * (Q'.ofNat (n * n) * floor) := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast,
        Q'.ofNat_num_cast, Q'.ofNat_den_cast,
        Int.natCast_mul, Int.one_mul]
      ac_rfl
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat (n * n)) hp (HeatKernelRGStep.zero_le_ofNat _)
    have hmul4 := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat (4 * (n * n))) hmul (HeatKernelRGStep.zero_le_ofNat _)
    unfold integerThetaTerm
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hc) hmul4
  have hlen : blockNcut 7 + 1 = radialSevenBlocks := by
    unfold radialSevenBlocks
    decide
  unfold fixedCutoffTerminalIntegerFourFourthSum
  rw [hlen]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      simpa only [lowerTerm] using radialSevenLowerTable_generated)) hterms

theorem integerThetaSum_seven_le_upperTable :
    integerThetaSum (blockWeight 7) (blockNcut 7) <=
      radialSevenUpperTable := by
  let physicalTerm := fun b => integerThetaTerm (blockWeight 7) (b + 1)
  let upperTerm := fun b =>
    Q'.ofNat ((b + 1) * (b + 1)) *
      fixedPointVal radialSevenScale radialSevenScale_pos
        (ceilPow radialSevenScale radialSevenBase
          (2 * ((b + 1) * (b + 1))))
  have hterms : fsum physicalTerm radialSevenBlocks <=
      fsum upperTerm radialSevenBlocks := by
    apply CubeRatioBounds.fsum_mono_lt
    intro b _
    unfold physicalTerm upperTerm integerThetaTerm
    exact Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat ((b + 1) * (b + 1)))
      (sevenPhysical_le_ceilPower (b + 1))
      (HeatKernelRGStep.zero_le_ofNat _)
  have hlen : blockNcut 7 + 1 = radialSevenBlocks := by
    unfold radialSevenBlocks
    decide
  unfold integerThetaSum
  rw [← MovingCutoff.fsum_eq_finSum, hlen]
  exact Q'.le_trans' _ _ _ hterms (Q'.le_of_eqv (by
    simpa only [upperTerm] using Q'.eqv_symm radialSevenUpperTable_generated))

private theorem sevenTerminalPower_le :
    qpow (blockWeight 7 * blockWeight 7)
        (radialSevenBlocks * radialSevenBlocks) <=
      radialSevenTerminalUpper := by
  have h := sevenPhysical_le_ceilPower radialSevenBlocks
  have hw : fixedPointVal radialSevenScale radialSevenScale_pos
        (ceilPow radialSevenScale radialSevenBase
          (2 * (radialSevenBlocks * radialSevenBlocks))) ≈
      radialSevenTerminalUpper := by
    rw [radialSevenTerminalPow_eq]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hw)

/-- The isolated first open scale is discharged by its exact table. -/
theorem terminalIntegerFourth_seven :
    let w := blockWeight 7
    let N := blockNcut 7
    let L := Q'.ofNat (N + 1)
    let Theta := integerThetaSum w N
    terminalRadialMomentCoeff * ((L * L) * Theta) +
        Q'.ofNat (2 * (N + 1) + 1) * integerThetaTerm w (N + 1) <=
      fixedCutoffTerminalIntegerFourFourthSum w N +
        Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
          integerThetaTerm w 1 + Q'.ofNat 2 * Theta := by
  let B := radialSevenBlocks
  let w := blockWeight 7
  let N := blockNcut 7
  let L := Q'.ofNat B
  let Theta := integerThetaSum w N
  let M4 := fixedCutoffTerminalIntegerFourFourthSum w N
  let A := terminalRadialMomentCoeff *
    (Q'.ofNat (B * B) * radialSevenUpperTable)
  let T := Q'.ofNat ((2 * B + 1) * (B * B)) * radialSevenTerminalUpper
  have htheta : Theta <= radialSevenUpperTable := by
    simpa only [Theta, w, N] using integerThetaSum_seven_le_upperTable
  have hL0 : (0 : Q') <= L * L := Q'.mul_nonneg _ _
    (HeatKernelRGStep.zero_le_ofNat _) (HeatKernelRGStep.zero_le_ofNat _)
  have halpha0 : (0 : Q') <= terminalRadialMomentCoeff := by
    unfold terminalRadialMomentCoeff
    decide
  have hsecond0 := Q'.mul_le_mul_of_nonneg_left _ _ (L * L) htheta hL0
  have hsecond1 := Q'.mul_le_mul_of_nonneg_left _ _
    terminalRadialMomentCoeff hsecond0 halpha0
  have hsecond : terminalRadialMomentCoeff * ((L * L) * Theta) <= A := by
    simpa only [A, L, B] using hsecond1
  have hpower := sevenTerminalPower_le
  have hterminal : Q'.ofNat (2 * B + 1) * integerThetaTerm w B <= T := by
    unfold integerThetaTerm
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat (B * B)) hpower (HeatKernelRGStep.zero_le_ofNat _)
    have hmul2 := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.ofNat (2 * B + 1)) hmul (HeatKernelRGStep.zero_le_ofNat _)
    have heq : Q'.ofNat (2 * B + 1) *
        (Q'.ofNat (B * B) * radialSevenTerminalUpper) ≈ T := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [T, Q'.mul_num_cast, Q'.mul_den_cast,
        Q'.ofNat_num_cast, Q'.ofNat_den_cast,
        Int.natCast_mul, Int.natCast_add, Int.one_mul]
      ac_rfl
    exact Q'.le_trans' _ _ _ hmul2 (Q'.le_of_eqv heq)
  have hsum := add_le_add_local hsecond hterminal
  have hbalance : A + T <= radialSevenLowerTable := by
    simpa only [A, T, B] using radialSevenFixedBalance
  have hlower : radialSevenLowerTable <= M4 := by
    simpa only [M4, w, N] using radialSevenLowerTable_le_fourthMoment
  have hstrong : terminalRadialMomentCoeff * ((L * L) * Theta) +
      Q'.ofNat (2 * B + 1) * integerThetaTerm w B <= M4 :=
    Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ hbalance hlower)
  have htermOne0 : (0 : Q') <= integerThetaTerm w 1 := by
    unfold integerThetaTerm
    exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (qpow_nonneg _ (Q'.mul_nonneg _ _
        (blockWeight_nonneg 7) (blockWeight_nonneg 7)) _)
  have hhead0 : (0 : Q') <=
      Q'.ofNat (2 * (B * B) - 1) * integerThetaTerm w 1 :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) htermOne0
  have htheta0 : (0 : Q') <= Theta := by
    unfold Theta integerThetaSum
    rw [← MovingCutoff.fsum_eq_finSum]
    exact BondMovingStep.fsum_nonneg (fun j => by
      unfold integerThetaTerm
      exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (qpow_nonneg _ (Q'.mul_nonneg _ _
          (blockWeight_nonneg 7) (blockWeight_nonneg 7)) _)) _
  have htwo0 : (0 : Q') <= Q'.ofNat 2 * Theta :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) htheta0
  have hweak : M4 <= M4 +
      Q'.ofNat (2 * (B * B) - 1) * integerThetaTerm w 1 +
        Q'.ofNat 2 * Theta :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hhead0)
      (Q'.add_le_self_of_nonneg _ _ htwo0)
  have hfinal := Q'.le_trans' _ _ _ hstrong hweak
  have hlen : blockNcut 7 + 1 = radialSevenBlocks := by
    unfold radialSevenBlocks
    decide
  dsimp only
  rw [hlen]
  simpa only [B, w, N, L, Theta, M4] using hfinal

/-- All physical scales `k>=7` satisfy the exact integer-theta moment field. -/
theorem terminalIntegerFourth_fromSeven
    (k : Nat) (hk : 7 <= k) :
    let w := blockWeight k
    let N := blockNcut k
    let L := Q'.ofNat (N + 1)
    let Theta := integerThetaSum w N
    terminalRadialMomentCoeff * ((L * L) * Theta) +
        Q'.ofNat (2 * (N + 1) + 1) * integerThetaTerm w (N + 1) <=
      fixedCutoffTerminalIntegerFourFourthSum w N +
        Q'.ofNat (2 * ((N + 1) * (N + 1)) - 1) *
          integerThetaTerm w 1 + Q'.ofNat 2 * Theta := by
  by_cases h7 : k = 7
  · subst k
    exact terminalIntegerFourth_seven
  · exact terminalIntegerFourth_fromEight k (by omega)

/-- The original physical radial-envelope field is therefore proved at every
open tail scale. -/
theorem terminalRadial_fromSeven
    (k : Nat) (hk : 7 <= k) :
    fixedCutoffTerminalRadialDiagEnvelope (blockWeight k) (blockNcut k) <=
      terminalRadialSplitCoeff *
        ((Q'.ofNat (blockNcut k + 1) * Q'.ofNat (blockNcut k + 1)) *
          coordNormSq (blockWeight k) (blockNcut k)) := by
  exact terminalRadial_le_of_integerFourFourthMoment k
    (terminalIntegerFourth_fromSeven k hk)

/-- Honest post-radial frontier.  The terminal endpoint and radial moment are
now installed; only trapezoid exchange and the independent fine reserve
remain. -/
structure BlockCompatibleP2PostRadialTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <= D1 * T4

def BlockCompatibleP2PostRadialTailFromSeven.toIntegerFourthTail
    (T : BlockCompatibleP2PostRadialTailFromSeven) :
    BlockCompatibleP2TerminalIntegerFourthTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalIntegerFourth := terminalIntegerFourth_fromSeven
  fineReserve := T.fineReserve

def BlockCompatibleP2PostRadialTailFromSeven.toThetaFactorizedTail
    (T : BlockCompatibleP2PostRadialTailFromSeven) :
    BlockCompatibleP2TerminalThetaFactorizedTailFromSeven :=
  T.toIntegerFourthTail.toThetaFactorizedTail

def BlockCompatibleP2PostRadialTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2PostRadialTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toIntegerFourthTail.toCoefficientSandwich

#print axioms radialTailLowerQ_le_scaledBase
#print axioms scaledBase_le_radialTailUpperQ
#print axioms terminalIntegerFourth_fromEight
#print axioms terminalIntegerFourth_seven
#print axioms terminalIntegerFourth_fromSeven
#print axioms terminalRadial_fromSeven
#print axioms BlockCompatibleP2PostRadialTailFromSeven.toIntegerFourthTail
#print axioms BlockCompatibleP2PostRadialTailFromSeven.toThetaFactorizedTail
#print axioms BlockCompatibleP2PostRadialTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedBlock
