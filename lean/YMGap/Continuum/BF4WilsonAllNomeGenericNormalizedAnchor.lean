/-
# The A03 normalized-anchor consumer for ANY normalized vacuum-complement state

`BF4WilsonAllNomeDyadicNormalizedMacroRatio` (line 132 onward) and
`BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival` consume a macro ratio
`kappa*R(s) <= R(2s)` of the dyadic UNIT excitation only. Their proofs use
exactly four pieces of unit-specific structure:

1. a CONCRETE `CReal` representative `N` of the anchor norm `R(2s)`, with
   explicit Type-level Cauchy data (`QCauchy N.approx`) and its pin;
2. a positive rational floor `q <= N` (only to build the inverse square root);
3. a range witness (`TimeSector.State`) whose value is `T(s) x`, used by the
   bond carrier and the real-time increment rows;
4. scalar facts about `s`: evenness (`s/2+s/2=s`), positivity, and a rational
   spacing with `s*spacing = 1`.

No locality, support, cube carrier, or source sign is used. This module packages
(1)-(3) as `NormalizedAnchorData` and reproves the whole downstream chain for
ANY such data. The original unit theorems follow as corollaries with their
original statements; the original files are untouched.

For the smoothed coherent state `Y_M` all three data are CONSTRUCTED:
(1) a finite double kernel sum of the existing centered time moments with
their existing Cauchy data, pinned to `R_M(2s)` by `smoothedResponse_pin`;
(3) an explicit representative recursion for `orbitSum`, giving a represented
preimage of `T(s-1) Y_M`. Only the floor (2) needs an estimate; along the dyadic
trajectory it follows from H1 (`PathEpsBound`) via the odd Jensen chain.
Hence `PathUnitRatioBridge` is NOT needed to reach the A03 normalized-anchor
target. H2 is not used for the normalized outputs.

Second part: the B04l cube-contraction producer exists only for `w <= 1/2`
(`radialEnvelope_succ_le_half` needs `4096*w^13 <= 1/2`). The changing-nome
requirement is stated as the named OPEN Prop `PathPhysicalContractionBand`:
a strict contraction at every `w_j` whose lattice margin `1-rate_j` is
pinched between two constant multiples of the spacing `2^-j`. Its lower half
is a uniform physical (lattice-transfer) mass gap. Nothing here proves it.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival
import YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory

namespace YMGap.Continuum.BF4WilsonAllNomeGenericNormalizedAnchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.HalfPow (half_nonneg)
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint)
open YMGap.Constructive.DyadicTimeRationals
  (value value_num value_den value_le_iff half_power_num half_power_den)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing unit_side side_positive)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (anchored_small_bound)
open YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower
  (response_shifted_block_step_lower response_shifted_block_geometric_lower)
open YMGap.Continuum.RationalBlockedSurvival (quarter quarter_positive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchorContinuity (half_den_small)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion bondCompletedInner
  bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (ofState bondValue_ofState)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
  (action action_value action_addTime action_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
  (incrementRows incrementRows_pin incrementRows_limit)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (rowPoint limit)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (pairingModulus row_pairing_bound)
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime approximation approximationReal approximationReal_equiv)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (addTime)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarAddCauchy scalarMulCauchy)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment centeredTimeMomentCauchy)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyState)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (orbitSum responseSum)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedSmul completedZero
  addition scalarContinuous)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio (macroGeometricRadius
  macroGeometricRadius_positive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival
  (positiveAction_response_integer_slack)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local notation "half" => YMGap.Constructive.HalfPow.half
local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Scalar helpers (local copies) -/

private theorem ga_scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (ofQ'_mul c q).symm

private theorem ga_scale_rational_one (c : Q') : RCscale c (Rq 1) = Rq c :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv c))

/-- Multiplication by a nonnegative constructive real is monotone on `RC`. -/
private theorem ga_mul_mono {a : CReal} (ha : leEv czero a) {b c : RC} (h : RCle b c) :
    RCle (RCmul (Quotient.mk crealSetoid a) b) (RCmul (Quotient.mk crealSetoid a) c) := by
  revert h
  refine Quotient.inductionOn₂ b c ?_
  intro b c h
  exact leEv_mul_nonneg_left ha h

/-- Real and rational scalings commute on `RC`. -/
private theorem ga_mul_scale (a : CReal) (q : Q') (b : RC) :
    RCmul (Quotient.mk crealSetoid a) (RCscale q b) =
      RCscale q (RCmul (Quotient.mk crealSetoid a) b) := by
  refine Quotient.inductionOn b ?_
  intro b
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun
      | 0 => a.approx n
      | 1 => q
      | _ => b.approx n))

private theorem ga_scaled_mesh_pin (count k : Nat) :
    value ⟨k,count⟩ ≈ Q'.ofNat count*half^k := by
  change (value ⟨k,count⟩).num*((Q'.ofNat count*half^k).den : Int) =
    (Q'.ofNat count*half^k).num*((value ⟨k,count⟩).den : Int)
  rw [value_num, value_den, Q'.mul_den_cast, Q'.mul_num_cast]
  change (count : Int)*(1*((half^k).den : Int)) =
    ((count : Int)*(half^k).num)*(2^k : Nat)
  rw [half_power_num k, half_power_den k, Int.one_mul, Int.mul_one]

private theorem ga_radius_error (kappa : Q') (hkappa : (0 : Q') < kappa)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    half^(epsilon*kappa).den*Q'.recipPos kappa hkappa ≤ epsilon := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ _
    (half_den_small (epsilon*kappa) (Q'.mul_pos he hkappa))
    (Q'.le_of_lt (Q'.recipPos_pos _ hkappa))
  have heq : (epsilon*kappa)*Q'.recipPos kappa hkappa ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv _ hkappa)) (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv heq)

private theorem ga_half_scalar (s : Nat) (heven : s/2+s/2 = s) :
    Q'.ofNat (s/2) ≈ Q'.ofNat s*half := by
  change (Q'.ofNat (s/2)).num*((Q'.ofNat s*half).den : Int) =
    (Q'.ofNat s*half).num*((Q'.ofNat (s/2)).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast]
  change ((s/2 : Nat) : Int)*(1*2) = ((s : Int)*1)*1
  simp only [Int.one_mul, Int.mul_one]
  exact_mod_cast (show (s/2)*2=s by omega)

private theorem ga_radius_double (s : Nat) (heven : s/2+s/2 = s) (kappa epsilon : Q') :
    Q'.ofNat s*macroGeometricRadius kappa epsilon +
        Q'.ofNat s*macroGeometricRadius kappa epsilon ≈
      Q'.ofNat (s/2)*half^(epsilon*kappa).den := by
  have hr : Q'.ofNat s*macroGeometricRadius kappa epsilon +
      Q'.ofNat s*macroGeometricRadius kappa epsilon ≈
      (Q'.ofNat s*half)*half^(epsilon*kappa).den :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 2) (.var 1)))
          (.mul (.var 0) (.mul (.var 2) (.var 1))))
        (.mul (.mul (.var 0) (.add (.var 2) (.var 2))) (.var 1)) (by decide)
        (fun
          | 0 => Q'.ofNat s
          | 1 => half^(epsilon*kappa).den
          | _ => quarter))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : quarter+quarter ≈ half)))
  exact Q'.eqv_trans _ _ _ hr
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ga_half_scalar s heven)))

private theorem ga_lattice_radius_positive (s : Nat) (hs : 0 < s) (kappa epsilon : Q') :
    (0 : Q') < Q'.ofNat s*macroGeometricRadius kappa epsilon := by
  have hq : (0 : Q') < Q'.ofNat s := by
    change (0 : Int)*1 < (s : Int)*1
    simp only [Int.mul_one]
    exact_mod_cast hs
  exact Q'.mul_pos hq (macroGeometricRadius_positive kappa epsilon)

private theorem ga_side_halves (scale : Nat) (hs : 2 ≤ side scale) :
    side scale/2+side scale/2=side scale := by
  cases scale with
  | zero =>
      have hzero : ¬ (2 ≤ side 0) := by decide
      exact False.elim (hzero hs)
  | succ k =>
      simp only [side, Nat.pow_succ] at hs ⊢
      omega

/-! ## 1. Generic normalized-anchor data -/

/-- Everything the A03 normalized-anchor consumer uses about its base state:
a vacuum-complement vector, a block length `s`, a CONCRETE real representative
of `B(x,T(2s)x)` with its own Cauchy data, a positive rational number (used
only to build the inverse square root; it must be a true floor for the
normalization theorems, see `normalizes`), and a range witness for `T(s)x`. -/
structure NormalizedAnchorData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : Type where
  base : VacuumComplement hw0 hw1 (width := width)
  block : Nat
  norm : CReal
  normCauchy : QCauchy norm.approx
  norm_pin : completedInner hw0 hw1 base.val (completedTime hw0 hw1 (2*block) base.val) =
    Quotient.mk crealSetoid norm
  floor : Q'
  floor_pos : (0 : Q') < floor
  sector : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
  sector_pin : sector.val = completedTime hw0 hw1 block base.val

namespace NormalizedAnchorData

variable {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')} {width : Nat}
  (d : NormalizedAnchorData hw0 hw1 width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- The existing constructive inverse square root, applied to `d.norm`. -/
def normalizer : CReal :=
  PositiveCRealNormalizationScalar.scalar d.norm d.normCauchy d.floor d.floor_pos

def normalizerCauchy : QCauchy d.normalizer.approx :=
  PositiveCRealNormalizationScalar.scalarCauchy d.norm d.normCauchy d.floor d.floor_pos

/-- `z = alpha * T(s) x`, with the vacuum-orthogonality proof retained. -/
def normalized : VacuumComplement hw0 hw1 (width := width) :=
  vacuumComplementRealSmul hw0 hw1 d.normalizer d.normalizerCauchy
    (vacuumComplementTime hw0 hw1 d.block d.base)

/-- The same vector with its range witness. -/
def normalizedSector : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 d.normalizer d.normalizerCauchy d.sector

/-- The same vector as a bond-carrier point. -/
def bondExcitation : BondCompletion hw0 hw1 (width := width) :=
  ofState hw0 hw1 d.normalizedSector

/-- The half-anchor preimage `alpha * T(s/2) x`. -/
def halfPreimage : Completion hw0 hw1 width :=
  completedRealSmul hw0 hw1 d.normalizer d.normalizerCauchy (T (d.block/2) d.base.val)

/-- The macro ratio of the base state at block `s`: `kappa R(s) <= R(2s)`. -/
def MacroRatio (kappa : Q') : Prop :=
  RCle (RCscale kappa (B d.base.val (T d.block d.base.val)))
    (B d.base.val (T (2*d.block) d.base.val))

theorem normalizer_nonnegative : leEv czero d.normalizer :=
  PositiveCRealNormalizationScalar.scalar_nonnegative d.norm d.normCauchy d.floor d.floor_pos

theorem normalizes (hfloor : leEv (ofQ' d.floor) d.norm) :
    Equiv (mul d.normalizer (mul d.normalizer d.norm)) cone :=
  PositiveCRealNormalizationScalar.scalar_normalizes d.norm d.normCauchy d.floor d.floor_pos
    hfloor

private theorem rc_normalizes (hfloor : leEv (ofQ' d.floor) d.norm) :
    RCmul (Quotient.mk crealSetoid d.normalizer)
      (RCmul (Quotient.mk crealSetoid d.normalizer) (Quotient.mk crealSetoid d.norm)) = Rq 1 :=
  Quotient.sound (d.normalizes hfloor)

/-- Exact normalized response: `B(z,T(n)z) = alpha^2 B(x,T(2s+n)x)`. -/
theorem response_pin (n : Nat) :
    B d.normalized.val (T n d.normalized.val) =
      RCmul (Quotient.mk crealSetoid d.normalizer)
        (RCmul (Quotient.mk crealSetoid d.normalizer)
          (B d.base.val (T (2*d.block+n) d.base.val))) := by
  change B (completedRealSmul hw0 hw1 d.normalizer d.normalizerCauchy (T d.block d.base.val))
    (T n (completedRealSmul hw0 hw1 d.normalizer d.normalizerCauchy
      (T d.block d.base.val))) = _
  rw [completedTime_realSmul, completedInner_realSmul_left,
    completedInner_realSmul_right, ← completedTime_add, completedInner_time_sum]
  rw [show d.block+(n+d.block) = 2*d.block+n by omega]

/-- Unit norm, given a true floor. -/
theorem normalized_norm (hfloor : leEv (ofQ' d.floor) d.norm) :
    B d.normalized.val d.normalized.val = Rq 1 := by
  have h := d.response_pin 0
  rw [completedTime_zero] at h
  rw [h, Nat.add_zero, d.norm_pin]
  exact rc_normalizes d hfloor

theorem normalizedSector_pin : d.normalizedSector.val = d.normalized.val := by
  change completedRealSmul hw0 hw1 d.normalizer d.normalizerCauchy d.sector.val = _
  rw [d.sector_pin]
  rfl

theorem bond_value : bondValue hw0 hw1 d.bondExcitation = d.normalized.val := by
  rw [bondExcitation, bondValue_ofState, normalizedSector_pin]

theorem bond_norm (hfloor : leEv (ofQ' d.floor) d.norm) :
    bondCompletedInner hw0 hw1 d.bondExcitation d.bondExcitation = Rq 1 := by
  rw [bondValue_inner, bond_value, normalized_norm d hfloor]

theorem halfPreimage_pin (heven : d.block/2+d.block/2 = d.block) :
    T (d.block/2) d.halfPreimage = d.normalized.val := by
  unfold halfPreimage
  rw [completedTime_realSmul, ← completedTime_add, heven]
  rfl

/-- **Generalized line 115.** -/
theorem halfPreimage_norm_cleared (kappa : Q') (heven : d.block/2+d.block/2 = d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa) :
    RCle (RCscale kappa (B d.halfPreimage d.halfPreimage)) (Rq 1) := by
  have ha := d.normalizer_nonnegative
  unfold halfPreimage
  rw [completedInner_realSmul_diagonal, completedInner_time_sum, heven,
    ← ga_mul_scale, ← ga_mul_scale, ← rc_normalizes d hfloor, ← d.norm_pin]
  exact ga_mul_mono ha (ga_mul_mono ha hratio)

/-- **Generalized line 132 (`normalizedAnchorResponse_block_floor`).** For ANY
normalized-anchor data with a macro ratio, every integer block has the
normalized response floor `kappa^j`. -/
theorem block_floor (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa) (j : Nat) :
    RCle (Rq (kappa^j)) (B d.normalized.val (T (j*d.block) d.normalized.val)) := by
  have hfirst : RCle (RCscale kappa (B d.base.val (T d.block d.base.val)))
      (B d.base.val (T (d.block+d.block) d.base.val)) := by
    rw [show d.block+d.block = 2*d.block by omega]
    exact hratio
  have hstep := response_shifted_block_step_lower hw0 hw1 d.base.val kappa
    (Q'.le_of_lt hkappa) d.block d.block hfirst 1
  have hsecond : RCle (RCscale kappa (B d.base.val (T (2*d.block) d.base.val)))
      (B d.base.val (T (2*d.block+d.block) d.base.val)) := by
    simpa only [Nat.one_mul, show d.block+d.block=2*d.block by omega] using hstep
  have hgeom := response_shifted_block_geometric_lower hw0 hw1 d.base.val kappa
    (Q'.le_of_lt hkappa) d.block (2*d.block) hsecond j
  have ha := d.normalizer_nonnegative
  have hscaled := ga_mul_mono ha (ga_mul_mono ha hgeom)
  rw [ga_mul_scale, ga_mul_scale, d.norm_pin, rc_normalizes d hfloor,
    ga_scale_rational_one] at hscaled
  rw [d.response_pin]
  exact hscaled

private theorem halfPreimage_norm_bound (kappa : Q') (hkappa : (0 : Q') < kappa)
    (heven : d.block/2+d.block/2 = d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa) :
    RCle (B d.halfPreimage d.halfPreimage) (Rq (Q'.recipPos kappa hkappa)) := by
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos _ hkappa))
    (d.halfPreimage_norm_cleared kappa heven hfloor hratio)
  have hi : Q'.recipPos kappa hkappa*kappa ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hkappa)
  rwa [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one,
    ga_scale_rational_one] at h

/-- **Generalized `normalizedMesh_increment_bound`.** -/
theorem mesh_increment_bound (kappa : Q') (hkappa : (0 : Q') < kappa)
    (heven : d.block/2+d.block/2 = d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa)
    (p : MeshPoint) (k : Nat) (ht : value p ≤ Q'.ofNat (d.block/2)*half^k) :
    RCle (completedDist hw0 hw1 (meshAction hw0 hw1 p.depth p.steps d.normalized.val)
        d.normalized.val)
      (Rq (half^k*Q'.recipPos kappa hkappa)) := by
  have htime : value p ≤ value ⟨k,d.block/2⟩ :=
    Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv (ga_scaled_mesh_pin _ _))
  have hsteps := (value_le_iff p ⟨k,d.block/2⟩).mp htime
  have hsmall : (p.steps*2^0)*2^k ≤ (d.block/2)*2^p.depth := by
    simpa only [Nat.pow_zero, Nat.mul_one] using hsteps
  have h := anchored_small_bound hw0 hw1 0 (d.block/2) p.depth p.steps k hsmall
    d.halfPreimage
  rw [mesh_original, d.halfPreimage_pin heven] at h
  exact RCle_trans h (by
    have hb := RCscale_mono (Q'.pow_nonneg half half_nonneg k)
      (halfPreimage_norm_bound d kappa hkappa heven hfloor hratio)
    rwa [ga_scale_rational] at hb)

private theorem normalized_real_increment (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs : 0 < d.block) (heven : d.block/2+d.block/2 = d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa)
    (epsilon : Q') (he : (0 : Q') < epsilon) (time : PositiveTime)
    (ht : RCle (realValue (timeValue time))
      (Rq (Q'.ofNat d.block*macroGeometricRadius kappa epsilon))) :
    RCle (completedDist hw0 hw1 (realTimeAction hw0 hw1 (timeValue time) d.normalized.val)
      d.normalized.val) (Rq epsilon) := by
  have hap : leEv (approximationReal time)
      (ofQ' (Q'.ofNat d.block*macroGeometricRadius kappa epsilon)) := by
    have hp : Quotient.mk crealSetoid (approximationReal time) = realValue (timeValue time) :=
      Quotient.sound (approximationReal_equiv time)
    rwa [← hp] at ht
  obtain ⟨N,hN⟩ := hap _ (ga_lattice_radius_positive d.block hs kappa epsilon)
  have hsmall (j : Nat) (hj : N ≤ j) :
      value (approximation time j) ≤ Q'.ofNat (d.block/2)*half^(epsilon*kappa).den :=
    Q'.le_trans' _ _ _ (hN j hj) (Q'.le_of_eqv (ga_radius_double d.block heven kappa epsilon))
  let state := d.normalizedSector
  let rows := incrementRows hw0 hw1 state.range time
  have hlimit : RCle (B (limit hw0 hw1 rows) (limit hw0 hw1 rows)) (Rq epsilon) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro delta hd
    let j := max (pairingModulus hw0 hw1 rows rows delta) N
    have hp := (row_pairing_bound hw0 hw1 rows rows delta hd j (Nat.le_max_left _ _)).2
    have hpoint : RCle (B (rowPoint hw0 hw1 rows j) (rowPoint hw0 hw1 rows j)) (Rq epsilon) := by
      rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_pin]
      rw [show state = d.normalizedSector from rfl, normalizedSector_pin]
      exact RCle_trans (d.mesh_increment_bound kappa hkappa heven hfloor hratio
        (approximation time j) (epsilon*kappa).den
        (hsmall j (Nat.le_max_right _ _)))
        (leEv_of_le (ofQ'_le_ofQ' (ga_radius_error kappa hkappa epsilon he)))
    exact RCle_trans hp (RCadd_le_add hpoint (RCle_refl _))
  rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_limit,
    show state = d.normalizedSector from rfl, normalizedSector_pin] at hlimit
  exact hlimit

/-- **Generalized `normalizedBond_geometric_real_increment`.** `sp` is any
rational spacing with `s*sp = 1`. -/
theorem real_increment (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs : 0 < d.block) (heven : d.block/2+d.block/2 = d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa)
    (sp : Q') (hsp : Q'.ofNat d.block*sp ≈ 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (time : PositiveTimeValue)
    (ht : RCle (RCscale sp (realValue time)) (Rq (macroGeometricRadius kappa epsilon))) :
    RCle (bondCompletedDistance hw0 hw1 (action hw0 hw1 time d.bondExcitation)
      d.bondExcitation) (Rq epsilon) := by
  have ht' := RCscale_mono (Q'.ofNat_nonneg d.block) ht
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hsp, RCscale_one,
    ga_scale_rational] at ht'
  rw [bondValue_distance, action_value, bond_value]
  revert ht'
  refine Quotient.inductionOn time ?_
  intro t ht'
  exact normalized_real_increment d kappa hkappa hs heven hfloor hratio epsilon he t ht'

/-- **Generalized `normalizedBond_geometric_real_forward_increment`.** -/
theorem real_forward_increment (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs : 0 < d.block) (heven : d.block/2+d.block/2 = d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa)
    (sp : Q') (hsp : Q'.ofNat d.block*sp ≈ 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (s t : PositiveTimeValue)
    (ht : RCle (RCscale sp (realValue t)) (Rq (macroGeometricRadius kappa epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 (addTime s t) d.bondExcitation)
      (action hw0 hw1 s d.bondExcitation)) (Rq epsilon) := by
  rw [action_addTime]
  exact RCle_trans (action_distance_bound hw0 hw1 s _ _)
    (d.real_increment kappa hkappa hs heven hfloor hratio sp hsp epsilon he t ht)

/-- **Generalized `normalizedBond_geometric_real_floor`** (the real-time
survival target): response `>= kappa^(j+1)` at every represented positive real
time of geometric size `<= j`. -/
theorem real_floor (kappa : Q') (hkappa : (0 : Q') < kappa) (hs : 0 < d.block)
    (hfloor : leEv (ofQ' d.floor) d.norm) (hratio : d.MacroRatio kappa)
    (sp : Q') (hsp : Q'.ofNat d.block*sp ≈ 1)
    (j : Nat) (time : PositiveTimeValue)
    (ht : RCle (RCscale sp (realValue time)) (Rq (Q'.ofNat j))) :
    RCle (Rq (kappa^(j+1)))
      (bondCompletedInner hw0 hw1 d.bondExcitation (action hw0 hw1 time d.bondExcitation)) := by
  have ht' := RCscale_mono (Q'.ofNat_nonneg d.block) ht
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hsp, RCscale_one,
    ga_scale_rational] at ht'
  have he : Rq (Q'.ofNat d.block*Q'.ofNat j) = Rq (Q'.ofNat (j*d.block)) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv j d.block))))
  rw [he] at ht'
  have hfl := d.block_floor kappa hkappa hfloor hratio (j+1)
  rw [bondValue_inner, action_value, bond_value]
  revert ht'
  refine Quotient.inductionOn time ?_
  intro t ht'
  change RCle (Rq (kappa^(j+1))) (B d.normalized.val
    (realTimeAction hw0 hw1 (timeValue t) d.normalized.val))
  rw [realTimeAction_pin]
  have hreal := positiveAction_response_integer_slack hw0 hw1 d.normalized.val t
    (j*d.block) d.block hs ht'
  rw [show j*d.block+d.block=(j+1)*d.block by
    rw [Nat.add_mul, Nat.one_mul]] at hreal
  exact RCle_trans hfl hreal

end NormalizedAnchorData

/-! ## 2. The original dyadic-unit theorems as corollaries -/

section Unit

open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor (anchoredSector anchoredSector_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity (halfAnchorPreimage)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

/-- The dyadic unit excitation as normalized-anchor data: literally the
original norm, Cauchy data, floor and anchored sector. -/
def unitAnchorData : NormalizedAnchorData hw0 hw1 width where
  base := dyadicUnitExcitation hw0 hw1 scale width hwidth
  block := side scale
  norm := anchorNorm hw0 hw1 scale width hwidth
  normCauchy := anchorNormCauchy hw0 hw1 scale width hwidth
  norm_pin := dyadicUnitResponse_pin hw0 hw1 scale width hwidth (2*side scale)
  floor := anchorNormFloor hw0 hw1 scale
  floor_pos := anchorNormFloor_positive hw0 hw1 scale
  sector := anchoredSector hw0 hw1 scale width hwidth 0
  sector_pin := by rw [anchoredSector_pin, Nat.add_zero]

/-- The original unit `hratio` is the generic macro ratio of `unitAnchorData`. -/
theorem unit_macroRatio (kappa : Q')
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale))) :
    (unitAnchorData hw0 hw1 scale width hwidth).MacroRatio kappa := by
  show RCle (RCscale kappa (completedInner hw0 hw1
      (dyadicUnitExcitation hw0 hw1 scale width hwidth).val
      (completedTime hw0 hw1 (side scale) (dyadicUnitExcitation hw0 hw1 scale width hwidth).val)))
    (completedInner hw0 hw1 (dyadicUnitExcitation hw0 hw1 scale width hwidth).val
      (completedTime hw0 hw1 (2*side scale) (dyadicUnitExcitation hw0 hw1 scale width hwidth).val))
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin]
  exact hratio

/-- Original statement of `halfAnchorPreimage_norm_cleared`, from the generic theorem. -/
theorem unit_halfAnchorPreimage_norm_cleared (kappa : Q') (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale))) :
    RCle (RCscale kappa
      (completedInner hw0 hw1 (halfAnchorPreimage hw0 hw1 scale width hwidth)
        (halfAnchorPreimage hw0 hw1 scale width hwidth))) (Rq 1) :=
  (unitAnchorData hw0 hw1 scale width hwidth).halfPreimage_norm_cleared kappa
    (ga_side_halves scale hs2) (anchorNorm_floor hw0 hw1 scale width hwidth)
    (unit_macroRatio hw0 hw1 scale width hwidth kappa hratio)

/-- Original statement of `normalizedAnchorResponse_block_floor` (line 132),
from the generic `block_floor`. -/
theorem unit_normalizedAnchorResponse_block_floor (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale)))
    (j : Nat) :
    leEv (ofQ' (kappa^j))
      (normalizedAnchorResponse hw0 hw1 scale width hwidth (j*side scale)) := by
  have h : RCle (Rq (kappa^j))
      (completedInner hw0 hw1 (normalizedVacuumExcitation hw0 hw1 scale width hwidth).val
        (completedTime hw0 hw1 (j*side scale)
          (normalizedVacuumExcitation hw0 hw1 scale width hwidth).val)) :=
    (unitAnchorData hw0 hw1 scale width hwidth).block_floor kappa hkappa
      (anchorNorm_floor hw0 hw1 scale width hwidth)
      (unit_macroRatio hw0 hw1 scale width hwidth kappa hratio) j
  rw [normalizedAnchorResponse_pin] at h
  exact h

/-- Original statement of `normalizedMesh_increment_bound`. -/
theorem unit_normalizedMesh_increment_bound (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale)))
    (p : MeshPoint) (k : Nat) (ht : value p ≤ Q'.ofNat (side scale/2)*half^k) :
    RCle (completedDist hw0 hw1 (meshAction hw0 hw1 p.depth p.steps
        (normalizedVacuumExcitation hw0 hw1 scale width hwidth).val)
        (normalizedVacuumExcitation hw0 hw1 scale width hwidth).val)
      (Rq (half^k*Q'.recipPos kappa hkappa)) :=
  (unitAnchorData hw0 hw1 scale width hwidth).mesh_increment_bound kappa hkappa
    (ga_side_halves scale hs2) (anchorNorm_floor hw0 hw1 scale width hwidth)
    (unit_macroRatio hw0 hw1 scale width hwidth kappa hratio) p k ht

private theorem unit_hsp : Q'.ofNat (side scale)*spacing scale ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side scale)

/-- Original statement of `normalizedBond_geometric_real_increment`. -/
theorem unit_normalizedBond_geometric_real_increment (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time))
      (Rq (macroGeometricRadius kappa epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 time (normalizedBondExcitation hw0 hw1 scale width hwidth))
      (normalizedBondExcitation hw0 hw1 scale width hwidth)) (Rq epsilon) :=
  (unitAnchorData hw0 hw1 scale width hwidth).real_increment kappa hkappa
    (side_positive scale) (ga_side_halves scale hs2)
    (anchorNorm_floor hw0 hw1 scale width hwidth)
    (unit_macroRatio hw0 hw1 scale width hwidth kappa hratio)
    (spacing scale) (unit_hsp scale) epsilon he time ht

/-- Original statement of `normalizedBond_geometric_real_forward_increment`. -/
theorem unit_normalizedBond_geometric_real_forward_increment
    (kappa : Q') (hkappa : (0 : Q') < kappa) (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (s t : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue t))
      (Rq (macroGeometricRadius kappa epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 (addTime s t) (normalizedBondExcitation hw0 hw1 scale width hwidth))
      (action hw0 hw1 s (normalizedBondExcitation hw0 hw1 scale width hwidth)))
      (Rq epsilon) :=
  (unitAnchorData hw0 hw1 scale width hwidth).real_forward_increment kappa hkappa
    (side_positive scale) (ga_side_halves scale hs2)
    (anchorNorm_floor hw0 hw1 scale width hwidth)
    (unit_macroRatio hw0 hw1 scale width hwidth kappa hratio)
    (spacing scale) (unit_hsp scale) epsilon he s t ht

/-- Original statement of `normalizedBond_geometric_real_floor`. -/
theorem unit_normalizedBond_geometric_real_floor (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hratio : leEv (mul (ofQ' kappa)
        (dyadicUnitResponse hw0 hw1 scale width hwidth (side scale)))
      (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale)))
    (j : Nat) (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time)) (Rq (Q'.ofNat j))) :
    RCle (Rq (kappa^(j+1)))
      (bondCompletedInner hw0 hw1
        (normalizedBondExcitation hw0 hw1 scale width hwidth)
        (action hw0 hw1 time (normalizedBondExcitation hw0 hw1 scale width hwidth))) :=
  (unitAnchorData hw0 hw1 scale width hwidth).real_floor kappa hkappa
    (side_positive scale) (anchorNorm_floor hw0 hw1 scale width hwidth)
    (unit_macroRatio hw0 hw1 scale width hwidth kappa hratio)
    (spacing scale) (unit_hsp scale) j time ht

end Unit

/-! ## 3. Constructed anchor data for the smoothed coherent state -/

/-- Finite rational-kernel sum of constructive reals. -/
def kernelCSum : List (Q' × Nat) → (Nat → CReal) → CReal
  | [], _ => ofQ' 0
  | (c,n)::cs, f => CReal.add (CReal.mul (ofQ' c) (f n)) (kernelCSum cs f)

private def ga_rationalCauchy (q : Q') : QCauchy (ofQ' q).approx where
  M _ := 0
  bound := fun _ he _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he), Q'.add_le_self_of_nonneg q _ (Q'.le_of_lt he)⟩

/-- Its explicit Cauchy data, from the summands' data. -/
def kernelCSumCauchy : (K : List (Q' × Nat)) → (f : Nat → CReal) →
    (∀ n, QCauchy (f n).approx) → QCauchy (kernelCSum K f).approx
  | [], _, _ => ga_rationalCauchy 0
  | (c,n)::cs, f, cf => scalarAddCauchy _ _
      (scalarMulCauchy _ _ (ga_rationalCauchy c) (cf n)) (kernelCSumCauchy cs f cf)

theorem responseSum_mk : (K : List (Q' × Nat)) → (f : Nat → CReal) →
    responseSum K (fun n => Quotient.mk crealSetoid (f n)) =
      Quotient.mk crealSetoid (kernelCSum K f)
  | [], _ => rfl
  | (c,n)::cs, f => by
      show RCadd (RCscale c (Quotient.mk crealSetoid (f n)))
        (responseSum cs (fun n => Quotient.mk crealSetoid (f n))) = _
      rw [responseSum_mk cs f]
      rfl

section Smoothed

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
  (hqs : ∀ p, p ∈ qs → p ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid (seminorm hw0 hw1 (width := width)))

/-- Representative-level orbit sum: the same operations on Cauchy streams. -/
def repOrbit (X : (D).Cauchy) : List (Q' × Nat) → (D).Cauchy
  | [] => (D).constant (BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.zero width)
  | (c,n)::cs => (addition hw0 hw1 (width := width)).mapCauchy
      ((scalarContinuous hw0 hw1 (width := width) c).mapCauchy
        ((timeNonexpansive hw0 hw1 (width := width) n).mapCauchy X))
      (repOrbit X cs)

theorem repOrbit_class (X : (D).Cauchy) :
    (K : List (Q' × Nat)) → Class (repOrbit hw0 hw1 width X K) = orbitSum hw0 hw1 (Class X) K
  | [] => rfl
  | (c,n)::cs => by
      show _ = completedAdd hw0 hw1 (completedSmul hw0 hw1 c (T n (Class X)))
        (orbitSum hw0 hw1 (Class X) cs)
      rw [← repOrbit_class X cs]
      rfl

/-- Explicit representative of the literal family vector. -/
def familyStream : (D).Cauchy :=
  BF4WilsonAllNomeCenteredVector.centeredStream hw0 hw1 (familyState width qs c hqs)

theorem familyStream_class :
    Class (familyStream hw0 hw1 width qs c hqs) =
      (familyExcitation hw0 hw1 width qs c hqs).val := rfl

/-- Range witness for `T(s) Y_M` (`s >= 1`): `fromTime` of the represented
preimage `T(s-1)` of the representative orbit. -/
def smoothedSector (M s : Nat) : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.fromTime hw0 hw1
    ((timeNonexpansive hw0 hw1 (width := width) (s-1)).mapCauchy
      (repOrbit hw0 hw1 width (familyStream hw0 hw1 width qs c hqs) (timeKernel M)))

theorem smoothedSector_pin (M s : Nat) (hs : 0 < s) :
    (smoothedSector hw0 hw1 width qs c hqs M s).val =
      T s (smoothedCoherentVector hw0 hw1 width qs c hqs M) := by
  change T 1 (T (s-1) (Class (repOrbit hw0 hw1 width (familyStream hw0 hw1 width qs c hqs)
    (timeKernel M)))) = _
  rw [repOrbit_class, ← completedTime_add, show 1+(s-1) = s by omega]
  rfl

/-- Concrete real representative of `R_M(n)` with explicit Cauchy data. -/
def smoothedNorm (M n : Nat) : CReal :=
  kernelCSum (timeKernel M) (fun m => kernelCSum (timeKernel M)
    (fun k => centeredTimeMoment hw0 hw1 (m+k+n)
      (familyState width qs c hqs) (familyState width qs c hqs)))

def smoothedNormCauchy (M n : Nat) :
    QCauchy (smoothedNorm hw0 hw1 width qs c hqs M n).approx :=
  kernelCSumCauchy (timeKernel M) _ (fun m => kernelCSumCauchy (timeKernel M) _
    (fun k => centeredTimeMomentCauchy hw0 hw1 (m+k+n)
      (familyState width qs c hqs) (familyState width qs c hqs)))

theorem smoothedNorm_pin (M n : Nat) :
    smoothedResponse hw0 hw1 width qs c hqs M n =
      Quotient.mk crealSetoid (smoothedNorm hw0 hw1 width qs c hqs M n) := by
  rw [smoothedResponse_pin]
  unfold smoothedNorm
  rw [← responseSum_mk]
  apply congrArg (responseSum (timeKernel M))
  funext m
  exact responseSum_mk (timeKernel M) _

/-- Normalized-anchor data of `Y_M` at block `s`, with a supplied positive
rational `fl` (a true floor is needed only by the normalization theorems). -/
def smoothedAnchorData (M s : Nat) (hs : 0 < s) (fl : Q') (hfl : (0 : Q') < fl) :
    NormalizedAnchorData hw0 hw1 width where
  base := smoothedCoherentState hw0 hw1 width qs c hqs M
  block := s
  norm := smoothedNorm hw0 hw1 width qs c hqs M (2*s)
  normCauchy := smoothedNormCauchy hw0 hw1 width qs c hqs M (2*s)
  norm_pin := smoothedNorm_pin hw0 hw1 width qs c hqs M (2*s)
  floor := fl
  floor_pos := hfl
  sector := smoothedSector hw0 hw1 width qs c hqs M s
  sector_pin := smoothedSector_pin hw0 hw1 width qs c hqs M s hs

/-- The generic macro ratio of this data IS `SmoothedMacroRatio` at `s = side scale`. -/
theorem smoothedAnchor_macroRatio (M scale : Nat) (fl : Q') (hfl : (0 : Q') < fl)
    (kappa : Q') (h : SmoothedMacroRatio hw0 hw1 width qs c hqs M scale kappa) :
    (smoothedAnchorData hw0 hw1 width qs c hqs M (side scale) (side_positive scale)
      fl hfl).MacroRatio kappa := h

end Smoothed

/-! ## 4. Along the dyadic trajectory: no unit bridge -/

theorem pathKappa_pos (delta : Q') (hdelta : delta < (1 : Q')) (a : Nat) :
    (0 : Q') < ((1 : Q') - delta)^(side a) :=
  HKPos.pow_pos (HKPos.one_sub_pos hdelta) _

/-- Normalized-anchor data of `Y_j` at block `side j`, floor `kappa^2 * floor_j`. -/
def trajAnchorData (tr : DyadicSmoothedTrajectory) (j : Nat) (kappa : Q')
    (hkappa : (0 : Q') < kappa) :
    NormalizedAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j) :=
  smoothedAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) (side j) (side_positive j)
    (kappa^2 * smoothedNormFloor (tr.schedule.nome_pos j) (tr.faces j) (tr.coeff j) (tr.radius j))
    (Q'.mul_pos (HKPos.pow_pos hkappa 2)
      (smoothedNormFloor_positive (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
        (tr.faces j) (tr.coeff j) (tr.coeff_mass_pos j) (tr.radius j)))

/-- The path instance: `kappa = (1-delta)^(2^a)`. -/
def pathAnchor (tr : DyadicSmoothedTrajectory) (delta : Q') (hdelta : delta < (1 : Q'))
    (a j : Nat) :
    NormalizedAnchorData (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j) :=
  trajAnchorData tr j (((1 : Q') - delta)^(side a)) (pathKappa_pos delta hdelta a)

/-- H1 makes the anchor floor of `pathAnchor` a TRUE floor (odd Jensen chain at
two blocks times the unconditional smoothed norm floor). -/
theorem path_anchor_floor (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (H1 : PathEpsBound tr c0)
    (j : Nat) (haj : a ≤ j) :
    leEv (ofQ' (pathAnchor tr delta hdelta a j).floor)
      (pathAnchor tr delta hdelta a j).norm := by
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hs := side_split a j haj
  have hL : 0 < side (j-a) := side_positive (j-a)
  have hE := blockEnergy_of_pathEps tr c0 delta a j haj hc0 H1
  have hnorm := smoothedCoherent_norm_floor hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.faces_nodup j) (tr.radius j)
  have hchain := block_survival_of_oneStep_energy hw0 hw1 (trajWidth j) (tr.state j)
    (side j) (side (j-a)) (side a) hs hL delta _ hdelta0 hdelta
    (smoothedNormFloor_positive hw0 hw1 (tr.faces j) (tr.coeff j) (tr.coeff_mass_pos j)
      (tr.radius j)) hnorm hE 2
  have hk2 : (0 : Q') ≤ (((1 : Q') - delta)^(side a))^2 :=
    CRealLog.pow_nonneg _ (Q'.le_of_lt (pathKappa_pos delta hdelta a)) 2
  have hscaled := RCscale_mono hk2 hnorm
  rw [ga_scale_rational] at hscaled
  have h := RCle_trans hscaled hchain
  rw [show side j * 2 = 2 * side j by omega] at h
  have hpin := smoothedNorm_pin hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
    (tr.faces_spatial j) (tr.radius j) (2 * side j)
  unfold smoothedResponse at hpin
  change RCle _ (completedInner hw0 hw1
    (smoothedCoherentVector hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.radius j))
    (completedTime hw0 hw1 (2 * side j) (smoothedCoherentVector hw0 hw1 (trajWidth j)
      (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j)))) at h
  rw [hpin] at h
  exact h

private theorem ga_traj_halves (j : Nat) (hj : 1 ≤ j) : side j/2+side j/2 = side j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

private theorem ga_traj_hsp (j : Nat) : Q'.ofNat (side j)*spacing j ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side j)

/-- **Bridge-free A03 path theorem.** From H1 alone, at every scale `j >= a`
the SAME smoothed state `Y_j`, normalized by its own constructed inverse
square root (`pathAnchor`), has: unit norm; block floors `kappa^i` at lag
`i*side j`; real-time survival `kappa^(i+1)` at every represented time of
geometric size `<= i`; and (for `j >= 1`) the geometric real-time increment
modulus. Here `kappa = (1-delta)^(2^a)`. No `PathUnitRatioBridge`. -/
theorem path_normalized_anchor (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (H1 : PathEpsBound tr c0) :
    ∀ j : Nat, a ≤ j →
      completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (pathAnchor tr delta hdelta a j).normalized.val
          (pathAnchor tr delta hdelta a j).normalized.val = Rq 1 ∧
      (∀ i : Nat, RCle (Rq ((((1 : Q') - delta)^(side a))^i))
        (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (pathAnchor tr delta hdelta a j).normalized.val
          (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (i * side j)
            (pathAnchor tr delta hdelta a j).normalized.val))) ∧
      (∀ (i : Nat) (time : PositiveTimeValue),
        RCle (RCscale (spacing j) (realValue time)) (Rq (Q'.ofNat i)) →
        RCle (Rq ((((1 : Q') - delta)^(side a))^(i+1)))
          (bondCompletedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
            (pathAnchor tr delta hdelta a j).bondExcitation
            (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
              (pathAnchor tr delta hdelta a j).bondExcitation))) ∧
      (1 ≤ j → ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ time : PositiveTimeValue,
        RCle (RCscale (spacing j) (realValue time))
          (Rq (macroGeometricRadius (((1 : Q') - delta)^(side a)) epsilon)) →
        RCle (bondCompletedDistance (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (action (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) time
            (pathAnchor tr delta hdelta a j).bondExcitation)
          (pathAnchor tr delta hdelta a j).bondExcitation) (Rq epsilon)) := by
  intro j haj
  have hkappa := pathKappa_pos delta hdelta a
  have hfloor := path_anchor_floor tr c0 delta a hdelta0 hdelta hc0 H1 j haj
  have hratio : (pathAnchor tr delta hdelta a j).MacroRatio (((1 : Q') - delta)^(side a)) :=
    path_macroRatio tr c0 delta a hdelta0 hdelta hc0 H1 j haj
  refine ⟨NormalizedAnchorData.normalized_norm (pathAnchor tr delta hdelta a j) hfloor,
    fun i => NormalizedAnchorData.block_floor (pathAnchor tr delta hdelta a j) _ hkappa
      hfloor hratio i,
    fun i time ht => NormalizedAnchorData.real_floor (pathAnchor tr delta hdelta a j) _ hkappa
      (side_positive j) hfloor hratio (spacing j) (ga_traj_hsp j) i time ht,
    fun hj epsilon he time ht => NormalizedAnchorData.real_increment
      (pathAnchor tr delta hdelta a j) _ hkappa (side_positive j) (ga_traj_halves j hj)
      hfloor hratio (spacing j) (ga_traj_hsp j) epsilon he time ht⟩

/-- H1 + H2 version: the bridge-free normalized block floors together with
the P6 un-normalized physical-time floor (the only place H2 enters). -/
theorem path_normalized_anchor_with_survival (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta)
    (H1 : PathEpsBound tr c0) (H2 : PathFamilyRadiusSurvival tr theta) :
    ∀ j : Nat, a ≤ j →
      (∀ i : Nat, RCle (Rq ((((1 : Q') - delta)^(side a))^i))
        (completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
          (pathAnchor tr delta hdelta a j).normalized.val
          (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (i * side j)
            (pathAnchor tr delta hdelta a j).normalized.val))) ∧
      ∀ i : Nat, RCle (RCscale ((((1 : Q') - delta)^(side a))^i * theta) (tr.familyNorm j))
        (tr.response j (side j * i)) := by
  intro j haj
  exact ⟨(path_normalized_anchor tr c0 delta a hdelta0 hdelta hc0 H1 j haj).2.1,
    (path_macro_conclusion tr c0 theta delta a hdelta0 hdelta hc0 H1 H2 j haj).2⟩

/-! ## 5. What a changing-nome (w -> 1) cube contraction would require -/

open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
  (CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData)
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
  (DynamicVacuumSectorPhysicalRateBand)

/-- OPEN (characterization only, not attempted): at EVERY scale nome `w_j`
there is a strict completed vacuum-sector contraction (B04l data) whose
lattice margin `1 - rate_j` lies between `m * 2^-j` and `M * 2^-j` for fixed
`0 < m, M`. The lower half is a scale-uniform PHYSICAL gap of the cube
transfer operator (`(1-rate_j)/a_j >= m`, i.e. a lattice mass gap in
lattice units `>= m a_j`); the upper half forces the lattice gap to close
like the spacing. The existing producer covers only `w <= 1/2`. -/
def PathPhysicalContractionBand (ns : NomeSchedule) : Prop :=
  ∃ m M : Q', (0 : Q') < m ∧ (0 : Q') < M ∧
    Nonempty (∀ j, {gap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
        (ns.nome_pos j) (ns.nome_lt_one j) 0 //
      m * spacing j ≤ (1 : Q') - gap.rate ∧ (1 : Q') - gap.rate ≤ M * spacing j})

/-- The band supplies P6's bare per-scale contraction input. -/
theorem pathCubeContraction_of_band (ns : NomeSchedule)
    (h : PathPhysicalContractionBand ns) : PathCubeContraction ns := by
  obtain ⟨_, _, _, _, ⟨g⟩⟩ := h
  exact ⟨fun j => (g j).val⟩

/-- The band is EXACTLY the B04l two-sided physical rate band on the
trajectory's dynamic family (same transfer, same dyadic spacing). -/
theorem rateBand_of_pathPhysicalContractionBand (ns : NomeSchedule)
    (h : PathPhysicalContractionBand ns) :
    ∃ gap : (∀ j, CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
        (ns.nome_pos j) (ns.nome_lt_one j) 0),
      Nonempty (DynamicVacuumSectorPhysicalRateBand (trajectoryDynamicFamily ns gap)) := by
  obtain ⟨m, M, hm, hM, ⟨g⟩⟩ := h
  exact ⟨fun j => (g j).val, ⟨{
    floor := m
    floor_pos := hm
    ceiling := M
    ceiling_pos := hM
    lowerRate := fun j => (g j).property.1
    upperRate := fun j => (g j).property.2 }⟩⟩

/-- Conversely, any B04l rate band on the trajectory family gives the Prop. -/
theorem pathPhysicalContractionBand_of_rateBand (ns : NomeSchedule)
    (gap : ∀ j, CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
        (ns.nome_pos j) (ns.nome_lt_one j) 0)
    (band : DynamicVacuumSectorPhysicalRateBand (trajectoryDynamicFamily ns gap)) :
    PathPhysicalContractionBand ns :=
  ⟨band.floor, band.ceiling, band.floor_pos, band.ceiling_pos,
    ⟨fun j => ⟨gap j, band.lowerRate j, band.upperRate j⟩⟩⟩

#print axioms NormalizedAnchorData
#print axioms NormalizedAnchorData.normalizer
#print axioms NormalizedAnchorData.normalized
#print axioms NormalizedAnchorData.MacroRatio
#print axioms NormalizedAnchorData.response_pin
#print axioms NormalizedAnchorData.normalized_norm
#print axioms NormalizedAnchorData.bond_norm
#print axioms NormalizedAnchorData.halfPreimage_norm_cleared
#print axioms NormalizedAnchorData.block_floor
#print axioms NormalizedAnchorData.mesh_increment_bound
#print axioms NormalizedAnchorData.real_increment
#print axioms NormalizedAnchorData.real_forward_increment
#print axioms NormalizedAnchorData.real_floor
#print axioms unitAnchorData
#print axioms unit_macroRatio
#print axioms unit_halfAnchorPreimage_norm_cleared
#print axioms unit_normalizedAnchorResponse_block_floor
#print axioms unit_normalizedMesh_increment_bound
#print axioms unit_normalizedBond_geometric_real_increment
#print axioms unit_normalizedBond_geometric_real_forward_increment
#print axioms unit_normalizedBond_geometric_real_floor
#print axioms kernelCSum
#print axioms kernelCSumCauchy
#print axioms responseSum_mk
#print axioms repOrbit
#print axioms repOrbit_class
#print axioms smoothedSector
#print axioms smoothedSector_pin
#print axioms smoothedNorm
#print axioms smoothedNorm_pin
#print axioms smoothedAnchorData
#print axioms smoothedAnchor_macroRatio
#print axioms pathKappa_pos
#print axioms trajAnchorData
#print axioms pathAnchor
#print axioms path_anchor_floor
#print axioms path_normalized_anchor
#print axioms path_normalized_anchor_with_survival
#print axioms PathPhysicalContractionBand
#print axioms pathCubeContraction_of_band
#print axioms rateBand_of_pathPhysicalContractionBand
#print axioms pathPhysicalContractionBand_of_rateBand

end YMGap.Continuum.BF4WilsonAllNomeGenericNormalizedAnchor
