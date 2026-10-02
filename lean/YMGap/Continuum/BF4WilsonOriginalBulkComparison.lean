/-
# Quantitative original bulk moments between independent spatial widths

The existing small-nome original-action comparison is passed through the
CURRENT fixed-width heat/time joint limits, not through a legacy spatial
completion. Three moments retain their OWN endpoint means and produce an
explicit connected-error budget and spatial modulus. The larger width,
heat cutoff and exterior time depth do not enter the budget; the nome,
source support and physical lattice-time window do. The same budget now
controls the actual completed physical correlations against the existing
reflected spatial limit, with its extra one-step bond clock intact.

No full completed-width map is asserted. The near-identity changing-family
estimate, physical spacing calibration and continuum Yang--Mills remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence
import YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
import YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay
import YMGap.Constructive.CRealAbsContinuity
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm

namespace YMGap.Continuum.BF4WilsonOriginalBulkComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit (rate_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
  (spatialLimit jointLimits_spatial_converge)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality (boxSize)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (carrierSize)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds chartIds_physical)
open YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds (finiteValue_abs_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (windowCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression chart unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (intrinsicForm intrinsicForm_chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
  (intrinsicForm_advanced_unit_right intrinsicForm_advanced_unit_left intrinsicForm_time_balance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (originalJoint_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (spatialLimit_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd crossOdd_within)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (bondForm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay (connected connected_source_pin)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.QuaternionHaarBiadditive (abs_product_bound)
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio heatRemainderBound)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

attribute [local irreducible] chartScalar originalWindowScalar originalJointLimit

/-- The already constructed ORIGINAL expectation at this actual padded width. -/
def expectation {base : Nat} (H : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) (r : Nat) : CReal :=
  originalJointLimit hw0 hw1 (2*H) (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)

theorem expectation_diagonal_converges {base : Nat} (H : Nat)
    (e : WindowExpression base) (he : Within (2*H) e) (r : Nat) :
    ConvergesTo (fun n => ofQ' (chartScalar hw0 hw1 H e r n n))
      (expectation hw0 hw1 H e he r) := by
  have hlim := originalJoint_diagonal_converges hw0 hw1 (2*H) (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  refine TrigAddCReal.convergesTo_congr_seq
    (s := fun n => ofQ' (originalWindowScalar hw0 hw1 (2*H) (centeredExpression r e) n n n))
    ?_ hlim
  intro n
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  change (originalWindowScalar hw0 hw1 (2*H) (centeredExpression r e) n n n).eqv
    (chartScalar hw0 hw1 H e r n n)
  exact Q'.eqv_symm (chartScalar_original_pin hw0 hw1 H e he r n n)

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

attribute [local irreducible] expectation

include hsmall in
/-- SAME literal source coordinates in two ORIGINAL widths, after heat and
time removal. This is a scalar comparison, not descent of either null relation. -/
theorem expectation_inclusion_bound {base larger : Nat} (h : base ≤ larger)
    (hb : 0 < base) (H : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) (r : Nat) :
    leEv (abs (sub
      (expectation hw0 hw1 H (includeExpression h e)
        ((includeExpression_within h (2*H) e).mpr he) r)
      (expectation hw0 hw1 H e he r)))
      (ofQ' (spatialAmplitude w hd hs H e *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))))) :=
  leEv_of_convergesTo_le
    (convergesTo_abs (TrigAddCReal.convergesTo_add
      (expectation_diagonal_converges hw0 hw1 H (includeExpression h e)
        ((includeExpression_within h (2*H) e).mpr he) r)
      (TrigAddCReal.convergesTo_neg
        (expectation_diagonal_converges hw0 hw1 H e he r))))
    (convergesTo_const _)
    (fun n => leEv_le_ofQ'_of_approx_le
      (fun _ => chartScalar_inclusion_bound hw0 hw1 hsmall hd hs h r H n n hb e he))

/-- A three-moment subtraction with two OWN means. It is a covariance only
when its sources are identified, as in the physical bond consumer below. -/
def connectedMoment {base : Nat} (H : Nat) (joint left right : WindowExpression base)
    (hj : Within (2*H) joint) (hl : Within (2*H) left) (hr : Within (2*H) right)
    (r : Nat) : CReal :=
  sub (expectation hw0 hw1 H joint hj r)
    (mul (expectation hw0 hw1 H left hl r) (expectation hw0 hw1 H right hr r))

private theorem covariance_heterogeneous_bound (a b ab a' b' ab' ca cb e0 e1 e2 : Q')
    (ha : Q'.abs a ≤ ca) (hb' : Q'.abs b' ≤ cb)
    (h0 : Q'.abs (ab + -ab') ≤ e0)
    (h1 : Q'.abs (a + -a') ≤ e1) (h2 : Q'.abs (b + -b') ≤ e2) :
    Q'.abs ((ab + -(a*b)) + -(ab' + -(a'*b'))) ≤ e0 + (ca*e2+cb*e1) := by
  have hprod : Q'.abs (a*b + -(a'*b')) ≤ ca*e2+cb*e1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (mul_sub_decomp a b a' b')))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.add_le_add (abs_product_bound ha h2) (abs_product_bound hb' h1)))
  have hsplit : ((ab + -(a*b)) + -(ab' + -(a'*b'))).eqv
      ((ab + -ab') + -(a*b + -(a'*b'))) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
        (.neg (.add (.var 3) (.neg (.mul (.var 4) (.var 5))))))
      (.add (.add (.var 0) (.neg (.var 3)))
        (.neg (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 4) (.var 5))))))
      (by decide) (fun | 0 => ab | 1 => a | 2 => b | 3 => ab' | 4 => a' | _ => b')
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add h0 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) hprod)))

/-- Computed observable-dependent budget, including BOTH mean corrections. -/
def connectedAmplitude {base : Nat} (H : Nat) (joint left right : WindowExpression base) : Q' :=
  spatialAmplitude w hd hs H joint +
    (windowCap left * spatialAmplitude w hd hs H right +
      windowCap right * spatialAmplitude w hd hs H left)

private theorem chart_abs_bound {base : Nat} (H : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) (r stage t : Nat) :
    Q'.abs (chartScalar hw0 hw1 H e r stage t) ≤ windowCap e := by
  unfold chartScalar
  exact finiteValue_abs_bound w hw0 hw1 _ _ (fun _ hi => chartIds_physical hi)
    _ _ (chart_interval r H t e he) stage

include hsmall in
theorem finite_connected_inclusion_bound {base larger : Nat} (h : base ≤ larger)
    (hb : 0 < base) (H : Nat) (joint left right : WindowExpression base)
    (hj : Within (2*H) joint) (hl : Within (2*H) left) (hr : Within (2*H) right)
    (r stage t : Nat) :
    Q'.abs ((chartScalar hw0 hw1 H (includeExpression h joint) r stage t +
      -(chartScalar hw0 hw1 H (includeExpression h left) r stage t *
        chartScalar hw0 hw1 H (includeExpression h right) r stage t)) +
      -(chartScalar hw0 hw1 H joint r stage t +
        -(chartScalar hw0 hw1 H left r stage t * chartScalar hw0 hw1 H right r stage t))) ≤
      connectedAmplitude hd hs H joint left right *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))) := by
  have ha := chart_abs_bound hw0 hw1 H (includeExpression h left)
    ((includeExpression_within h (2*H) left).mpr hl) r stage t
  rw [includeExpression_cap] at ha
  have hb' := chart_abs_bound hw0 hw1 H right hr r stage t
  have h0 := chartScalar_inclusion_bound hw0 hw1 hsmall hd hs h r H t stage hb joint hj
  have h1 := chartScalar_inclusion_bound hw0 hw1 hsmall hd hs h r H t stage hb left hl
  have h2 := chartScalar_inclusion_bound hw0 hw1 hsmall hd hs h r H t stage hb right hr
  have hc := covariance_heterogeneous_bound _ _ _ _ _ _ _ _ _ _ _ ha hb' h0 h1 h2
  refine Q'.le_trans' _ _ _ hc (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 5))
      (.add (.mul (.var 1) (.mul (.var 2) (.var 5)))
        (.mul (.var 3) (.mul (.var 4) (.var 5)))))
    (.mul (.add (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))) (.var 5))
    (by decide) (fun i => match i with
      | 0 => spatialAmplitude w hd hs H joint
      | 1 => windowCap left
      | 2 => spatialAmplitude w hd hs H right
      | 3 => windowCap right
      | 4 => spatialAmplitude w hd hs H left
      | _ => (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))))

private theorem connected_diagonal_converges {base : Nat} (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) (r : Nat) :
    ConvergesTo (fun n => ofQ' (chartScalar hw0 hw1 H joint r n n +
      -(chartScalar hw0 hw1 H left r n n * chartScalar hw0 hw1 H right r n n)))
      (connectedMoment hw0 hw1 H joint left right hj hl hr r) := by
  unfold connectedMoment
  have hp := convergesTo_mul_general
    (expectation_diagonal_converges hw0 hw1 H left hl r)
    (expectation_diagonal_converges hw0 hw1 H right hr r)
  have hc := TrigAddCReal.convergesTo_add
    (expectation_diagonal_converges hw0 hw1 H joint hj r)
    (TrigAddCReal.convergesTo_neg hp)
  refine TrigAddCReal.convergesTo_congr_seq ?_ hc
  intro n
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

attribute [local irreducible] connectedMoment

include hsmall in
/-- Actual connected moments between independent CURRENT original widths.
Only the already proved small-nome action bound supplies the errors. -/
theorem connected_inclusion_bound {base larger : Nat} (h : base ≤ larger)
    (hb : 0 < base) (H : Nat) (joint left right : WindowExpression base)
    (hj : Within (2*H) joint) (hl : Within (2*H) left) (hr : Within (2*H) right) (r : Nat) :
    leEv (abs (sub
      (connectedMoment hw0 hw1 H (includeExpression h joint) (includeExpression h left)
        (includeExpression h right) ((includeExpression_within h (2*H) joint).mpr hj)
        ((includeExpression_within h (2*H) left).mpr hl)
        ((includeExpression_within h (2*H) right).mpr hr) r)
      (connectedMoment hw0 hw1 H joint left right hj hl hr r)))
      (ofQ' (connectedAmplitude hd hs H joint left right *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))))) :=
  leEv_of_convergesTo_le
    (convergesTo_abs (TrigAddCReal.convergesTo_add
      (connected_diagonal_converges hw0 hw1 H (includeExpression h joint)
        (includeExpression h left) (includeExpression h right)
        ((includeExpression_within h (2*H) joint).mpr hj)
        ((includeExpression_within h (2*H) left).mpr hl)
        ((includeExpression_within h (2*H) right).mpr hr) r)
      (TrigAddCReal.convergesTo_neg
        (connected_diagonal_converges hw0 hw1 H joint left right hj hl hr r))))
    (convergesTo_const _)
    (fun n => leEv_le_ofQ'_of_approx_le
      (fun _ => finite_connected_inclusion_bound hw0 hw1 hsmall hd hs h hb H
        joint left right hj hl hr r n n))

theorem connectedAmplitude_nonnegative {base : Nat} (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) :
    (0 : Q') ≤ connectedAmplitude hd hs H joint left right :=
  Q'.zero_le_add _ _ (spatialAmplitude_nonnegative w hd hs H joint hj)
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (chart_interval 0 H 0 left hl).nonnegative
        (spatialAmplitude_nonnegative w hd hs H right hr))
      (Q'.mul_nonneg _ _ (chart_interval 0 H 0 right hr).nonnegative
        (spatialAmplitude_nonnegative w hd hs H left hl)))

/-- A spatial tolerance modulus independent of the larger width. -/
def comparisonModulus {base : Nat} (H : Nat) (joint left right : WindowExpression base)
    (epsilon : Q') : Nat :=
  carrierSize (boxSize base (2*H)) + geometricCutoff
    (entropyRate 625 (adjustedCoreRate w hd)) (connectedAmplitude hd hs H joint left right) epsilon

include hsmall in
theorem connected_inclusion_close {base larger : Nat} (h : base ≤ larger)
    (hb : 0 < base) (H : Nat) (joint left right : WindowExpression base)
    (hj : Within (2*H) joint) (hl : Within (2*H) left) (hr : Within (2*H) right)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (r : Nat)
    (hradius : comparisonModulus hd hs H joint left right epsilon ≤ r) :
    leEv (abs (sub
      (connectedMoment hw0 hw1 H (includeExpression h joint) (includeExpression h left)
        (includeExpression h right) ((includeExpression_within h (2*H) joint).mpr hj)
        ((includeExpression_within h (2*H) left).mpr hl)
        ((includeExpression_within h (2*H) right).mpr hr) r)
      (connectedMoment hw0 hw1 H joint left right hj hl hr r))) (ofQ' epsilon) := by
  have hn : geometricCutoff (entropyRate 625 (adjustedCoreRate w hd))
      (connectedAmplitude hd hs H joint left right) epsilon ≤
        r+1-carrierSize (boxSize base (2*H)) := by
    unfold comparisonModulus at hradius
    omega
  have hgeo := geometric_bound (rate_nonnegative hw0 hd) hs
    (connectedAmplitude_nonnegative hd hs H joint left right hj hl hr) heps _ hn
  exact leEv_trans (connected_inclusion_bound hw0 hw1 hsmall hd hs h hb H
    joint left right hj hl hr r) (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hgeo))

/-- Recenter the literal source, retaining its original reflection radius. -/
def bulkSource {base : Nat} (r : Nat) (x : IntrinsicExpression base) :
    IntrinsicExpression (paddedWidth base r) :=
  ⟨x.radius, centeredExpression r x.expression,
    (centered_within r x.radius x.expression).mpr x.within⟩

theorem bulkSource_unit (base r : Nat) :
    bulkSource r (unit base) = unit (paddedWidth base r) := rfl

theorem bulkSource_advance {base : Nat} (r lag : Nat) (x : IntrinsicExpression base) :
    bulkSource r (advance lag x) = advance lag (bulkSource r x) := rfl

/-- Reflection, the central one-step buffer, signs and time offsets all survive. -/
theorem bulkSource_crossOdd {base : Nat} (r : Nat) (x y : IntrinsicExpression base) :
    crossOdd (bulkSource r x) (bulkSource r y) = centeredExpression r (crossOdd x y) := by
  simp only [crossOdd, bulkSource, chart, advance, centeredExpression,
    recenterExpression, mirror, shift, recenter_mapOffsets]

private theorem odd_within {base : Nat} (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+1 ≤ H) (hy : y.radius+1 ≤ H) : Within (2*H) (crossOdd x y) :=
  within_mono (by omega : 2*(max x.radius y.radius)+1 ≤ 2*H) _ (crossOdd_within x y)

attribute [local irreducible] bondForm

/-- The CURRENT physical bond pairing equals the current original bulk
expectation. Native odd horizons are padded, without shifting any time. -/
theorem bondForm_bulkSource_pin {base : Nat} (H r : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+1 ≤ H) (hy : y.radius+1 ≤ H) :
    bondForm hw0 hw1 (bulkSource r x) (bulkSource r y) =
      Quotient.mk crealSetoid
        (expectation hw0 hw1 H (crossOdd x y) (odd_within H x y hx hy) r) := by
  unfold bondForm expectation
  simp only [bulkSource_crossOdd]
  apply Quotient.sound
  let L := 2*(max x.radius y.radius)+1
  have hL : L ≤ 2*H := by dsimp [L]; omega
  have hp := originalJoint_padding hw0 hw1 L 0 (2*H-L)
    (centeredExpression r (crossOdd x y))
    ((centered_within r L (crossOdd x y)).mpr (crossOdd_within x y))
  have hlen : L+0+(2*H-L)=2*H := by omega
  simpa only [hlen, shift_zero, bulkSource, L] using hp.symm

/-- An actual physical completed connected correlation, not a hypothetical
cross-width vector map or a separately chosen functional. -/
def bulkConnected {base : Nat} (lag : Nat) (x y : IntrinsicExpression base) (r : Nat) : RC :=
  connected hw0 hw1 lag (ofSource hw0 hw1 (bulkSource r x))
    (ofSource hw0 hw1 (bulkSource r y))

theorem bulkConnected_pin {base : Nat} (H lag r : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+1 ≤ H) (hy : y.radius+lag+1 ≤ H) :
    bulkConnected hw0 hw1 lag x y r = Quotient.mk crealSetoid
      (connectedMoment hw0 hw1 H (crossOdd x (advance lag y))
        (crossOdd x (unit base)) (crossOdd (unit base) y)
        (odd_within H x (advance lag y) hx hy)
        (odd_within H x (unit base) hx (by change 0+1 ≤ H; omega))
        (odd_within H (unit base) y (by change 0+1 ≤ H; omega) (by omega)) r) := by
  unfold bulkConnected
  rw [connected_source_pin, ← bulkSource_advance, ← bulkSource_unit base r,
    bondForm_bulkSource_pin hw0 hw1 H r x (advance lag y) hx hy,
    bondForm_bulkSource_pin hw0 hw1 H r x (unit base) hx (by change 0+1 ≤ H; omega),
    bondForm_bulkSource_pin hw0 hw1 H r (unit base) y (by change 0+1 ≤ H; omega) (by omega)]
  unfold connectedMoment
  rfl

private theorem crossOdd_inclusion {base larger : Nat} (h : base ≤ larger)
    (x y : IntrinsicExpression base) :
    crossOdd (inclusion h x) (inclusion h y) = includeExpression h (crossOdd x y) := by
  simp only [crossOdd, inclusion, chart, advance, includeExpression_mul,
    includeExpression_mirror, shift, includeExpression_mapOffsets]

private theorem abs_bound_two_sided {A B : CReal} {c : Q'}
    (h : leEv (abs (sub A B)) (ofQ' c)) :
    leEv A (add B (ofQ' c)) ∧ leEv B (add A (ofQ' c)) := by
  constructor
  · intro epsilon he
    obtain ⟨N,hN⟩ := h epsilon he
    refine ⟨N, fun n hn => ?_⟩
    have hs := Q'.le_trans' _ _ _ (Q'.le_abs_self (A.approx n + -B.approx n)) (hN n hn)
    have ha := Q'.le_add_of_sub_le hs
    exact Q'.le_trans' _ _ _ ha (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _))
  · intro epsilon he
    obtain ⟨N,hN⟩ := h epsilon he
    refine ⟨N, fun n hn => ?_⟩
    have hs := Q'.le_trans' _ _ _ (Q'.le_abs_self (B.approx n + -A.approx n))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hN n hn))
    have ha := Q'.le_add_of_sub_le hs
    exact Q'.le_trans' _ _ _ ha (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _))

include hsmall in
/-- Quantitative comparison of the SAME-source completed PHYSICAL bond
correlations. Each width retains its OWN vacuum means and the full lag+one
buffer. The computed spatial modulus is independent of the larger width. -/
theorem bulkConnected_inclusion_close {base larger : Nat} (h : base ≤ larger)
    (hb : 0 < base) (H lag : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+1 ≤ H) (hy : y.radius+lag+1 ≤ H)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (r : Nat)
    (hradius : comparisonModulus hd hs H (crossOdd x (advance lag y))
      (crossOdd x (unit base)) (crossOdd (unit base) y) epsilon ≤ r) :
    RCle (bulkConnected hw0 hw1 lag (inclusion h x) (inclusion h y) r)
      (RCadd (bulkConnected hw0 hw1 lag x y r) (Quotient.mk crealSetoid (ofQ' epsilon))) ∧
    RCle (bulkConnected hw0 hw1 lag x y r)
      (RCadd (bulkConnected hw0 hw1 lag (inclusion h x) (inclusion h y) r)
        (Quotient.mk crealSetoid (ofQ' epsilon))) := by
  have hcmp := connected_inclusion_close hw0 hw1 hsmall hd hs h hb H
    (crossOdd x (advance lag y)) (crossOdd x (unit base)) (crossOdd (unit base) y)
    (odd_within H x (advance lag y) hx hy)
    (odd_within H x (unit base) hx (by change 0+1 ≤ H; omega))
    (odd_within H (unit base) y (by change 0+1 ≤ H; omega) (by omega)) epsilon heps r hradius
  have hlarger := bulkConnected_pin hw0 hw1 H lag r (inclusion h x) (inclusion h y) hx hy
  simp only [← inclusion_advance, ← inclusion_unit h, crossOdd_inclusion] at hlarger
  rw [hlarger, bulkConnected_pin hw0 hw1 H lag r x y hx hy]
  exact abs_bound_two_sided hcmp

/-! ## Quantitative convergence of the CURRENT physical correlations

The target is the existing spatial form, not a freely chosen limit. The
propositional convergence lemmas are used only in order-preserving limit
arguments; the actual tolerance modulus is the existing computed geometric
cutoff, and is not extracted from any existential convergence proof.
-/

include hsmall in
theorem expectation_spatial_converges {base : Nat} (hb : 0 < base) (H : Nat)
    (e : WindowExpression base) (he : Within (2*H) e) :
    ConvergesTo (expectation hw0 hw1 H e he)
      (spatialLimit hw0 hw1 H e he hsmall hd hs hb) := by
  unfold expectation
  exact jointLimits_spatial_converge hw0 hw1 H e he hsmall hd hs hb

/-- Three already constructed spatial moments, retaining both OWN means. -/
def spatialConnectedMoment {base : Nat} (hb : 0 < base) (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) : CReal :=
  sub (spatialLimit hw0 hw1 H joint hj hsmall hd hs hb)
    (mul (spatialLimit hw0 hw1 H left hl hsmall hd hs hb)
      (spatialLimit hw0 hw1 H right hr hsmall hd hs hb))

include hsmall in
theorem connectedMoment_spatial_converges {base : Nat} (hb : 0 < base) (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) :
    ConvergesTo (connectedMoment hw0 hw1 H joint left right hj hl hr)
      (spatialConnectedMoment hw0 hw1 hsmall hd hs hb H joint left right hj hl hr) := by
  unfold connectedMoment spatialConnectedMoment
  exact TrigAddCReal.convergesTo_add
    (expectation_spatial_converges hw0 hw1 hsmall hd hs hb H joint hj)
    (TrigAddCReal.convergesTo_neg (convergesTo_mul_general
      (expectation_spatial_converges hw0 hw1 hsmall hd hs hb H left hl)
      (expectation_spatial_converges hw0 hw1 hsmall hd hs hb H right hr)))

include hsmall in
private theorem finite_connected_spatial_bound {base : Nat} (hb : 0 < base) (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) (r d stage t : Nat) :
    Q'.abs ((chartScalar hw0 hw1 H joint (r+d) stage t +
      -(chartScalar hw0 hw1 H left (r+d) stage t * chartScalar hw0 hw1 H right (r+d) stage t)) +
      -(chartScalar hw0 hw1 H joint r stage t +
        -(chartScalar hw0 hw1 H left r stage t * chartScalar hw0 hw1 H right r stage t))) ≤
      connectedAmplitude hd hs H joint left right *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))) := by
  have hc := covariance_heterogeneous_bound _ _ _ _ _ _ _ _ _ _ _
    (chart_abs_bound hw0 hw1 H left hl (r+d) stage t)
    (chart_abs_bound hw0 hw1 H right hr r stage t)
    (chartScalar_spatial_bound hw0 hw1 hsmall hd hs hb H joint hj r d stage t)
    (chartScalar_spatial_bound hw0 hw1 hsmall hd hs hb H left hl r d stage t)
    (chartScalar_spatial_bound hw0 hw1 hsmall hd hs hb H right hr r d stage t)
  refine Q'.le_trans' _ _ _ hc (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 5))
      (.add (.mul (.var 1) (.mul (.var 2) (.var 5)))
        (.mul (.var 3) (.mul (.var 4) (.var 5)))))
    (.mul (.add (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))) (.var 5))
    (by decide) (fun i => match i with
      | 0 => spatialAmplitude w hd hs H joint
      | 1 => windowCap left
      | 2 => spatialAmplitude w hd hs H right
      | 3 => windowCap right
      | 4 => spatialAmplitude w hd hs H left
      | _ => (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))))

include hsmall in
theorem connectedMoment_spatial_tail_bound {base : Nat} (hb : 0 < base) (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) (r d : Nat) :
    leEv (abs (sub (connectedMoment hw0 hw1 H joint left right hj hl hr (r+d))
      (connectedMoment hw0 hw1 H joint left right hj hl hr r)))
      (ofQ' (connectedAmplitude hd hs H joint left right *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))))) :=
  leEv_of_convergesTo_le
    (convergesTo_abs (TrigAddCReal.convergesTo_add
      (connected_diagonal_converges hw0 hw1 H joint left right hj hl hr (r+d))
      (TrigAddCReal.convergesTo_neg
        (connected_diagonal_converges hw0 hw1 H joint left right hj hl hr r))))
    (convergesTo_const _)
    (fun n => leEv_le_ofQ'_of_approx_le (fun _ =>
      finite_connected_spatial_bound hw0 hw1 hsmall hd hs hb H joint left right hj hl hr r d n n))

include hsmall in
/-- The same geometric error survives the limit of the later spatial row.
This is a bound against the existing limit, not only a Cauchy comparison. -/
theorem connectedMoment_spatial_limit_bound {base : Nat} (hb : 0 < base) (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right) (r : Nat) :
    leEv (abs (sub (spatialConnectedMoment hw0 hw1 hsmall hd hs hb H joint left right hj hl hr)
      (connectedMoment hw0 hw1 H joint left right hj hl hr r)))
      (ofQ' (connectedAmplitude hd hs H joint left right *
        (entropyRate 625 (adjustedCoreRate w hd))^
          (r+1-carrierSize (boxSize base (2*H))))) := by
  have hconv := connectedMoment_spatial_converges hw0 hw1 hsmall hd hs hb H
    joint left right hj hl hr
  have htail : ConvergesTo (fun d => connectedMoment hw0 hw1 H joint left right hj hl hr (r+d))
      (spatialConnectedMoment hw0 hw1 hsmall hd hs hb H joint left right hj hl hr) := by
    intro epsilon heps
    obtain ⟨N,hN⟩ := hconv epsilon heps
    exact ⟨N, fun d hd' => hN (r+d) (by omega)⟩
  exact leEv_of_convergesTo_le
    (convergesTo_abs (TrigAddCReal.convergesTo_add htail
      (TrigAddCReal.convergesTo_neg (convergesTo_const _))))
    (convergesTo_const _) (fun d =>
      connectedMoment_spatial_tail_bound hw0 hw1 hsmall hd hs hb H joint left right hj hl hr r d)

include hsmall in
theorem connectedMoment_spatial_close {base : Nat} (hb : 0 < base) (H : Nat)
    (joint left right : WindowExpression base) (hj : Within (2*H) joint)
    (hl : Within (2*H) left) (hr : Within (2*H) right)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (r : Nat)
    (hradius : comparisonModulus hd hs H joint left right epsilon ≤ r) :
    leEv (abs (sub (spatialConnectedMoment hw0 hw1 hsmall hd hs hb H joint left right hj hl hr)
      (connectedMoment hw0 hw1 H joint left right hj hl hr r))) (ofQ' epsilon) := by
  have hn : geometricCutoff (entropyRate 625 (adjustedCoreRate w hd))
      (connectedAmplitude hd hs H joint left right) epsilon ≤
        r+1-carrierSize (boxSize base (2*H)) := by
    unfold comparisonModulus at hradius
    omega
  have hgeo := geometric_bound (rate_nonnegative hw0 hd) hs
    (connectedAmplitude_nonnegative hd hs H joint left right hj hl hr) heps _ hn
  exact leEv_trans (connectedMoment_spatial_limit_bound hw0 hw1 hsmall hd hs hb H
    joint left right hj hl hr r) (leEv_le_ofQ'_of_approx_le (fun _ =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hgeo))

include hsmall in
/-- Bond reflection retains its extra one step at the spatial limit. -/
theorem spatialLimit_crossOdd_pin {base : Nat} (hb : 0 < base) (H : Nat)
    (x y : IntrinsicExpression base) (hx : x.radius+1 ≤ H) (hy : y.radius+1 ≤ H) :
    Equiv (spatialLimit hw0 hw1 H (crossOdd x y) (odd_within H x y hx hy) hsmall hd hs hb)
      (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance 1 y)) := by
  let S := max x.radius y.radius+1
  have hSH : S ≤ H := by dsimp [S]; omega
  have hxS : x.radius ≤ S := by dsimp [S]; omega
  have hyS : (advance 1 y).radius ≤ S := by change y.radius+1 ≤ S; dsimp [S]; omega
  have he : Within (2*S) (crossOdd x y) :=
    odd_within S x y (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hp := spatialLimit_padding hw0 hw1 hsmall hd hs hb S H 0 (2*H-2*S)
    (by omega) (crossOdd x y) he
  have hf := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x (advance 1 y) S hxS hyS
  have hnative : Equiv (spatialLimit hw0 hw1 S (crossOdd x y) he hsmall hd hs hb)
      (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance 1 y)) := by
    simpa only [form, crossOdd, S] using hf.symm
  have houter : Equiv
      (spatialLimit hw0 hw1 H (crossOdd x y) (odd_within H x y hx hy) hsmall hd hs hb)
      (spatialLimit hw0 hw1 S (crossOdd x y) he hsmall hd hs hb) := by
    simpa only [shift_zero] using hp
  exact houter.trans hnative

/-- The already constructed reflected spatial connected value. The clock is
lag PLUS one, and its two means are the stationary means of the SAME form. -/
def spatialConnected {base : Nat} (hb : 0 < base) (lag : Nat)
    (x y : IntrinsicExpression base) : CReal :=
  sub (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance (lag+1) y))
    (mul (intrinsicForm hw0 hw1 hsmall hd hs hb x (unit base))
      (intrinsicForm hw0 hw1 hsmall hd hs hb (unit base) y))

include hsmall in
theorem spatialConnectedMoment_pin {base : Nat} (hb : 0 < base) (H lag : Nat)
    (x y : IntrinsicExpression base) (hx : x.radius+1 ≤ H) (hy : y.radius+lag+1 ≤ H) :
    Equiv (spatialConnectedMoment hw0 hw1 hsmall hd hs hb H
      (crossOdd x (advance lag y)) (crossOdd x (unit base)) (crossOdd (unit base) y)
      (odd_within H x (advance lag y) hx hy)
      (odd_within H x (unit base) hx (by change 0+1 ≤ H; omega))
      (odd_within H (unit base) y (by change 0+1 ≤ H; omega) (by omega)))
      (spatialConnected hw0 hw1 hsmall hd hs hb lag x y) := by
  have hj := spatialLimit_crossOdd_pin hw0 hw1 hsmall hd hs hb H x (advance lag y) hx hy
  simp only [advance_add, Nat.add_comm 1 lag] at hj
  have hl := (spatialLimit_crossOdd_pin hw0 hw1 hsmall hd hs hb H x (unit base) hx
    (by change 0+1 ≤ H; omega)).trans
      (intrinsicForm_advanced_unit_right hw0 hw1 hsmall hd hs hb 1 x)
  have hr := (spatialLimit_crossOdd_pin hw0 hw1 hsmall hd hs hb H (unit base) y
    (by change 0+1 ≤ H; omega) (by omega)).trans
      ((intrinsicForm_time_balance hw0 hw1 hsmall hd hs hb 1 (unit base) y).symm.trans
        (intrinsicForm_advanced_unit_left hw0 hw1 hsmall hd hs hb 1 y))
  exact Equiv_add hj (neg_congr ((mul_congr_left hl).trans (TrigSignedAdd.mul_congr_right hr)))

include hsmall in
/-- ACTUAL completed physical correlations converge quantitatively to the
existing reflected spatial connected form. The modulus is explicit Nat data;
no completed-width map or nome/spacing-uniform assertion is needed. -/
theorem bulkConnected_spatial_close {base : Nat} (hb : 0 < base) (H lag : Nat)
    (x y : IntrinsicExpression base) (hx : x.radius+1 ≤ H) (hy : y.radius+lag+1 ≤ H)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (r : Nat)
    (hradius : comparisonModulus hd hs H (crossOdd x (advance lag y))
      (crossOdd x (unit base)) (crossOdd (unit base) y) epsilon ≤ r) :
    RCle (bulkConnected hw0 hw1 lag x y r)
      (RCadd (Quotient.mk crealSetoid (spatialConnected hw0 hw1 hsmall hd hs hb lag x y))
        (Quotient.mk crealSetoid (ofQ' epsilon))) ∧
    RCle (Quotient.mk crealSetoid (spatialConnected hw0 hw1 hsmall hd hs hb lag x y))
      (RCadd (bulkConnected hw0 hw1 lag x y r) (Quotient.mk crealSetoid (ofQ' epsilon))) := by
  have hclose := connectedMoment_spatial_close hw0 hw1 hsmall hd hs hb H
    (crossOdd x (advance lag y)) (crossOdd x (unit base)) (crossOdd (unit base) y)
    (odd_within H x (advance lag y) hx hy)
    (odd_within H x (unit base) hx (by change 0+1 ≤ H; omega))
    (odd_within H (unit base) y (by change 0+1 ≤ H; omega) (by omega)) epsilon heps r hradius
  have hpin := spatialConnectedMoment_pin hw0 hw1 hsmall hd hs hb H lag x y hx hy
  have hp := abs_bound_two_sided hclose
  rw [bulkConnected_pin hw0 hw1 H lag r x y hx hy]
  exact ⟨leEv_trans hp.2 (leEv_add (leEv_of_equiv hpin) (leEv_refl _)),
    leEv_trans (leEv_of_equiv hpin.symm) hp.1⟩

private theorem rc_half_chain (A B C : RC) (epsilon : Q')
    (hab : RCle A (RCadd B (Quotient.mk crealSetoid (ofQ' (HalfPow.half*epsilon)))))
    (hbc : RCle B (RCadd C (Quotient.mk crealSetoid (ofQ' (HalfPow.half*epsilon))))) :
    RCle A (RCadd C (Quotient.mk crealSetoid (ofQ' epsilon))) := by
  revert hab hbc
  refine Quotient.inductionOn₃ A B C ?_
  intro a b c hab hbc
  have hc : Equiv
      (add (add c (ofQ' (HalfPow.half*epsilon))) (ofQ' (HalfPow.half*epsilon)))
      (add c (ofQ' epsilon)) := SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left (c.approx n) _ _ (ExpNeg.two_halves epsilon)))
  exact leEv_trans hab
    (leEv_trans (leEv_add hbc (leEv_refl _)) (leEv_of_equiv hc))

include hsmall in
/-- Uniform in ANY larger ambient width. The same smaller-source spatial
modulus controls the ACTUAL included physical correlations against the SAME
smaller-source spatial value; each finite width still retains its OWN means. -/
theorem bulkConnected_included_spatial_close {base larger : Nat} (h : base ≤ larger)
    (hb : 0 < base) (H lag : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius+1 ≤ H) (hy : y.radius+lag+1 ≤ H)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (r : Nat)
    (hradius : comparisonModulus hd hs H (crossOdd x (advance lag y))
      (crossOdd x (unit base)) (crossOdd (unit base) y) (HalfPow.half*epsilon) ≤ r) :
    RCle (bulkConnected hw0 hw1 lag (inclusion h x) (inclusion h y) r)
      (RCadd (Quotient.mk crealSetoid (spatialConnected hw0 hw1 hsmall hd hs hb lag x y))
        (Quotient.mk crealSetoid (ofQ' epsilon))) ∧
    RCle (Quotient.mk crealSetoid (spatialConnected hw0 hw1 hsmall hd hs hb lag x y))
      (RCadd (bulkConnected hw0 hw1 lag (inclusion h x) (inclusion h y) r)
        (Quotient.mk crealSetoid (ofQ' epsilon))) := by
  have hhalf := ExpNeg.half_mul_pos epsilon heps
  have hwidth := bulkConnected_inclusion_close hw0 hw1 hsmall hd hs h hb H lag x y hx hy
    (HalfPow.half*epsilon) hhalf r hradius
  have hlimit := bulkConnected_spatial_close hw0 hw1 hsmall hd hs hb H lag x y hx hy
    (HalfPow.half*epsilon) hhalf r hradius
  exact ⟨rc_half_chain _ _ _ epsilon hwidth.1 hlimit.1,
    rc_half_chain _ _ _ epsilon hlimit.2 hwidth.2⟩

#print axioms expectation
#print axioms expectation_diagonal_converges
#print axioms expectation_inclusion_bound
#print axioms covariance_heterogeneous_bound
#print axioms finite_connected_inclusion_bound
#print axioms connected_diagonal_converges
#print axioms connectedMoment
#print axioms connectedAmplitude
#print axioms connected_inclusion_bound
#print axioms connectedAmplitude_nonnegative
#print axioms comparisonModulus
#print axioms connected_inclusion_close
#print axioms bulkSource
#print axioms bulkSource_unit
#print axioms bulkSource_advance
#print axioms bulkSource_crossOdd
#print axioms bondForm_bulkSource_pin
#print axioms bulkConnected
#print axioms bulkConnected_pin
#print axioms crossOdd_inclusion
#print axioms abs_bound_two_sided
#print axioms bulkConnected_inclusion_close
#print axioms expectation_spatial_converges
#print axioms spatialConnectedMoment
#print axioms connectedMoment_spatial_converges
#print axioms finite_connected_spatial_bound
#print axioms connectedMoment_spatial_tail_bound
#print axioms connectedMoment_spatial_limit_bound
#print axioms connectedMoment_spatial_close
#print axioms spatialLimit_crossOdd_pin
#print axioms spatialConnected
#print axioms spatialConnectedMoment_pin
#print axioms bulkConnected_spatial_close
#print axioms rc_half_chain
#print axioms bulkConnected_included_spatial_close

end YMGap.Continuum.BF4WilsonOriginalBulkComparison
