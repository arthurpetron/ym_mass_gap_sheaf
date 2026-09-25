/-
An order-respecting tail modulus for a rational geometric sequence.
The closure constant is explicit data: `1 + r * H ≤ H`.  In particular,
the result does not hide a summability assumption in a Prop-level existence.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.BernsteinStageData
import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.GeometricAntitoneTailControl

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HKPos
open YMGap.Continuum.SemicircleConvClosed
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.SummableCRealStepVariation

local infix:50 " ≈ " => Q'.eqv

/-- A representation-invariant cutoff for `r^N * H ≤ ε`. -/
def geometricTailRate {r : Q'} (hr1 : r < (1 : Q')) (H epsilon : Q') : Nat :=
  if h : (0 : Q') < epsilon then
    qCeilNat (H * Q'.recipPos ((1 + (-r)) * epsilon)
      (q_mul_pos (one_sub_pos hr1) h))
  else 0

theorem geometricTailRate_antitone {r H : Q'}
    (hr1 : r < (1 : Q')) (hH : (0 : Q') ≤ H)
    (epsilon delta : Q') (hdelta : (0 : Q') < delta)
    (hde : delta ≤ epsilon) :
    geometricTailRate hr1 H epsilon ≤ geometricTailRate hr1 H delta := by
  have hepsilon : (0 : Q') < epsilon := Q'.pos_of_lt_of_le hdelta hde
  unfold geometricTailRate
  rw [dif_pos hepsilon, dif_pos hdelta]
  apply qCeilNat_mono
  apply Q'.mul_le_mul_of_nonneg_left _ _ H _ hH
  apply recipPos_antitone
    ((1 + (-r)) * delta) ((1 + (-r)) * epsilon)
    (q_mul_pos (one_sub_pos hr1) hdelta)
    (q_mul_pos (one_sub_pos hr1) hepsilon)
  exact Q'.mul_le_mul_of_nonneg_left delta epsilon (1 + (-r)) hde
    (Q'.le_of_lt (one_sub_pos hr1))

theorem geometricTailRate_bound {r H epsilon : Q'}
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (hepsilon : (0 : Q') < epsilon) :
    H * r ^ (geometricTailRate hr1 H epsilon) ≤ epsilon := by
  let g : Q' := 1 + (-r)
  have hg : (0 : Q') < g := one_sub_pos hr1
  have hgε : (0 : Q') < g * epsilon := q_mul_pos hg hepsilon
  let N := geometricTailRate hr1 H epsilon
  let w := H * Q'.recipPos (g * epsilon) hgε
  have hw : w ≤ Q'.ofNat N := by
    unfold N geometricTailRate
    rw [dif_pos hepsilon]
    exact q_le_qCeilNat w
  have hH_le : H ≤ Q'.ofNat N * (g * epsilon) := by
    have hm := Q'.mul_le_mul_of_nonneg_right w (Q'.ofNat N) (g * epsilon)
      hw (Q'.le_of_lt hgε)
    have heq : (w * (g * epsilon)).eqv H := by
      unfold w
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv H _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left H _ _
          (Q'.mul_comm_eqv (Q'.recipPos (g * epsilon) hgε) (g * epsilon))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left H _ _
          (Q'.mul_recipPos_eqv (g * epsilon) hgε)) ?_
      exact Q'.mul_one_eqv H
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hm
  have hB : H ≤ bScale g N * epsilon := by
    have hrewrite : (Q'.ofNat N * (g * epsilon)).eqv
        ((Q'.ofNat N * g) * epsilon) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat N) g epsilon)
    have hscale := Q'.mul_le_mul_of_nonneg_right
      (Q'.ofNat N * g) (bScale g N) epsilon
      (ofNat_mul_le_bScale (Q'.le_of_lt hg) N) (Q'.le_of_lt hepsilon)
    exact Q'.le_trans' _ _ _ hH_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) hscale)
  have hpow : (0 : Q') ≤ r ^ N := Q'.pow_nonneg r (Q'.le_of_lt hr0) N
  have hprod := Q'.mul_le_mul_of_nonneg_right H (bScale g N * epsilon)
    (r ^ N) hB hpow
  have hcomm : ((bScale g N * epsilon) * r ^ N).eqv
      (epsilon * (bScale g N * r ^ N)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (bScale g N) epsilon (r ^ N)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (bScale g N) _ _
        (Q'.mul_comm_eqv epsilon (r ^ N))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (bScale g N) (r ^ N) epsilon)) ?_
    exact Q'.mul_comm_eqv (bScale g N * r ^ N) epsilon
  have hbern : bScale g N * r ^ N ≤ (1 : Q') :=
    bernoulli_pow (Q'.le_of_lt hr0) (Q'.le_of_lt hr1) N
  have hlast := Q'.mul_le_mul_of_nonneg_left
    (bScale g N * r ^ N) 1 epsilon hbern (Q'.le_of_lt hepsilon)
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
      (Q'.le_trans' _ _ _ hlast (Q'.le_of_eqv (Q'.mul_one_eqv epsilon))))

/-- A fixed subunit rational base has a computable, order-antitone finite-tail
modulus.  The rate uses a rational ceiling, never an unreduced numerator. -/
def geometricPowerTailControl {r : Q'}
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q')) :
    AntitoneTailControl (fun n => r ^ n) := by
  let H : Q' := HKConv.divPos 1 (1 + (-r))
  have hH : (0 : Q') ≤ H :=
    HKConv.divPos_nonneg (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))
  refine {
    tailRate := geometricTailRate hr1 H
    tailRate_antitone := ?_
    tailBound := ?_ }
  · intro epsilon delta hdelta hde
    exact geometricTailRate_antitone hr1 hH epsilon delta hdelta hde
  · intro epsilon hepsilon start hstart length
    have hterm : (finSum (fun offset => r ^ (start + offset)) length).eqv
        (finSum (fun offset => geoIncrBase 1 r (start + offset)) length) :=
      finSum_eqv_congr _ _ (fun offset =>
        Q'.eqv_symm (Q'.one_mul_eqv (r ^ (start + offset)))) length
    have hseries : finSum (fun offset => r ^ (start + offset)) length ≤
        geoTailBase 1 r start :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hterm)
        (geoTailBase_series_le
          (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))) hr0 hr1 start length)
    have hpow : r ^ start ≤ r ^ (geometricTailRate hr1 H epsilon) :=
      pow_base_antitone (Q'.le_of_lt hr0) (Q'.le_of_lt hr1) hstart
    have hscaled : H * r ^ start ≤ H * r ^ (geometricTailRate hr1 H epsilon) :=
      Q'.mul_le_mul_of_nonneg_left _ _ H hpow hH
    have heq : (geoTailBase 1 r start).eqv (H * r ^ start) := by
      unfold geoTailBase H
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (r ^ start))) ?_
      exact Q'.mul_comm_eqv _ _
    exact Q'.le_trans' _ _ _ hseries
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
        (Q'.le_trans' _ _ _ hscaled
          (geometricTailRate_bound hr0 hr1 hepsilon)))

#print axioms geometricTailRate_antitone
#print axioms geometricTailRate_bound
#print axioms geometricPowerTailControl

end YMGap.Continuum.GeometricAntitoneTailControl
