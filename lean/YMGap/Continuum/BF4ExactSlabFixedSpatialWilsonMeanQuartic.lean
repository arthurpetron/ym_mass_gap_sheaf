/-
# Source-aware Wilson energy with both chordal moments paid

The full noncommuting word has chordal second-moment ceiling
6*(1-w)*length^2, without a coordinate-factor loss. The computed log-split
quartic ceiling pays its fourth moment under the SAME original edge law.
Young about the actual odd mean c therefore gives

 t*E/Z <= t^2*Var_odd + (t+c^2)*R_log + t*(4-c^2)*L_word.

Every original source, spatial factor, terminal depth and partition remains.
The computed cutoff handles BOTH kinetic and quartic guards. This eliminates
the mixed radial moment for a literal one-loop trace. It does not supply a
useful variance-relative scaling rate, a changing-width map, or the complete
signed-family estimate; no concentration or physical trajectory is assumed.
-/

import YMGap.Continuum.QuaternionHaarWordQuadratic
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper
import YMGap.Continuum.BF4ExactSlabFixedSpatialLogQuartic

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanQuartic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
  (lower_supported upper_supported lower_unit upper_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyKineticUpper (oriented_displacement_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement (wordChordal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial
open YMGap.Continuum.BF4ExactSlabFixedSpatialLogQuartic
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2HeatQuarticDyadicSchedule (nome nome_pos nome_lt_one)
open YMGap.Continuum.SU2HeatQuarticLogDyadicBudget (logOnset)
open YMGap.Continuum.QuaternionHaarWordQuadratic (word_norm_quadratic_bound)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass edgeMoment mean
  wordChordal sourceCharacter

/-- Exact path-length dependence, with no width/depth/source-floor factor. -/
def wordQuadraticRate (w : Q') {width : Nat} (loop : SourceLoop width) : Q' :=
  (6*(1-w))*(Q'.ofNat loop.edges.length*Q'.ofNat loop.edges.length)

private theorem shuffle_rate (h m z : Q') :
    (m*m)*((6*h)*z) ≈ ((6*h)*(m*m))*z :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.const 6) (.var 1)) (.var 2)))
    (.mul (.mul (.mul (.const 6) (.var 1)) (.mul (.var 0) (.var 0))) (.var 2))
    (by decide) (fun | 0 => m | 1 => h | _ => z)

/-- All four coordinates are summed before charging the per-link budget. -/
theorem word_quadratic_nome_cleared {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width depth : Nat) (hK : sufficientCutoff w ≤ K+1) (hH : headCutoff w ≤ K+1)
    (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w (K+1) width (terminalMessage w (K+1) width depth))
        (wordChordal width loop)) ≤
      wordQuadraticRate w loop*oddMass w (K+1) width depth := by
  have h := word_norm_quadratic_bound
    (edgeCertificate hw0 hw1 (K+1) width hH (terminalMessage_supported w (K+1) width depth)
      (terminalMessage_certificate hw0 hw1 (K+1) width hH depth))
    (orientedLink width) (upperOriented width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
    (fun e he => upper_supported (loop.physical e he))
    (fun e he => lower_unit (loop.physical e he))
    (fun e he => upper_unit (loop.physical e he))
    ((6*(1-w))*oddMass w (K+1) width depth)
    (fun e he => oriented_displacement_bound hw0 hw1 K width depth hK
      (loop.physical e he) (hactive e he))
  unfold wordChordal
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (shuffle_rate (1-w) (Q'.ofNat loop.edges.length) (oddMass w (K+1) width depth)))

private theorem normalize_ceiling (A C Z : Q') (hZ : (0 : Q') < Z) (h : A ≤ C*Z) :
    A*Q'.recipPos Z hZ ≤ C :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (Q'.recipPos_pos Z hZ)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left C _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv C))))

theorem word_quadratic_nome_normalized {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width depth : Nat) (hK : sufficientCutoff w ≤ K+1) (hH : headCutoff w ≤ K+1)
    (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    edgeMoment hw0 hw1 (K+1) width hH depth (wordChordal width loop) ≤ wordQuadraticRate w loop := by
  unfold edgeMoment
  exact normalize_ceiling _ _ _ (oddMass_positive hw0 hw1 (K+1) width hH depth)
    (word_quadratic_nome_cleared hw0 hw1 K width depth hK hH loop hactive)

/-- The additional kinetic onset is computed, not hidden in a uniform constant. -/
def meanCutoff (r stage : Nat) : Nat :=
  logCutoff r (sufficientCutoff (nome (2*r))+stage)+1

theorem meanCutoff_head (r stage : Nat) : headCutoff (nome (2*r)) ≤ meanCutoff r stage :=
  Nat.le_trans (head_le_logCutoff r _) (Nat.le_succ _)

theorem meanCutoff_kinetic (r stage : Nat) : sufficientCutoff (nome (2*r)) ≤ meanCutoff r stage := by
  unfold meanCutoff logCutoff
  omega

/-- The original log-quartic producer applies at every computed late stage. -/
theorem word_quartic_mean_normalized (r : Nat) (hr : logOnset ≤ r)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    edgeMoment (nome_pos (by change 22 ≤ r at hr; omega)) (nome_lt_one (2*r))
      (meanCutoff r stage) width (meanCutoff_head r stage) depth
      (polyMul (wordChordal width loop) (wordChordal width loop)) ≤ wordLogRate r loop := by
  have hw0 := nome_pos (show 6 ≤ 2*r by change 22 ≤ r at hr; omega)
  have hraw := word_quartic_log_bound r hr (sufficientCutoff (nome (2*r))+stage+1)
    width depth loop hactive
  have hcut : logCutoff r (sufficientCutoff (nome (2*r))+stage+1) = meanCutoff r stage := by
    unfold meanCutoff logCutoff
    omega
  rw [hcut] at hraw
  unfold edgeMoment
  exact normalize_ceiling _ _ _
    (oddMass_positive hw0 (nome_lt_one (2*r)) _ width (meanCutoff_head r stage) depth) hraw

/-- No mixed radial moment remains: the residual is the actual mean
correction and the explicit quartic/variance budget on the SAME odd law. -/
theorem wilson_energy_mean_log_budget (r : Nat) (hr : logOnset ≤ r)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (t : Q') (ht : (0 : Q') ≤ t) :
    let hw0 := nome_pos (show 6 ≤ 2*r by change 22 ≤ r at hr; omega)
    let hw1 := nome_lt_one (2*r)
    let K := meanCutoff r stage
    let hK := meanCutoff_head r stage
    let f := sourceCharacter width loop.edges 1
    let c := mean hw0 hw1 K width hK depth f
    t*normalizedEnergy hw0 hw1 K width hK depth f ≤
      (t*t)*oddVariance hw0 hw1 K width hK depth f +
      (t+c*c)*wordLogRate r loop +
      (t*(4+ -(c*c)))*wordQuadraticRate (nome (2*r)) loop := by
  dsimp only
  let hw0 := nome_pos (show 6 ≤ 2*r by change 22 ≤ r at hr; omega)
  let hw1 := nome_lt_one (2*r)
  let K := meanCutoff r stage
  let hK := meanCutoff_head r stage
  let f := sourceCharacter width loop.edges 1
  let c := mean hw0 hw1 K width hK depth f
  have h := wilson_energy_mean_moments hw0 hw1 K width hK depth loop t ht
  have hq := word_quartic_mean_normalized r hr stage width depth loop hactive
  have hl := word_quadratic_nome_normalized hw0 hw1
    (logCutoff r (sufficientCutoff (nome (2*r))+stage)) width depth
    (meanCutoff_kinetic r stage) hK loop hactive
  have hc : (0 : Q') ≤ t+c*c := Q'.zero_le_add _ _ ht (SumOfSquares.q_mul_self_nonneg c)
  have hrad : (0 : Q') ≤ t*(4+ -(c*c)) :=
    Q'.mul_nonneg _ _ ht (radial_coefficient_nonnegative hw0 hw1 K width hK depth loop)
  exact Q'.le_trans' _ _ _ h
    (Q'.add_le_add
      (Q'.add_le_add (Q'.le_refl' _)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hq hc))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hl hrad))

#print axioms wordQuadraticRate
#print axioms word_quadratic_nome_cleared
#print axioms word_quadratic_nome_normalized
#print axioms meanCutoff
#print axioms meanCutoff_head
#print axioms meanCutoff_kinetic
#print axioms word_quartic_mean_normalized
#print axioms wilson_energy_mean_log_budget

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanQuartic
