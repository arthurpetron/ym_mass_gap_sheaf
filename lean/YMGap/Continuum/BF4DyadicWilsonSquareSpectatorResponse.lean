/-
# Original growing Wilson-square response with its exterior retained

The actual endpoint q=V*u_(n+1) is compared with the constructed local
spectator R, not assumed independent of the loop. The full active heat sends
R*f to w^(12*side)*(P R)*f. A single erased edge proves the corresponding
zero first moment without dropping a heat factor from the statement.

The existing dual-test band argument then bounds COMPLETE original temporal
energy relative to OWN interacting variance. The explicit positive response
fraction depends on nome and perimeter, not ambient width, later cutoff or
positive terminal depth. It requires no small total heat loss. These constants
do not supply useful changing-family scaling, physical mass or continuum
survival. The fundamental label guard 1<=K is separate from headCutoff<=K.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSpectatorWilsonWord
import YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
import YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse

namespace YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt)
open YMGap.Continuum.SU2QuaternionProductHeatSpectatorWilsonWord
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (link orientedLink spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceWord sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_nodup activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual (active_erased_spectator)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (energy_source_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (centered_unprojected_square energy_shifted)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding
  (source_edges_active_after_padding)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareNodup
open YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage energy sourceCharacter

private theorem wordAt_sourceWord (width : Nat) :
    ∀ (es : List OrientedBF4Link),
      (∀ e, e ∈ es → e.link ∈ baseLinks width) →
      wordAt (fun e => (baseLinks width).idxOf e.link) es = sourceWord width es
  | [], _ => rfl
  | e::es, hphysical => by
      have he := hphysical e List.mem_cons_self
      have ht := fun f hf => hphysical f (List.mem_cons_of_mem e hf)
      change PolyQuaternion.mul
          (orientedCoordinateQuaternion ((baseLinks width).idxOf e.link) e.reverse)
          (wordAt (fun f => (baseLinks width).idxOf f.link) es) =
        PolyQuaternion.mul (orientedLink width e) (sourceWord width es)
      rw [wordAt_sourceWord width es ht]
      unfold orientedLink link
      rw [if_pos he]
      rfl

private theorem square_character_pin (scale width : Nat) (hwidth : side scale < width) :
    characterPolynomial
      (wordAt (fun e => (baseLinks width).idxOf e.link)
        (paddedSquare scale width hwidth).edges).scalar 1 =
      sourceCharacter width (paddedSquare scale width hwidth).edges 1 := by
  rw [wordAt_sourceWord width _ (paddedSquare scale width hwidth).physical]
  unfold sourceCharacter
  rfl

/-- Constructed exterior, with the full original predecessor terminal input. -/
def squareSpectator (w : Q') (K scale width : Nat) (hwidth : side scale < width)
    (n : Nat) : RatPoly :=
  spectator w K width n ((paddedSquare scale width hwidth).edges.map (fun e => e.link))

theorem squareSpectator_supported (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (n : Nat) :
    SupportedQuaternionBlocks (N width) (squareSpectator w K scale width hwidth n) :=
  spectator_supported w K width n _

private theorem squareSpectator_independent (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (n : Nat) (e : OrientedBF4Link)
    (he : e ∈ (paddedSquare scale width hwidth).edges) :
    QuaternionBlockIndependent ((baseLinks width).idxOf e.link)
      (squareSpectator w K scale width hwidth n) :=
  spectator_independent w K width n _ e.link
    (List.mem_map.mpr ⟨e, he, rfl⟩) ((paddedSquare scale width hwidth).physical e he)

private theorem square_active (scale width : Nat) (hwidth : side scale < width)
    (e : OrientedBF4Link) (he : e ∈ (paddedSquare scale width hwidth).edges) :
    (baseLinks width).idxOf e.link ∈ activeBlocks width := by
  apply source_edges_active_after_padding hwidth (square scale) e
  rw [← paddedSquare_edges scale width hwidth]
  exact he

/-- Full active heat transmission, including the transformed exterior. -/
theorem paddedSquare_spectator_kinetic (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK1 : 1 ≤ K) (n : Nat) :
    let R := squareSpectator w K scale width hwidth n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width) (polyMul R f))
      (polySmul (qpow w (12*side scale))
        (polyMul (productMap (N width) w K (activeBlocks width) R) f)) := by
  dsimp only
  have h := productMap_fundamental_word_spectator (N width) w K hK1
    (fun e => (baseLinks width).idxOf e.link) (paddedSquare scale width hwidth).edges
    (activeBlocks width) (activeBlocks_nodup width) (activeBlocks_lt width)
    (paddedSquare_indices_nodup scale width hwidth)
    (square_active scale width hwidth)
    (squareSpectator w K scale width hwidth n)
    (squareSpectator_supported w K scale width hwidth n)
    (squareSpectator_independent w K scale width hwidth n)
  have hlen : 3*(paddedSquare scale width hwidth).edges.length = 12*side scale := by
    rw [paddedSquare_edges, square_length]
    omega
  simpa only [square_character_pin, hlen] using h

/-- One erased edge is only a proof representative; the statement keeps the
entire active heat and has no cutoff or positivity assumption. -/
theorem paddedSquare_spectator_zero (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K n : Nat) :
    let R := squareSpectator w K scale width hwidth n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    H width (polyMul (polyMul R (productMap (N width) w K (activeBlocks width) R)) f) ≈ 0 := by
  dsimp only
  let block := fun e : OrientedBF4Link => (baseLinks width).idxOf e.link
  let R := squareSpectator w K scale width hwidth n
  let P := productMap (N width) w K (activeBlocks width)
  let i := block selectedEdge
  let E := productMap (N width) w K (eraseIndex i (activeBlocks width)) R
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hmem := selectedEdge_mem_paddedSquare scale width hwidth
  have hi : i ∈ activeBlocks width := square_active scale width hwidth selectedEdge hmem
  have hR := squareSpectator_supported w K scale width hwidth n
  have hRI := squareSpectator_independent w K scale width hwidth n selectedEdge hmem
  have hpair := active_erased_spectator width w K i hi R hR hRI
  have hE : SupportedQuaternionBlocks (N width) E :=
    productMap_supported (N width) w K _
      (fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj)) hR
  have hnd := paddedSquare_indices_nodup scale width hwidth
  rw [paddedSquare_edges_split, List.map_cons, List.nodup_cons] at hnd
  have habsent : ∀ d, d ∈ dyadicTail scale → block selectedEdge ≠ block d := by
    intro d hd heq
    exact hnd.1 (List.mem_map.mpr ⟨d, hd, heq.symm⟩)
  have hz := fundamental_word_first_moment (N width) block selectedEdge (dyadicTail scale)
    (activeBlocks_lt width i hi) (by rfl) habsent (polyMul R E)
    (quaternionBlockIndependent_polyMul hRI hpair.2)
  have hfpin : characterPolynomial (wordAt block (selectedEdge::dyadicTail scale)).scalar 1 = f := by
    rw [← paddedSquare_edges_split scale width hwidth]
    exact square_character_pin scale width hwidth
  rw [hfpin] at hz
  have htest := supported_polyMul hR
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)
  have hleft : RatPolyCoeffEqv (polyMul (polyMul R (P R)) f) (polyMul (polyMul R f) (P R)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => R | 1 => P R | _ => f)
  have hright : RatPolyCoeffEqv (polyMul (polyMul R f) E) (polyMul f (polyMul R E)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => R | 1 => E | _ => f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hleft)
    (Q'.eqv_trans _ _ _ (hpair.1 (polyMul R f) htest)
      (Q'.eqv_trans _ _ _ (haar_of_coeff hright) hz))

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ k : Nat, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (qpow_positive hw k) hw

private theorem qpow_rg (w : Q') : ∀ n, qpow w n = RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun x : Q' => x*w) (qpow_rg w n)

/-- Explicit finite response fraction; no width, cutoff or depth argument. -/
def squareResponseFraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale : Nat) : Q' :=
  (qpow w (12*side scale)*(localLower w (4*side scale)*localLower w (4*side scale))) *
    Q'.recipPos (localUpper w (4*side scale)*localUpper w (4*side scale))
      (Q'.mul_pos (localUpper_positive hw0 hw1 _) (localUpper_positive hw0 hw1 _))

theorem squareResponseFraction_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    (0 : Q') < squareResponseFraction hw0 hw1 scale :=
  Q'.mul_pos (Q'.mul_pos (qpow_positive hw0 _)
    (Q'.mul_pos (localLower_positive hw0 hw1 _) (localLower_positive hw0 hw1 _)))
    (Q'.recipPos_pos _ _)

attribute [local irreducible] oddMass oddVariance normalizedMoment marginalWeight normalizedEnergy

/-- Original OWN-centered variance and COMPLETE energy, with the explicit
positive band cap left cleared. No independent-source premise is present. -/
theorem paddedSquare_energy_band_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let M := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
    let l := localLower w (4*side scale)
    let u := localUpper w (4*side scale)
    (u*u)*energy w K width (terminalMessage w K width (n+1)) f +
      (qpow w (12*side scale)*(l*l))*M ≤ (u*u)*M := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let g := terminalMessage w K width (n+1)
  let q := endpointSource w K width g
  let R := squareSpectator w K scale width hwidth n
  let l := localLower w (4*side scale)
  let u := localUpper w (4*side scale)
  let center := normalizedMoment (N width) (marginalWeight w K width (n+1)) f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  let psi := shifted f center
  let A := sourceMoment (N width) w K (activeBlocks width) q (polyMul psi psi)
  let B := kineticPair (N width) w K (activeBlocks width) (polyMul q psi) (polyMul q psi)
  let M := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hg := terminalMessage_supported w K width (n+1)
  have hq := supported_polyMul (spatialWeight_supported w K width) hg
  have Q := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK (n+1))
  have hsize : ((paddedSquare scale width hwidth).edges.map (fun e => e.link)).length ≤ 4*side scale := by
    exact Nat.le_of_eq (by rw [List.length_map, paddedSquare_edges, square_length])
  have hr := response_band_cleared hw0 hw1 K hK (activeBlocks width)
    (activeBlocks_lt width) hq (squareSpectator_supported w K scale width hwidth n) hf Q
    (spectator_certificate hw0 hw1 K width hK n _) (qpow w (12*side scale)) l u center
    (qpow_positive hw0 _) (by
      rw [qpow_rg]
      exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _)
    (Q'.le_of_lt (localLower_positive hw0 hw1 _))
    (Q'.le_of_lt (localUpper_positive hw0 hw1 _))
    (endpoint_localLowerCertificate hw0 hw1 K width hK n _ _ hsize)
    (endpoint_localUpperCertificate hw0 hw1 K width hK n _ _ hsize)
    (paddedSquare_spectator_kinetic scale width hwidth w K hK1 n)
    (paddedSquare_spectator_zero scale width hwidth w K n)
  have hpin : A ≈ M := centered_unprojected_square hw0 hw1 K width hK (n+1) hf
  have hE : energy w K width g f ≈ A + -B :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (energy_shifted w K width hg hf center))
      (energy_source_pin w K width g psi)
  have hclear : (u*u)*(A + -B)+(qpow w (12*side scale)*(l*l))*A ≤ (u*u)*A := by
    have h := Q'.add_le_add_left ((u*u)*(A + -B)) _ _ hr
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.var 1)) (by decide) (fun | 0 => u*u | 1 => A | _ => B)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left (u*u) _ _ hE)
    (Q'.mul_eqv_congr_left (qpow w (12*side scale)*(l*l)) _ _ hpin.symm)))
    (Q'.le_trans' _ _ _ hclear (Q'.le_of_eqv (Q'.mul_eqv_congr_left (u*u) _ _ hpin)))

/-- Divide only by the explicit band cap, never by interacting variance. -/
theorem paddedSquare_energy_band_raw {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    energy w K width (terminalMessage w K width (n+1)) f ≤
      (1-squareResponseFraction hw0 hw1 scale)*
        (oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let E := energy w K width (terminalMessage w K width (n+1)) f
  let M := oddMass w K width (n+1)*oddVariance hw0 hw1 K width hK (n+1) f
  let l := localLower w (4*side scale)
  let u := localUpper w (4*side scale)
  let A := qpow w (12*side scale)*(l*l)
  let U := u*u
  let hU := Q'.mul_pos (localUpper_positive hw0 hw1 (4*side scale))
    (localUpper_positive hw0 hw1 (4*side scale))
  let r := Q'.recipPos U hU
  let delta := A*r
  have hUr : r*U ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv r U) (Q'.mul_recipPos_eqv U hU)
  have hclear : U*E+A*M ≤ U*M :=
    paddedSquare_energy_band_cleared hw0 hw1 K width hK hK1 n scale hwidth
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ r hclear (Q'.le_of_lt (Q'.recipPos_pos U hU))
  have hleft : r*(U*E+A*M) ≈ E+delta*M :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 3) (.var 0)) (.var 4)))
      (by decide) (fun | 0 => r | 1 => U | 2 => E | 3 => A | _ => M))
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ E hUr) (Q'.one_mul_eqv E))
        (Q'.eqv_refl _))
  have hright : r*(U*M) ≈ M := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r U M))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ M hUr) (Q'.one_mul_eqv M))
  have hbudget : E+delta*M ≤ M := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  have he : M + -(E+delta*M) ≈ (1-delta)*M + -E :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.mul (.var 2) (.var 0)))))
      (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 0)) (.neg (.var 1)))
      (by decide) (fun | 0 => M | 1 => E | _ => delta)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hbudget) (Q'.le_of_eqv he))

/-- Normalization uses the SAME original positive partition. This bound is
uniform in ambient width, later cutoff and positive depth at FIXED nome/scale. -/
theorem paddedSquare_energy_band {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    normalizedEnergy hw0 hw1 K width hK (n+1) f ≤
      (1-squareResponseFraction hw0 hw1 scale)*oddVariance hw0 hw1 K width hK (n+1) f := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let z := oddMass w K width (n+1)
  let hz := oddMass_positive hw0 hw1 K width hK (n+1)
  let r := Q'.recipPos z hz
  let v := oddVariance hw0 hw1 K width hK (n+1) f
  let c := 1-squareResponseFraction hw0 hw1 scale
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (paddedSquare_energy_band_raw hw0 hw1 K width hK hK1 n scale hwidth)
    (Q'.le_of_lt (Q'.recipPos_pos z hz))
  have hright : (c*(z*v))*r ≈ c*v :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => c | 1 => z | 2 => v | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (c*v) (Q'.mul_recipPos_eqv z hz))
        (Q'.one_mul_eqv (c*v)))
  unfold normalizedEnergy
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright)

#print axioms squareSpectator
#print axioms squareSpectator_supported
#print axioms paddedSquare_spectator_kinetic
#print axioms paddedSquare_spectator_zero
#print axioms squareResponseFraction
#print axioms squareResponseFraction_positive
#print axioms paddedSquare_energy_band_cleared
#print axioms paddedSquare_energy_band_raw
#print axioms paddedSquare_energy_band

end YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
