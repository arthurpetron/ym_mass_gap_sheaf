/-
Actual original connected-dual gain for the padded Wilson square.
The upper local certificate alone makes the OWN positive centered mass
overlap the retained spectator. Consequently the computed connected dual
denominator is strictly positive; no alignment or inverse is assumed.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualOverlap
import YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor
import YMGap.Continuum.SU2QuaternionProductHeatBandResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
import YMGap.Continuum.BF4ExactSlabLocalStarComparison
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_smul productMap_neg)
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand (erasedCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse (square_moment_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (centered_unprojected_square)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localUpper localUpper_positive endpoint_localUpperCertificate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
  (starRatio starRatio_positive)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareSpectator squareSpectator_supported)
open YMGap.Continuum.BF4DyadicWilsonSquareSignedOverlapGain
  (squareSpectatorOverlap)
open YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualOverlap
  (squareConnectedDualMoment paddedSquare_connectedDualMoment_nonnegative
    paddedSquare_energy_connected_overlap_cleared)
open YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor
  (paddedSquare_oddVariance_floor)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage spatialWeight sourceCharacter

private def squareCharacter (scale width : Nat) (hwidth : side scale < width) : RatPoly :=
  sourceCharacter width (paddedSquare scale width hwidth).edges 1

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (qpow_positive hw n) hw

private theorem right_pos_of_mul_pos {left right : Q'}
    (hleft : (0 : Q') ≤ left) (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hp := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hp
  have hl : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hr
  exact (Int.not_lt_of_ge (Int.mul_nonpos_of_nonneg_of_nonpos hl hr)) hp

private theorem lt_add_of_pos_right (x y : Q') (hy : (0 : Q') < y) :
    x < x+y := by
  show x.num * ((x+y).den : Int) < (x+y).num * (x.den : Int)
  have hynum : (0 : Int) < y.num := Q'.num_pos_of_pos hy
  show x.num * ((x.den*y.den : Nat) : Int) <
    (x.num*(y.den : Int)+y.num*(x.den : Int))*(x.den : Int)
  have hcast : ((x.den*y.den : Nat) : Int) =
      (x.den : Int)*(y.den : Int) := by push_cast; rfl
  rw [hcast]
  have hden : (0 : Int) < (x.den : Int) := by exact_mod_cast x.den_pos
  have hpositive : (0 : Int) < y.num*(x.den : Int)*(x.den : Int) :=
    Int.mul_pos (Int.mul_pos hynum hden) hden
  have hrewrite :
      (x.num*(y.den : Int)+y.num*(x.den : Int))*(x.den : Int) =
        x.num*((x.den : Int)*(y.den : Int))+
          y.num*(x.den : Int)*(x.den : Int) := by
    rw [Int.add_mul]
    have hh : x.num*(y.den : Int)*(x.den : Int) =
        x.num*((x.den : Int)*(y.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (y.den : Int) (x.den : Int)]
    rw [hh]
  rw [hrewrite]
  omega

private theorem lt_of_lt_of_le {x y z : Q'} (hxy : x < y) (hyz : y ≤ z) :
    x < z := by
  have e1 : x.num*(y.den : Int) < y.num*(x.den : Int) := hxy
  have e2 : y.num*(z.den : Int) ≤ z.num*(y.den : Int) := hyz
  show x.num*(z.den : Int) < z.num*(x.den : Int)
  have s1 : (x.num*(z.den : Int))*(y.den : Int) <
      (y.num*(x.den : Int))*(z.den : Int) := by
    have hh := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast z.den_pos : (0 : Int) < (z.den : Int))
    have hr : (x.num*(y.den : Int))*(z.den : Int) =
        (x.num*(z.den : Int))*(y.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (y.den : Int) (z.den : Int)]
    rwa [hr] at hh
  have s2 : (y.num*(x.den : Int))*(z.den : Int) ≤
      (z.num*(x.den : Int))*(y.den : Int) := by
    have hh := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt x.den_pos : (0 : Int) ≤ (x.den : Int))
    have hr : (y.num*(z.den : Int))*(x.den : Int) =
        (y.num*(x.den : Int))*(z.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (z.den : Int) (x.den : Int)]
    have hr2 : (z.num*(y.den : Int))*(x.den : Int) =
        (z.num*(x.den : Int))*(y.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (y.den : Int) (x.den : Int)]
    rw [hr, hr2] at hh
    exact hh
  exact Int.lt_of_mul_lt_mul_right (Int.lt_of_lt_of_le s1 s2)
    (by exact_mod_cast Nat.le_of_lt y.den_pos : (0 : Int) ≤ (y.den : Int))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
  (hwidth : side scale < width)

local notation "f" => squareCharacter scale width hwidth
local notation "q" => endpointSource w K width (terminalMessage w K width (n+1))
local notation "R" => squareSpectator w K scale width hwidth n
local notation "PR" => productMap (N width) w K (activeBlocks width) R
local notation "Pq" => productMap (N width) w K (activeBlocks width) q
local notation "psi" => oddCentered hw0 hw1 K width hK (n+1) f
local notation "u" => localUpper w (4*side scale)
local notation "a" => qpow w (12*side scale)
local notation "Z" => oddMass w K width (n+1)
local notation "S" => Z*oddVariance hw0 hw1 K width hK (n+1) f
local notation "U" => squareSpectatorOverlap hw0 hw1 K width hK n scale hwidth
local notation "D0" => squareConnectedDualMoment hw0 hw1 K width hK n scale hwidth
local notation "E" => energy w K width (terminalMessage w K width (n+1)) f

/-- The original centered unprojected square is bounded by the upper local
band times the actual retained-spectator overlap. No lower band is used. -/
theorem paddedSquare_original_upper_overlap : S ≤ u*U := by
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hq := supported_polyMul (spatialWeight_supported w K width)
    (terminalMessage_supported w K width (n+1))
  have hR := squareSpectator_supported w K scale width hwidth n
  have Q : Certificate (N width) q :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK (n+1))
  have hsize : ((paddedSquare scale width hwidth).edges.map (fun e => e.link)).length ≤
      4*side scale := by
    exact Nat.le_of_eq (by rw [List.length_map, paddedSquare_edges, square_length])
  have CU : Certificate (N width) (polyAdd (polySmul u R) (polyNeg q)) :=
    endpoint_localUpperCertificate hw0 hw1 K width hK n _ _ hsize
  have hmap : RatPolyCoeffEqv
      (productMap (N width) w K (activeBlocks width)
        (polyAdd (polySmul u R) (polyNeg q)))
      (polyAdd (polySmul u PR) (polyNeg Pq)) :=
    (productMap_add (N width) w K (activeBlocks width) _ _).trans
      ((productMap_smul (N width) w K (activeBlocks width) u R).add
        (productMap_neg (N width) w K (activeBlocks width) q))
  have CUP : Certificate (N width) (polyAdd (polySmul u PR) (polyNeg Pq)) :=
    .ofCoeff hmap.symm
      (erasedCertificate (N width) hw0 hw1 K hK (activeBlocks width)
        (activeBlocks_lt width)
        (supported_add (polySmul_supported hR u) (by
          intro t ht
          obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
          exact hq v hv)) CU)
  have hcoeff : RatPolyCoeffEqv
      (polyAdd (polySmul u (polyMul q PR)) (polyNeg (polyMul q Pq)))
      (polyMul q (polyAdd (polySmul u PR) (polyNeg Pq))) := by
    refine ((cap_mul_left u (polyMul q PR)).symm.add (RatPolyCoeffEqv.refl _)).trans ?_
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.var 1) (.var 3))))
      (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))))
      (by decide) (fun | 0 => cap u | 1 => q | 2 => PR | _ => Pq)).trans ?_
    exact (RatPolyCoeffEqv.refl q).mul
      ((cap_mul_left u PR).add (RatPolyCoeffEqv.refl _))
  have C : Certificate (N width)
      (polyAdd (polySmul u (polyMul q PR)) (polyNeg (polyMul q Pq))) :=
    .ofCoeff hcoeff (Q.mul CUP)
  have horder := square_moment_order C
    (oddCentered_supported hw0 hw1 K width hK (n+1) hf)
  have hsource : H width (polyMul (polyMul q Pq) (polyMul psi psi)) ≈ S :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => q | 1 => Pq | _ => polyMul psi psi)))
      (centered_unprojected_square hw0 hw1 K width hK (n+1) hf)
  have hoverlap : H width
      (polyMul (polySmul u (polyMul q PR)) (polyMul psi psi)) ≈ u*U := by
    refine Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left u (polyMul q PR) _)) ?_
    exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (N width) u _)
      (Q'.mul_eqv_congr_left u _ _ (Q'.eqv_refl _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
    (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv hoverlap))

/-- The actual OWN variance floor makes the original centered mass strictly
positive, including the zero-depth predecessor case. -/
theorem paddedSquare_centered_mass_positive : (0 : Q') < S :=
  Q'.mul_pos (oddMass_positive hw0 hw1 K width hK (n+1))
    (Q'.pos_of_lt_of_le (starRatio_positive hw0 hw1)
      (paddedSquare_oddVariance_floor hw0 hw1 K width hK (n+1) scale hwidth))

/-- The retained overlap is strictly positive as a consequence of the
actual upper certificate, not as a hypothesis. -/
theorem paddedSquare_overlap_positive : (0 : Q') < U := by
  have hsu := paddedSquare_original_upper_overlap hw0 hw1 K width hK n scale hwidth
  have hup : (0 : Q') < u*U := Q'.pos_of_lt_of_le
    (paddedSquare_centered_mass_positive hw0 hw1 K width hK n scale hwidth) hsu
  exact right_pos_of_mul_pos (Q'.le_of_lt (localUpper_positive hw0 hw1 _)) hup

/-- The cleared connected inequality implies the simpler positive-mass
comparison needed to prove strict positivity of the computed denominator. -/
theorem paddedSquare_connected_mass_overlap_cleared (hK1 : 1 ≤ K) :
    a*Z*(U*U) ≤ S*D0 := by
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hE : (0 : Q') ≤ E :=
    energy_nonnegative hw0 hw1 K width hK
      (terminalMessage_supported w K width (n+1)) hf
      (terminalMessage_certificate hw0 hw1 K width hK (n+1))
  have hD : (0 : Q') ≤ D0 :=
    paddedSquare_connectedDualMoment_nonnegative hw0 hw1 K width hK n scale hwidth hK1
  have hED : (0 : Q') ≤ E*D0 := Q'.mul_nonneg _ _ hE hD
  have hbound := paddedSquare_energy_connected_overlap_cleared
    hw0 hw1 K width hK n scale hwidth hK1
  have hstep : a*Z*(U*U) ≤ E*D0+a*Z*(U*U) :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hED)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.le_trans' _ _ _ hstep hbound

/-- The projected denominator is genuinely nonzero for every admissible
original depth. Its positivity is deduced, not postulated. -/
theorem paddedSquare_connectedDualMoment_positive (hK1 : 1 ≤ K) :
    (0 : Q') < D0 := by
  have hZ := oddMass_positive hw0 hw1 K width hK (n+1)
  have hU := paddedSquare_overlap_positive hw0 hw1 K width hK n scale hwidth
  have hleft : (0 : Q') < a*Z*(U*U) :=
    Q'.mul_pos (Q'.mul_pos (qpow_positive hw0 _) hZ) (Q'.mul_pos hU hU)
  have hright : (0 : Q') < S*D0 := Q'.pos_of_lt_of_le hleft
    (paddedSquare_connected_mass_overlap_cleared
      hw0 hw1 K width hK n scale hwidth hK1)
  exact right_pos_of_mul_pos
    (Q'.le_of_lt (paddedSquare_centered_mass_positive
      hw0 hw1 K width hK n scale hwidth)) hright

/-- A cleared quantitative floor for the computed connected denominator.
The only cancellation is by the already produced strictly positive S. -/
theorem paddedSquare_connectedDualMoment_floor (hK1 : 1 ≤ K) :
    a*Z*S ≤ (u*u)*D0 := by
  have hS := paddedSquare_centered_mass_positive hw0 hw1 K width hK n scale hwidth
  have hU := paddedSquare_overlap_positive hw0 hw1 K width hK n scale hwidth
  have hu := localUpper_positive hw0 hw1 (4*side scale)
  have hsu := paddedSquare_original_upper_overlap hw0 hw1 K width hK n scale hwidth
  have hProd := Q'.mul_pos hu hU
  have hsq : S*S ≤ (u*U)*(u*U) :=
    Q'.mul_le_mul_of_nonneg hsu hsu (Q'.le_of_lt hProd) (Q'.le_of_lt hS)
  have hsq' : S*S ≤ (u*u)*(U*U) :=
    Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => u | _ => U)))
  have haZ : (0 : Q') < a*Z :=
    Q'.mul_pos (qpow_positive hw0 _) (oddMass_positive hw0 hw1 K width hK (n+1))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (a*Z) hsq'
    (Q'.le_of_lt haZ)
  have hbase := paddedSquare_connected_mass_overlap_cleared
    hw0 hw1 K width hK n scale hwidth hK1
  have hscaledBase := Q'.mul_le_mul_of_nonneg_left _ _ (u*u) hbase
    (Q'.le_of_lt (Q'.mul_pos hu hu))
  have hchain : S*((a*Z)*S) ≤ S*((u*u)*D0) := by
    have hl : S*((a*Z)*S) ≈ (a*Z)*(S*S) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 0)))
        (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 0)))
        (by decide) (fun | 0 => S | 1 => a | _ => Z)
    have hm : (a*Z)*((u*u)*(U*U)) ≈ (u*u)*(a*Z*(U*U)) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
        (.mul (.mul (.var 2) (.var 2))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 3))))
        (by decide) (fun | 0 => a | 1 => Z | 2 => u | _ => U)
    have hr : (u*u)*(S*D0) ≈ S*((u*u)*D0) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 2)))
        (by decide) (fun | 0 => u | 1 => S | _ => D0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hm)
          (Q'.le_trans' _ _ _ hscaledBase (Q'.le_of_eqv hr))))
  exact Q'.le_of_mul_le_mul_left hchain hS

/-- The explicit reciprocal is formed only after the computed denominator
has been proved strictly positive from the original overlap and variance. -/
theorem paddedSquare_connected_gain (hK1 : 1 ≤ K) :
    E+(a*Z*(U*U))*Q'.recipPos D0
      (paddedSquare_connectedDualMoment_positive hw0 hw1 K width hK n scale hwidth hK1) ≤ S := by
  let hD := paddedSquare_connectedDualMoment_positive
    hw0 hw1 K width hK n scale hwidth hK1
  let r := Q'.recipPos D0 hD
  have hclear := paddedSquare_energy_connected_overlap_cleared
    hw0 hw1 K width hK n scale hwidth hK1
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ r hclear
    (Q'.le_of_lt (Q'.recipPos_pos D0 hD))
  have hcancel : D0*r ≈ 1 := Q'.mul_recipPos_eqv D0 hD
  have hl : r*(E*D0+a*Z*(U*U)) ≈ E+(a*Z*(U*U))*r := by
    have hn : r*(E*D0+a*Z*(U*U)) ≈
        (D0*r)*E+(a*Z*(U*U))*r :=
      poly_identity_of_normal_eq
        (.mul (.var 0)
          (.add (.mul (.var 1) (.var 2))
            (.mul (.mul (.var 3) (.var 4)) (.mul (.var 5) (.var 5)))))
        (.add (.mul (.mul (.var 2) (.var 0)) (.var 1))
          (.mul (.mul (.mul (.var 3) (.var 4)) (.mul (.var 5) (.var 5))) (.var 0)))
        (by decide) (fun | 0 => r | 1 => E | 2 => D0 | 3 => a | 4 => Z | _ => U)
    exact Q'.eqv_trans _ _ _ hn
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ E hcancel)
          (Q'.one_mul_eqv E)) (Q'.eqv_refl _))
  have hr : r*(S*D0) ≈ S := by
    have hn : r*(S*D0) ≈ (D0*r)*S :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 2) (.var 0)) (.var 1))
        (by decide) (fun | 0 => r | 1 => S | _ => D0)
    exact Q'.eqv_trans _ _ _ hn
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ S hcancel) (Q'.one_mul_eqv S))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hr))

/-- The computed connected response is a strict finite improvement on the
same original OWN variance; this is not a scale-uniform contraction. -/
theorem paddedSquare_energy_strictly_below_own_variance (hK1 : 1 ≤ K) :
    E < S := by
  let hD := paddedSquare_connectedDualMoment_positive
    hw0 hw1 K width hK n scale hwidth hK1
  have hterm : (0 : Q') <
      (a*Z*(U*U))*Q'.recipPos D0 hD :=
    Q'.mul_pos
      (Q'.mul_pos (Q'.mul_pos (qpow_positive hw0 _)
        (oddMass_positive hw0 hw1 K width hK (n+1)))
        (Q'.mul_pos
          (paddedSquare_overlap_positive hw0 hw1 K width hK n scale hwidth)
          (paddedSquare_overlap_positive hw0 hw1 K width hK n scale hwidth)))
      (Q'.recipPos_pos D0 hD)
  exact lt_of_lt_of_le (lt_add_of_pos_right E _ hterm)
    (paddedSquare_connected_gain hw0 hw1 K width hK n scale hwidth hK1)

end YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_original_upper_overlap
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_centered_mass_positive
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_overlap_positive
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_connected_mass_overlap_cleared
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_connectedDualMoment_positive
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_connectedDualMoment_floor
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_connected_gain
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareConnectedDualGain.paddedSquare_energy_strictly_below_own_variance
