/-
# Qualitative nondegeneracy of the shifted A03 anchor under padding

Companion to `audits/AUDIT-SHIFTED-PADDED-NONDEGENERATE-2026-10-06.md`.

`PathShiftedNondegenerate tr fl` asks for a positive rational floor
`fl_j ≤ R_j(side_j)` at EACH scale `j` separately. Every consumer
(`path_shifted_macroRatio`, `path_shifted_anchor_floor`,
`path_normalized_anchor_shifted`, `path_normalized_anchor_of_windowSurvival`,
`path_shiftedEps_forces_rate`) uses `fl j` only as a positive number at that
same `j` (input to the constructive inverse square root and to division);
no conclusion depends on its size, so a floor that decays in `j` is enough.

This file proves the floor, with no anchor edit, from existing pieces:

* `smoothedResponse_ge_family_response`: the box kernel `timeKernel M` has
  lags `0..M` (ONE-SIDED, weights `1/(M+1)`), so the orbit expansion
  `R_Y(n) = Σ_{m,k ≤ M} (M+1)^(-2) R_x(m+k+n)` has maximal lag `2M+n`, and
  antitonicity (`response_le_of_le`) plus unit kernel mass gives
  `R_x(2M+n) ≤ R_Y(n)`. This is the lag-`n` form of
  `smoothedCoherent_norm_ge_family_response` (`n = 0`).
* `family_time_geometric_floor` (needs `faces ⊆ spatialFaces base`,
  `base < width`): `ρ^L B(x,x) ≤ R_x(L)`.
* `familyExcitation_norm_floor`: `varianceFloor(w)·Σc² ≤ B(x,x)`.

Hence, under the padding hypothesis `PathFacesPadded tr`
(`faces j ⊆ spatialFaces (side_j²)`, one layer inside `trajWidth j = side_j²+1`),

  `ρ_j^(2M_j+side_j) · varianceFloor(w_j) · Σ_p c_j(p)² ≤ R_j(side_j)`.

The floor is exponentially small in `side_j`; it gives nondegeneracy only and
no help with window survival.

A concrete trajectory satisfying the padding is constructed
(`paddedZeroMomentumTrajectory`: dyadic nome schedule, radius factor 1, all
spatial faces of `spatialFaces (side_j²)`, unit coefficients).

No `sorry`, no axioms.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondOrbit

namespace YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq Z4Plane Dir4 dirsOf)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces spatialFaces_nodup spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
  (varianceFloor varianceFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (familyResponseFraction familyResponseFraction_positive)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (responseSum)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
  (familyExcitation familyExcitation_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState
  (smoothingWeight smoothingWeight_nonneg timeKernel kernelMass timeKernel_mass
   smoothedResponse smoothedResponse_orbit_expand)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (boxSum_ge_const response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyBondOrbit (family_time_geometric_floor)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory.DyadicSmoothedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (PathShiftedEpsBound PathShiftedNondegenerate ShiftedAnchorPackage
   path_normalized_anchor_shifted)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival
  (PathShiftedWindowSurvival path_normalized_anchor_of_windowSurvival)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## Local scalar helpers (standard private copies) -/

private theorem pn_pow_pos (a : Q') (ha : (0 : Q') < a) :
    ∀ n : Nat, (0 : Q') < a^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos ha (pn_pow_pos a ha n)

private theorem pn_scale_rational (r v : Q') :
    RCscale r (Rq v) = Rq (r*v) :=
  Quotient.sound (CRealAlg.ofQ'_mul r v).symm

private theorem pn_lt_of_lt_of_le {a b c : Q'} (hab : a < b) (hbc : b ≤ c) : a < c := by
  have habCross : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have hbcCross : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hfirst :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (b.num * (a.den : Int)) * (c.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right habCross
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hreorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (b.num * (a.den : Int)) * (c.den : Int) ≤
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right hbcCross
      (by exact_mod_cast Nat.zero_le a.den : (0 : Int) ≤ (a.den : Int))
    have hleft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    have hright :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hleft, hright] at hscaled
  have hcombined := Int.lt_of_lt_of_le hfirst hsecond
  exact Int.lt_of_mul_lt_mul_right hcombined
    (by exact_mod_cast Nat.zero_le b.den : (0 : Int) ≤ (b.den : Int))

private theorem pn_listQSum_nonneg {A : Type} (f : A → Q') (hf : ∀ x, (0 : Q') ≤ f x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum f xs
  | [] => Q'.le_refl' 0
  | x :: xs => Q'.zero_le_add _ _ (hf x) (pn_listQSum_nonneg f hf xs)

/-! ## 1. Lag-`n` domination by the unsmoothed family (one-sided box kernel) -/

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)
  (qs : List Z4Plaq) (c : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "x0" => Subtype.val (familyExcitation hw0 hw1 width qs c hqs)

/-- `R_x(2M+n) ≤ R_Y(n)`. The kernel `timeKernel M` has lags `0..M`
(one-sided), so every orbit term `R_x(m+k+n)` has `m+k+n ≤ 2M+n`; antitone
responses and unit kernel mass give the bound. `n = 0` is
`smoothedCoherent_norm_ge_family_response`. -/
theorem smoothedResponse_ge_family_response (M n : Nat) :
    RCle (B x0 (T (2*M+n) x0)) (smoothedResponse hw0 hw1 width qs c hqs M n) := by
  have hr := smoothingWeight_nonneg M
  rw [smoothedResponse_orbit_expand hw0 hw1 width qs c hqs M n]
  have hinner : ∀ m, m ≤ M →
      RCle (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M+n) x0)))
        (responseSum (timeKernel M) (fun k => B x0 (T (m+k+n) x0))) := fun m hm =>
    boxSum_ge_const hr (fun k => B x0 (T (m+k+n) x0)) _ M
      (fun k hk => response_le_of_le hw0 hw1 width x0 (by omega : m+k+n ≤ 2*M+n))
  have houter : RCle (RCscale (kernelMass (timeKernel M))
        (RCscale (kernelMass (timeKernel M)) (B x0 (T (2*M+n) x0))))
      (responseSum (timeKernel M)
        (fun m => responseSum (timeKernel M) (fun k => B x0 (T (m+k+n) x0)))) :=
    boxSum_ge_const hr _ _ M hinner
  have hm := timeKernel_mass M
  have hmm : kernelMass (timeKernel M) * kernelMass (timeKernel M) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hm)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.one_mul_eqv 1))
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hmm, RCscale_one] at houter
  exact houter

end Generic

/-! ## 2. The padded path floor -/

/-- Padding: every face of `Y_j` lies one layer inside the carrier,
`faces j ⊆ spatialFaces (side_j²)` while `trajWidth j = side_j² + 1`. -/
def PathFacesPadded (tr : DyadicSmoothedTrajectory) : Prop :=
  ∀ j p, p ∈ tr.faces j → p ∈ spatialFaces (side j * side j)

/-- The per-scale floor `ρ_j^(2M_j+side_j) · varianceFloor(w_j) · Σ_p c_j(p)²`,
`ρ_j = familyResponseFraction(w_j, |faces j|)`. Exponentially small in `side_j`. -/
def paddedNondegFloor (tr : DyadicSmoothedTrajectory) (j : Nat) : Q' :=
  familyResponseFraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.faces j).length ^ (2 * tr.radius j + side j) *
    (varianceFloor (tr.schedule.nome j) (tr.schedule.nome_pos j) *
      listQSum (fun face => tr.coeff j face * tr.coeff j face) (tr.faces j))

theorem paddedNondegFloor_pos (tr : DyadicSmoothedTrajectory) :
    ∀ j, (0 : Q') < paddedNondegFloor tr j := fun j =>
  Q'.mul_pos
    (pn_pow_pos _ (familyResponseFraction_positive (tr.schedule.nome_pos j)
      (tr.schedule.nome_lt_one j) _) _)
    (Q'.mul_pos (varianceFloor_positive (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j))
      (tr.coeff_mass_pos j))

/-- **`PathShiftedNondegenerate` for the current `Y_j` under padding.** -/
theorem pathShiftedNondegenerate_of_padded (tr : DyadicSmoothedTrajectory)
    (hpad : PathFacesPadded tr) :
    PathShiftedNondegenerate tr (paddedNondegFloor tr) := by
  intro j
  have hw0 := tr.schedule.nome_pos j
  have hw1 := tr.schedule.nome_lt_one j
  have hpow : (0 : Q') ≤ familyResponseFraction hw0 hw1 (tr.faces j).length ^
      (2 * tr.radius j + side j) :=
    Q'.le_of_lt (pn_pow_pos _ (familyResponseFraction_positive hw0 hw1 _) _)
  have h1 := RCscale_mono hpow
    (familyExcitation_norm_floor hw0 hw1 (trajWidth j) (tr.faces j) (tr.coeff j)
      (tr.faces_spatial j) (tr.faces_nodup j))
  rw [pn_scale_rational] at h1
  have h2 := family_time_geometric_floor hw0 hw1 (trajWidth_ratio j) (tr.faces j)
    (tr.coeff j) (hpad j) (2 * tr.radius j + side j)
  have h3 := smoothedResponse_ge_family_response hw0 hw1 (trajWidth j) (tr.faces j)
    (tr.coeff j) (tr.faces_spatial j) (tr.radius j) (side j)
  exact RCle_trans h1 (RCle_trans h2 h3)

/-- **Shifted A03 package from window survival and padding** (window survival
remains the single OPEN input). -/
theorem path_normalized_anchor_of_windowSurvival_padded (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (hpad : PathFacesPadded tr) (Hw : PathShiftedWindowSurvival tr theta) :
    ShiftedAnchorPackage tr delta hdelta a (paddedNondegFloor tr) (paddedNondegFloor_pos tr) :=
  path_normalized_anchor_of_windowSurvival tr c0 theta delta a ha h0 h1 hc0 hc1 hdelta0 hdelta
    hcd (paddedNondegFloor tr) (paddedNondegFloor_pos tr) Hw
    (pathShiftedNondegenerate_of_padded tr hpad)

/-- Same, from the shifted H1 directly. -/
theorem path_normalized_anchor_shifted_padded (tr : DyadicSmoothedTrajectory) (c0 delta : Q')
    (a : Nat) (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta)
    (hpad : PathFacesPadded tr) (H1s : PathShiftedEpsBound tr c0) :
    ShiftedAnchorPackage tr delta hdelta a (paddedNondegFloor tr) (paddedNondegFloor_pos tr) :=
  path_normalized_anchor_shifted tr c0 delta a ha hdelta0 hdelta hc0 (paddedNondegFloor tr)
    (paddedNondegFloor_pos tr) H1s (pathShiftedNondegenerate_of_padded tr hpad)

/-! ## 3. A concrete padded trajectory (padding is satisfiable) -/

private theorem pn_unit_mass_pos {A : Type} (a : A) :
    ∀ xs : List A, a ∈ xs → (0 : Q') < listQSum (fun _ => (1 : Q') * 1) xs
  | [], h => nomatch h
  | _ :: xs, _ =>
      pn_lt_of_lt_of_le (by decide : (0 : Q') < 1 * 1)
        (Q'.add_le_self_of_nonneg _ _
          (pn_listQSum_nonneg _ (fun _ => (by decide : (0 : Q') ≤ 1 * 1)) xs))

/-- The origin `(x0,x1)` plaquette is a spatial face at every positive width. -/
theorem origin_face_mem (s : Nat) (hs : 0 < s) :
    (((0, 0, 0, 0), Z4Plane.p01) : Z4Plaq) ∈ spatialFaces s :=
  (spatialFaces_mem_iff s _).mpr ⟨hs, hs, hs, rfl, by decide⟩

/-- Concrete trajectory: dyadic nome schedule `w_j = 1 - 2^-(j+1)`, radius
factor 1 (`M_j = side_j`), faces = ALL spatial faces of `spatialFaces (side_j²)`
(the zero-momentum sum over the padded interior), unit coefficients. -/
def paddedZeroMomentumTrajectory : DyadicSmoothedTrajectory where
  schedule := dyadicNomeSchedule
  radiusFactor := 1
  radiusFactor_pos := Nat.one_pos
  faces := fun j => spatialFaces (side j * side j)
  coeff := fun _ _ => 1
  faces_spatial := fun j _ hp => spatialFaces_mono (Nat.le_of_lt (trajWidth_ratio j)) hp
  faces_nodup := fun j => spatialFaces_nodup (side j * side j)
  coeff_mass_pos := fun j => pn_unit_mass_pos _ _
    (origin_face_mem _ (Nat.mul_pos (side_positive j) (side_positive j)))

theorem paddedZeroMomentum_padded : PathFacesPadded paddedZeroMomentumTrajectory :=
  fun _ _ hp => hp

/-- Nondegeneracy holds on the concrete padded trajectory. -/
theorem paddedZeroMomentum_nondegenerate :
    PathShiftedNondegenerate paddedZeroMomentumTrajectory
      (paddedNondegFloor paddedZeroMomentumTrajectory) :=
  pathShiftedNondegenerate_of_padded _ paddedZeroMomentum_padded

end YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate

#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.smoothedResponse_ge_family_response
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.PathFacesPadded
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.paddedNondegFloor
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.paddedNondegFloor_pos
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.pathShiftedNondegenerate_of_padded
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.path_normalized_anchor_of_windowSurvival_padded
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.path_normalized_anchor_shifted_padded
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.origin_face_mem
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.paddedZeroMomentumTrajectory
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.paddedZeroMomentum_padded
#print axioms YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate.paddedZeroMomentum_nondegenerate
