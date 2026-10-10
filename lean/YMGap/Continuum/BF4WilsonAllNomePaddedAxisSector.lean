/-
# The actual padded all-face state lies in the spatial-axis even sector

The x1/x2 swap permutes the complete list of physical spatial faces, including
the reversed p12 boundary. The ordered source-character pin identifies each
swapped face on the SAME original all-nome Wilson completion. We carry this
identity through the already constructed unit centering and the literal BOX
orbit sum. The result applies to the moving AF trajectory, including scale zero.

This is a sector statement only. It supplies no late-response, relative-energy,
mass-gap, or continuum estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
import YMGap.Continuum.BF4WilsonAllNomeCenteringPin

namespace YMGap.Continuum.BF4WilsonAllNomePaddedAxisSector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
  (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
  (swapPlaquette swapPlaquette_spatialFaces_mem_iff swap_spatialFaces_perm)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
  (familyState familyExpression)
open YMGap.Continuum.BF4WilsonAllNomeOriginPlaquetteOrbitResponse
  (faceVector axis_faceVector faceExpression)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion embed completedInner unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSmul completedZero completedNeg completedSub)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedAdd_comm completedZero_add completedAdd_zero
    completedNeg_add completedSmul_one completedSmul_zero completedSmul_mul
    completedSmul_congr)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (orbitSum completedTime_zero_element)
open YMGap.Continuum.BF4WilsonAllNomeWindowPins
  (embedWindow embedWindow_zero completedAdd_embedWindow completedSmul_embedWindow)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
  (unitProjection unitProjection_pairing centeredPart)
open YMGap.Continuum.BF4WilsonAllNomeCenteringPin (centeredPart_embed)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (familyExcitation)
open YMGap.Continuum.BF4WilsonAllNomeSmoothedCoherentState (smoothedCoherentVector)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
  (trajWidth DyadicSmoothedTrajectory)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afPaddedZeroMomentumTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion
  (completedSwap completedSwap_embed completedSwap_add completedSwap_smul
    completedSwap_sub completedSwap_zero completedSwap_unit completedSwap_time
    completedInner_swap_balance evenPart evenPart_detector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (completed_eq_of_pairings)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "U" => completedSwap hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "B" => completedInner hw0 hw1

private def actualFace (p : Z4Plaq) : V :=
  if hp : p ∈ spatialFaces width then faceVector hw0 hw1 p hp else Z

private def faceSum (f : Z4Plaq → V) : List Z4Plaq → V
  | [] => Z
  | p :: ps => A (f p) (faceSum f ps)

private theorem faceSum_perm (f : Z4Plaq → V) {ps qs : List Z4Plaq}
    (hp : ps.Perm qs) : faceSum hw0 hw1 f ps = faceSum hw0 hw1 f qs := by
  induction hp with
  | nil => rfl
  | cons p _ ih => exact congrArg (A (f p)) ih
  | swap p q ps =>
      change A (f q) (A (f p) (faceSum hw0 hw1 f ps)) =
        A (f p) (A (f q) (faceSum hw0 hw1 f ps))
      rw [← completedAdd_assoc, completedAdd_comm hw0 hw1 (f q) (f p),
        completedAdd_assoc]
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem actualFace_swap (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    U (actualFace hw0 hw1 (width := width) p) =
      actualFace hw0 hw1 (width := width) (swapPlaquette p) := by
  have hs : swapPlaquette p ∈ spatialFaces width :=
    (swapPlaquette_spatialFaces_mem_iff width p).mpr hp
  simp only [actualFace, dif_pos hp, dif_pos hs]
  exact axis_faceVector hw0 hw1 p hp

private theorem faceSum_swap (ps : List Z4Plaq)
    (hps : ∀ p, p ∈ ps → p ∈ spatialFaces width) :
    U (faceSum hw0 hw1 (width := width)
      (actualFace hw0 hw1 (width := width)) ps) =
      faceSum hw0 hw1 (width := width)
        (actualFace hw0 hw1 (width := width)) (ps.map swapPlaquette) := by
  induction ps with
  | nil => exact completedSwap_zero hw0 hw1
  | cons p ps ih =>
      change U (A (actualFace hw0 hw1 p)
          (faceSum hw0 hw1 (actualFace hw0 hw1) ps)) =
        A (actualFace hw0 hw1 (swapPlaquette p))
          (faceSum hw0 hw1 (actualFace hw0 hw1) (ps.map swapPlaquette))
      rw [completedSwap_add, actualFace_swap hw0 hw1 p (hps p List.mem_cons_self),
        ih (fun q hq => hps q (List.mem_cons_of_mem p hq))]

private theorem familyValue_nil
    (hqs : ∀ p, p ∈ ([] : List Z4Plaq) → p ∈ spatialFaces width) :
    embed hw0 hw1 (familyState width [] (fun _ => 1) hqs) = Z := by
  change embedWindow hw0 hw1 0 (.smul 0 .one) True.intro = Z
  exact embedWindow_zero hw0 hw1 0

private theorem familyValue_cons (p : Z4Plaq) (ps : List Z4Plaq)
    (hqs : ∀ q, q ∈ p :: ps → q ∈ spatialFaces width) :
    embed hw0 hw1 (familyState width (p :: ps) (fun _ => 1) hqs) =
      A (faceVector hw0 hw1 p (hqs p List.mem_cons_self))
        (embed hw0 hw1 (familyState width ps (fun _ => 1)
          (fun q hq => hqs q (List.mem_cons_of_mem p hq)))) := by
  change embedWindow hw0 hw1 0
      (.add (.smul 1 (.loop 0
        (BF4ExactSlabFixedSpatialWilsonPlaquette.plaquetteLoop p
          (hqs p List.mem_cons_self)) 1))
        (familyExpression width ps (fun _ => 1)
          (fun q hq => hqs q (List.mem_cons_of_mem p hq)))) _ = _
  rw [← completedAdd_embedWindow, ← completedSmul_embedWindow,
    completedSmul_one]
  rfl

private theorem familyValue_sum (ps : List Z4Plaq)
    (hps : ∀ p, p ∈ ps → p ∈ spatialFaces width) :
    embed hw0 hw1 (familyState width ps (fun _ => 1) hps) =
      faceSum hw0 hw1 (actualFace hw0 hw1) ps := by
  induction ps with
  | nil => exact familyValue_nil hw0 hw1 hps
  | cons p ps ih =>
      rw [familyValue_cons hw0 hw1 p ps hps]
      change A (faceVector hw0 hw1 p (hps p List.mem_cons_self))
          (embed hw0 hw1 (familyState width ps (fun _ => 1)
            (fun q hq => hps q (List.mem_cons_of_mem p hq)))) =
        A (actualFace hw0 hw1 p)
          (faceSum hw0 hw1 (actualFace hw0 hw1) ps)
      rw [ih (fun q hq => hps q (List.mem_cons_of_mem p hq))]
      simp only [actualFace, dif_pos (hps p List.mem_cons_self)]

/-- Every all-unit spatial-face family, including the empty base-zero list,
is fixed by the actual swap on the padded or unpadded ORIGINAL completion. -/
theorem allFace_raw_even (base : Nat) (hbase : base ≤ width) :
    U (embed hw0 hw1 (familyState width (spatialFaces base) (fun _ => 1)
      (fun p hp => spatialFaces_mono hbase hp))) =
      embed hw0 hw1 (familyState width (spatialFaces base) (fun _ => 1)
        (fun p hp => spatialFaces_mono hbase hp)) := by
  let hqs : ∀ p, p ∈ spatialFaces base → p ∈ spatialFaces width :=
    fun p hp => spatialFaces_mono hbase hp
  change U (embed hw0 hw1 (familyState width (spatialFaces base) (fun _ => 1) hqs)) =
    embed hw0 hw1 (familyState width (spatialFaces base) (fun _ => 1) hqs)
  rw [familyValue_sum hw0 hw1 (spatialFaces base) hqs,
    faceSum_swap hw0 hw1 (spatialFaces base) hqs]
  exact faceSum_perm hw0 hw1 (actualFace hw0 hw1)
    (swap_spatialFaces_perm base)

private theorem unitProjection_swap (x : V) :
    U (unitProjection hw0 hw1 x) = unitProjection hw0 hw1 (U x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [completedInner_swap_balance, unitProjection_pairing,
    unitProjection_pairing]
  have hz : B (unitState hw0 hw1 width) (U z) =
      B (unitState hw0 hw1 width) z := by
    rw [← completedInner_swap_balance, completedSwap_unit]
  have hx : B (U x) (unitState hw0 hw1 width) =
      B x (unitState hw0 hw1 width) := by
    rw [completedInner_swap_balance, completedSwap_unit]
  rw [hz, hx]

private theorem centeredPart_swap (x : V) :
    U (centeredPart hw0 hw1 x) = centeredPart hw0 hw1 (U x) := by
  unfold centeredPart
  rw [completedSwap_sub, unitProjection_swap]

/-- The actual centered all-face family retains its original unit projection. -/
theorem allFace_centered_even (base : Nat) (hbase : base ≤ width) :
    U (familyExcitation hw0 hw1 width (spatialFaces base) (fun _ => 1)
      (fun _ hp => spatialFaces_mono hbase hp)).val =
      (familyExcitation hw0 hw1 width (spatialFaces base) (fun _ => 1)
        (fun _ hp => spatialFaces_mono hbase hp)).val := by
  let x := familyState width (spatialFaces base) (fun _ => 1)
    (fun _ hp => spatialFaces_mono hbase hp)
  change U (BF4WilsonAllNomeCenteredVector.centeredVector hw0 hw1 x) =
    BF4WilsonAllNomeCenteredVector.centeredVector hw0 hw1 x
  calc
    U (BF4WilsonAllNomeCenteredVector.centeredVector hw0 hw1 x) =
        U (centeredPart hw0 hw1 (embed hw0 hw1 x)) :=
      congrArg U (centeredPart_embed hw0 hw1 x).symm
    _ = centeredPart hw0 hw1 (U (embed hw0 hw1 x)) :=
      centeredPart_swap hw0 hw1 (embed hw0 hw1 x)
    _ = centeredPart hw0 hw1 (embed hw0 hw1 x) :=
      congrArg (centeredPart hw0 hw1) (allFace_raw_even hw0 hw1 base hbase)
    _ = BF4WilsonAllNomeCenteredVector.centeredVector hw0 hw1 x :=
      centeredPart_embed hw0 hw1 x

private theorem orbitSum_swap (x : V) (cs : List (Q' × Nat)) :
    U (orbitSum hw0 hw1 x cs) = orbitSum hw0 hw1 (U x) cs := by
  induction cs with
  | nil => exact completedSwap_zero hw0 hw1
  | cons a cs ih =>
      rcases a with ⟨c,n⟩
      change U (A (completedSmul hw0 hw1 c (completedTime hw0 hw1 n x))
        (orbitSum hw0 hw1 x cs)) =
        A (completedSmul hw0 hw1 c (completedTime hw0 hw1 n (U x)))
          (orbitSum hw0 hw1 (U x) cs)
      rw [completedSwap_add, completedSwap_smul, completedSwap_time, ih]

private theorem smul_zero_element (c : Q') : completedSmul hw0 hw1 c Z = Z := by
  calc
    completedSmul hw0 hw1 c Z =
        completedSmul hw0 hw1 c (completedSmul hw0 hw1 0 Z) :=
      congrArg (completedSmul hw0 hw1 c) (completedSmul_zero hw0 hw1 Z).symm
    _ = completedSmul hw0 hw1 (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = completedSmul hw0 hw1 0 Z :=
      completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv c) Z
    _ = Z := completedSmul_zero hw0 hw1 Z

/-- The time filter is the literal BOX orbit sum, not a single transfer step. -/
theorem allFace_smoothed_even (base : Nat) (hbase : base ≤ width) (M : Nat) :
    U (smoothedCoherentVector hw0 hw1 width (spatialFaces base) (fun _ => 1)
      (fun _ hp => spatialFaces_mono hbase hp) M) =
      smoothedCoherentVector hw0 hw1 width (spatialFaces base) (fun _ => 1)
        (fun _ hp => spatialFaces_mono hbase hp) M := by
  unfold smoothedCoherentVector
  rw [orbitSum_swap, allFace_centered_even hw0 hw1 base hbase]

/-- Unconditional sector pin for the moving AF family at every scale. -/
theorem afPadded_state_even (j : Nat) :
    completedSwap (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j)
      (afPaddedZeroMomentumTrajectory.state j) =
        afPaddedZeroMomentumTrajectory.state j := by
  change completedSwap (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j)
      (smoothedCoherentVector (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
        (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j)
        (trajWidth j) (spatialFaces (side j * side j)) (fun _ => 1)
        (fun p hp => spatialFaces_mono (Nat.le_of_lt
          (BF4WilsonAllNomeDyadicSmoothedTrajectory.trajWidth_ratio j)) hp)
        (afPaddedZeroMomentumTrajectory.radius j)) = _
  exact allFace_smoothed_even _ _ (side j * side j)
    (Nat.le_of_lt (BF4WilsonAllNomeDyadicSmoothedTrajectory.trajWidth_ratio j))
    (afPaddedZeroMomentumTrajectory.radius j)

/-- Every completed test has the same detector after even projection. -/
theorem afPadded_evenPart_detector (j : Nat)
    (v : Completion (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j) (trajWidth j)) :
    completedInner (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j)
      (afPaddedZeroMomentumTrajectory.state j)
      (evenPart (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
        (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j) v) =
    completedInner (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j)
      (afPaddedZeroMomentumTrajectory.state j) v :=
  evenPart_detector _ _ _ v (afPadded_state_even j)

/-- Every lag of the actual AF state is orthogonal to any swap-odd completed
test vector. No late-response or positive norm for that test is asserted. -/
theorem afPadded_odd_lag_zero (j n : Nat)
    (v : Completion (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j) (trajWidth j))
    (hv : completedSwap (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j) v =
      completedNeg (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
        (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j) v) :
    completedInner (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
      (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j)
      (afPaddedZeroMomentumTrajectory.state j)
      (completedTime (afPaddedZeroMomentumTrajectory.schedule.nome_pos j)
        (afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j) n v) = RCzero := by
  let hw0 := afPaddedZeroMomentumTrajectory.schedule.nome_pos j
  let hw1 := afPaddedZeroMomentumTrajectory.schedule.nome_lt_one j
  let x := afPaddedZeroMomentumTrajectory.state j
  have heven : evenPart hw0 hw1 v = completedZero hw0 hw1 (trajWidth j) := by
    unfold evenPart
    rw [hv, show completedAdd hw0 hw1 v (completedNeg hw0 hw1 v) =
      completedZero hw0 hw1 (trajWidth j) from
        (completedAdd_comm hw0 hw1 v (completedNeg hw0 hw1 v)).trans
          (completedNeg_add hw0 hw1 v)]
    exact smul_zero_element hw0 hw1 _
  have htime : evenPart hw0 hw1 (completedTime hw0 hw1 n v) =
      completedZero hw0 hw1 (trajWidth j) := by
    rw [BF4WilsonAllNomeSpatialAxisSwapCompletion.evenPart_time,
      heven, completedTime_zero_element]
  have hdet := evenPart_detector hw0 hw1 x (completedTime hw0 hw1 n v)
    (afPadded_state_even j)
  rw [htime,
    BF4WilsonAllNomeBilinearTime.completedInner_zero_right] at hdet
  exact hdet.symm

#print axioms allFace_raw_even
#print axioms allFace_centered_even
#print axioms allFace_smoothed_even
#print axioms afPadded_state_even
#print axioms afPadded_evenPart_detector
#print axioms afPadded_odd_lag_zero

end YMGap.Continuum.BF4WilsonAllNomePaddedAxisSector
