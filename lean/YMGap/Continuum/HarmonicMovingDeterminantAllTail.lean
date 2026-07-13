/-
Symbolic all-tail normal form for the coupled moving determinant.

Unlike the boundary files, this module performs no finite-scale evaluation.
It exposes the normalized slack at an arbitrary scale as a three-scale theta
carrier.  The favorable coefficient is the exact normalized spacing gain;
the unfavorable coefficient is its complement inside the rotated-shell
fraction.  This is the form in which a uniform cutoff-tail modulus can be
composed without splitting the signed mass cross into pointwise cells.
-/

import YMGap.Continuum.HarmonicMovingDeterminantK38

namespace YMGap.Continuum.HarmonicMovingDeterminantAllTail

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionUTuranTrunc
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicMovingDeterminantRecurrence
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Exact arbitrary-scale coefficients -/

/-- The cutoff-normalized spacing decrease. -/
def normalizedSpacingGain (k : Nat) : Q' :=
  movingCutoffScale k *
    (harmonicSpacing k - harmonicSpacing (k + 1))

/-- What remains of the rotated-shell fraction after paying the exact
normalized spacing gain. -/
def normalizedDemandCoeff (k : Nat) : Q' :=
  shellDropFraction - normalizedSpacingGain k

/-- Closed rational presentation of the normalized spacing gain. -/
def normalizedSpacingGainClosed (k : Nat) : Q' :=
  Q'.ofNat (2 * (k + 2) + 1) *
    unit ((k + 3) * (k + 3)) (Nat.mul_pos (by omega) (by omega))

/-- One copy of the arbitrary-scale normalized boundary carrier. -/
def allTailBoundaryCore (k : Nat) : Q' :=
  (shellDropFraction * (harmonicD (k + 1) - harmonicA (k + 1))) * harmonicD k -
    (normalizedDemandCoeff k * (harmonicD k - harmonicA k)) * harmonicD (k + 1)

/-- The doubled carrier, matching `normalizedGlobalSlack`. -/
def allTailBoundaryForm (k : Nat) : Q' :=
  allTailBoundaryCore k + allTailBoundaryCore k

private theorem ofNat_mul_unit_eqv_one (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * unit n hn ≈ (1 : Q') := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one,
    Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

theorem movingCutoffScale_mul_spacing (k : Nat) :
    movingCutoffScale k * harmonicSpacing k ≈ (1 : Q') := by
  unfold movingCutoffScale harmonicSpacing
  exact ofNat_mul_unit_eqv_one (Ncut k) (Ncut_pos k)

private theorem int_succ_sq_sub_sq (m : Int) :
    (m + 1) * (m + 1) + -(m * m) = 2 * m + 1 := by
  rw [Int.add_mul, Int.mul_add]
  omega

theorem normalizedSpacingGain_eq_closed (k : Nat) :
    normalizedSpacingGain k ≈ normalizedSpacingGainClosed k := by
  unfold normalizedSpacingGain normalizedSpacingGainClosed movingCutoffScale
    harmonicSpacing Ncut unit
  change Q'.ofNat ((k + 2) * (k + 2)) *
      (Q'.mkPos 1 ((k + 2) * (k + 2)) _ +
        -(Q'.mkPos 1 ((k + 3) * (k + 3)) _)) ≈
    Q'.ofNat (2 * (k + 2) + 1) *
      Q'.mkPos 1 ((k + 3) * (k + 3)) _
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.add_mul,
    Int.neg_mul, Int.mul_neg, Int.one_mul, Int.mul_one]
  push_cast
  let m : Int := (k : Int) + 2
  change m * m * ((m + 1) * (m + 1) + -(m * m)) *
      ((m + 1) * (m + 1)) =
    (2 * m + 1) * (m * m * ((m + 1) * (m + 1)))
  rw [int_succ_sq_sub_sq]
  ac_rfl

/-- The diagonal normalizer grows along the harmonic schedule.  The proof is
termwise on the retained common window and then uses positivity of the newly
added cutoff shell. -/
theorem harmonicD_mono_step (k : Nat) : harmonicD k ≤ harmonicD (k + 1) := by
  let f := fun i => coeffW (harmW k) i * coeffW (harmW k) i
  let g := fun i => coeffW (harmW (k + 1)) i * coeffW (harmW (k + 1)) i
  have hterm : ∀ i, f i ≤ g i := by
    intro i
    dsimp only [f, g]
    exact Q'.mul_le_mul_of_nonneg
      (FusedAmplitudeDerivation.coeffW_mono_w
        (harmW_nonneg k) (HarmonicDriftAntisymmetry.harmW_mono_step k) i)
      (FusedAmplitudeDerivation.coeffW_mono_w
        (harmW_nonneg k) (HarmonicDriftAntisymmetry.harmW_mono_step k) i)
      (coeffW_nonneg (harmW_nonneg (k + 1)) i)
      (coeffW_nonneg (harmW_nonneg k) i)
  have hcommon : fsum f (Ncut k + 1) ≤ fsum g (Ncut k + 1) :=
    FusedAmplitudeDerivation.fsum_le_fsum' hterm (Ncut k + 1)
  have hcut : fsum g (Ncut k + 1) ≤ fsum g (Ncut (k + 1) + 1) := by
    apply fsum_le_extend
    · intro i
      dsimp only [g]
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg (k + 1)) i)
        (coeffW_nonneg (harmW_nonneg (k + 1)) i)
    · unfold Ncut
      exact Nat.add_le_add_right
        (Nat.mul_le_mul (by omega) (by omega)) 1
  unfold harmonicD coordNormSq
  dsimp only [f, g] at hcommon hcut
  exact Q'.le_trans' _ _ _ hcommon hcut

/-! ## 2. Cancellation-preserving algebra -/

private theorem collect_twice_plus_algebra
    (C E d D r X s : Q') :
    C * ((((E * d) * D) + -((r * X) * s)) +
      (((E * d) * D) + -((r * X) * s))) ≈
    (((((C * d) * E) * D)) + -((((C * s) * r) * X))) +
      (((((C * d) * E) * D)) + -((((C * s) * r) * X))) := by
  ring_qeqv

private theorem quotient_cross_cancel (D0 A0 D1 A1 : Q') :
    (D0 - A0) * D1 + -((D1 - A1) * D0) ≈
      A1 * D0 + -(A0 * D1) := by
  have hleft : (D0 - A0) * D1 ≈ D0 * D1 + -(A0 * D1) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv D0 (-A0) D1) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv A0 D1)
  have hright : -((D1 - A1) * D0) ≈ -(D1 * D0) + A1 * D0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_mul_eqv D1 (-A1) D0)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (D1 * D0) ((-A1) * D0)) ?_
    refine Q'.add_eqv_congr_left (-(D1 * D0)) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv A1 D0)) ?_
    exact Q'.neg_neg_eqv (A1 * D0)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hleft hright) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_interchange (D0 * D1) (-(A0 * D1))
      (-(D1 * D0)) (A1 * D0)) ?_
  have hcancel : D0 * D1 + -(D1 * D0) ≈ (0 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (D0 * D1) _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv D1 D0))) ?_
    exact Q'.add_neg_self_eqv (D0 * D1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hcancel) ?_
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
  exact Q'.add_comm_eqv (-(A0 * D1)) (A1 * D0)

private theorem signed_three_reorder (a b c : Q') :
    (a + -b) + c ≈ c + (-b + a) := by
  ring_qeqv

private theorem weighted_cross_regroup
    (r g U V X : Q') (hX : X ≈ U - V) :
    g * U - r * X ≈ r * V - ((r - g) * U) := by
  let a := g * U
  let b := r * U
  let c := r * V
  have hmulX : r * X ≈ b + -c := by
    refine Q'.eqv_trans _ (r * (U - V)) _
      (Q'.mul_eqv_congr_left r _ _ hX) ?_
    refine Q'.eqv_trans _ (r * U + r * (-V)) _
      (Q'.mul_add_eqv r U (-V)) ?_
    exact Q'.add_eqv_congr_left (r * U) _ _ (Q'.mul_neg_eqv r V)
  have hnegX : -(r * X) ≈ -b + c := by
    refine Q'.eqv_trans _ (-(b + -c)) _
      (Q'.neg_eqv_congr _ _ hmulX) ?_
    refine Q'.eqv_trans _ (-b + -(-c)) _
      (Q'.neg_add_eqv b (-c)) ?_
    exact Q'.add_eqv_congr_left (-b) _ _ (Q'.neg_neg_eqv c)
  have hleft : g * U - r * X ≈ (a + -b) + c := by
    refine Q'.eqv_trans _ (a + (-b + c)) _
      (Q'.add_eqv_congr_left a _ _ hnegX) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv a (-b) c)
  have hmulRG : (r - g) * U ≈ b + -a := by
    refine Q'.eqv_trans _ (r * U + (-g) * U) _
      (Q'.add_mul_eqv r (-g) U) ?_
    exact Q'.add_eqv_congr_left (r * U) _ _ (Q'.neg_mul_eqv g U)
  have hnegRG : -((r - g) * U) ≈ -b + a := by
    refine Q'.eqv_trans _ (-(b + -a)) _
      (Q'.neg_eqv_congr _ _ hmulRG) ?_
    refine Q'.eqv_trans _ (-b + -(-a)) _
      (Q'.neg_add_eqv b (-a)) ?_
    exact Q'.add_eqv_congr_left (-b) _ _ (Q'.neg_neg_eqv a)
  have hright : r * V - ((r - g) * U) ≈ c + (-b + a) :=
    Q'.add_eqv_congr_left c _ _ hnegRG
  exact Q'.eqv_trans _ ((a + -b) + c) _ hleft
    (Q'.eqv_trans _ (c + (-b + a)) _
      (signed_three_reorder a b c) (Q'.eqv_symm hright))

private theorem cross_regroup_plus_algebra
    (D0 A0 D1 A1 r g : Q') :
    let L := (g * (D0 + -A0)) * D1 +
      -(r * ((A1 * D0) + -(A0 * D1)))
    let R := (r * (D1 + -A1)) * D0 +
      -(((r + -g) * (D0 + -A0)) * D1)
    L + L ≈ R + R := by
  dsimp only
  let U := (D0 + -A0) * D1
  let V := (D1 + -A1) * D0
  let X := (A1 * D0) + -(A0 * D1)
  have hX : X ≈ U - V := by
    dsimp only [U, V, X]
    exact Q'.eqv_symm (quotient_cross_cancel D0 A0 D1 A1)
  have hone :
      (g * (D0 + -A0)) * D1 +
          -(r * ((A1 * D0) + -(A0 * D1))) ≈
        (r * (D1 + -A1)) * D0 +
          -(((r + -g) * (D0 + -A0)) * D1) := by
    refine Q'.eqv_trans _ (g * U - r * X) _ ?_ ?_
    · dsimp only [U, X]
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_assoc_eqv g (D0 + -A0) D1)
    refine Q'.eqv_trans _ (r * V - ((r - g) * U)) _
      (weighted_cross_regroup r g U V X hX) ?_
    dsimp only [U, V]
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_assoc_eqv r (D1 + -A1) D0))
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (r - g) (D0 + -A0) D1)))
  exact Q'.add_eqv_congr' hone hone

private theorem normalized_boundary_algebra
    (C s t D0 A0 D1 A1 r g c : Q')
    (hgap : C * (s - t) ≈ g) (hunit : C * s ≈ (1 : Q'))
    (hc : r - g ≈ c) :
    C *
        ((((D0 - A0) * (s - t)) * D1 -
            (r * (A1 * D0 - A0 * D1)) * s) +
          (((D0 - A0) * (s - t)) * D1 -
            (r * (A1 * D0 - A0 * D1)) * s)) ≈
      (((r * (D1 - A1)) * D0 - (c * (D0 - A0)) * D1) +
        ((r * (D1 - A1)) * D0 - (c * (D0 - A0)) * D1)) := by
  let E0 := D0 - A0
  let E1 := D1 - A1
  let X := A1 * D0 - A0 * D1
  have hcollect :
      C * (((E0 * (s - t)) * D1 - (r * X) * s) +
        ((E0 * (s - t)) * D1 - (r * X) * s)) ≈
      (((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X)) +
        ((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X))) := by
    dsimp only [E0, X]
    exact collect_twice_plus_algebra C (D0 - A0) (s - t) D1 r
      (A1 * D0 - A0 * D1) s
  have hreplace :
      (((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X)) +
        ((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X))) ≈
      ((((g * E0) * D1) - (r * X)) +
        (((g * E0) * D1) - (r * X))) := by
    have hleft : ((C * (s - t)) * E0) * D1 ≈ (g * E0) * D1 :=
      Q'.mul_eqv_congr_right _ _ D1
        (Q'.mul_eqv_congr_right _ _ E0 hgap)
    have hright : ((C * s) * r) * X ≈ r * X := by
      refine Q'.mul_eqv_congr_right _ _ X ?_
      exact Q'.eqv_trans _ ((1 : Q') * r) _
        (Q'.mul_eqv_congr_right _ _ r hunit) (Q'.one_mul_eqv r)
    have hone :
        ((((C * (s - t)) * E0) * D1) - (((C * s) * r) * X)) ≈
        (((g * E0) * D1) - (r * X)) :=
      Q'.add_eqv_congr' hleft (Q'.neg_eqv_congr _ _ hright)
    exact Q'.add_eqv_congr' hone hone
  have hregroup :
      ((((g * E0) * D1) - (r * X)) +
        (((g * E0) * D1) - (r * X))) ≈
      ((((r * E1) * D0) - (((r - g) * E0) * D1)) +
        (((r * E1) * D0) - (((r - g) * E0) * D1))) := by
    dsimp only [E0, E1, X]
    exact cross_regroup_plus_algebra D0 A0 D1 A1 r g
  have hcTerm : (((r - g) * E0) * D1) ≈ (c * E0) * D1 :=
    Q'.mul_eqv_congr_right _ _ D1
      (Q'.mul_eqv_congr_right _ _ E0 hc)
  refine Q'.eqv_trans _ _ _ hcollect ?_
  refine Q'.eqv_trans _ _ _ hreplace ?_
  refine Q'.eqv_trans _ _ _ hregroup ?_
  have hone :
      ((r * E1) * D0 - (((r - g) * E0) * D1)) ≈
      ((r * E1) * D0 - ((c * E0) * D1)) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hcTerm)
  exact Q'.add_eqv_congr' hone hone

/-! ## 3. Symbolic all-tail carrier -/

/-- The arbitrary-scale exact analogue of the two boundary-form identities.
No prefix evaluation and no finite case split enters this theorem. -/
theorem normalizedGlobalSlack_eq_allTailBoundaryForm (k : Nat) :
    normalizedGlobalSlack k ≈ allTailBoundaryForm k := by
  unfold normalizedGlobalSlack movingDetSpacingResidual allTailBoundaryForm
    allTailBoundaryCore normalizedDemandCoeff normalizedSpacingGain
    harmonicMassCross
  apply normalized_boundary_algebra
  · exact Q'.eqv_refl _
  · exact movingCutoffScale_mul_spacing k
  · exact Q'.eqv_refl _

/-- Monotonicity of the exact three-scale carrier transports directly to
monotonicity of the normalized global slack. -/
theorem normalizedGlobalSlack_mono_of_boundaryForm
    (k : Nat) (h : allTailBoundaryForm k ≤ allTailBoundaryForm (k + 1)) :
    normalizedGlobalSlack k ≤ normalizedGlobalSlack (k + 1) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedGlobalSlack_eq_allTailBoundaryForm k))
    (Q'.le_trans' _ _ _ h
      (Q'.ge_of_eqv (normalizedGlobalSlack_eq_allTailBoundaryForm (k + 1))))

#print axioms normalizedSpacingGain
#print axioms normalizedDemandCoeff
#print axioms normalizedSpacingGainClosed
#print axioms allTailBoundaryCore
#print axioms allTailBoundaryForm
#print axioms movingCutoffScale_mul_spacing
#print axioms normalizedSpacingGain_eq_closed
#print axioms harmonicD_mono_step
#print axioms normalizedGlobalSlack_eq_allTailBoundaryForm
#print axioms normalizedGlobalSlack_mono_of_boundaryForm

end YMGap.Continuum.HarmonicMovingDeterminantAllTail
