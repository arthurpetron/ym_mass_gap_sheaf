/-
Normalized cutoff telescope for an ACTUAL finite ORIGINAL face list.

At the named corridor 0 <= w <= 1/2 and inclusive K >= 1, changing every
occurrence from K to K+L costs at most 2*c*|ids|*(81/1055)*(1/72)^(K-1).
The induction retains arbitrary actual mixed-cutoff spectator factors,
repetitions and shared links. Every intermediate mass is produced positive;
both OWN partitions are kept by the existing one-face rational cancellation.

At strict nome the very same estimate reaches the EXISTING all-nome selected
face expectation by its original common-cutoff stream. Its headCutoff and
limit/modulus are unchanged. The face-count factor is explicit: no volume-
uniform, w -> 1, OS-norm, retention or physical/continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeOneFaceCutoffStability
import YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
import YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations
import YMGap.Constructive.CRealAbsContinuity

namespace YMGap.Continuum.BF4ExactSlabSmallNomeCutoffStability

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence (normalizedMoment_congr)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
  (polynomialProduct polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabSmallNomeOneFaceCutoffStability
  (background backgroundCertificate background_mass_positive relativeTailCap
    original_background_normalized)
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (half)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- One cutoff per actual occurrence, not per distinct face. -/
def atCutoff (K : Nat) (ids : List Nat) : List (Nat × Nat) :=
  ids.map (fun id => (id,K))

private theorem atCutoff_physical {extent K : Nat} (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    ∀ e, e ∈ atCutoff K ids → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2 := by
  intro e he
  obtain ⟨id,hid,rfl⟩ := List.mem_map.mp he
  exact ⟨hi id hid,hK⟩

private theorem append_physical {extent : Nat} (es fs : List (Nat × Nat))
    (he : ∀ e, e ∈ es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    (hf : ∀ e, e ∈ fs → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2) :
    ∀ e, e ∈ es ++ fs → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2 := by
  intro e h
  rcases List.mem_append.mp h with h|h
  · exact he e h
  · exact hf e h

/-- The literal normalized moment of the produced ORIGINAL mixed-cutoff law. -/
def entryValue {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (extent : Nat)
    (es : List (Nat × Nat))
    (he : ∀ e, e ∈ es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    (p : RatPoly) : Q' :=
  normalizedMoment (blocks extent) (background w extent es) p
    (background_mass_positive hw0 hw extent es he)

private theorem entryValue_perm {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent : Nat) {es fs : List (Nat × Nat)}
    (he : ∀ e, e ∈ es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    (hf : ∀ e, e ∈ fs → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    (p : RatPoly) (h : es.Perm fs) :
    entryValue hw0 hw extent es he p ≈ entryValue hw0 hw extent fs hf p :=
  normalizedMoment_congr _ _ (polynomialProduct_perm _ h) (RatPolyCoeffEqv.refl p)

private theorem cons_physical {extent id J : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (hJ : 1 ≤ J)
    (es : List (Nat × Nat))
    (he : ∀ e, e ∈ es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2) :
    ∀ e, e ∈ (id,J)::es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2 := by
  intro e h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨hi,hJ⟩
  · exact he e h

private theorem entryValue_face_pin {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent id J : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hJ : 1 ≤ J)
    (es : List (Nat × Nat))
    (he : ∀ e, e ∈ es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    (p : RatPoly) (hZ : (0 : Q') < faceMass w J extent id (background w extent es)) :
    entryValue hw0 hw extent ((id,J)::es) (cons_physical hi hJ es he) p ≈
      faceMoment w J extent id (background w extent es) p *
        Q'.recipPos (faceMass w J extent id (background w extent es)) hZ := by
  have hd : quaternionHaar (blocks extent) (background w extent ((id,J)::es)) ≈
      faceMass w J extent id (background w extent es) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hn : quaternionHaar (blocks extent)
      (polyMul (background w extent ((id,J)::es)) p) ≈
      faceMoment w J extent id (background w extent es) p :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 2) (.var 1)) (.var 0)) (by decide)
      (fun
        | 0 => faceHeatPolynomial w J extent id
        | 1 => background w extent es
        | _ => p))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hn)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.recipPos_eqv_congr _ _ _ hZ hd))

private theorem entryValue_oneFace {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent id K L : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : 1 ≤ K)
    (es : List (Nat × Nat))
    (he : ∀ e, e ∈ es → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (entryValue hw0 hw extent ((id,K+L)::es)
        (cons_physical hi (by omega) es he) p +
      -(entryValue hw0 hw extent ((id,K)::es) (cons_physical hi hK es he) p)) ≤
      2*c*relativeTailCap K := by
  have hz (J : Nat) (hJ : 1 ≤ J) :
      (0 : Q') < faceMass w J extent id (background w extent es) :=
    Q'.pos_of_lt_of_le
      (background_mass_positive hw0 hw extent ((id,J)::es) (cons_physical hi hJ es he))
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have h := original_background_normalized hw0 hw K L extent id hi hK es he P
  dsimp only at h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr'
    (entryValue_face_pin hw0 hw extent id (K+L) hi (by omega) es he p (hz _ (by omega)))
    (Q'.neg_eqv_congr _ _ (entryValue_face_pin hw0 hw extent id K hi hK es he p (hz _ hK)))))) h

private theorem abs_triangle (a b d : Q') :
    Q'.abs (a + -d) ≤ Q'.abs (a + -b) + Q'.abs (b + -d) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (by decide) (fun | 0 => a | 1 => b | _ => d)))) (ExpNeg.abs_add_le _ _)

/-- Finite-list telescope with arbitrary actual mixed-cutoff frozen spectators.
No independence, distinct-face or unit-partition premise is used. -/
theorem original_mixed_cutoff_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K L extent : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (frozen : List (Nat × Nat))
    (hf : ∀ e, e ∈ frozen → e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (entryValue hw0 hw extent (atCutoff (K+L) ids ++ frozen)
        (append_physical _ _ (atCutoff_physical (by omega) ids hi) hf) p +
      -(entryValue hw0 hw extent (atCutoff K ids ++ frozen)
        (append_physical _ _ (atCutoff_physical hK ids hi) hf) p)) ≤
      2*c*Q'.ofNat ids.length*relativeTailCap K := by
  induction ids generalizing frozen with
  | nil =>
      exact Q'.le_of_eqv (by
        change Q'.abs (_ + -_) ≈ 2*c*Q'.ofNat 0*relativeTailCap K
        exact Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr (Q'.add_neg_self_eqv _))
          (Q'.eqv_trans _ _ _ (by decide : Q'.abs (0 : Q') ≈ 0)
            (Q'.eqv_symm (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _)) (Q'.zero_mul_eqv _)))))
  | cons id ids ih =>
      have hid := hi id List.mem_cons_self
      have hit := fun j hj => hi j (List.mem_cons_of_mem id hj)
      let oldEs := atCutoff K ids ++ frozen
      let newEs := atCutoff (K+L) ids ++ frozen
      have ho : ∀ e, e ∈ oldEs →
          e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2 :=
        append_physical _ _ (atCutoff_physical hK ids hit) hf
      have hn : ∀ e, e ∈ newEs →
          e.1 ∈ slabPhysicalFaceEdges extent ∧ 1 ≤ e.2 :=
        append_physical _ _ (atCutoff_physical (by omega : 1 ≤ K+L) ids hit) hf
      let old := entryValue hw0 hw extent ((id,K)::oldEs) (cons_physical hid hK _ ho) p
      let middle := entryValue hw0 hw extent ((id,K+L)::oldEs)
        (cons_physical hid (by omega : 1 ≤ K+L) _ ho) p
      let later := entryValue hw0 hw extent ((id,K+L)::newEs)
        (cons_physical hid (by omega : 1 ≤ K+L) _ hn) p
      have one : Q'.abs (middle + -old) ≤ 2*c*relativeTailCap K :=
        entryValue_oneFace hw0 hw extent id K L hid hK oldEs ho P
      have hf' := cons_physical hid (by omega : 1 ≤ K+L) frozen hf
      have tail := ih hit ((id,K+L)::frozen) hf'
      have hnew := entryValue_perm hw0 hw extent
        (cons_physical hid (by omega : 1 ≤ K+L) _ hn)
        (append_physical _ _ (atCutoff_physical (by omega : 1 ≤ K+L) ids hit) hf') p
        (List.perm_middle (a := (id,K+L)) (l₁ := atCutoff (K+L) ids) (l₂ := frozen)).symm
      have hmid := entryValue_perm hw0 hw extent
        (cons_physical hid (by omega : 1 ≤ K+L) _ ho)
        (append_physical _ _ (atCutoff_physical hK ids hit) hf') p
        (List.perm_middle (a := (id,K+L)) (l₁ := atCutoff K ids) (l₂ := frozen)).symm
      have tail' : Q'.abs (later + -middle) ≤
          2*c*Q'.ofNat ids.length*relativeTailCap K :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
          (Q'.add_eqv_congr' hnew (Q'.neg_eqv_congr _ _ hmid)))) tail
      have hcount : Q'.ofNat (ids.length+1) ≈ Q'.ofNat ids.length + 1 :=
        Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv _ 1)
          (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.ofNat 1 ≈ (1 : Q')))
      have hsum : (2*c*Q'.ofNat ids.length*relativeTailCap K) + (2*c*relativeTailCap K) ≈
          2*c*Q'.ofNat (ids.length+1)*relativeTailCap K :=
        Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.add (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
              (.mul (.mul (.const 2) (.var 0)) (.var 2)))
            (.mul (.mul (.mul (.const 2) (.var 0)) (.add (.var 1) (.const 1))) (.var 2))
            (by decide) (fun | 0 => c | 1 => Q'.ofNat ids.length | _ => relativeTailCap K))
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hcount)))
      exact Q'.le_trans' _ _ _ (abs_triangle later middle old)
        (Q'.le_trans' _ _ _ (Q'.add_le_add tail' one) (Q'.le_of_eqv hsum))

private theorem uniform_background (w : Q') (extent K : Nat) : ∀ ids : List Nat,
    background w extent (atCutoff K ids) =
      polynomialProduct (faceHeatPolynomial w K extent) ids
  | [] => rfl
  | _::ids => congrArg (polyMul _) (uniform_background w extent K ids)

/-- Positivity of the actual uniform-cutoff ORIGINAL product, even at early K. -/
theorem product_mass_positive {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent K : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    (0 : Q') < quaternionHaar (blocks extent)
      (polynomialProduct (faceHeatPolynomial w K extent) ids) := by
  rw [← uniform_background w extent K ids]
  exact background_mass_positive hw0 hw extent _ (atCutoff_physical hK ids hi)

/-- Raw normalized moment with its OWN produced same-cutoff partition. -/
def cutoffValue {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent K : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (p : RatPoly) : Q' :=
  normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial w K extent) ids) p
    (product_mass_positive hw0 hw extent K hK ids hi)

private theorem cutoffValue_entry_pin {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (extent K : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (p : RatPoly) :
    cutoffValue hw0 hw extent K hK ids hi p ≈
      entryValue hw0 hw extent (atCutoff K ids) (atCutoff_physical hK ids hi) p :=
  normalizedMoment_congr _ _
    (by rw [uniform_background]; exact RatPolyCoeffEqv.refl _) (RatPolyCoeffEqv.refl p)

/-- Actual normalized finite-list cutoff error; multiplicities count literally. -/
theorem original_cutoff_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K L extent : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    Q'.abs (cutoffValue hw0 hw extent (K+L) (by omega) ids hi p +
      -(cutoffValue hw0 hw extent K hK ids hi p)) ≤
      2*c*Q'.ofNat ids.length*relativeTailCap K := by
  have h := original_mixed_cutoff_bound hw0 hw K L extent hK ids hi [] (fun _ h => nomatch h) P
  simp only [List.append_nil] at h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr'
    (cutoffValue_entry_pin hw0 hw extent (K+L) (by omega) ids hi p)
    (Q'.neg_eqv_congr _ _ (cutoffValue_entry_pin hw0 hw extent K hK ids hi p))))) h

open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (expectation)
open YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations
  (commonValue commonValue_formula commonValue_converges)

/-- The canonical offset stream uses exactly this original cutoff density and
its OWN reciprocal; the different positivity witnesses carry no extra input. -/
theorem commonValue_cutoff_pin {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (extent K : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (p : RatPoly) (n : Nat) :
    commonValue w hw0 (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q')))
      extent ids hi p (headCutoff w+K) n ≈
      cutoffValue (Q'.le_of_lt hw0) hw extent (headCutoff w+K+n) (by omega) ids hi p := by
  have h := commonValue_formula w hw0
    (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q')))
    extent ids hi p (headCutoff w+K) n (Nat.le_add_right _ _)
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))

private theorem commonValue_early_bound {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (K extent : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) (n : Nat) :
    Q'.abs (commonValue w hw0 (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q')))
        extent ids hi p (headCutoff w+K) n +
      -(cutoffValue (Q'.le_of_lt hw0) hw extent K hK ids hi p)) ≤
      2*c*Q'.ofNat ids.length*relativeTailCap K := by
  have h := original_cutoff_bound (Q'.le_of_lt hw0) hw K (headCutoff w+n) extent hK ids hi P
  have h' : Q'.abs (cutoffValue (Q'.le_of_lt hw0) hw extent
      (headCutoff w+K+n) (by omega) ids hi p +
        -(cutoffValue (Q'.le_of_lt hw0) hw extent K hK ids hi p)) ≤
      2*c*Q'.ofNat ids.length*relativeTailCap K := by
    simpa only [Nat.add_assoc, Nat.add_left_comm] using h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr'
    (commonValue_cutoff_pin hw0 hw extent K hK ids hi p n) (Q'.eqv_refl _)))) h'

/-- The SAME pre-existing all-nome expectation is within the early-cutoff budget.
No new limit, discarded head guard or differentiation/exchange premise is used. -/
theorem expectation_cutoff_bound {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (K extent : Nat) (hK : 1 ≤ K) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    leEv (CReal.abs (CReal.sub
      (expectation w hw0 (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q'))) extent ids hi p)
      (ofQ' (cutoffValue (Q'.le_of_lt hw0) hw extent K hK ids hi p))))
      (ofQ' (2*c*Q'.ofNat ids.length*relativeTailCap K)) := by
  have h := convergesTo_abs (convergesTo_add
    (commonValue_converges w hw0 (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q')))
      extent ids hi p (headCutoff w+K))
    (TrigAddCReal.convergesTo_neg (convergesTo_const
      (ofQ' (cutoffValue (Q'.le_of_lt hw0) hw extent K hK ids hi p)))))
  have hc : ConvergesTo (fun n => ofQ' (Q'.abs
      (commonValue w hw0 (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q')))
          extent ids hi p (headCutoff w+K) n +
        -(cutoffValue (Q'.le_of_lt hw0) hw extent K hK ids hi p))))
      (CReal.abs (CReal.sub
        (expectation w hw0 (Q'.lt_of_le_of_lt hw (by decide : half < (1 : Q'))) extent ids hi p)
        (ofQ' (cutoffValue (Q'.le_of_lt hw0) hw extent K hK ids hi p)))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ h
    intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const _)
  intro epsilon he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (commonValue_early_bound hw0 hw K extent hK ids hi P n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

#print axioms atCutoff
#print axioms entryValue
#print axioms original_mixed_cutoff_bound
#print axioms product_mass_positive
#print axioms cutoffValue
#print axioms original_cutoff_bound
#print axioms commonValue_cutoff_pin
#print axioms expectation_cutoff_bound

end YMGap.Continuum.BF4ExactSlabSmallNomeCutoffStability
