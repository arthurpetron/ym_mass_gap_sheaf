/-
# Exact support pushforward of the finite corrected-slab Gram

The finite corrected-slab Gram is indexed by lower-half spin labellings.  For
support-measurable observables, all spin decorations can be summed exactly at
fixed occupied lower-half support.  We implement this as the deterministic
pushforward of the complete pair kernel, so every cross term and every fixed
interface channel is retained.

The resulting support quadratic is exactly the original spin quadratic with
the coefficient pulled back along the support code.  The equality persists
after division by the physical corrected-slab partition.  This is the
strongest support-only finite Gram restriction; no claim that arbitrary
spin-sensitive coefficients factor through it is made here.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4CanonicalExhaustiveCylinder
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

namespace YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CanonicalExhaustiveCylinder
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## The finite lower-half support code -/

/-- Occupied lower-half face identifiers of a bounded half-state, in the
canonical lower-face order. -/
def centralHalfSupportCode (half : Nat)
    (state : EdgeLabelling) : List Nat :=
  (centralLowerFaceIds half).filter
    (fun id => decide (1 ≤ state id))

/-- Complete finite support target.  Unphysical support lists are harmless:
their deterministic fibres are empty. -/
def centralHalfSupportSpace (half : Nat) : List (List Nat) :=
  sublists (centralLowerFaceIds half)

theorem centralHalfSupportCode_mem
    (half : Nat) (state : EdgeLabelling) :
    centralHalfSupportCode half state ∈ centralHalfSupportSpace half := by
  unfold centralHalfSupportCode centralHalfSupportSpace
  exact filter_mem_sublists _ _

private theorem rangeNodupLocal (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

private theorem centralLowerFaceIds_nodup_local (half : Nat) :
    (centralLowerFaceIds half).Nodup := by
  have hfull :
      (slabPhysicalFaceEdges (centralExtent half)).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  have hall :
      ((centralLowerFaceIds half ++ centralFixedFaceIds half) ++
        centralUpperFaceIds half).Nodup := by
    simpa [centralLowerFaceIds, centralFixedFaceIds,
      centralUpperFaceIds] using
      ((centralSlabFaceIdParts_perm half).symm.nodup hfull)
  exact (List.nodup_append.mp (List.nodup_append.mp hall).1).1

theorem centralHalfSupportSpace_nodup (half : Nat) :
    (centralHalfSupportSpace half).Nodup := by
  unfold centralHalfSupportSpace
  exact sublists_nodup (centralLowerFaceIds half)
    (centralLowerFaceIds_nodup_local half)

/-! ## Exhaustive Boolean fingerprints of lower supports -/

/-- Boolean membership fingerprint of a lower support against the complete
ordered lower-face list. -/
def centralSupportFingerprint (half : Nat)
    (support : List Nat) : List Bool :=
  (centralLowerFaceIds half).map (memberB support)

/-- Fingerprint read directly from a lower spin state. -/
def centralHalfSupportFingerprint (half : Nat)
    (state : EdgeLabelling) : List Bool :=
  centralSupportFingerprint half (centralHalfSupportCode half state)

private theorem selectByBoolFingerprint_memberB_eq_filter
    {A : Type} [DecidableEq A] :
    ∀ (ambient family : List A),
      selectByBoolFingerprint ambient (ambient.map (memberB family)) =
        ambient.filter (memberB family)
  | [], family => rfl
  | item :: ambient, family => by
      simp only [List.map_cons]
      cases hmember : memberB family item
      · simp only [selectByBoolFingerprint_cons_false, List.filter_cons,
          hmember, Bool.false_eq_true, ↓reduceIte]
        exact selectByBoolFingerprint_memberB_eq_filter ambient family
      · simp only [selectByBoolFingerprint_cons_true, List.filter_cons,
          hmember, ↓reduceIte, List.cons.injEq, true_and]
        exact selectByBoolFingerprint_memberB_eq_filter ambient family

/-- The complete Boolean fingerprint literally reconstructs every lower
support in the support target space. -/
theorem centralSupportFingerprint_recovers
    {half : Nat} {support : List Nat}
    (hsupport : support ∈ centralHalfSupportSpace half) :
    selectByBoolFingerprint (centralLowerFaceIds half)
        (centralSupportFingerprint half support) = support := by
  unfold centralSupportFingerprint
  rw [selectByBoolFingerprint_memberB_eq_filter]
  exact filter_memberB_eq_of_mem_sublists
    (centralLowerFaceIds_nodup_local half) hsupport

theorem centralSupportFingerprint_injective_on
    {half : Nat} {left right : List Nat}
    (hleft : left ∈ centralHalfSupportSpace half)
    (hright : right ∈ centralHalfSupportSpace half)
    (heq : centralSupportFingerprint half left =
      centralSupportFingerprint half right) :
    left = right := by
  have hdecode := congrArg
    (selectByBoolFingerprint (centralLowerFaceIds half)) heq
  rw [centralSupportFingerprint_recovers hleft,
    centralSupportFingerprint_recovers hright] at hdecode
  exact hdecode

/-! ## Pair kernel pushed to support pairs -/

def centralHalfStatePairs (K half : Nat) :
    List (EdgeLabelling × EdgeLabelling) :=
  cartesian (centralHalfStates K half) (centralHalfStates K half)

def centralHalfSupportPairs (half : Nat) :
    List (List Nat × List Nat) :=
  cartesian (centralHalfSupportSpace half)
    (centralHalfSupportSpace half)

def centralHalfSupportPairCode (half : Nat)
    (pair : EdgeLabelling × EdgeLabelling) : List Nat × List Nat :=
  (centralHalfSupportCode half pair.1,
    centralHalfSupportCode half pair.2)

theorem centralHalfSupportPairs_nodup (half : Nat) :
    (centralHalfSupportPairs half).Nodup := by
  unfold centralHalfSupportPairs
  exact cartesian_nodup _ _
    (centralHalfSupportSpace_nodup half)
    (centralHalfSupportSpace_nodup half)

theorem centralHalfSupportPairCode_mem
    (K half : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    pair ∈ centralHalfStatePairs K half →
      centralHalfSupportPairCode half pair ∈
        centralHalfSupportPairs half := by
  intro _
  apply (mem_cartesian_iff _ _ _).2
  exact ⟨centralHalfSupportCode_mem half pair.1,
    centralHalfSupportCode_mem half pair.2⟩

/-- Complete reflected pair-kernel mass over all spin decorations with one
fixed pair of occupied supports. -/
def centralSupportReflectedKernel
    (w : Q') (K half : Nat)
    (leftSupport rightSupport : List Nat) : Q' :=
  fiberWeight
    (centralHalfStatePairs K half)
    (fun pair =>
      centralPhysicalReflectedKernel w K half pair.1 pair.2)
    (centralHalfSupportPairCode half)
    (leftSupport, rightSupport)

/-- Reflection quadratic on occupied supports after exact decoration
pushforward. -/
def centralSupportReflectionQuadratic
    (w : Q') (K half : Nat)
    (coefficient : List Nat → Q') : Q' :=
  finiteJointQuadratic
    (centralHalfSupportSpace half) coefficient
    (centralSupportReflectedKernel w K half)

/-! ## Generic exact pair-pushforward algebra -/

theorem listQSum_cartesian_eq_nested
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- Multiplication by a coefficient on the target can be moved inside its
deterministic source fibre and read back through the source code. -/
theorem coefficient_mul_fiberWeight_eqv
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A → Q') (code : A → B)
    (coefficient : B → Q') (target : B) :
    coefficient target * fiberWeight source weight code target ≈
      fiberWeight source
        (fun item => coefficient (code item) * weight item)
        code target := by
  unfold fiberWeight
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_mul_left (coefficient target) weight
        (source.filter (fun item => decide (target = code item))))) ?_
  apply listQSum_congr_on
  intro item hitem
  have hcode : target = code item :=
    of_decide_eq_true (List.mem_filter.mp hitem).2
  rw [hcode]
  exact Q'.eqv_refl _

/-! ## Exact support-measurable Gram identification -/

/-- Summing every spin decoration at fixed lower support preserves the full
finite reflection quadratic exactly. -/
theorem centralSupportReflectionQuadratic_eq_physical
    (w : Q') (K half : Nat)
    (coefficient : List Nat → Q') :
    centralSupportReflectionQuadratic w K half coefficient ≈
      centralPhysicalReflectionQuadratic w K half
        (fun state => coefficient (centralHalfSupportCode half state)) := by
  let stateWeight : EdgeLabelling × EdgeLabelling → Q' := fun pair =>
    (coefficient (centralHalfSupportCode half pair.1) *
      coefficient (centralHalfSupportCode half pair.2)) *
        centralPhysicalReflectedKernel w K half pair.1 pair.2
  let supportCoefficient : List Nat × List Nat → Q' := fun pair =>
    coefficient pair.1 * coefficient pair.2
  have htoPairs :
      centralSupportReflectionQuadratic w K half coefficient ≈
        listQSum
          (fun supportPair =>
            supportCoefficient supportPair *
              fiberWeight
                (centralHalfStatePairs K half)
                (fun pair =>
                  centralPhysicalReflectedKernel
                    w K half pair.1 pair.2)
                (centralHalfSupportPairCode half)
                supportPair)
          (centralHalfSupportPairs half) := by
    unfold centralSupportReflectionQuadratic finiteJointQuadratic
      centralHalfSupportPairs supportCoefficient
      centralSupportReflectedKernel
    exact Q'.eqv_symm
      (listQSum_cartesian_eq_nested
        (fun supportPair =>
          (coefficient supportPair.1 * coefficient supportPair.2) *
            fiberWeight
              (centralHalfStatePairs K half)
              (fun pair =>
                centralPhysicalReflectedKernel
                  w K half pair.1 pair.2)
              (centralHalfSupportPairCode half)
              supportPair)
        (centralHalfSupportSpace half)
        (centralHalfSupportSpace half))
  have hinside :
      listQSum
          (fun supportPair =>
            supportCoefficient supportPair *
              fiberWeight
                (centralHalfStatePairs K half)
                (fun pair =>
                  centralPhysicalReflectedKernel
                    w K half pair.1 pair.2)
                (centralHalfSupportPairCode half)
                supportPair)
          (centralHalfSupportPairs half) ≈
        listQSum
          (fiberWeight
            (centralHalfStatePairs K half) stateWeight
            (centralHalfSupportPairCode half))
          (centralHalfSupportPairs half) := by
    apply listQSum_congr
    intro supportPair
    exact coefficient_mul_fiberWeight_eqv
      (centralHalfStatePairs K half)
      (fun pair =>
        centralPhysicalReflectedKernel w K half pair.1 pair.2)
      (centralHalfSupportPairCode half)
      supportCoefficient supportPair
  have htotal :
      listQSum
          (fiberWeight
            (centralHalfStatePairs K half) stateWeight
            (centralHalfSupportPairCode half))
          (centralHalfSupportPairs half) ≈
        listQSum stateWeight (centralHalfStatePairs K half) := by
    exact fiberWeight_total
      (centralHalfStatePairs K half) stateWeight
      (centralHalfSupportPairCode half)
      (centralHalfSupportPairs half)
      (centralHalfSupportPairs_nodup half)
      (centralHalfSupportPairCode_mem K half)
  have hfromPairs :
      listQSum stateWeight (centralHalfStatePairs K half) ≈
        centralPhysicalReflectionQuadratic w K half
          (fun state => coefficient (centralHalfSupportCode half state)) := by
    unfold centralHalfStatePairs stateWeight
      centralPhysicalReflectionQuadratic
    exact listQSum_cartesian_eq_nested
      (fun pair =>
        (coefficient (centralHalfSupportCode half pair.1) *
          coefficient (centralHalfSupportCode half pair.2)) *
            centralPhysicalReflectedKernel w K half pair.1 pair.2)
      (centralHalfStates K half) (centralHalfStates K half)
  exact Q'.eqv_trans _ _ _ htoPairs
    (Q'.eqv_trans _ _ _ hinside
      (Q'.eqv_trans _ _ _ htotal hfromPairs))

theorem centralSupportReflectionQuadratic_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Nat → Q') :
    (0 : Q') ≤
      centralSupportReflectionQuadratic w K half coefficient := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalReflectionQuadratic_nonnegative hw
      (fun state => coefficient (centralHalfSupportCode half state)))
    (Q'.le_of_eqv (Q'.eqv_symm
      (centralSupportReflectionQuadratic_eq_physical
        w K half coefficient)))

/-! ## Normalized corrected-slab equality -/

def centralNormalizedSupportReflectionQuadratic
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Nat → Q') : Q' :=
  Q'.divPos
    (centralSupportReflectionQuadratic w K half coefficient)
    (slabParametricKPhysicalPartition w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos hw K (centralExtent half))

/-- Exact normalized identification with the pre-existing full corrected-slab
OS quadratic for the pulled-back support coefficient. -/
theorem centralNormalizedSupportReflectionQuadratic_eq_full
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Nat → Q') :
    centralNormalizedSupportReflectionQuadratic
        w hw K half coefficient ≈
      centralNormalizedFullPhysicalReflectionQuadratic w hw K half
        (fun state => coefficient (centralHalfSupportCode half state)) := by
  unfold centralNormalizedSupportReflectionQuadratic
    centralNormalizedFullPhysicalReflectionQuadratic Q'.divPos
  apply Q'.mul_eqv_congr_right _ _ _
  exact Q'.eqv_trans _ _ _
    (centralSupportReflectionQuadratic_eq_physical
      w K half coefficient)
    (centralPhysicalReflectionQuadratic_eq_full
      w K half
      (fun state => coefficient (centralHalfSupportCode half state)))

theorem centralNormalizedSupportReflectionQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Nat → Q') :
    (0 : Q') ≤
      centralNormalizedSupportReflectionQuadratic
        w hw K half coefficient := by
  exact Q'.le_trans' _ _ _
    (centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
      w hw K half
      (fun state => coefficient (centralHalfSupportCode half state)))
    (Q'.le_of_eqv (Q'.eqv_symm
      (centralNormalizedSupportReflectionQuadratic_eq_full
        w hw K half coefficient)))

/-- Pull a rational coefficient on the exhaustive Boolean fingerprint back to
the support target space. -/
def centralSupportFingerprintCoefficient (half : Nat)
    (coefficient : List Bool → Q') (support : List Nat) : Q' :=
  coefficient (centralSupportFingerprint half support)

/-- Exact normalized Gram identification stated directly for arbitrary
coefficients on exhaustive finite support fingerprints. -/
theorem centralNormalizedSupportFingerprintQuadratic_eq_full
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Bool → Q') :
    centralNormalizedSupportReflectionQuadratic w hw K half
        (centralSupportFingerprintCoefficient half coefficient) ≈
      centralNormalizedFullPhysicalReflectionQuadratic w hw K half
        (fun state =>
          coefficient (centralHalfSupportFingerprint half state)) := by
  simpa only [centralSupportFingerprintCoefficient,
    centralHalfSupportFingerprint] using
      (centralNormalizedSupportReflectionQuadratic_eq_full
        w hw K half
        (centralSupportFingerprintCoefficient half coefficient))

theorem centralNormalizedSupportFingerprintQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : List Bool → Q') :
    (0 : Q') ≤
      centralNormalizedSupportReflectionQuadratic w hw K half
        (centralSupportFingerprintCoefficient half coefficient) :=
  centralNormalizedSupportReflectionQuadratic_nonnegative
    w hw K half (centralSupportFingerprintCoefficient half coefficient)

#print axioms centralHalfSupportCode_mem
#print axioms centralHalfSupportSpace_nodup
#print axioms centralSupportFingerprint_recovers
#print axioms centralSupportFingerprint_injective_on
#print axioms listQSum_cartesian_eq_nested
#print axioms coefficient_mul_fiberWeight_eqv
#print axioms centralSupportReflectionQuadratic_eq_physical
#print axioms centralSupportReflectionQuadratic_nonnegative
#print axioms centralNormalizedSupportReflectionQuadratic_eq_full
#print axioms centralNormalizedSupportReflectionQuadratic_nonnegative
#print axioms centralNormalizedSupportFingerprintQuadratic_eq_full
#print axioms centralNormalizedSupportFingerprintQuadratic_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
