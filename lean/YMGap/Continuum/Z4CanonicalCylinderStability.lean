/-
# Normalized stability of finite canonical cylinder events

The marked-cylinder connected residue is absorbed into the forward and
mirrored carrier tails, specialized to canonically transported local roots,
and divided by the two positive finite-volume partitions.  Complementing the
Boolean predicate supplies the reverse inequality, hence an absolute modulus.
-/

import YMGap.Continuum.Z4CanonicalCylinderConnectedTail
import YMGap.Continuum.Z4CanonicalOccurrenceCofinal

namespace YMGap.Continuum.Z4CanonicalCylinderStability

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderConnectedTail
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalOccurrenceCofinal
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. Certified transported roots and their geometry -/

def transportedCanonicalCylinderAtoms
    {small n : Nat} (hsmall : small ≤ n)
    (rawRoots : List (List Nat))
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small) :
    List (CanonicalAtom n) :=
  canonicalAtomsOfRoots
    (transportedCylinderRoots small n rawRoots)
    (fun root hroot => by
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hroot
      subst root
      exact transportPolymer_mem_canonicalSurfacePolymers
        hsmall (hroots source hsource))

theorem transportedCanonicalCylinderAtoms_values
    {small n : Nat} (hsmall : small ≤ n)
    (rawRoots : List (List Nat))
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small) :
    (transportedCanonicalCylinderAtoms hsmall rawRoots hroots).map
        Subtype.val =
      transportedCylinderRoots small n rawRoots := by
  unfold transportedCanonicalCylinderAtoms
  exact canonicalAtomsOfRoots_values _ _

theorem transportedCanonicalCylinderAtoms_length
    {small n : Nat} (hsmall : small ≤ n)
    (rawRoots : List (List Nat))
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small) :
    (transportedCanonicalCylinderAtoms hsmall rawRoots hroots).length =
      rawRoots.length := by
  have hvalues := congrArg List.length
    (transportedCanonicalCylinderAtoms_values hsmall rawRoots hroots)
  simpa [transportedCylinderRoots] using hvalues

theorem transportedCanonicalCylinderAtom_source
    {small n : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (root : CanonicalAtom n)
    (hroot : root ∈
      transportedCanonicalCylinderAtoms hsmall rawRoots hroots) :
    ∃ source, source ∈ rawRoots ∧
      transportPolymer small n source = root.val := by
  have hvalue : root.val ∈ transportedCylinderRoots small n rawRoots := by
    rw [← transportedCanonicalCylinderAtoms_values hsmall rawRoots hroots]
    exact List.mem_map.mpr ⟨root, hroot, rfl⟩
  unfold transportedCylinderRoots at hvalue
  exact List.mem_map.mp hvalue

theorem transportedCanonicalCylinderAtoms_inside_source
    {small n : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small) :
    ∀ root, root ∈
        transportedCanonicalCylinderAtoms hsmall rawRoots hroots →
      polymerInsideBoxB small n root.val = true := by
  intro root hroot
  obtain ⟨source, hsource, hsourceEq⟩ :=
    transportedCanonicalCylinderAtom_source hsmall hroots root hroot
  apply (polymerInsideBoxB_true_iff small n root.val).2
  rw [← hsourceEq]
  exact transportPolymer_inside_source_box hsmall (hroots source hsource)

theorem transportedCanonicalCylinderAtoms_inner_face
    {small n inner : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (hinside : ∀ root, root ∈ rawRoots →
      PolymerInsideBox inner small root) :
    ∀ root, root ∈
        transportedCanonicalCylinderAtoms hsmall rawRoots hroots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner := by
  intro root hroot
  obtain ⟨source, hsource, hsourceEq⟩ :=
    transportedCanonicalCylinderAtom_source hsmall hroots root hroot
  have hsourceCanonical := hroots source hsource
  obtain ⟨sourceFace, hsourceFace⟩ :=
    canonicalSurfacePolymers_allNonempty small source hsourceCanonical
  obtain ⟨targetFace, htargetFace, hfaceEq⟩ :=
    transportPolymerMemberTarget hsmall
      (canonicalSurfacePolymer_mem_faceSupports hsourceCanonical)
      hsourceFace
  refine ⟨targetFace, ?_, ?_⟩
  · rw [← hsourceEq]
    exact htargetFace
  · rw [← hfaceEq]
    apply hinside source hsource (boxPlaquetteAt small sourceFace)
    exact List.mem_map.mpr ⟨sourceFace, hsourceFace, rfl⟩

/-! ## 2. Cross-numerator tail with the finite local prefactor -/

def cylinderBoundaryEpsilon (rootCount distance : Nat) : Q' :=
  Q'.ofNat rootCount *
    (occurrenceBoundaryEpsilon distance + occurrenceBoundaryEpsilon distance)

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

theorem cylinderBoundaryEpsilon_nonnegative (rootCount distance : Nat) :
    (0 : Q') ≤ cylinderBoundaryEpsilon rootCount distance := by
  unfold cylinderBoundaryEpsilon
  exact Q'.mul_nonneg _ _ (ofNat_nonnegative_local rootCount)
    (Q'.zero_le_add _ _
      (occurrenceBoundaryEpsilon_nonnegative distance)
      (occurrenceBoundaryEpsilon_nonnegative distance))

theorem cylinderBoundaryTail_eqv_normalized
    (rootCount small n distance : Nat) :
    Q'.ofNat rootCount *
        cylinderSingleRootTwoSidedTail small n distance ≈
      cylinderBoundaryEpsilon rootCount distance *
        (anchorCanonicalPartition small * anchorCanonicalPartition n) := by
  unfold cylinderSingleRootTwoSidedTail
    cylinderSingleRootBoundaryTail cylinderBoundaryEpsilon
    occurrenceBoundaryEpsilon
  ring_qeqv

theorem anchorCylinderCrossDifference_le_boundaryTail_of_inside
    {small n inner distance : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (hinside : ∀ root, root ∈ rawRoots →
      PolymerInsideBox inner small root)
    (predicate : List Bool → Bool)
    (hbox : inner + distance = small) :
    anchorEventNumerator n
          (targetCylinderEvent small n rawRoots predicate) *
        anchorCanonicalPartition small -
      anchorEventNumerator small
          (sourceCylinderEvent rawRoots predicate) *
        anchorCanonicalPartition n ≤
      cylinderBoundaryEpsilon rawRoots.length distance *
        (anchorCanonicalPartition small * anchorCanonicalPartition n) := by
  let roots := transportedCanonicalCylinderAtoms hsmall rawRoots hroots
  have hconnected := anchorCylinderCrossDifference_le_connected
    hsmall hroots predicate
  have htail := connectedCylinderPairSum_le_boundaryTail
    hsmall roots predicate
    (transportedCanonicalCylinderAtoms_inside_source hsmall hroots)
    (transportedCanonicalCylinderAtoms_inner_face
      hsmall hroots hinside)
    hbox
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  have hlength : roots.length = rawRoots.length :=
    transportedCanonicalCylinderAtoms_length hsmall rawRoots hroots
  rw [hlength] at hbound
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv
      (cylinderBoundaryTail_eqv_normalized
        rawRoots.length small n distance))

/-! ## 3. Positive-denominator normalization -/

theorem anchorEventProbability_sub_le_of_cross
    {small n : Nat} (targetEvent sourceEvent : List (List Nat) → Bool)
    (epsilon : Q')
    (hcross :
      anchorEventNumerator n targetEvent * anchorCanonicalPartition small -
          anchorEventNumerator small sourceEvent *
            anchorCanonicalPartition n ≤
        epsilon *
          (anchorCanonicalPartition small * anchorCanonicalPartition n)) :
    anchorEventProbability n targetEvent -
        anchorEventProbability small sourceEvent ≤ epsilon := by
  let targetNumerator := anchorEventNumerator n targetEvent
  let sourceNumerator := anchorEventNumerator small sourceEvent
  let targetPartition := anchorCanonicalPartition n
  let sourcePartition := anchorCanonicalPartition small
  have hadd :
      targetNumerator * sourcePartition ≤
        sourceNumerator * targetPartition +
          epsilon * (sourcePartition * targetPartition) :=
    le_add_of_sub_le_local hcross
  have hreorder :
      (sourceNumerator * targetPartition +
          epsilon * (sourcePartition * targetPartition)).eqv
        ((sourceNumerator + epsilon * sourcePartition) *
          targetPartition) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (sourceNumerator * targetPartition)
        (epsilon * (sourcePartition * targetPartition))
        ((epsilon * sourcePartition) * targetPartition)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv epsilon sourcePartition targetPartition))) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv sourceNumerator
        (epsilon * sourcePartition) targetPartition)
  have hratio := divPos_le_divPos_of_cross_local
    targetNumerator targetPartition
    (sourceNumerator + epsilon * sourcePartition) sourcePartition
    (anchorCanonicalPartition_pos n)
    (anchorCanonicalPartition_pos small)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    sourceNumerator epsilon sourcePartition
    (anchorCanonicalPartition_pos small)
  have hprob :
      anchorEventProbability n targetEvent ≤
        anchorEventProbability small sourceEvent + epsilon := by
    unfold anchorEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem anchorCylinderProbability_sub_le_boundaryEpsilon_of_inside
    {small n inner distance : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (hinside : ∀ root, root ∈ rawRoots →
      PolymerInsideBox inner small root)
    (predicate : List Bool → Bool)
    (hbox : inner + distance = small) :
    anchorEventProbability n
          (targetCylinderEvent small n rawRoots predicate) -
        anchorEventProbability small
          (sourceCylinderEvent rawRoots predicate) ≤
      cylinderBoundaryEpsilon rawRoots.length distance := by
  apply anchorEventProbability_sub_le_of_cross
  exact anchorCylinderCrossDifference_le_boundaryTail_of_inside
    hsmall hroots hinside predicate hbox

/-! ## 4. Complement symmetry and the absolute modulus -/

def complementCylinderPredicate
    (predicate : List Bool → Bool) : List Bool → Bool :=
  fun bits => !(predicate bits)

theorem anchorEventNumerator_add_complement_eqv_partition
    (n : Nat) (event : List (List Nat) → Bool) :
    anchorEventNumerator n event +
        anchorEventNumerator n (fun family => !(event family)) ≈
      anchorCanonicalPartition n := by
  unfold anchorEventNumerator anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (canonicalSurfaceFamilyActivity anchorCoupling n) event
      (canonicalCompatibleAmbientFamilies n))

private theorem add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem anchorEventProbability_add_complement_eqv_one
    (n : Nat) (event : List (List Nat) → Bool) :
    anchorEventProbability n event +
        anchorEventProbability n (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit := anchorEventNumerator_add_complement_eqv_partition n event
  unfold anchorEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (anchorEventNumerator n event)
      (anchorEventNumerator n (fun family => !(event family)))
      (anchorCanonicalPartition n)
      (anchorCanonicalPartition_pos n)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos (anchorCanonicalPartition n)
        (anchorCanonicalPartition_pos n)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (anchorCanonicalPartition n) (anchorCanonicalPartition_pos n)

private theorem left_eqv_one_sub_right {a complement : Q'}
    (hsum : a + complement ≈ (1 : Q')) :
    a ≈ (1 : Q') - complement := by
  refine Q'.eqv_trans _ (a + 0) _
    (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' a))) ?_
  refine Q'.eqv_trans _ (a + (complement + (-complement))) _
    (Q'.add_eqv_congr_left a 0 (complement + (-complement))
      (Q'.eqv_symm (Q'.add_neg_self_eqv complement))) ?_
  refine Q'.eqv_trans _ ((a + complement) + (-complement)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv a complement (-complement))) ?_
  exact Q'.add_eqv_congr_right
    (a + complement) 1 (-complement) hsum

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem eventReverseSub_eqv_complementSub
    {a aComplement b bComplement : Q'}
    (ha : a + aComplement ≈ (1 : Q'))
    (hb : b + bComplement ≈ (1 : Q')) :
    a - b ≈ bComplement - aComplement := by
  refine Q'.eqv_trans _
    (((1 : Q') - aComplement) - ((1 : Q') - bComplement)) _
    (sub_eqv_both_local
      (left_eqv_one_sub_right ha)
      (left_eqv_one_sub_right hb)) ?_
  change
    ((1 + (-aComplement)) + (-(1 + (-bComplement)))).eqv
      (bComplement + (-aComplement))
  have hneg : (-(1 + (-bComplement))).eqv
      ((-1) + bComplement) := by
    refine Q'.eqv_trans _ ((-1) + (-(-bComplement))) _
      (Q'.neg_add_eqv 1 (-bComplement)) ?_
    exact Q'.add_eqv_congr_left (-1) (-(-bComplement)) bComplement
      (Q'.neg_neg_eqv bComplement)
  refine Q'.eqv_trans _
    ((1 + (-aComplement)) + ((-1) + bComplement)) _
    (Q'.add_eqv_congr_left (1 + (-aComplement)) _ _ hneg) ?_
  refine Q'.eqv_trans _
    ((1 + (-1)) + ((-aComplement) + bComplement)) _
    (Q'.add_swap_inner 1 (-aComplement) (-1) bComplement) ?_
  refine Q'.eqv_trans _
    (0 + ((-aComplement) + bComplement)) _
    (Q'.add_eqv_congr_right (1 + (-1)) 0
      ((-aComplement) + bComplement)
      (Q'.add_neg_self_eqv 1)) ?_
  refine Q'.eqv_trans _ ((-aComplement) + bComplement) _
    (Q'.eqv_of_eq (Q'.zero_add' ((-aComplement) + bComplement))) ?_
  exact Q'.add_comm_eqv (-aComplement) bComplement

theorem anchorCylinderProbability_reverse_sub_le_boundaryEpsilon_of_inside
    {small n inner distance : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (hinside : ∀ root, root ∈ rawRoots →
      PolymerInsideBox inner small root)
    (predicate : List Bool → Bool)
    (hbox : inner + distance = small) :
    anchorEventProbability small
          (sourceCylinderEvent rawRoots predicate) -
        anchorEventProbability n
          (targetCylinderEvent small n rawRoots predicate) ≤
      cylinderBoundaryEpsilon rawRoots.length distance := by
  let sourceEvent := sourceCylinderEvent rawRoots predicate
  let targetEvent := targetCylinderEvent small n rawRoots predicate
  let sourceComplement :=
    sourceCylinderEvent rawRoots (complementCylinderPredicate predicate)
  let targetComplement :=
    targetCylinderEvent small n rawRoots
      (complementCylinderPredicate predicate)
  have hcomplement :=
    anchorCylinderProbability_sub_le_boundaryEpsilon_of_inside
      hsmall hroots hinside (complementCylinderPredicate predicate) hbox
  have hsourcePointwise : sourceComplement =
      (fun family => !(sourceEvent family)) := by
    funext family
    rfl
  have htargetPointwise : targetComplement =
      (fun family => !(targetEvent family)) := by
    funext family
    rfl
  have hsourceSum :
      anchorEventProbability small sourceEvent +
          anchorEventProbability small sourceComplement ≈ (1 : Q') := by
    rw [hsourcePointwise]
    exact anchorEventProbability_add_complement_eqv_one small sourceEvent
  have htargetSum :
      anchorEventProbability n targetEvent +
          anchorEventProbability n targetComplement ≈ (1 : Q') := by
    rw [htargetPointwise]
    exact anchorEventProbability_add_complement_eqv_one n targetEvent
  have hreorder :
      anchorEventProbability small sourceEvent -
          anchorEventProbability n targetEvent ≈
        anchorEventProbability n targetComplement -
          anchorEventProbability small sourceComplement :=
    eventReverseSub_eqv_complementSub hsourceSum htargetSum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hcomplement

private theorem sub_swap_eqv_neg_local (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a).eqv (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

/-- Full finite-volume modulus for an arbitrary Boolean function of a finite
canonical occurrence fingerprint. -/
theorem anchorCylinderProbability_abs_sub_le_boundaryEpsilon_of_inside
    {small n inner distance : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (hinside : ∀ root, root ∈ rawRoots →
      PolymerInsideBox inner small root)
    (predicate : List Bool → Bool)
    (hbox : inner + distance = small) :
    Q'.abs
        (anchorEventProbability n
            (targetCylinderEvent small n rawRoots predicate) -
          anchorEventProbability small
            (sourceCylinderEvent rawRoots predicate)) ≤
      cylinderBoundaryEpsilon rawRoots.length distance := by
  apply Q'.abs_le
  · have hreverse :=
      anchorCylinderProbability_reverse_sub_le_boundaryEpsilon_of_inside
        hsmall hroots hinside predicate hbox
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (sub_swap_eqv_neg_local
            (anchorEventProbability small
              (sourceCylinderEvent rawRoots predicate))
            (anchorEventProbability n
              (targetCylinderEvent small n rawRoots predicate)))))
  · exact anchorCylinderProbability_sub_le_boundaryEpsilon_of_inside
      hsmall hroots hinside predicate hbox

end YMGap.Continuum.Z4CanonicalCylinderStability

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderStability.transportedCanonicalCylinderAtoms_inner_face
#print axioms YMGap.Continuum.Z4CanonicalCylinderStability.anchorCylinderCrossDifference_le_boundaryTail_of_inside
#print axioms YMGap.Continuum.Z4CanonicalCylinderStability.anchorCylinderProbability_sub_le_boundaryEpsilon_of_inside
#print axioms YMGap.Continuum.Z4CanonicalCylinderStability.anchorCylinderProbability_reverse_sub_le_boundaryEpsilon_of_inside
#print axioms YMGap.Continuum.Z4CanonicalCylinderStability.anchorCylinderProbability_abs_sub_le_boundaryEpsilon_of_inside
