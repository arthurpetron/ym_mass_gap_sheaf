/-
# Constructive-real positivity of the strict reflected local Gram matrix

The strict lower/upper local query has a fixed number of Boolean outputs.
We enumerate every Boolean word of that length once and for all.  At every
centered stage, the normalized corrected-slab pair law is the deterministic
pushforward of the exact finite reflection Gram to this fixed space.  Words
which are not attained have empty fibres and hence contribute exactly zero.

Consequently the finite quadratic on this stage-independent state list is
nonnegative for every exact rational coefficient.  The entrywise half-power
modulus from the strict centered limit gives an explicit Cauchy modulus for
the whole quadratic, and finite-stage positivity passes both to the standard
constructive-real order and to the sound eventual lower-bound relation.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteJointKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerFaceQueryDecoder
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One fixed exhaustive fingerprint space -/

def strictJointFingerprintSpace : Nat → List (List Bool)
  | 0 => [[]]
  | count + 1 =>
      (strictJointFingerprintSpace count).map (fun bits => false :: bits) ++
        (strictJointFingerprintSpace count).map (fun bits => true :: bits)

theorem strictJointFingerprintSpace_complete :
    ∀ {count : Nat} (bits : List Bool), bits.length = count →
      bits ∈ strictJointFingerprintSpace count
  | 0, bits, hlength => by
      cases bits with
      | nil => exact List.mem_cons_self
      | cons bit tail =>
          simp only [List.length_cons] at hlength
          omega
  | count + 1, [], hlength => by
      simp only [List.length_nil] at hlength
      omega
  | count + 1, bit :: bits, hlength => by
      have htail : bits.length = count := by
        simp only [List.length_cons] at hlength
        omega
      cases bit with
      | false =>
          apply List.mem_append_left
          exact List.mem_map.mpr
            ⟨bits, strictJointFingerprintSpace_complete bits htail, rfl⟩
      | true =>
          apply List.mem_append_right
          exact List.mem_map.mpr
            ⟨bits, strictJointFingerprintSpace_complete bits htail, rfl⟩

theorem strictJointFingerprintSpace_sound :
    ∀ {count : Nat} {bits : List Bool},
      bits ∈ strictJointFingerprintSpace count → bits.length = count
  | 0, bits, hbits => by
      have hsingleton : bits = [] := List.mem_singleton.mp hbits
      rw [hsingleton]
      rfl
  | count + 1, bits, hbits => by
      change bits ∈
        (strictJointFingerprintSpace count).map (fun word => false :: word) ++
          (strictJointFingerprintSpace count).map
            (fun word => true :: word) at hbits
      rcases List.mem_append.mp hbits with hfalse | htrue
      · obtain ⟨tail, htail, hbitsEq⟩ := List.mem_map.mp hfalse
        rw [← hbitsEq]
        simp only [List.length_cons]
        rw [strictJointFingerprintSpace_sound htail]
      · obtain ⟨tail, htail, hbitsEq⟩ := List.mem_map.mp htrue
        rw [← hbitsEq]
        simp only [List.length_cons]
        rw [strictJointFingerprintSpace_sound htail]

theorem mem_strictJointFingerprintSpace_iff
    {count : Nat} {bits : List Bool} :
    bits ∈ strictJointFingerprintSpace count ↔ bits.length = count :=
  ⟨strictJointFingerprintSpace_sound,
    strictJointFingerprintSpace_complete bits⟩

theorem strictJointFingerprintSpace_nodup :
    ∀ count : Nat, (strictJointFingerprintSpace count).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | count + 1 => by
      have ih := strictJointFingerprintSpace_nodup count
      have hfalse :
          ((strictJointFingerprintSpace count).map
            (fun bits => false :: bits)).Nodup :=
        nodup_map_of_cons_injOn (strictJointFingerprintSpace count) ih
      have htrue :
          ((strictJointFingerprintSpace count).map
            (fun bits => true :: bits)).Nodup :=
        nodup_map_of_cons_injOn (strictJointFingerprintSpace count) ih
      apply List.nodup_append.mpr
      refine ⟨hfalse, htrue, ?_⟩
      intro left hleft right hright heq
      obtain ⟨leftTail, hleftTail, hleftEq⟩ := List.mem_map.mp hleft
      obtain ⟨rightTail, hrightTail, hrightEq⟩ := List.mem_map.mp hright
      rw [← hleftEq, ← hrightEq] at heq
      exact Bool.false_ne_true (List.cons.inj heq).1

theorem centralStrictLocalQueryCode_length
    (radius base : Nat) (roots : List (List Nat))
    (support : List Nat) :
    (centralStrictLocalQueryCode radius base roots support).length =
      roots.length := by
  unfold centralStrictLocalQueryCode
    Z4HalfTimeReflectionLowerSupportLocalQuery.centralLowerSupportQueryFingerprint
    canonicalRootsSupportQueryFingerprint
  simp only [List.length_map, centralStrictLowerCylinderRoots_length]

theorem centralStrictLocalQueryCode_mem_fixedSpace
    (radius base : Nat) (roots : List (List Nat))
    (support : List Nat) :
    centralStrictLocalQueryCode radius base roots support ∈
      strictJointFingerprintSpace roots.length :=
  strictJointFingerprintSpace_complete _
    (centralStrictLocalQueryCode_length radius base roots support)

/-! ## 2. The fixed finite Gram quadratic at one stage -/

def centralNormalizedStrictJointFixedQuadraticSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) : Q' :=
  finiteJointQuadratic
    (strictJointFingerprintSpace roots.length) coefficient
    (fun left right =>
      centralNormalizedStrictJointGramSequence
        coupling hcoupling base roots left right stage)

theorem centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) :
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base roots coefficient stage ≈
      centralNormalizedSupportReflectionQuadratic
        coupling hcoupling
        (centralStrictJointCenteredStageCutoff base stage)
        (strictQueryBase base + stage)
        (centralLocalSupportCoefficient
          (centralStrictLocalQueryCode
            (strictQueryBase base + stage) base roots)
          coefficient) := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let code := centralStrictLocalQueryCode radius base roots
  let source := centralHalfSupportSpace radius
  let joint := centralNormalizedSupportPairLaw
    coupling hcoupling cutoff radius
  have hpush := finiteJointQuadratic_pushforward_eqv_pullback
    source joint code (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace_nodup roots.length)
    (fun support _ => by
      exact centralStrictLocalQueryCode_mem_fixedSpace
        radius base roots support)
    coefficient
  have hreflection :=
    centralNormalizedSupportReflectionQuadratic_eq_jointLaw
      coupling hcoupling cutoff radius
      (centralLocalSupportCoefficient code coefficient)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hreflection)
  simpa only [centralNormalizedStrictJointFixedQuadraticSequence,
    centralNormalizedStrictJointGramSequence,
    centralNormalizedLocalSupportPairLaw,
    centralLocalSupportCoefficient, radius, cutoff, code, source, joint]
    using hpush

theorem centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (coefficient : List Bool → Q') (stage : Nat) :
    (0 : Q') ≤ centralNormalizedStrictJointFixedQuadraticSequence
      coupling hcoupling base roots coefficient stage := by
  have hreflection := centralNormalizedSupportReflectionQuadratic_nonnegative
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
    (centralLocalSupportCoefficient
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base roots)
      coefficient)
  exact Q'.le_trans' _ _ _ hreflection
    (Q'.ge_of_eqv
      (centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
        coupling hcoupling base roots coefficient stage))

/-! ## 3. An explicit quadratic half-power modulus -/

theorem coefficientL1_nonnegative_local
    {State : Type} (states : List State) (coefficient : State → Q') :
    (0 : Q') ≤ coefficientL1 states coefficient := by
  unfold coefficientL1
  apply listQSum_nonnegative_on
  intro state hstate
  exact Q'.abs_nonneg (coefficient state)

def strictJointFixedQuadraticCauchyCoefficient
    (roots : List (List Nat))
    (coefficient : List Bool → Q') : Q' :=
  (coefficientL1 (strictJointFingerprintSpace roots.length) coefficient *
      coefficientL1 (strictJointFingerprintSpace roots.length) coefficient) *
    strictJointGivenSlabCauchyCoefficient
      (roots.length + roots.length)

theorem strictJointFixedQuadraticCauchyCoefficient_nonnegative
    (roots : List (List Nat))
    (coefficient : List Bool → Q') :
    (0 : Q') ≤ strictJointFixedQuadraticCauchyCoefficient
      roots coefficient := by
  unfold strictJointFixedQuadraticCauchyCoefficient
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (coefficientL1_nonnegative_local _ coefficient)
      (coefficientL1_nonnegative_local _ coefficient))
    (strictJointGivenSlabCauchyCoefficient_nonnegative
      (roots.length + roots.length))

theorem centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    Q'.abs
        (centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient later -
          centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base roots coefficient earlier) ≤
      strictJointFixedQuadraticCauchyCoefficient roots coefficient *
        HalfPow.half ^ earlier := by
  let states := strictJointFingerprintSpace roots.length
  let entryCoefficient := strictJointGivenSlabCauchyCoefficient
    (roots.length + roots.length)
  let epsilon := entryCoefficient * HalfPow.half ^ earlier
  have hepsilon : (0 : Q') ≤ epsilon :=
    Q'.mul_nonneg _ _
      (strictJointGivenSlabCauchyCoefficient_nonnegative
        (roots.length + roots.length))
      (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg earlier)
  have hfinite := finiteJointQuadratic_abs_sub_le_square
    states coefficient
    (fun left right =>
      centralNormalizedStrictJointGramSequence
        coupling hcoupling base roots left right later)
    (fun left right =>
      centralNormalizedStrictJointGramSequence
        coupling hcoupling base roots left right earlier)
    epsilon hepsilon
    (fun left right _ _ => by
      exact centralNormalizedStrictJointGramSequence_pair_abs_le
        hcoupling hle hstage hroots left right)
  have hreorder :
      (coefficientL1 states coefficient * coefficientL1 states coefficient) *
          (entryCoefficient * HalfPow.half ^ earlier) ≈
        strictJointFixedQuadraticCauchyCoefficient roots coefficient *
          HalfPow.half ^ earlier := by
    unfold strictJointFixedQuadraticCauchyCoefficient
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficientL1 states coefficient * coefficientL1 states coefficient)
        entryCoefficient (HalfPow.half ^ earlier))
  change Q'.abs
      (finiteJointQuadratic states coefficient
          (fun left right =>
            centralNormalizedStrictJointGramSequence
              coupling hcoupling base roots left right later) +
        (-finiteJointQuadratic states coefficient
          (fun left right =>
            centralNormalizedStrictJointGramSequence
              coupling hcoupling base roots left right earlier))) ≤
    strictJointFixedQuadraticCauchyCoefficient roots coefficient *
      HalfPow.half ^ earlier
  exact Q'.le_trans' _ _ _ hfinite (Q'.le_of_eqv hreorder)

/-! ## 4. The reflection-positive constructive-real quadratic -/

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) ≤ epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

def centralNormalizedStrictJointFixedQuadraticLimit
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') : CReal where
  approx := centralNormalizedStrictJointFixedQuadraticSequence
    coupling hcoupling base roots coefficient
  cauchy := by
    intro tolerance htolerance
    let cauchyCoefficient :=
      strictJointFixedQuadraticCauchyCoefficient roots coefficient
    let scaledTolerance :=
      tolerance * Q'.invSucc cauchyCoefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ cauchyCoefficient :=
      strictJointFixedQuadraticCauchyCoefficient_nonnegative
        roots coefficient
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos htolerance
        (Q'.invSucc_pos cauchyCoefficient.num.toNat)
    have hscaledFinal :
        cauchyCoefficient * scaledTolerance ≤ tolerance :=
      ExpNeg.mul_le_of_mul_invSucc_toNat cauchyCoefficient tolerance
        hcoefficient (Q'.le_of_lt htolerance)
    refine ⟨scaledTolerance.den, fun m n hm hn => ?_⟩
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
          hcoupling hle hmn hroots coefficient
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance cauchyCoefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient n -
            centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient m) ≤ tolerance :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
          hcoupling hle hnm hroots coefficient
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den ≤
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance cauchyCoefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient m -
            centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient n) ≤ tolerance :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

@[simp] theorem centralNormalizedStrictJointFixedQuadraticLimit_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    (centralNormalizedStrictJointFixedQuadraticLimit
      coupling hcoupling hle hroots coefficient).approx stage =
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base roots coefficient stage := rfl

theorem centralNormalizedStrictJointFixedQuadraticLimit_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    CReal.ofQ' 0 ≤ centralNormalizedStrictJointFixedQuadraticLimit
      coupling hcoupling hle hroots coefficient := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  exact centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
    coupling hcoupling base roots coefficient stage

/-- Sound limiting reflection positivity for every exact rational
coefficient on the fixed finite strict-query fingerprint space. -/
theorem centralNormalizedStrictJointFixedQuadraticLimit_reflectionPositive
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    ExpPos.geRat
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle hroots coefficient) 0 := by
  apply ExpPos.geRat_of_eventually
  exact ⟨0, fun stage _ =>
    centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
      coupling hcoupling base roots coefficient stage⟩

#print axioms strictJointFingerprintSpace_complete
#print axioms strictJointFingerprintSpace_nodup
#print axioms centralStrictLocalQueryCode_mem_fixedSpace
#print axioms centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
#print axioms centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
#print axioms centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
#print axioms centralNormalizedStrictJointFixedQuadraticLimit
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_nonnegative
#print axioms centralNormalizedStrictJointFixedQuadraticLimit_reflectionPositive

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
