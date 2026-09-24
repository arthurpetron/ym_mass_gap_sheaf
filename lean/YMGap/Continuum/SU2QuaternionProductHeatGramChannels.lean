/-
# Explicit finite Gram channels for the product heat kernel

The representation-column Gram identity is flattened into a literal list of
nonnegative weighted lower-half polynomials.  Cartesian multiplication of
these lists gives the corresponding expansion of the original product heat
kernel.  Repeated selected blocks are retained.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPositive
import YMGap.Continuum.QuaternionHaarAngularCarrier
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.SU2QuaternionProductHeatGramChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionPolynomialGramPositivity
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2CharacterVacuumHaar (coeffAt)
open YMGap.Continuum.BondMovingStep

abbrev GramChannel := Q' × RatPoly

/-- The literal weighted sum of lower/upper copies of the channel polynomial. -/
def channelKernel (n : Nat) : List GramChannel → RatPoly
  | [] => polyZero
  | c :: cs => polyAdd
      (polySmul c.1 (polyMul c.2 (liftBoundary n c.2)))
      (channelKernel n cs)

private theorem channelKernel_append (n : Nat) : ∀ as bs,
    RatPolyCoeffEqv (channelKernel n (as ++ bs))
      (polyAdd (channelKernel n as) (channelKernel n bs))
  | [], _ => (RatPolyCoeffEqv.zero_add _).symm
  | _ :: as, bs =>
      ((RatPolyCoeffEqv.refl _).add (channelKernel_append n as bs)).trans
        (RatPolyCoeffEqv.add_assoc _ _ _).symm

private theorem channelKernel_flatMap {A : Type} (n : Nat) (f : A → List GramChannel) :
    ∀ xs, RatPolyCoeffEqv (channelKernel n (xs.flatMap f))
      (finitePolySum (fun a => channelKernel n (f a)) xs)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => (channelKernel_append n (f a) (xs.flatMap f)).trans
      ((RatPolyCoeffEqv.refl _).add (channelKernel_flatMap n f xs))

/-- Real and imaginary scalar leaves of a polynomial tensor. -/
def tensorLeaves : (degree : Nat) → PolyTensor degree → List RatPoly
  | 0, x => [x.1, x.2]
  | degree + 1, x => tensorLeaves degree (x false) ++ tensorLeaves degree (x true)

def columnChannels (w : Q') (degree k : Nat) (x : PolyTensor degree) : List GramChannel :=
  (tensorLeaves degree x).map fun p => (w * basisInverseWeight degree k, p)

/-- All real column channels of one selected heat factor. -/
def heatChannels (slot : Nat) (w : Q') (K : Nat) : List GramChannel :=
  (List.range (K+1)).flatMap fun degree =>
    (List.range (degree+1)).flatMap fun k =>
      columnChannels (coeffAt (heatKernelPacket K w) degree) degree k
        (polynomialColumn
          (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k)

def multiplyChannel (a b : GramChannel) : GramChannel :=
  (a.1 * b.1, polyMul a.2 b.2)

def multiplyChannels (as bs : List GramChannel) : List GramChannel :=
  as.flatMap fun a => bs.map fun b => multiplyChannel a b

/-- Cartesian tensor product of the selected one-link channel lists. -/
def productChannels (n : Nat) (w : Q') (K : Nat) : List Nat → List GramChannel
  | [] => [(1, polyOne)]
  | i :: ids => multiplyChannels (heatChannels i w K) (productChannels n w K ids)

private theorem support_one (n : Nat) : SupportedQuaternionBlocks n polyOne := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  exact Nat.zero_le _

private theorem support_smul {n : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_add {n : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks n (polyAdd p q) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_twice {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))

private theorem mul_add_left_coeff (left right factor : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd left right) factor)
      (polyAdd (polyMul left factor) (polyMul right factor)) :=
  (RatPolyCoeffEqv.mul_comm _ _).trans
    ((RatPolyCoeffEqv.mul_add_right factor left right).trans
      ((RatPolyCoeffEqv.mul_comm factor left).add
        (RatPolyCoeffEqv.mul_comm factor right)))

/-- A padded coefficient identity between two genuinely supported carrier
polynomials is strong enough for arbitrary later insertions. -/
private theorem carrier_of_padded {n : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (h : PaddedPolynomialCoeffEqv n p q) : HaarCarrierEqv n p q := by
  let identity := identityQuaternionBlockInvolution n
  have hpi : HaarCarrierEqv n
      (reindexQuaternionPolynomial identity p) p :=
    carrierOfPrefix (reindex_supported identity p) hp
      (identityReindexQuaternionPolynomial_prefix n p)
  have hqi : HaarCarrierEqv n
      (reindexQuaternionPolynomial identity q) q :=
    carrierOfPrefix (reindex_supported identity q) hq
      (identityReindexQuaternionPolynomial_prefix n q)
  exact hpi.symm.trans ((RatPolyCoeffEqv.haarCarrier h).trans hqi)

private theorem tensorLeaves_supported {n degree : Nat} {x : PolyTensor degree}
    (hx : PolyTensorSupported n degree x) : ∀ p, p ∈ tensorLeaves degree x →
      SupportedQuaternionBlocks n p := by
  induction degree with
  | zero =>
      intro p hp
      simp only [tensorLeaves, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hx.1
      · rcases hp with rfl | hp
        · exact hx.2
        · exact False.elim (List.not_mem_nil hp)
  | succ degree ih =>
      intro p hp
      simp only [tensorLeaves, List.mem_append] at hp
      exact hp.elim (ih (hx false) p) (ih (hx true) p)

private theorem columnChannels_supported {n slot degree k : Nat} (hslot : slot < n) :
    ∀ c, c ∈ columnChannels (1 : Q') degree k
      (polynomialColumn
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k) →
      SupportedQuaternionBlocks n c.2 := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact tensorLeaves_supported (coordinateColumn_supported hslot degree k) p hp

theorem heatChannels_supported {n slot : Nat} (hslot : slot < n) (w : Q') (K : Nat) :
    ∀ c, c ∈ heatChannels slot w K → SupportedQuaternionBlocks n c.2 := by
  intro c hc
  obtain ⟨degree, hd, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨k, hk, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact tensorLeaves_supported (coordinateColumn_supported hslot degree k) p hp

/-- Every channel polynomial stays on the original lower carrier. -/
theorem productChannels_supported (n : Nat) (w : Q') (K : Nat) : ∀ ids,
    (∀ i, i ∈ ids → i < n) → ∀ c, c ∈ productChannels n w K ids →
      SupportedQuaternionBlocks n c.2
  | [], _, c, hc => by
      simp only [productChannels, List.mem_singleton] at hc
      subst c
      exact support_one n
  | i :: ids, hi, c, hc => by
      obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hab
      exact supported_polyMul
        (heatChannels_supported (hi i List.mem_cons_self) w K a ha)
        (productChannels_supported n w K ids
          (fun j hj => hi j (List.mem_cons_of_mem i hj)) b hb)

private theorem columnChannels_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (degree k : Nat) (x : PolyTensor degree) :
    ∀ c, c ∈ columnChannels w degree k x → (0 : Q') ≤ c.1 := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact Q'.mul_nonneg _ _ hw (Q'.le_of_lt (basisInverseWeight_pos degree k))

private theorem heatChannels_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (slot K : Nat) :
    ∀ c, c ∈ heatChannels slot w K → (0 : Q') ≤ c.1 := by
  intro c hc
  obtain ⟨degree, hd, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨k, hk, hc⟩ := List.mem_flatMap.mp hc
  have hc0 : (0 : Q') ≤ coeffAt (heatKernelPacket K w) degree := by
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hd)]
    exact coeffW_nonneg hw degree
  exact columnChannels_nonnegative hc0 degree k _ c hc

/-- Every Cartesian channel weight is nonnegative for a nonnegative nome. -/
theorem productChannels_nonnegative (n : Nat) {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    ∀ ids, ∀ c, c ∈ productChannels n w K ids → (0 : Q') ≤ c.1
  | [], c, hc => by
      simp only [productChannels, List.mem_singleton] at hc
      subst c
      decide
  | i :: ids, c, hc => by
      obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hab
      exact Q'.mul_nonneg _ _ (heatChannels_nonnegative hw i K a ha)
        (productChannels_nonnegative n hw K ids b hb)

/- The remaining identities flatten the already-proved complex Gram equality.
They are stated on the Haar carrier so arbitrary downstream insertions are
preserved. -/
private theorem tensorLeaves_kernel {n degree : Nat} {x y : PolyTensor degree}
    (hx : PolyTensorSupported n degree x)
    (hy : PolyTensorSupported (n+n) degree y)
    (hxy : TensorLiftImage n degree x y) (weight : Q') :
    HaarCarrierEqv (n+n) (polySmul weight (polyTensorInner degree x y).1)
      (channelKernel n ((tensorLeaves degree x).map fun p => (weight, p))) := by
  induction degree with
  | zero =>
      have hre : RatPolyCoeffEqv (polyTensorInner 0 x y).1
          (polyAdd (polyMul x.1 y.1) (polyMul x.2 y.2)) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.neg (.var 1)) (.var 3))))
          (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
          (fun | 0 => x.1 | 1 => x.2 | 2 => y.1 | _ => y.2)
      refine (RatPolyCoeffEqv.haarCarrier ((hre.smul weight).trans
        (RatPolyCoeffEqv.smul_add weight _ _))).trans ?_
      have h1 : PaddedPolynomialCoeffEqv (n+n)
          (polySmul weight (polyMul x.1 y.1))
          (polySmul weight (polyMul x.1 (liftBoundary n x.1))) :=
        ((PaddedPolynomialCoeffEqv.of_coeff
          (RatPolyCoeffEqv.polyMul_smul_left weight x.1 y.1).symm).trans
            ((PaddedPolynomialCoeffEqv.refl _ (polySmul weight x.1)).mul hxy.1.symm)).trans
          (PaddedPolynomialCoeffEqv.of_coeff
            (RatPolyCoeffEqv.polyMul_smul_left weight x.1 (liftBoundary n x.1)))
      have h2 : PaddedPolynomialCoeffEqv (n+n)
          (polySmul weight (polyMul x.2 y.2))
          (polySmul weight (polyMul x.2 (liftBoundary n x.2))) :=
        ((PaddedPolynomialCoeffEqv.of_coeff
          (RatPolyCoeffEqv.polyMul_smul_left weight x.2 y.2).symm).trans
            ((PaddedPolynomialCoeffEqv.refl _ (polySmul weight x.2)).mul hxy.2.symm)).trans
          (PaddedPolynomialCoeffEqv.of_coeff
            (RatPolyCoeffEqv.polyMul_smul_left weight x.2 (liftBoundary n x.2)))
      exact (carrier_of_padded
        (support_add (support_smul weight (supported_polyMul (support_twice hx.1) hy.1))
          (support_smul weight (supported_polyMul (support_twice hx.2) hy.2)))
        (support_add
          (support_smul weight (supported_polyMul (support_twice hx.1)
            (lift_supported hx.1 n)))
          (support_smul weight (supported_polyMul (support_twice hx.2)
            (lift_supported hx.2 n)))) (h1.add h2)).trans
        (RatPolyCoeffEqv.haarCarrier
          ((RatPolyCoeffEqv.refl _).add
            (RatPolyCoeffEqv.add_zero _).symm))
  | succ degree ih =>
      have hadd := HaarCarrierEqv.trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_add weight _ _))
        (HaarCarrierEqv.add
          (ih (hx false) (hy false) (hxy false))
          (ih (hx true) (hy true) (hxy true)))
      refine hadd.trans ?_
      rw [tensorLeaves, List.map_append]
      exact RatPolyCoeffEqv.haarCarrier
        (channelKernel_append n
          ((tensorLeaves degree (x false)).map fun p => (weight, p))
          ((tensorLeaves degree (x true)).map fun p => (weight, p))).symm

private theorem gramPrefix_carrier (n slot degree : Nat) (hslot : slot < n)
    (coefficient : Q') : ∀ count,
    HaarCarrierEqv (n+n)
      (polySmul coefficient
        (polynomialSum count (fun k =>
          polyRealScale (basisInverseWeight degree k)
            (polyTensorInner degree
              (polynomialColumn
                (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k)
              (polynomialColumn
                (asRepresentationQuaternion (PolyQuaternion.coordinateVariable (n+slot))) degree k)))).1)
      (channelKernel n ((List.range count).flatMap fun k =>
        columnChannels coefficient degree k
          (polynomialColumn
            (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k)))
  | 0 => RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_zero coefficient)
  | count + 1 => by
      have ih := gramPrefix_carrier n slot degree hslot coefficient count
      have hterm := tensorLeaves_kernel
        (coordinateColumn_supported hslot degree count)
        (coordinateColumn_supported (by omega : n+slot < n+n) degree count)
        (coordinateColumn_lift n slot degree count)
        (coefficient * basisInverseWeight degree count)
      have hhead : HaarCarrierEqv (n+n)
          (polySmul coefficient
            (polyRealScale (basisInverseWeight degree count)
              (polyTensorInner degree
                (polynomialColumn
                  (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree count)
                (polynomialColumn
                  (asRepresentationQuaternion
                    (PolyQuaternion.coordinateVariable (n+slot))) degree count))).1)
          (channelKernel n (columnChannels coefficient degree count
            (polynomialColumn
              (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree count))) :=
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.smul_assoc coefficient
            (basisInverseWeight degree count) _)).trans hterm
      refine (RatPolyCoeffEqv.haarCarrier
        (RatPolyCoeffEqv.smul_add coefficient _ _)).trans ?_
      refine (HaarCarrierEqv.add ih hhead).trans ?_
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact RatPolyCoeffEqv.haarCarrier
        (channelKernel_append n
          ((List.range count).flatMap fun k =>
            columnChannels coefficient degree k
              (polynomialColumn
                (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k))
          (columnChannels coefficient degree count
            (polynomialColumn
              (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree count))).symm

private theorem finiteChannels_carrier {A : Type} (n : Nat)
    (f : A → RatPoly) (channels : A → List GramChannel) : ∀ xs : List A,
    (∀ a, a ∈ xs → HaarCarrierEqv (n+n) (f a) (channelKernel n (channels a))) →
    HaarCarrierEqv (n+n) (finitePolySum f xs)
      (channelKernel n (xs.flatMap channels))
  | [], _ => HaarCarrierEqv.refl _ _
  | a :: xs, h =>
      (HaarCarrierEqv.add (h a List.mem_cons_self)
        (finiteChannels_carrier n f channels xs
          (fun b hb => h b (List.mem_cons_of_mem a hb)))).trans
        (RatPolyCoeffEqv.haarCarrier
          (channelKernel_append n (channels a) (xs.flatMap channels)).symm)

theorem heatChannels_carrier (n slot : Nat) (hslot : slot < n) (w : Q') (K : Nat) :
    HaarCarrierEqv (n+n) (heatAt slot (n+slot) w K)
      (channelKernel n (heatChannels slot w K)) := by
  refine (RatPolyCoeffEqv.haarCarrier (heatAt_symm slot (n+slot) w K)).trans ?_
  unfold heatAt heatChannels
  apply finiteChannels_carrier
  intro degree hdegree
  have hg := (character_haar_gram_of_unit_radii
    (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot))
    (asRepresentationQuaternion (PolyQuaternion.coordinateVariable (n+slot)))
    (haarNorm_coordinate (by omega : slot < n+n))
    (haarNorm_coordinate (by omega : n+slot < n+n)) degree).1
  have hs := characterPolynomial_coeffEqv
    (pathProduct_scalar (PolyQuaternion.coordinateVariable slot)
      (PolyQuaternion.coordinateVariable (n+slot))) degree
  refine (HaarCarrierEqv.smul (coeffAt (heatKernelPacket K w) degree)
    ((RatPolyCoeffEqv.haarCarrier hs).trans hg)).trans ?_
  exact gramPrefix_carrier n slot degree hslot
    (coeffAt (heatKernelPacket K w) degree) (degree+1)

private theorem channelKernel_product (n : Nat) (as bs : List GramChannel) :
    HaarCarrierEqv (n+n) (polyMul (channelKernel n as) (channelKernel n bs))
      (channelKernel n (multiplyChannels as bs)) := by
  induction as with
  | nil => exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_left _)
  | cons a as ih =>
      have hhead : HaarCarrierEqv (n+n)
          (polyMul (polySmul a.1 (polyMul a.2 (liftBoundary n a.2)))
            (channelKernel n bs))
          (channelKernel n (bs.map fun b => multiplyChannel a b)) := by
        clear ih
        induction bs with
        | nil => exact RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _)
        | cons b bs hb =>
            refine (RatPolyCoeffEqv.haarCarrier
              (RatPolyCoeffEqv.mul_add_right _ _ _)).trans ?_
            have hterm : RatPolyCoeffEqv
                (polyMul (polySmul a.1 (polyMul a.2 (liftBoundary n a.2)))
                  (polySmul b.1 (polyMul b.2 (liftBoundary n b.2))))
                (polySmul (a.1*b.1) (polyMul (polyMul a.2 b.2)
                  (liftBoundary n (polyMul a.2 b.2)))) := by
              refine (RatPolyCoeffEqv.polyMul_smul_left a.1
                (polyMul a.2 (liftBoundary n a.2))
                (polySmul b.1 (polyMul b.2 (liftBoundary n b.2)))).trans ?_
              refine ((RatPolyCoeffEqv.polyMul_smul_right b.1
                (polyMul a.2 (liftBoundary n a.2))
                (polyMul b.2 (liftBoundary n b.2))).smul a.1).trans ?_
              refine (RatPolyCoeffEqv.smul_assoc a.1 b.1 _).trans ?_
              rw [lift_product]
              exact (coeffEvalExpr_eqv_of_normalize_eq
                (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
                (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
                (by decide)
                (fun | 0 => a.2 | 1 => liftBoundary n a.2
                     | 2 => b.2 | _ => liftBoundary n b.2)).smul (a.1*b.1)
            exact HaarCarrierEqv.add (RatPolyCoeffEqv.haarCarrier hterm) hb
      refine (RatPolyCoeffEqv.haarCarrier (mul_add_left_coeff _ _ _)).trans ?_
      refine (HaarCarrierEqv.add hhead ih).trans ?_
      exact RatPolyCoeffEqv.haarCarrier
        (channelKernel_append n (bs.map fun b => multiplyChannel a b)
          (multiplyChannels as bs)).symm

private theorem channelKernel_unit (n : Nat) :
    HaarCarrierEqv (n+n) polyOne (channelKernel n [(1, polyOne)]) := by
  have hfirst : PaddedPolynomialCoeffEqv (n+n)
      (channelKernel n [(1, polyOne)])
      (polyAdd (polySmul 1 (polyMul polyOne polyOne)) polyZero) :=
    ((((PaddedPolynomialCoeffEqv.refl _ polyOne).mul
      (lift_one (n+n) n)).smul 1).add (PaddedPolynomialCoeffEqv.refl _ polyZero))
  have hstep : PaddedPolynomialCoeffEqv (n+n)
      (polyAdd (polySmul 1 (polyMul polyOne polyOne)) polyZero)
      (polyAdd polyOne polyZero) :=
    PaddedPolynomialCoeffEqv.of_coeff
      ((((RatPolyCoeffEqv.one_mul polyOne).smul 1).trans
        (RatPolyCoeffEqv.one_smul polyOne)).add (RatPolyCoeffEqv.refl polyZero))
  have hfinal : PaddedPolynomialCoeffEqv (n+n)
      (polyAdd polyOne polyZero) polyOne :=
    PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.add_zero polyOne)
  have h := hfirst.trans (hstep.trans hfinal)
  have hq : SupportedQuaternionBlocks (n+n) (channelKernel n [(1, polyOne)]) :=
    support_add (support_smul 1 (supported_polyMul (support_one _) (lift_supported (support_one n) n)))
      (fun _ hm => False.elim (List.not_mem_nil hm))
  exact (carrier_of_padded hq (support_one _) h).symm

/-- Exact finite Gram-channel expansion of the original product heat kernel. -/
theorem productHeat_gram_carrier (n : Nat) (w : Q') (K : Nat) : ∀ ids,
    (∀ i, i ∈ ids → i < n) →
    HaarCarrierEqv (n+n) (productHeat n w K ids)
      (channelKernel n (productChannels n w K ids))
  | [], _ => channelKernel_unit n
  | i :: ids, hi =>
      HaarCarrierEqv.trans
        (HaarCarrierEqv.mul
          (heatChannels_carrier n i (hi i List.mem_cons_self) w K)
          (productHeat_gram_carrier n w K ids
            (fun j hj => hi j (List.mem_cons_of_mem i hj))))
        (channelKernel_product n _ _)

end YMGap.Continuum.SU2QuaternionProductHeatGramChannels

#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.channelKernel
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.productChannels
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.heatChannels_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.heatChannels_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.productChannels_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.productChannels_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatGramChannels.productHeat_gram_carrier
