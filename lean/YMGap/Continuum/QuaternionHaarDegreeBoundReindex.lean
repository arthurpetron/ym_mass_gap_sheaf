/-
# Block-degree ceilings under quaternion block reindexing

A bounded total degree in a source quaternion block is carried to the
corresponding target block under an explicit block involution. The proof uses
the padded exponent lookup directly, so monomials shorter than the full
coordinate prefix are covered as well.
-/

import YMGap.Continuum.SU2QuaternionBlockDegreeBound
import YMGap.Continuum.BF4ExactSlabSelectedFaceFold

namespace YMGap.Continuum.QuaternionHaarDegreeBoundReindex

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (quaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial
    exponentAt_reindexQuaternionExponents)
open YMGap.Continuum.SU2QuaternionBlockDegreeBound (DegreeLE)

/-- Degree ceilings transform contravariantly: target block `t` reads the
source block `permutation.map t`. Exponent lookups are padded by zero, so this
also applies to monomials shorter than `4 * blocks`. -/
theorem degreeLE_reindex
    {blocks source target degree : Nat}
    (permutation : QuaternionBlockInvolution blocks)
    (htarget : target < blocks)
    (hmap : permutation.map target = source)
    {polynomial : RatPoly}
    (hdegree : DegreeLE source degree polynomial) :
    DegreeLE target degree
      (reindexQuaternionPolynomial permutation polynomial) := by
  intro term hterm
  unfold reindexQuaternionPolynomial at hterm
  obtain ⟨original, horiginal, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq]
  have horiginalDegree := hdegree original horiginal
  unfold quaternionBlockDegree at horiginalDegree ⊢
  rw [exponentAt_reindexQuaternionExponents permutation original.1 (by omega),
    exponentAt_reindexQuaternionExponents permutation original.1 (by omega),
    exponentAt_reindexQuaternionExponents permutation original.1 (by omega),
    exponentAt_reindexQuaternionExponents permutation original.1 (by omega)]
  have hd0 : (4 * target) / 4 = target := by omega
  have hm0 : (4 * target) % 4 = 0 := by omega
  have hd1 : (4 * target + 1) / 4 = target := by omega
  have hm1 : (4 * target + 1) % 4 = 1 := by omega
  have hd2 : (4 * target + 2) / 4 = target := by omega
  have hm2 : (4 * target + 2) % 4 = 2 := by omega
  have hd3 : (4 * target + 3) / 4 = target := by omega
  have hm3 : (4 * target + 3) % 4 = 3 := by omega
  rw [hd0, hm0, hd1, hm1, hd2, hm2, hd3, hm3, hmap]
  simpa only [Nat.add_zero] using horiginalDegree

#print axioms degreeLE_reindex

end YMGap.Continuum.QuaternionHaarDegreeBoundReindex
