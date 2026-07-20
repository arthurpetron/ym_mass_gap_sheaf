/-
# Public arbitrary-block support for fundamental quaternion coefficients

This leaf exposes the small exponent-offset and block-locality facts shared by
the four- and six-valent partial Haar projectors.  Keeping them above those
projectors avoids duplicating symbolic `4 * block + component` reductions and
does not enlarge the dependency cone of the foundational partial-Schur leaf.

No bounded assignment family or multi-index Boolean sum is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur

namespace YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur

/-! ## 1. Exact exponent lookup at a symbolic quaternion-block offset -/

theorem exponentAt_varMono (source coordinate : Nat) :
    exponentAt (varMono source) coordinate =
      if coordinate = source then 1 else 0 := by
  induction source generalizing coordinate with
  | zero =>
      cases coordinate <;> rfl
  | succ source ih =>
      have hvar : varMono (source + 1) = 0 :: varMono source := by
        unfold varMono
        rw [List.replicate_succ]
        rfl
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          rw [hvar]
          simpa only [exponentAt, List.getD,
            List.getElem?_cons_succ, Nat.add_one_inj]
            using ih coordinate

theorem exponentAt_blockVariableNat
    (block component query : Nat) :
    exponentAt (varMono (4 * block + component)) (4 * block + query) =
      if query = component then 1 else 0 := by
  rw [exponentAt_varMono]
  by_cases heq : query = component
  · simp only [heq, if_true]
  · have hcoordinate :
        4 * block + query ≠ 4 * block + component := by omega
    simp only [hcoordinate, heq, if_false]

theorem exponentAt_blockBase_query (block query : Nat) :
    exponentAt (varMono (4 * block)) (4 * block + query) =
      if query = 0 then 1 else 0 := by
  simpa only [Nat.add_zero] using
    exponentAt_blockVariableNat block 0 query

theorem exponentAt_blockComponent_base (block component : Nat) :
    exponentAt (varMono (4 * block + component)) (4 * block) =
      if 0 = component then 1 else 0 := by
  simpa only [Nat.add_zero] using
    exponentAt_blockVariableNat block component 0

theorem exponentAt_blockBase_base (block : Nat) :
    exponentAt (varMono (4 * block)) (4 * block) = 1 := by
  simpa only [Nat.add_zero] using
    exponentAt_blockVariableNat block 0 0

/-! ## 2. Public locality of the oriented fundamental coefficients -/

private theorem quaternionBlockLocal_polyVar
    (block : Nat) (component : Fin 4) :
    QuaternionBlockLocal block
      (polyVar (4 * block + component.val)) := by
  intro term hterm coordinate hout
  simp only [polyVar, List.mem_singleton] at hterm
  subst term
  rw [exponentAt_varMono]
  have hne : coordinate ≠ 4 * block + component.val := by
    intro heq
    apply hout
    rw [heq]
    unfold coordinateInQuaternionBlock
    exact ⟨by omega, by omega⟩
  simp only [hne, if_false]

private theorem quaternionBlockLocal_polyNeg
    {block : Nat} {polynomial : RatPoly}
    (hlocal : QuaternionBlockLocal block polynomial) :
    QuaternionBlockLocal block (polyNeg polynomial) := by
  intro term hterm coordinate hout
  unfold polyNeg at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hlocal source hsource coordinate hout

private theorem complexQuaternionBlockLocal_conj
    {block : Nat} {value : ComplexRatPoly}
    (hlocal : ComplexQuaternionBlockLocal block value) :
    ComplexQuaternionBlockLocal block (complexRatPolyConj value) := by
  exact ⟨hlocal.1, quaternionBlockLocal_polyNeg hlocal.2⟩

/-- A forward fundamental matrix coefficient is supported on precisely its
selected quaternion block. -/
theorem complexQuaternionBlockLocal_forwardFundamentalCoefficient
    (block : Nat) (row column : Bool) :
    ComplexQuaternionBlockLocal block
      (forwardFundamentalCoefficient block row column) := by
  have h0 : QuaternionBlockLocal block (polyVar (4 * block)) := by
    simpa using quaternionBlockLocal_polyVar block (⟨0, by omega⟩ : Fin 4)
  have h1 : QuaternionBlockLocal block (polyVar (4 * block + 1)) :=
    quaternionBlockLocal_polyVar block (⟨1, by omega⟩ : Fin 4)
  have h2 : QuaternionBlockLocal block (polyVar (4 * block + 2)) :=
    quaternionBlockLocal_polyVar block (⟨2, by omega⟩ : Fin 4)
  have h3 : QuaternionBlockLocal block (polyVar (4 * block + 3)) :=
    quaternionBlockLocal_polyVar block (⟨3, by omega⟩ : Fin 4)
  cases row <;> cases column
  · exact ⟨h0, h1⟩
  · exact ⟨h2, h3⟩
  · exact ⟨quaternionBlockLocal_polyNeg h2, h3⟩
  · exact ⟨h0, quaternionBlockLocal_polyNeg h1⟩

/-- A reverse coefficient, including its conjugate transpose, is supported
on precisely its selected quaternion block. -/
theorem complexQuaternionBlockLocal_reverseFundamentalCoefficient
    (block : Nat) (row column : Bool) :
    ComplexQuaternionBlockLocal block
      (reverseFundamentalCoefficient block row column) := by
  exact complexQuaternionBlockLocal_conj
    (complexQuaternionBlockLocal_forwardFundamentalCoefficient
      block column row)

#print axioms exponentAt_blockVariableNat
#print axioms exponentAt_blockBase_query
#print axioms exponentAt_blockComponent_base
#print axioms exponentAt_blockBase_base
#print axioms complexQuaternionBlockLocal_forwardFundamentalCoefficient
#print axioms complexQuaternionBlockLocal_reverseFundamentalCoefficient

end YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
