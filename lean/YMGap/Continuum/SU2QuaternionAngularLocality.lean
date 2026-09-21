/-
# Block locality of quaternion angular derivatives

Formal differentiation only lowers an exponent, so it cannot introduce a
previously absent quaternion block.  Consequently a head angular derivative
preserves any block-local support predicate that contains the head block.
The final theorem transports this fact through an explicit involutive block
reindexing.  These are syntactic support statements only: no Haar identity,
positivity estimate, or response bound is asserted.
-/

import YMGap.Continuum.SU2QuaternionBlockLocality
import YMGap.Continuum.SU2QuaternionAngularDerivative

namespace YMGap.Continuum.SU2QuaternionAngularLocality

set_option autoImplicit false

open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionBlockLocality

private theorem exponentAt_lowerExponentAt_eq_zero
    (coordinate target : Nat) : forall monomial : List Nat,
    exponentAt monomial target = 0 ->
      exponentAt (lowerExponentAt coordinate monomial) target = 0
  | [], _ => by
      simp [lowerExponentAt, exponentAt]
  | exponent :: rest, h => by
      cases coordinate with
      | zero =>
          cases target with
          | zero =>
              simp only [lowerExponentAt, exponentAt, List.getD_cons_zero] at h ⊢
              omega
          | succ target =>
              simpa only [lowerExponentAt, exponentAt, List.getD_cons_succ] using h
      | succ coordinate =>
          cases target with
          | zero =>
              simpa only [lowerExponentAt, exponentAt, List.getD_cons_zero] using h
          | succ target =>
              simp only [lowerExponentAt, exponentAt, List.getD_cons_succ] at h ⊢
              exact exponentAt_lowerExponentAt_eq_zero coordinate target rest h

/-- A formal partial derivative preserves every block-local support predicate.
Zero-coefficient derivative terms may remain in the literal list, but their
lowered monomials still vanish in every forbidden block. -/
theorem BlockLocal.ratDerivative {blocks : Nat} {allowed : Nat -> Prop}
    {p : RatPoly} (hp : BlockLocal blocks allowed p) (coordinate : Nat) :
    BlockLocal blocks allowed (ratDerivative coordinate p) := by
  intro term ht block hb hnot component hc
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ht
  exact exponentAt_lowerExponentAt_eq_zero coordinate (4 * block + component)
    source.1 (hp source hsource block hb hnot component hc)

/-- A coordinate-plane rotation in the head quaternion preserves block
locality whenever block zero is among the allowed blocks. -/
theorem angularDerivative_local {blocks : Nat} {allowed : Nat -> Prop}
    {p : RatPoly} (hp : BlockLocal blocks allowed p) (hhead : allowed 0)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    BlockLocal blocks allowed (angularDerivative i j p) := by
  unfold angularDerivative
  have hai : allowed (i / 4) := by
    rw [Nat.div_eq_of_lt hi]
    exact hhead
  have haj : allowed (j / 4) := by
    rw [Nat.div_eq_of_lt hj]
    exact hhead
  exact ((BlockLocal.coordinate i hai).mul (BlockLocal.ratDerivative hp j)).add
    (((BlockLocal.coordinate j haj).mul (BlockLocal.ratDerivative hp i)).smul (-1))

/-- Conjugating a head angular derivative by the same block involution
preserves the original locality predicate.  The selected source block is
`permutation.map 0`; `hblocks` makes that head an actual carrier block. -/
theorem conjugatedHead_angularDerivative_local
    {blocks : Nat} {allowed : Nat -> Prop}
    (permutation : QuaternionBlockInvolution blocks) {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (hblocks : 0 < blocks)
    (hselected : allowed (permutation.map 0)) {i j : Nat}
    (hi : i < 4) (hj : j < 4) :
    BlockLocal blocks allowed
      (reindexQuaternionPolynomial permutation
        (angularDerivative i j
          (reindexQuaternionPolynomial permutation p))) := by
  have _hselected_lt : permutation.map 0 < blocks :=
    permutation.map_lt 0 hblocks
  let pulledAllowed : Nat -> Prop := fun block => allowed (permutation.map block)
  have hpull : BlockLocal blocks pulledAllowed
      (reindexQuaternionPolynomial permutation p) :=
    hp.reindex permutation (fun _ _ h => h)
  have hhead : pulledAllowed 0 := hselected
  have hd := angularDerivative_local hpull hhead hi hj
  apply hd.reindex permutation
  intro block hblock hallowed
  change allowed block
  change allowed (permutation.map (permutation.map block)) at hallowed
  rw [permutation.involutive block hblock] at hallowed
  exact hallowed

end YMGap.Continuum.SU2QuaternionAngularLocality

#print axioms YMGap.Continuum.SU2QuaternionAngularLocality.BlockLocal.ratDerivative
#print axioms YMGap.Continuum.SU2QuaternionAngularLocality.angularDerivative_local
#print axioms YMGap.Continuum.SU2QuaternionAngularLocality.conjugatedHead_angularDerivative_local
