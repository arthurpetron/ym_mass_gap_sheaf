/-
# Multi-link polynomial Haar and the multi-plaquette SU(2) torus PolyGibbs

ADDITIVE (YM Group Realizer); does not edit the Prover's files.

* `multiLinkHaar n : PolyLinkHaar` — exact product of `n` normalized `S³` Haar
  factors (`quaternionHaar n`, which is *by definition* the block product of
  `quaternionPolyLinkHaar` = `quaternionHaar 1`); linear, normalized.
  `multiLinkHaar_square_nonneg`: positive on squares of polynomials supported
  in the `n` blocks (from `finiteProductHaar_square_nonneg` via
  `quaternionHaar_eq_finiteProductHaar`).
* Link coordinates: link `ℓ` of a finite link list `links` uses block
  `links.idxOf ℓ` (coordinates `4·idx … 4·idx+3`).
* `plaqWord links N p` — the polynomial holonomy word, mirroring
  `TorusWilsonAction.holonomy` (`U₁ U₂ U₃⁻¹ U₄⁻¹`, inverse = conjugate).
* Heat-kernel weight with `c_s = BondMovingStep.coeffW w s = (s+1) w^{s(s+2)}`:
  `plaqWeight w M links N p = Σ_{s≤M} coeffW w s · χ_s(U_p)`.
* `torusIntegrand`, `torusPolyPartition w M N
    = ∫ Π_{p ∈ torusPlaquettes N} plaqWeight … dU` over `torusLinks N`.

Cheap evaluation lemmas: `coeffW_zero_eqv`, `eval_plaqCharacter`,
`integrand_nil`, `partition_nil` (empty plaquette list ⇒ `1`).

OPEN (not fields, not faked):
* left/right invariance (needs a polynomial translation operator wired to the
  repo's `SU2QuaternionTranslation*` lemmas);
* factorization over disjoint link sets (`DisjointFactorizes`, stated as a
  `Prop`, not proved);
* any closed form / positivity of `torusPolyPartition` for `N ≥ 1`;
* general-spin Schur.
-/

import YMGap.Continuum.SU2TorusPolyGibbs
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
import YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
import YMGap.Continuum.TorusWilsonAction
import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2PolyLinkHaar
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry

/-! ## 1. Multi-link Haar -/

theorem quaternionHaar_polyOne (n : Nat) : (quaternionHaar n polyOne).eqv 1 := by
  show (1 * quaternionHaarMono n [] + 0).eqv 1
  exact Q'.eqv_trans _ _ _ (YMGap.Constructive.QPoly.q_add_zero_eqv _)
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one n))

/-- Exact product Haar on `n` links. -/
def multiLinkHaar (n : Nat) : PolyLinkHaar where
  h := quaternionHaar n
  add := fun p q => YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append n p q
  smul := fun c p => YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul n c p
  norm := quaternionHaar_polyOne n

/-- One link is the constructed single-link functional. -/
theorem multiLinkHaar_one : (multiLinkHaar 1).h = quaternionPolyLinkHaar.h := rfl

/-- **Positive on squares** of block-supported polynomials. -/
theorem multiLinkHaar_square_nonneg (n : Nat) (p : RatPoly)
    (hs : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks n p) :
    (0 : Q') ≤ (multiLinkHaar n).h (polyMul p p) :=
  Q'.le_trans' _ _ _
    (YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity.finiteProductHaar_square_nonneg
      n p hs)
    (Q'.le_of_eqv (Q'.eqv_symm
      (YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_eq_finiteProductHaar n _)))

/-- OPEN (stated, not proved): factorization over the block split `n = a + b`
for `p` on the first `a` blocks and `q` on the last `b` blocks (`q` given in
local coordinates and shifted by `shift`). -/
def DisjointFactorizes (a b : Nat) (shift : RatPoly → RatPoly) : Prop :=
  ∀ p q : RatPoly,
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks a p →
    YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks b q →
    ((multiLinkHaar (a + b)).h (polyMul p (shift q))).eqv
      ((multiLinkHaar a).h p * (multiLinkHaar b).h q)

/-! ## 2. Plaquette words and the heat-kernel weight -/

/-- Quaternion coordinate polynomial of link `ℓ` in `links`. -/
def linkVar (links : List Z4Link) (ℓ : Z4Link) : PolyQuaternion :=
  PolyQuaternion.coordinateVariable (links.idxOf ℓ)

/-- Polynomial holonomy word, matching `TorusWilsonAction.holonomy`. -/
def plaqWord (links : List Z4Link) (N : Nat) (p : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul (linkVar links (p.1, (dirsOf p.2).1))
      (linkVar links (tAdd N p.1 (dirsOf p.2).1, (dirsOf p.2).2)))
    (PolyQuaternion.mul
      (PolyQuaternion.conj (linkVar links (tAdd N p.1 (dirsOf p.2).2, (dirsOf p.2).1)))
      (PolyQuaternion.conj (linkVar links (p.1, (dirsOf p.2).2))))

/-- `χ_s(U_p)` as a polynomial. -/
def plaqCharacter (links : List Z4Link) (N : Nat) (p : Z4Plaq) (s : Nat) : RatPoly :=
  characterPolynomial (plaqWord links N p).scalar s

/-- Heat-kernel coefficient (the repo's, not Bessel). -/
abbrev coeffW (w : Q') (s : Nat) : Q' := YMGap.Continuum.BondMovingStep.coeffW w s

theorem coeffW_zero_eqv (w : Q') : (coeffW w 0).eqv 1 := by
  show (YMGap.Continuum.RGTransport.dimQ 0 * YMGap.Continuum.RGTransport.qpow w 0).eqv 1
  rw [YMGap.Continuum.RGTransport.dimQ_zero, YMGap.Continuum.RGTransport.qpow_zero]
  exact Q'.one_mul_eqv 1

/-- `Σ_{s≤M} coeffW w s · χ_s(U_p)`. -/
def plaqWeight (w : Q') (links : List Z4Link) (N : Nat) (p : Z4Plaq) : Nat → RatPoly
  | 0 => polySmul (coeffW w 0) (plaqCharacter links N p 0)
  | M + 1 => polyAdd (plaqWeight w links N p M)
      (polySmul (coeffW w (M + 1)) (plaqCharacter links N p (M + 1)))

/-- `Π_p plaqWeight`. -/
def torusIntegrand (w : Q') (M : Nat) (links : List Z4Link) (N : Nat) :
    List Z4Plaq → RatPoly
  | [] => polyOne
  | p :: ps => polyMul (plaqWeight w links N p M) (torusIntegrand w M links N ps)

/-- General finite version: links `links`, plaquettes `plaqs`. -/
def polyPartition (w : Q') (M : Nat) (links : List Z4Link) (N : Nat)
    (plaqs : List Z4Plaq) : Q' :=
  (multiLinkHaar links.length).h (torusIntegrand w M links N plaqs)

/-- **Target**: `∫ Π_{p} (Σ_{s≤M} coeffW w s · χ_s(U_p)) dU` on the `N`-torus. -/
def torusPolyPartition (w : Q') (M N : Nat) : Q' :=
  polyPartition w M (torusLinks N) N (torusPlaquettes N)

/-! ## 3. Cheap evaluation lemmas -/

theorem eval_plaqCharacter (rho : Nat → Q') (links : List Z4Link) (N : Nat)
    (p : Z4Plaq) (s : Nat) :
    (evalRatPoly rho (plaqCharacter links N p s)).eqv
      (YMGap.Continuum.Cheb.U s (evalRatPoly rho (plaqWord links N p).scalar)) :=
  eval_characterPolynomial rho _ s

theorem integrand_nil (w : Q') (M : Nat) (links : List Z4Link) (N : Nat) :
    torusIntegrand w M links N [] = polyOne := rfl

theorem partition_nil (w : Q') (M : Nat) (links : List Z4Link) (N : Nat) :
    (polyPartition w M links N []).eqv 1 :=
  (multiLinkHaar links.length).norm

theorem plaqWeight_zero (w : Q') (links : List Z4Link) (N : Nat) (p : Z4Plaq) :
    plaqWeight w links N p 0 = polySmul (coeffW w 0) (plaqCharacter links N p 0) := rfl

end YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

#print axioms YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.multiLinkHaar
#print axioms YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.multiLinkHaar_square_nonneg
#print axioms YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.coeffW_zero_eqv
#print axioms YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.eval_plaqCharacter
#print axioms YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.partition_nil
#print axioms YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.torusPolyPartition
