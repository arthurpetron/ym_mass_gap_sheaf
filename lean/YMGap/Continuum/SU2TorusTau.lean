/-
# Torus RP (g3): the time translation `τ_t` on polynomials, and Haar invariance

`tau N t hN X = σ_t (σ_0 X)`: two block-involution reindexings on the `torusLinks N` order, with
`ρ_t ∘ ρ_0 = shv t` (`SU2TorusTimeRefl.rl_comp`). Proved: `haar_tau`, i.e. `∫ τ_t X ≈ ∫ X` for supported `X`.

**OPEN**: `τ_t (Π T_K) ≡ Π T_K` (via `tk_shift` + `tp_shift_perm`), `Θ∘τ_x ≡ τ_{−x}∘Θ`, and the correlator identity.
-/

import YMGap.Continuum.SU2TorusTimeRefl
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.SU2TorusTau

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (reindexQuaternionPolynomial quaternionHaar_reindex)
open YMGap.Continuum.SU2TorusTimeRefl (sigma)

def tau (N t : Nat) (hN : 0 < N) (X : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (sigma N t hN) (reindexQuaternionPolynomial (sigma N 0 hN) X)

theorem haar_tau (N t : Nat) (hN : 0 < N) (X : RatPoly)
    (hX : YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks (torusLinks N).length X) :
    (quaternionHaar (torusLinks N).length (tau N t hN X)).eqv (quaternionHaar (torusLinks N).length X) :=
  Q'.eqv_trans _ _ _
    (quaternionHaar_reindex (sigma N t hN) _
      (YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported (sigma N 0 hN) X))
    (quaternionHaar_reindex (sigma N 0 hN) X hX)

end YMGap.Continuum.SU2TorusTau

#print axioms YMGap.Continuum.SU2TorusTau.haar_tau
