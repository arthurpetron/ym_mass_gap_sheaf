/-
# Torus RP assembly (a): padding by free Haar blocks

`pad_haar`: `∫_{n+k} p ≈ ∫_n p` for `p` supported on the first `n` blocks. This adds the `k` split variables of the
crossing links. Proof: `haar_factor n k p polyOne`, then `p · shift 1 ≡ p` (`pe_zeros`) and `∫_k 1 = 1`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (obligations (b)–(d) of the scope doc remain).
-/

import YMGap.Continuum.SU2TorusRPKernel

namespace YMGap.Continuum.SU2TorusRPPad

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_haar pe_mulL pe_comm pe_const)
open YMGap.Continuum.SU2MultiLinkHaarFactorization (shiftPoly haar_factor)
open YMGap.Continuum.SU2TorusRPCore (Sup pe_zeros)

theorem pad_haar (n k : Nat) (p : RatPoly) (hp : Sup n p) :
    (quaternionHaar (n + k) p).eqv (quaternionHaar n p) := by
  have h1 : PE (n + k) (polyMul p (shiftPoly n polyOne)) p := by
    refine pe_trans _ (pe_mulL _ p ?_) (pe_trans _ (pe_comm _ _ _) (pe_const _ 1 (Q'.eqv_refl 1) p))
    show PE _ [(List.replicate (4 * n) 0 ++ [], (1 : Q'))] polyOne
    rw [List.append_nil]; exact pe_zeros _ _
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (pe_haar _ h1)) ?_
  refine Q'.eqv_trans _ _ _ (haar_factor n k p hp polyOne) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.quaternionHaar_polyOne k)) ?_
  exact Q'.mul_one_eqv _

end YMGap.Continuum.SU2TorusRPPad

#print axioms YMGap.Continuum.SU2TorusRPPad.pad_haar
