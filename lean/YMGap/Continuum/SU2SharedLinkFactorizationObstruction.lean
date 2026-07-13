/-
# Exact obstruction to naively factorizing overlapping SU(2) plaquettes

The volume tensor checkpoints control disjoint copies of the frozen
plaquette block.  Actual lattice plaquettes share link variables.  This file
banks the smallest exact fence against silently identifying those two
situations.

Use the SAME normalized non-unit Wilson weight

    K = 1 + (1/4) chi_1

against the completed bare SU(2) Haar functional.  A single fundamental
character has Wilson moment `1/4`.  Two occurrences on the SAME link fuse
before Haar integration, and their moment is `1`.  Treating the two
occurrences as independent instead gives `(1/4)^2 = 1/16`.  The two exact
rationals are apart.

Thus the disjoint tensor theorem cannot be transported to overlapping
plaquettes by definitional identification or product-state factorization.
A genuine shared-link fusion comparison/intertwiner is required.

Honest scope: this refutes one invalid bridge.  It is not itself the needed
comparison theorem and makes no finite-volume or continuum-gap claim.
-/

import YMGap.Continuum.SU2PeterWeylVolumeGNS

namespace YMGap.Continuum.SU2SharedLinkFactorizationObstruction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialChebUniqueness
open YMGap.Continuum.SU2ClassPolynomialHaarDescent
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

/-- Wilson expectation formed from the same bare-Haar state and the same
non-unit retained heat-kernel weight as the plaquette checkpoint. -/
def wilsonMoment (p : Poly) : Q' :=
  bareVacuumHaar (pmul interactionKernel p)

theorem wilsonMoment_normalized : wilsonMoment chi0 ≈ 1 := by decide

/-- One fundamental character insertion has exact moment `1/4`. -/
theorem wilsonMoment_fundamental : wilsonMoment chi1 ≈ quarter := by decide

/-- Two fundamental occurrences on one shared link fuse before integration;
their exact Wilson moment is `1`. -/
theorem wilsonMoment_shared_fundamental_square :
    wilsonMoment (pmul chi1 chi1) ≈ 1 := by decide

/-- Two disjoint copies would instead contribute the product `1/16`. -/
theorem wilsonMoment_disjoint_product :
    wilsonMoment chi1 * wilsonMoment chi1 ≈
      Q'.mkPos 1 16 (by decide) := by decide

/-- **Kernel-checked factorization obstruction.**  Shared-link fusion is not
the product of two independent link moments. -/
theorem shared_link_not_independent :
    ¬ (wilsonMoment (pmul chi1 chi1) ≈
      wilsonMoment chi1 * wilsonMoment chi1) := by decide

/-- The numerical mismatch is exactly the nonzero rational `15/16`; no
measurement or floating-point estimate enters the fence. -/
theorem shared_minus_disjoint_exact :
    (wilsonMoment (pmul chi1 chi1) +
      -(wilsonMoment chi1 * wilsonMoment chi1)) ≈
      Q'.mkPos 15 16 (by decide) := by decide

end YMGap.Continuum.SU2SharedLinkFactorizationObstruction

#print axioms YMGap.Continuum.SU2SharedLinkFactorizationObstruction.wilsonMoment_normalized
#print axioms YMGap.Continuum.SU2SharedLinkFactorizationObstruction.wilsonMoment_fundamental
#print axioms YMGap.Continuum.SU2SharedLinkFactorizationObstruction.wilsonMoment_shared_fundamental_square
#print axioms YMGap.Continuum.SU2SharedLinkFactorizationObstruction.wilsonMoment_disjoint_product
#print axioms YMGap.Continuum.SU2SharedLinkFactorizationObstruction.shared_link_not_independent
#print axioms YMGap.Continuum.SU2SharedLinkFactorizationObstruction.shared_minus_disjoint_exact
