/-
# Torus RP (f0): statement shapes for the RP Cauchy–Schwarz (definitions only, NOTHING PROVED)

`rpB hM β K F G = ∫_{|torusLinks|} Θ(F)·G·Π T_K` is the RP form for the torus `T_K` measure. `TorusCS` is the
target **Cauchy–Schwarz** in the cross-multiplied rational shape that `SU2LogConvexGap.LogConvex` consumes
(`G(j+1)·G(j+1) ≤ G j · G(j+2)`): `rpB F G · rpB F G ≤ rpB F F · rpB G G`. `TorusRPPoly` is the target
**general-polynomial RP** for supported polynomials (`PtSup`), a class closed under subtracting constants.

**OPEN: `TorusCS` and `TorusRPPoly` are stated here and not proved. RP holds for `Obs` observables (`torus_rp`).**
-/

import YMGap.Continuum.SU2TorusRPHW

namespace YMGap.Continuum.SU2TorusRPCSShape

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusRPChoosePC (Pt)
open YMGap.Continuum.SU2TorusRPObs (thetaT)

variable {M : Nat} (hM : 1 ≤ M) (β : Q') (K : Nat)

/-- The RP sesquilinear form `⟨ΘF·G⟩` under the unnormalised torus `T_K` weight. -/
def rpB (F G : RatPoly) : Q' :=
  quaternionHaar (torusLinks (2 * M)).length
    (polyMul (polyMul (thetaT hM F) G)
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M) β K)
        (torusPlaquettes (2 * M))))

/-- Support on positive links in `torusLinks` order: every variable that occurs lies in a `Pt M` block, and each
monomial has length at most `4·|torusLinks|`. -/
def PtSup (F : RatPoly) : Prop :=
  ∀ t ∈ F, t.1.length ≤ 4 * (torusLinks (2 * M)).length ∧
    ∀ i, exponentAt t.1 i ≠ 0 → (torusLinks (2 * M)).getD (i / 4) YMGap.Continuum.SU2TorusRPThetaPoly.d0 ∈ Pt M

/-- Target (1): RP for general polynomials supported on `Pt M`. -/
def TorusRPPoly : Prop := ∀ F : RatPoly, PtSup (M := M) F → (0 : Q') ≤ rpB hM β K F F

/-- Target (2): RP Cauchy–Schwarz, cross-multiplied, rational. -/
def TorusCS : Prop :=
  ∀ F G : RatPoly, PtSup (M := M) F → PtSup (M := M) G → rpB hM β K F G * rpB hM β K F G ≤ rpB hM β K F F * rpB hM β K G G

end YMGap.Continuum.SU2TorusRPCSShape
