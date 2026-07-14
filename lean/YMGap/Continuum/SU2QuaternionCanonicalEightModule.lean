/-
# Non-vacuous polynomial module for the canonical quaternion carrier

The GNS interface needs additive and scalar structure modulo a meaningful
observable equality.  Here equality is pointwise polynomial equality under
every rational environment, transported through the exact dense embedding.
This is neither literal-list equality nor a vacuous relation: it identifies
precisely the duplicate-term and coefficient presentations with the same
rational polynomial value.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity
import YMGap.Continuum.ReferenceWeightTimeGeometry
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS

namespace YMGap.Continuum.SU2QuaternionCanonicalEightModule

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.WilsonGNS.WilsonGNSData
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS

local infix:50 " ≈ " => Q'.eqv

def evalCanonicalPoly8 (rho : Nat → Q') (p : Poly8) : Q' :=
  evalRatPoly rho (embedPoly8 p)

/-- Extensional rational-polynomial equality on the canonical carrier. -/
def CanonicalPoly8Eqv (p q : Poly8) : Prop :=
  ∀ rho, evalCanonicalPoly8 rho p ≈ evalCanonicalPoly8 rho q

theorem evalCanonicalPoly8_zero (rho : Nat → Q') :
    evalCanonicalPoly8 rho polyZero8 ≈ 0 := Q'.eqv_refl 0

theorem evalCanonicalPoly8_add (rho : Nat → Q') (p q : Poly8) :
    evalCanonicalPoly8 rho (polyAdd8 p q) ≈
      evalCanonicalPoly8 rho p + evalCanonicalPoly8 rho q := by
  unfold evalCanonicalPoly8 embedPoly8 polyAdd8
  rw [List.map_append]
  exact evalRatPoly_add rho _ _

theorem evalCanonicalPoly8_neg (rho : Nat → Q') : ∀ p : Poly8,
    evalCanonicalPoly8 rho (polyNeg8 p) ≈ -evalCanonicalPoly8 rho p
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | t :: p => by
      change
        (-t.2) * evalMono rho (mono8ToList t.1) +
            evalCanonicalPoly8 rho (polyNeg8 p) ≈
          -(t.2 * evalMono rho (mono8ToList t.1) +
            evalCanonicalPoly8 rho p)
      refine Q'.eqv_trans _
        (-(t.2 * evalMono rho (mono8ToList t.1)) +
          -evalCanonicalPoly8 rho p) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.neg_mul_eqv t.2 (evalMono rho (mono8ToList t.1)))
          (evalCanonicalPoly8_neg rho p)
      · exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

private theorem embedPoly8_smul (c : Q') : ∀ p : Poly8,
    embedPoly8 (polySmul8 c p) = polySmul c (embedPoly8 p)
  | [] => rfl
  | t :: p => by
      change (mono8ToList t.1, c * t.2) ::
          embedPoly8 (polySmul8 c p) =
        (mono8ToList t.1, c * t.2) :: polySmul c (embedPoly8 p)
      rw [embedPoly8_smul c p]

theorem evalCanonicalPoly8_smul (rho : Nat → Q') (c : Q') (p : Poly8) :
    evalCanonicalPoly8 rho (polySmul8 c p) ≈
      c * evalCanonicalPoly8 rho p := by
  unfold evalCanonicalPoly8
  rw [embedPoly8_smul]
  exact evalRatPoly_smul rho c (embedPoly8 p)

theorem evalCanonicalPoly8_mul (rho : Nat → Q') (p q : Poly8) :
    evalCanonicalPoly8 rho (polyMul8 p q) ≈
      evalCanonicalPoly8 rho p * evalCanonicalPoly8 rho q := by
  unfold evalCanonicalPoly8
  rw [embedPoly8_mul]
  exact evalRatPoly_mul rho (embedPoly8 p) (embedPoly8 q)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- The semantic polynomial module used by the canonical Wilson/GNS datum. -/
def canonicalPoly8Module :
    CarrierModule canonicalQuaternionPairAlg where
  veq := CanonicalPoly8Eqv
  veq_refl := fun p rho => Q'.eqv_refl (evalCanonicalPoly8 rho p)
  veq_symm := fun h rho => Q'.eqv_symm (h rho)
  veq_trans := fun h₁ h₂ rho => Q'.eqv_trans _ _ _ (h₁ rho) (h₂ rho)
  zero := polyZero8
  add := polyAdd8
  neg := polyNeg8
  smul := polySmul8
  add_congr := fun {a a' b b'} ha hb rho =>
    Q'.eqv_trans _ _ _ (evalCanonicalPoly8_add rho a b)
      (Q'.eqv_trans _ _ _ (QPoly.q_add_congr (ha rho) (hb rho))
        (Q'.eqv_symm (evalCanonicalPoly8_add rho a' b')))
  neg_congr := fun {a a'} h rho =>
    Q'.eqv_trans _ _ _ (evalCanonicalPoly8_neg rho a)
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (h rho))
        (Q'.eqv_symm (evalCanonicalPoly8_neg rho a')))
  smul_congr := fun s {a a'} h rho =>
    Q'.eqv_trans _ _ _ (evalCanonicalPoly8_smul rho s a)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left s _ _ (h rho))
        (Q'.eqv_symm (evalCanonicalPoly8_smul rho s a')))
  add_assoc := fun a b c rho => by
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho (polyAdd8 a b) + evalCanonicalPoly8 rho c) _
      (evalCanonicalPoly8_add rho (polyAdd8 a b) c) ?_
    refine Q'.eqv_trans _
      ((evalCanonicalPoly8 rho a + evalCanonicalPoly8 rho b) +
        evalCanonicalPoly8 rho c) _
      (QPoly.q_add_congr (evalCanonicalPoly8_add rho a b)
        (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho a +
        (evalCanonicalPoly8 rho b + evalCanonicalPoly8 rho c)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho a + evalCanonicalPoly8 rho (polyAdd8 b c)) _
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (Q'.eqv_symm (evalCanonicalPoly8_add rho b c))) ?_
    exact Q'.eqv_symm (evalCanonicalPoly8_add rho a (polyAdd8 b c))
  add_comm := fun a b rho =>
    Q'.eqv_trans _ _ _ (evalCanonicalPoly8_add rho a b)
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.eqv_symm (evalCanonicalPoly8_add rho b a)))
  zero_add := fun a rho =>
    Q'.eqv_trans _ _ _ (evalCanonicalPoly8_add rho polyZero8 a)
      (Q'.eqv_trans _ _ _
        (QPoly.q_add_congr (evalCanonicalPoly8_zero rho) (Q'.eqv_refl _))
        (QPoly.q_zero_add_eqv _))
  neg_add := fun a rho => by
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho (polyNeg8 a) + evalCanonicalPoly8 rho a) _
      (evalCanonicalPoly8_add rho (polyNeg8 a) a) ?_
    refine Q'.eqv_trans _
      (-evalCanonicalPoly8 rho a + evalCanonicalPoly8 rho a) _
      (QPoly.q_add_congr (evalCanonicalPoly8_neg rho a) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.neg_add_self_eqv _) ?_
    exact Q'.eqv_symm (evalCanonicalPoly8_zero rho)
  mul_congr := fun {a a' b b'} ha hb rho =>
    Q'.eqv_trans _ _ _ (evalCanonicalPoly8_mul rho a b)
      (Q'.eqv_trans _ _ _ (q_mul_congr (ha rho) (hb rho))
        (Q'.eqv_symm (evalCanonicalPoly8_mul rho a' b')))
  star_congr := fun h => h
  star_add := fun a b rho => Q'.eqv_refl _
  star_smul := fun s a rho => Q'.eqv_refl _
  mul_add_right := fun a b c rho => by
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho (polyAdd8 a b) * evalCanonicalPoly8 rho c) _
      (evalCanonicalPoly8_mul rho (polyAdd8 a b) c) ?_
    refine Q'.eqv_trans _
      ((evalCanonicalPoly8 rho a + evalCanonicalPoly8 rho b) *
        evalCanonicalPoly8 rho c) _
      (Q'.mul_eqv_congr_right _ _ _ (evalCanonicalPoly8_add rho a b)) ?_
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho a * evalCanonicalPoly8 rho c +
        evalCanonicalPoly8 rho b * evalCanonicalPoly8 rho c) _
      (Q'.add_mul_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho (polyMul8 a c) +
        evalCanonicalPoly8 rho (polyMul8 b c)) _
      (QPoly.q_add_congr
        (Q'.eqv_symm (evalCanonicalPoly8_mul rho a c))
        (Q'.eqv_symm (evalCanonicalPoly8_mul rho b c))) ?_
    exact Q'.eqv_symm
      (evalCanonicalPoly8_add rho (polyMul8 a c) (polyMul8 b c))
  smul_mul := fun s a b rho => by
    refine Q'.eqv_trans _
      (evalCanonicalPoly8 rho (polySmul8 s a) * evalCanonicalPoly8 rho b) _
      (evalCanonicalPoly8_mul rho (polySmul8 s a) b) ?_
    refine Q'.eqv_trans _
      ((s * evalCanonicalPoly8 rho a) * evalCanonicalPoly8 rho b) _
      (Q'.mul_eqv_congr_right _ _ _ (evalCanonicalPoly8_smul rho s a)) ?_
    refine Q'.eqv_trans _
      (s * (evalCanonicalPoly8 rho a * evalCanonicalPoly8 rho b)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (s * evalCanonicalPoly8 rho (polyMul8 a b)) _
      (Q'.mul_eqv_congr_left s _ _
        (Q'.eqv_symm (evalCanonicalPoly8_mul rho a b))) ?_
    exact Q'.eqv_symm (evalCanonicalPoly8_smul rho s (polyMul8 a b))

end YMGap.Continuum.SU2QuaternionCanonicalEightModule

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightModule.evalCanonicalPoly8_mul
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightModule.canonicalPoly8Module
