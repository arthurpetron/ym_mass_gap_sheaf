/-
# Explicit convergence certificates from summable CReal variation

`SummableCRealStepVariation` already carries the data needed to construct a
constructive-real cutoff limit.  This module keeps the same object and
promotes the resulting convergence to the Type-level certificate required by
continuum-facing consumers: a term-stage modulus and an approximation-stage
modulus are both exposed explicitly.

The construction is the same three-quarter-step estimate used by the existing
`ConvergesTo` theorem.  No modulus is extracted from a proposition and no new
analytic estimate is asserted here; this is a witness-preserving compiler for
an already supplied summable variation certificate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealConvergenceCertificate
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.SummableCRealStepVariation

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail

variable {s : Nat → CReal}

/-! ## The witness-bearing upgrade -/

/-- Compile a summable two-sided variation certificate into an explicit
convergence certificate for the very same constructive-real sequence and the
very same diagonal limit.

For tolerance `ε`, the outer stage uses the stored tail rate at
`q = ε/4`.  The approximation stage combines the term's inner modulus at `q`
with `q.den`, exactly as in the diagonal completion proof. -/
def toExplicitConvergenceCertificate
    (V : SummableCRealStepVariation s) :
  CReal.ExplicitConvergenceCertificate
      s (CReal.completeLimitCauchy s V.toModCauchyEv) where
  modulus := fun ε =>
    V.tailRate (HalfPow.half * (HalfPow.half * ε))
  approximationModulus := fun ε N =>
    max (V.innerRate N (HalfPow.half * (HalfPow.half * ε)))
      (HalfPow.half * (HalfPow.half * ε)).den
  bound := by
    intro ε hε N hN n hn
    let c := V.toModCauchyEv
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hregNn : V.innerRate N q ≤ n := by
      exact Nat.le_trans (Nat.le_max_left _ _) hn
    have hqdenn : q.den ≤ n := by
      exact Nat.le_trans (Nat.le_max_right _ _) hn
    have hinvn : Q'.invSucc n ≤ q :=
      Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn)
        (HalfPow.invSucc_den_le q hqpos)
    have hinvnpos : (0 : Q') < Q'.invSucc n := Q'.invSucc_pos n
    let Kpair : Nat := c.boundK q N (CReal.MhatE s c n)
    let J : Nat := max (CReal.RhatE s c n) Kpair
    have hRn_J : CReal.RhatE s c n ≤ J := Nat.le_max_left _ _
    have hK_J : Kpair ≤ J := Nat.le_max_right _ _
    have hn_R : n ≤ CReal.RhatE s c n :=
      CReal.k_le_RhatE s c n
    have hregN_R : V.innerRate N q ≤ CReal.RhatE s c n := by
      exact Nat.le_trans hregNn hn_R
    have hregN_J : V.innerRate N q ≤ J :=
      Nat.le_trans hregN_R hRn_J
    have hregMn_R : V.innerRate (CReal.MhatE s c n)
        (Q'.invSucc n) ≤ CReal.RhatE s c n :=
      CReal.reg_le_RhatE s c n
    have hregMn_J : V.innerRate (CReal.MhatE s c n)
        (Q'.invSucc n) ≤ J :=
      Nat.le_trans hregMn_R hRn_J
    have hMqn : V.tailRate q ≤ CReal.MhatE s c n := by
      exact Nat.le_trans
        (c.Mmono q (Q'.invSucc n) hinvnpos hinvn)
        (CReal.M_le_MhatE s c n)
    obtain ⟨hI1, hI2⟩ :=
      V.innerRegular N q hqpos n J hregNn hregN_J
    obtain ⟨hO1, hO2⟩ :=
      c.bound q hqpos N (CReal.MhatE s c n) hN hMqn J hK_J
    obtain ⟨hII1, hII2⟩ :=
      V.innerRegular (CReal.MhatE s c n) (Q'.invSucc n)
        hinvnpos J (CReal.RhatE s c n) hregMn_J hregMn_R
    have hII1' :
        (s (CReal.MhatE s c n)).approx J ≤
          (s (CReal.MhatE s c n)).approx (CReal.RhatE s c n) + q :=
      Q'.le_trans' _ _ _ hII1 (Q'.add_le_add_left _ _ q hinvn)
    have hII2' :
        (s (CReal.MhatE s c n)).approx (CReal.RhatE s c n) ≤
          (s (CReal.MhatE s c n)).approx J + q :=
      Q'.le_trans' _ _ _ hII2 (Q'.add_le_add_left _ _ q hinvn)
    have h3q : ∀ w : Q', ((w + q) + q) + q ≤ w + ε := by
      intro w
      have hreassoc : (((w + q) + q) + q).eqv
          (w + ((q + q) + q)) := by
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (w + q) q q) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv w q (q + q)) ?_
        exact Q'.add_eqv_congr_left w (q + (q + q)) ((q + q) + q)
          (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
      have hqq_half : q + q ≤ HalfPow.half * ε := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv (ExpNeg.two_halves (HalfPow.half * ε))) ?_
        exact Q'.le_refl' _
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
      refine Q'.add_le_add_left w ((q + q) + q) ε ?_
      have hstep1 : (q + q) + q ≤ (HalfPow.half * ε) + q :=
        Q'.add_le_add_right (q + q) (HalfPow.half * ε) q hqq_half
      have hqle : q ≤ HalfPow.half * ε := by
        refine Q'.le_trans' _ _ _ ?_ hqq_half
        exact Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hqpos)
      have hstep2 : (HalfPow.half * ε) + q ≤
          (HalfPow.half * ε) + (HalfPow.half * ε) :=
        Q'.add_le_add_left (HalfPow.half * ε) q
          (HalfPow.half * ε) hqle
      refine Q'.le_trans' _ _ _ hstep1 ?_
      refine Q'.le_trans' _ _ _ hstep2 ?_
      exact Q'.le_of_eqv (ExpNeg.two_halves ε)
    refine ⟨?_, ?_⟩
    · show (s N).approx n ≤
        (CReal.completeLimitCauchy s c).approx n + ε
      have hchain : (s N).approx n ≤
          (((s (CReal.MhatE s c n)).approx (CReal.RhatE s c n) + q) + q) + q := by
        refine Q'.le_trans' _ _ _ hI1 ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1) ?_
        exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hII1')
      exact Q'.le_trans' _ _ _ hchain
        (h3q ((s (CReal.MhatE s c n)).approx (CReal.RhatE s c n)))
    · show (CReal.completeLimitCauchy s c).approx n ≤
        (s N).approx n + ε
      have hchain :
          (s (CReal.MhatE s c n)).approx (CReal.RhatE s c n) ≤
            (((s N).approx n + q) + q) + q := by
        refine Q'.le_trans' _ _ _ hII2' ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2) ?_
        exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hI2)
      exact Q'.le_trans' _ _ _ hchain (h3q ((s N).approx n))

end YMGap.Continuum.SummableCRealStepVariation

/-! ## Dependency gate -/

#print axioms
  YMGap.Continuum.SummableCRealStepVariation.toExplicitConvergenceCertificate
