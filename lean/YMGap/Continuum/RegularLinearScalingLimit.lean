/-
Constructive spacing limits of positive linear functionals.

The older `FunctionalContinuumTarget` is phrased on `ObsAlg`, whose carrier has
no addition or scalar action.  Positivity and normalization are expressible
there, but linearity is not.  This module takes the independent linear substrate
already present in `RegularFunctional` and closes the missing limit theorem:
an explicit modulus-Cauchy family of rational positive linear functionals has a
positive linear functional as its spacing limit.

The proof does not assume that limits preserve algebraic operations.  It proves
that addition and rational scaling preserve `RegularCReal.ConvergesTo`, transports
limits across pointwise rational equivalence, and then invokes the existing
constructive uniqueness of limits.  Thus the limit's additivity and homogeneity
are theorems, not fields copied from the finite stages.
-/

import YMGap.Continuum.RegularFunctional
import YMGap.Continuum.HamiltonianScalar
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.RegularLinearScalingLimit

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RegularFunctional

/-! ## 1. Algebraic closure of regular-real convergence -/

/-- A constant regular-real sequence converges to its constant value. -/
theorem convergesTo_const (x : RegularCReal) :
    ConvergesTo (fun _ => x) x := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩
  exact ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε),
    Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε)⟩

/-- Pointwise rational equivalence of every approximation transports a limit.
This stronger relation is exactly what finite-stage `Q'` linearity supplies. -/
theorem convergesTo_of_approx_eqv
    {s t : Nat → RegularCReal} {L : RegularCReal}
    (hst : ∀ N n, ((s N).approx n).eqv ((t N).approx n))
    (hs : ConvergesTo s L) : ConvergesTo t L := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨P, hP⟩ := hN k hk
  refine ⟨P, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hP n hn
  refine ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hst k n)) h1, ?_⟩
  exact Q'.le_trans' _ _ _ h2
    (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (hst k n)))

/-- Addition preserves convergence.  The proof uses the exact index doubling
in `RegularCReal.add` and splits the tolerance into two equal halves. -/
theorem convergesTo_add
    {s t : Nat → RegularCReal} {A B : RegularCReal}
    (hs : ConvergesTo s A) (ht : ConvergesTo t B) :
    ConvergesTo (fun N => add (s N) (t N)) (add A B) := by
  intro ε hε
  have hh : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Ns, hNs⟩ := hs (HalfPow.half * ε) hh
  obtain ⟨Nt, hNt⟩ := ht (HalfPow.half * ε) hh
  refine ⟨max Ns Nt, fun N hN => ?_⟩
  obtain ⟨Ps, hPs⟩ := hNs N (Nat.le_trans (Nat.le_max_left _ _) hN)
  obtain ⟨Pt, hPt⟩ := hNt N (Nat.le_trans (Nat.le_max_right _ _) hN)
  refine ⟨max Ps Pt, fun n hn => ?_⟩
  let m := 2 * n + 1
  have hms : Ps ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hn) (by omega)
  have hmt : Pt ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hn) (by omega)
  obtain ⟨hs1, hs2⟩ := hPs m hms
  obtain ⟨ht1, ht2⟩ := hPt m hmt
  show (s N).approx m + (t N).approx m ≤ (A.approx m + B.approx m) + ε ∧
    A.approx m + B.approx m ≤ ((s N).approx m + (t N).approx m) + ε
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add hs1 ht1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_regroup (A.approx m) (HalfPow.half * ε)
        (B.approx m) (HalfPow.half * ε))) ?_
    exact Q'.le_of_eqv (Q'.add_eqv_congr_left (A.approx m + B.approx m)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε))
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add hs2 ht2) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_regroup ((s N).approx m) (HalfPow.half * ε)
        ((t N).approx m) (HalfPow.half * ε))) ?_
    exact Q'.le_of_eqv (Q'.add_eqv_congr_left ((s N).approx m + (t N).approx m)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε))

/-- Rational scaling preserves convergence, for arbitrary signed scalars.  The
clamped reciprocal `oneOver1p |q|` pays the scaling of the tolerance, and the
sign-cased `mul_le_of_bounds` handles negative `q` constructively. -/
theorem convergesTo_qmul (q : Q')
    {s : Nat → RegularCReal} {A : RegularCReal}
    (hs : ConvergesTo s A) :
    ConvergesTo (fun N => qmul q (s N)) (qmul q A) := by
  intro ε hε
  have hBnn : (0 : Q') ≤ Q'.abs q := Q'.abs_nonneg q
  have hqU : q ≤ Q'.abs q := Q'.le_abs_self q
  have hqL : -(Q'.abs q) ≤ q :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs q))
      (Q'.le_of_eqv (Q'.neg_neg_eqv q))
  have hInvPos : (0 : Q') < ExpUBInstance.oneOver1p (Q'.abs q) :=
    oneOver1p_pos (Q'.abs q)
  have hδpos : (0 : Q') < ε * ExpUBInstance.oneOver1p (Q'.abs q) :=
    Q'.mul_pos hε hInvPos
  have hbudget : Q'.abs q * (ε * ExpUBInstance.oneOver1p (Q'.abs q)) ≤ ε :=
    key_bound (Q'.abs q) ε hBnn (Q'.le_of_lt hε)
  obtain ⟨N, hN⟩ := hs (ε * ExpUBInstance.oneOver1p (Q'.abs q)) hδpos
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨P, hP⟩ := hN k hk
  refine ⟨P, fun n hn => ?_⟩
  let m := qIdx q n
  have hm : P ≤ m := Nat.le_trans hn (le_qIdx q n)
  obtain ⟨h1, h2⟩ := hP m hm
  have hd1 : (s k).approx m + (-(A.approx m))
      ≤ ε * ExpUBInstance.oneOver1p (Q'.abs q) :=
    Q'.sub_le_of_le_add h1
  have hd2 : -(ε * ExpUBInstance.oneOver1p (Q'.abs q))
      ≤ (s k).approx m + (-(A.approx m)) :=
    Q'.neg_le_sub_of_le_add h2
  have hd1' : A.approx m + (-((s k).approx m))
      ≤ ε * ExpUBInstance.oneOver1p (Q'.abs q) :=
    Q'.sub_le_of_le_add h2
  have hd2' : -(ε * ExpUBInstance.oneOver1p (Q'.abs q))
      ≤ A.approx m + (-((s k).approx m)) :=
    Q'.neg_le_sub_of_le_add h1
  have hqd : q * ((s k).approx m + (-(A.approx m))) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_of_bounds hBnn (Q'.le_of_lt hδpos) hqL hqU hd2 hd1) hbudget
  have hqd' : q * (A.approx m + (-((s k).approx m))) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_of_bounds hBnn (Q'.le_of_lt hδpos) hqL hqU hd2' hd1') hbudget
  show q * (s k).approx m ≤ q * A.approx m + ε ∧
    q * A.approx m ≤ q * (s k).approx m + ε
  refine ⟨?_, ?_⟩
  · have he : (q * (s k).approx m).eqv
        (q * A.approx m + q * ((s k).approx m + (-(A.approx m)))) := by
      have e0 : ((s k).approx m).eqv
          (A.approx m + ((s k).approx m + (-(A.approx m)))) :=
        Q'.add_sub_cancel_eqv ((s k).approx m) (A.approx m)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ e0)
        (Q'.mul_add_eqv q (A.approx m) ((s k).approx m + (-(A.approx m))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_add_left _ _ _ hqd)
  · have he : (q * A.approx m).eqv
        (q * (s k).approx m + q * (A.approx m + (-((s k).approx m)))) := by
      have e0 : (A.approx m).eqv
          ((s k).approx m + (A.approx m + (-((s k).approx m)))) :=
        Q'.add_sub_cancel_eqv (A.approx m) ((s k).approx m)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ e0)
        (Q'.mul_add_eqv q ((s k).approx m) (A.approx m + (-((s k).approx m))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_add_left _ _ _ hqd')

/-! ## 2. Finite rational functionals and their spacing modulus -/

/-- A positive normalized `Q'`-linear functional on the enriched observable
algebra.  Equality is rational equivalence, so no normalization of fractions is
smuggled into the finite-stage laws. -/
structure QLinearFunctional (A : LinearObsAlg) where
  E : A.carrier → Q'
  normalized : (E A.one).eqv 1
  positive : ∀ a, (0 : Q') ≤ E (A.mul (A.star a) a)
  additive : ∀ a b, (E (A.add a b)).eqv (E a + E b)
  homogeneous : ∀ q a, (E (A.smul q a)).eqv (q * E a)

/-- The honest spacing-limit datum: a finite-stage positive linear functional
at every spacing and an explicit constructive outer Cauchy modulus for every
observable. -/
structure LinearScalingLimitModulus (A : LinearObsAlg) where
  atSpacing : Nat → QLinearFunctional A
  modOf : ∀ o : A.carrier,
    ModCauchy (fun j => ofQ' ((atSpacing j).E o))

def regSeq {A : LinearObsAlg} (L : LinearScalingLimitModulus A)
    (o : A.carrier) : Nat → RegularCReal :=
  fun j => ofQ' ((L.atSpacing j).E o)

/-- The constructive spacing-limit expectation. -/
def limitE {A : LinearObsAlg} (L : LinearScalingLimitModulus A)
    (o : A.carrier) : RegularCReal :=
  completeLimit (regSeq L o) (L.modOf o)

theorem regSeq_converges {A : LinearObsAlg} (L : LinearScalingLimitModulus A)
    (o : A.carrier) : ConvergesTo (regSeq L o) (limitE L o) :=
  convergesTo_completeLimit (regSeq L o) (L.modOf o)

/-- The spacing limit is normalized. -/
theorem limitE_normalized {A : LinearObsAlg} (L : LinearScalingLimitModulus A) :
    Equiv (limitE L A.one) (ofQ' 1) := by
  have hc : ConvergesTo (fun _ : Nat => ofQ' (1 : Q')) (ofQ' 1) :=
    convergesTo_const (ofQ' 1)
  have hu : ConvergesTo (regSeq L A.one) (ofQ' 1) :=
    convergesTo_of_approx_eqv
      (fun j n => by
        change ((1 : Q')).eqv ((L.atSpacing j).E A.one)
        exact Q'.eqv_symm (L.atSpacing j).normalized) hc
  exact convergesTo_unique (regSeq L A.one) (regSeq_converges L A.one) hu

/-- Finite-stage positivity passes to the spacing limit. -/
theorem limitE_positive {A : LinearObsAlg} (L : LinearScalingLimitModulus A)
    (a : A.carrier) : czero ≤ limitE L (A.mul (A.star a) a) := by
  show ofQ' 0 ≤ completeLimit
    (regSeq L (A.mul (A.star a) a)) (L.modOf (A.mul (A.star a) a))
  exact ofQ'_le_completeLimit _ _
    (fun j _ => (L.atSpacing j).positive a)

/-- Additivity is preserved by the spacing limit. -/
theorem limitE_additive {A : LinearObsAlg} (L : LinearScalingLimitModulus A)
    (a b : A.carrier) :
    Equiv (limitE L (A.add a b)) (add (limitE L a) (limitE L b)) := by
  have hab : ConvergesTo
      (fun j => add (regSeq L a j) (regSeq L b j))
      (add (limitE L a) (limitE L b)) :=
    convergesTo_add (regSeq_converges L a) (regSeq_converges L b)
  have hab' : ConvergesTo (regSeq L (A.add a b))
      (add (limitE L a) (limitE L b)) :=
    convergesTo_of_approx_eqv
      (fun j n => by
        change ((L.atSpacing j).E a + (L.atSpacing j).E b).eqv
          ((L.atSpacing j).E (A.add a b))
        exact Q'.eqv_symm ((L.atSpacing j).additive a b)) hab
  exact convergesTo_unique (regSeq L (A.add a b))
    (regSeq_converges L (A.add a b)) hab'

/-- Rational homogeneity is preserved by the spacing limit, including negative
scalars. -/
theorem limitE_homogeneous {A : LinearObsAlg} (L : LinearScalingLimitModulus A)
    (q : Q') (a : A.carrier) :
    Equiv (limitE L (A.smul q a)) (qmul q (limitE L a)) := by
  have hq : ConvergesTo (fun j => qmul q (regSeq L a j))
      (qmul q (limitE L a)) :=
    convergesTo_qmul q (regSeq_converges L a)
  have hq' : ConvergesTo (regSeq L (A.smul q a))
      (qmul q (limitE L a)) :=
    convergesTo_of_approx_eqv
      (fun j n => by
        change (q * (L.atSpacing j).E a).eqv
          ((L.atSpacing j).E (A.smul q a))
        exact Q'.eqv_symm ((L.atSpacing j).homogeneous q a)) hq
  exact convergesTo_unique (regSeq L (A.smul q a))
    (regSeq_converges L (A.smul q a)) hq'

/-- Main constructor: the modulus-Cauchy spacing family produces a positive
normalized linear functional, with both linearity laws proved by uniqueness of
constructive limits. -/
def linearFunctionalOfScalingLimit {A : LinearObsAlg}
    (L : LinearScalingLimitModulus A) : RegLinearFunctional A where
  E := limitE L
  normalized := limitE_normalized L
  positive := limitE_positive L
  additive := limitE_additive L
  homogeneous := limitE_homogeneous L

/-! ## 3. Non-vacuity: constant spacing towers -/

/-- Any finite positive linear functional gives a constant spacing tower. -/
def constantScaling {A : LinearObsAlg} (F : QLinearFunctional A) :
    LinearScalingLimitModulus A where
  atSpacing := fun _ => F
  modOf := fun o => constSeqModCauchy (F.E o)

/-- The rational line is a genuine finite positive linear functional. -/
def qLinearFunctional : QLinearFunctional qLinearAlg where
  E := id
  normalized := Q'.eqv_refl 1
  positive := fun a => SumOfSquares.q_mul_self_nonneg a
  additive := fun _ _ => Q'.eqv_refl _
  homogeneous := fun _ _ => Q'.eqv_refl _

/-- A concrete, nondegenerate constant spacing family. -/
def qConstantScaling : LinearScalingLimitModulus qLinearAlg :=
  constantScaling qLinearFunctional

@[simp] theorem constantScaling_limitE_approx {A : LinearObsAlg}
    (F : QLinearFunctional A) (o : A.carrier) (n : Nat) :
    (limitE (constantScaling F) o).approx n = F.E o := rfl

#print axioms convergesTo_const
#print axioms convergesTo_of_approx_eqv
#print axioms convergesTo_add
#print axioms convergesTo_qmul
#print axioms QLinearFunctional
#print axioms LinearScalingLimitModulus
#print axioms limitE_normalized
#print axioms limitE_positive
#print axioms limitE_additive
#print axioms limitE_homogeneous
#print axioms linearFunctionalOfScalingLimit
#print axioms constantScaling
#print axioms qLinearFunctional
#print axioms qConstantScaling

end YMGap.Continuum.RegularLinearScalingLimit
