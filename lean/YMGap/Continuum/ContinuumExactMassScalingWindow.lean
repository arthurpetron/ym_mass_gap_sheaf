/-
M4y -- isolate the scaling-window input and transport the lattice decay bound
to the selected continuum correlator.

The corrected exact-mass target already pins one spacing-indexed physical
family to the selected projective correlator.  One geometric fact is still
needed before its finite-spacing decay inequality can be passed to the limit:

* the source-defined dimensionless ratio
  `max(1/(n+1), n/(L+1))` must enter its vanishing window at positive
  separation; canonical floor sampling supplies its UV half, while its IR
  half is the genuine physical-volume-growth input; and
Constructive continuity of `expNegCD`, fixed powers, and fixed amplitudes then
derives convergence of the sampled physical exponential envelope.

Those facts are recorded below as an explicit, deliberately uninhabited
scaling-window extension.  From it, the continuum decay inequality is proved
using constructive continuity of absolute value and the existing order-limit
transport theorem.  No continuum Yang--Mills or scaling-window inhabitant is
constructed here.
-/

import YMGap.Continuum.ContinuumCorrectedExactMassTarget
import YMGap.Constructive.CRealAbsContinuity
import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero

namespace YMGap.Continuum.ContinuumExactMassScalingWindow

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.UniformCorrelationDecay

/-- The unweighted exact-mass exponential factor at integer physical
separation `t`.  Spacing `1` makes the exponent `m * t`. -/
def exactMassContinuumDecayFactor
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t : Nat) : CReal :=
  let U := T.uniform.uniformDecay
  physEnvelope U.m (Q'.ofNat 1) (U.expData (Q'.ofNat 1)) t

/-- The amplitude-weighted exact-mass exponential envelope.  The quotient
identity in the corrected target identifies `m` with the canonical exact
logarithmic physical mass. -/
def exactMassContinuumEnvelope
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t : Nat) : CReal :=
  CReal.mul T.uniform.uniformDecay.A
    (exactMassContinuumDecayFactor T t)

/-- Absolute sampled correlation appearing on the left side of the uniform
finite-spacing decay estimate. -/
def sampledAbsoluteCorrelation
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) : CReal :=
  CReal.ofQ' (Q'.abs
    ((T.uniform.uniformDecay.fam
      (T.exact.physicalSpacing.spacing j)
      (T.exact.physicalSpacing.spacing_pos j)).corr
        (T.exact.sampling.latticeSteps j t)))

/-- The unweighted physical exponential factor at the target spacing and
sampled separation. -/
def sampledPhysicalDecayFactor
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) : CReal :=
  let U := T.uniform.uniformDecay
  physEnvelope U.m
    (T.exact.physicalSpacing.spacing j)
    (U.expData (T.exact.physicalSpacing.spacing j))
    (T.exact.sampling.latticeSteps j t)

/-- One `(t+1)`-st chunk of the per-step exponent.  Chunking keeps the
variable exponent inside the unit interval required by `expNegCD`, while the
outer physical-time power is fixed. -/
def sampledTimeChunkExponent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (Q'.invSucc t))
    (CReal.mul T.uniform.uniformDecay.m
      (CReal.ofQ' (T.exact.physicalSpacing.spacing j)))

/-- The constructive modulus data for the time chunk.  Multiplication by
`1/(t+1)` is sub-unit, so `scaleQData` reuses the per-step exponent modulus. -/
def sampledTimeChunkExpData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) :
    CReal.ExpNegCData (sampledTimeChunkExponent T t j) :=
  CReal.scaleQData (Q'.invSucc t) (Q'.invSucc_nonneg t)
    (CReal.invSucc_le_one t)
    (CReal.mul T.uniform.uniformDecay.m
      (CReal.ofQ' (T.exact.physicalSpacing.spacing j)))
    (T.uniform.uniformDecay.expData (T.exact.physicalSpacing.spacing j))

/-- Repeating the `(t+1)`-st chunk exactly `t+1` times recovers the original
per-step mass exponent, approximation by approximation. -/
theorem sampledTimeChunk_descent_approx
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j k : Nat) :
    ((CReal.scaleN (t + 1) (sampledTimeChunkExponent T t j)).approx k).eqv
      ((CReal.mul T.uniform.uniformDecay.m
        (CReal.ofQ' (T.exact.physicalSpacing.spacing j))).approx k) := by
  let u := (CReal.mul T.uniform.uniformDecay.m
    (CReal.ofQ' (T.exact.physicalSpacing.spacing j))).approx k
  refine Q'.eqv_trans _ _ _
    (CReal.scaleN_approx (t + 1) (sampledTimeChunkExponent T t j) k) ?_
  change (Q'.ofNat (t + 1) * (Q'.invSucc t * u)).eqv u
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat (t + 1)) (Q'.invSucc t) u)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ u (Q'.ofNat_succ_mul_invSucc t)) ?_
  exact Q'.one_mul_eqv u

/-- Constructive-real form of the exact chunk descent. -/
theorem sampledTimeChunk_descent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) :
    CReal.Equiv
      (CReal.scaleN (t + 1) (sampledTimeChunkExponent T t j))
      (CReal.mul T.uniform.uniformDecay.m
        (CReal.ofQ' (T.exact.physicalSpacing.spacing j))) :=
  SumOfSquares.Equiv_of_approx_eqv (sampledTimeChunk_descent_approx T t j)

/-- The exact chunk descent inherits the unit upper bound of the original
per-step exponent. -/
theorem sampledTimeChunk_descent_le_one
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j k : Nat) :
    (CReal.scaleN (t + 1) (sampledTimeChunkExponent T t j)).approx k ≤
      (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (sampledTimeChunk_descent_approx T t j k))
    ((T.uniform.uniformDecay.expData
      (T.exact.physicalSpacing.spacing j)).hle1 k)

/-- Modulus data for the recovered per-step exponent viewed as a chunk sum. -/
def sampledTimeChunkDescentExpData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) :
    CReal.ExpNegCData
      (CReal.scaleN (t + 1) (sampledTimeChunkExponent T t j)) :=
  CReal.scaleData (sampledTimeChunkExponent T t j)
    (sampledTimeChunkExpData T t j) (t + 1)
    (sampledTimeChunk_descent_le_one T t j)

/-- The sampled exponent normalized by the fixed positive physical time
`t+1`: `n_j * (m*a_j/(t+1))`. -/
def sampledNormalizedExponent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) : CReal :=
  CReal.scaleN (T.exact.sampling.latticeSteps j (t + 1))
    (sampledTimeChunkExponent T t j)

/-- Approximation-level form of the normalized exponent/physical-distance
identity. -/
theorem sampledNormalizedExponent_approx_eqv_distance
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j k : Nat) :
    ((sampledNormalizedExponent T t j).approx k).eqv
      (Q'.invSucc t *
        (T.uniform.uniformDecay.m.approx k *
          (T.exact.physicalSpacing.spacing j *
            Q'.ofNat (T.exact.sampling.latticeSteps j (t + 1))))) := by
  let n := T.exact.sampling.latticeSteps j (t + 1)
  let c := Q'.invSucc t
  let a := T.exact.physicalSpacing.spacing j
  let m := T.uniform.uniformDecay.m.approx k
  change ((CReal.scaleN n
      (CReal.mul (CReal.ofQ' c)
        (CReal.mul T.uniform.uniformDecay.m (CReal.ofQ' a)))).approx k).eqv
    (c * (m * (a * Q'.ofNat n)))
  refine Q'.eqv_trans _ _ _ (CReal.scaleN_approx n _ k) ?_
  change (Q'.ofNat n * (c * (m * a))).eqv
    (c * (m * (a * Q'.ofNat n)))
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) c (m * a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat n) c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c (Q'.ofNat n) (m * a)) ?_
  refine Q'.mul_eqv_congr_left c _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) m a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv (Q'.ofNat n) m)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv m (Q'.ofNat n) a) ?_
  exact Q'.mul_eqv_congr_left m _ _ (Q'.mul_comm_eqv (Q'.ofNat n) a)

/-- The normalized sampled exponent is definitionally tied, up to
constructive-real equivalence, to the physical sampled distance. -/
theorem sampledNormalizedExponent_equiv_distance
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) :
    CReal.Equiv (sampledNormalizedExponent T t j)
      (CReal.mul (CReal.ofQ' (Q'.invSucc t))
        (CReal.mul T.uniform.uniformDecay.m
          (CReal.ofQ'
            (T.exact.physicalSpacing.spacing j *
              Q'.ofNat (T.exact.sampling.latticeSteps j (t + 1)))))) :=
  SumOfSquares.Equiv_of_approx_eqv
    (sampledNormalizedExponent_approx_eqv_distance T t j)

/-- The normalized exponent converges automatically to the one-step mass
exponent.  This is the dimensional heart of the chunking reduction: it uses
only the already-pinned physical-distance sampling. -/
theorem sampledNormalizedExponent_converges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t : Nat) :
    CReal.ConvergesTo (sampledNormalizedExponent T t)
      (CReal.mul T.uniform.uniformDecay.m (CReal.ofQ' (Q'.ofNat 1))) := by
  let U := T.uniform.uniformDecay
  let c := Q'.invSucc t
  have hdistance := T.exact.sampling.distanceConverges (t + 1)
  have hmass := CReal.convergesTo_const_mul U.m hdistance
  have hscaled := CReal.convergesTo_const_mul (CReal.ofQ' c) hmass
  have hseq := YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (fun j => (sampledNormalizedExponent_equiv_distance T t j).symm) hscaled
  refine CReal.convergesTo_limit_congr hseq ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun k => ?_)
  change (c * (U.m.approx k * Q'.ofNat (t + 1))).eqv
    (U.m.approx k * Q'.ofNat 1)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_comm_eqv (U.m.approx k) (Q'.ofNat (t + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv c (Q'.ofNat (t + 1)) (U.m.approx k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (U.m.approx k)
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv c (Q'.ofNat (t + 1)))
        (Q'.ofNat_succ_mul_invSucc t))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (U.m.approx k)) ?_
  exact Q'.eqv_symm (Q'.mul_one_eqv (U.m.approx k))

/-- The amplitude-weighted physical exponential at the target spacing and
sampled separation. -/
def sampledWeightedEnvelope
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) : CReal :=
  CReal.mul T.uniform.uniformDecay.A (sampledPhysicalDecayFactor T t j)

/-- The scaling error at the target spacing and sampled separation. -/
def sampledDecayError
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t j : Nat) : CReal :=
  T.uniform.uniformDecay.err
    (physicalScalingRatio
      (T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j))
      (T.exact.sampling.latticeSteps j t))

/-! ## The actual dimensionless scaling variable

At lattice separation `n` inside a correlator of linear size `L+1`, the two
discrete ratios are `1/(n+1)` and `n/(L+1)`.  The first is the regularized
lattice-spacing/physical-distance ratio `a/(|x|+a)`; the second is exactly the
separation/volume ratio.  Their maximum is defined for `n=0`, but it approaches
one there.  Consequently the decay transport is stated only at positive
physical separation.  The ratio itself is defined at the source in
`UniformCorrelationDecay`, so no later same-object ratio pin is needed. -/

/-- For the canonical floor sampling, the actual UV ratio `1/(n+1)` is at
most the lattice spacing.  This turns any spacing-to-zero modulus into the UV
half of the physical scaling window. -/
theorem floorLatticeUVRatio_le_spacing
    (A : PhysicalSpacing) (j t : Nat) :
    latticeUVRatio (floorLatticeSteps A j (t + 1)) <= A.spacing j := by
  let a := A.spacing j
  let p : Nat := a.num.toNat
  let d : Nat := a.den
  let n : Nat := ((t + 1) * d) / p
  have hp : 0 < p := by
    dsimp [p, a]
    exact spacingNumToNat_pos A j
  have hpInt : (0 : Int) < a.num := Q'.num_pos_of_pos (A.spacing_pos j)
  have hpCast : (p : Int) = a.num := by
    dsimp [p]
    exact Int.toNat_of_nonneg (Int.le_of_lt hpInt)
  have hstrict : (t + 1) * d < p * (n + 1) := by
    have hmod : ((t + 1) * d) % p < p := Nat.mod_lt _ hp
    have hdecomp : p * n + ((t + 1) * d) % p = (t + 1) * d := by
      dsimp [n]
      exact Nat.div_add_mod ((t + 1) * d) p
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hdle : d <= p * (n + 1) := by
    have hd : d <= (t + 1) * d := by
      rw [Nat.add_mul]
      omega
    exact Nat.le_trans hd (Nat.le_of_lt hstrict)
  show (Q'.mkPos 1 (floorLatticeSteps A j (t + 1) + 1)
      (Nat.succ_pos _)).num * (a.den : Int) <=
    a.num * ((Q'.mkPos 1 (floorLatticeSteps A j (t + 1) + 1)
      (Nat.succ_pos _)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den, Int.one_mul]
  change (d : Int) <= a.num * ((n + 1 : Nat) : Int)
  rw [<- hpCast]
  exact_mod_cast hdle

/-- The canonical floor sampler therefore supplies a constructive UV cutoff
for every positive physical separation. -/
def floorLatticeUVWindow
    (A : PhysicalSpacing) (Z : SpacingToZero A)
    (t : Nat) (δ : Q') (hδ : (0 : Q') < δ) :
    { J : Nat // forall j : Nat, J <= j ->
      latticeUVRatio (floorLatticeSteps A j (t + 1)) <= δ } :=
  ⟨Z.modulus δ, fun j hj =>
    Q'.le_trans' _ _ _ (floorLatticeUVRatio_le_spacing A j t)
      (Z.spacing_le δ hδ j hj)⟩

/-! ## A denominator-free thermodynamic IR certificate

The rational condition `n/(L+1) ≤ δ` is exactly the integer cross-product
condition `n * δ.den ≤ δ.num * (L+1)`.  The latter states directly that the
linear volume dominates the sampled separation at the requested modulus and
is the form expected from constructive finite-volume estimates. -/

/-- Denominator-free form of the thermodynamic dominance inequality. -/
def thermodynamicIRDominance
    (P : PhysicalCorrelator) (n : Nat) (δ : Q') : Prop :=
  (n : Int) * (δ.den : Int) ≤ δ.num * ((P.L + 1 : Nat) : Int)

/-- The quotient IR bound and its cross-multiplied volume-growth condition
are definitionally the same rational inequality. -/
theorem latticeIRRatio_le_iff_thermodynamicIRDominance
    (P : PhysicalCorrelator) (n : Nat) (δ : Q') :
    latticeIRRatio P n ≤ δ ↔ thermodynamicIRDominance P n δ := by
  change
    (Q'.mkPos n (P.L + 1) (Nat.succ_pos P.L)).num * (δ.den : Int) ≤
        δ.num *
          ((Q'.mkPos n (P.L + 1) (Nat.succ_pos P.L)).den : Int) ↔
      (n : Int) * (δ.den : Int) ≤
        δ.num * ((P.L + 1 : Nat) : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]

/-- Constructive thermodynamic-limit data on the exact physical correlator
selected by `T`: for each fixed positive physical separation and tolerance,
it returns a scale after which the linear volume dominates the sampled
separation in cross-multiplied integer form.  This structure is deliberately
uninhabited. -/
structure SelectedThermodynamicIRPins
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  volumeDominates : forall (t : Nat) (δ : Q'), (0 : Q') < δ ->
    { J : Nat // forall j : Nat, J ≤ j ->
      thermodynamicIRDominance
        (T.uniform.uniformDecay.fam
          (T.exact.physicalSpacing.spacing j)
          (T.exact.physicalSpacing.spacing_pos j))
        (T.exact.sampling.latticeSteps j (t + 1)) δ }

namespace SelectedThermodynamicIRPins

/-- Cross-multiplied thermodynamic dominance supplies the quotient IR window
used by the concrete scaling ratio. -/
def irWindow
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (H : SelectedThermodynamicIRPins T)
    (t : Nat) (δ : Q') (hδ : (0 : Q') < δ) :
    { J : Nat // forall j : Nat, J ≤ j ->
      latticeIRRatio
        (T.uniform.uniformDecay.fam
          (T.exact.physicalSpacing.spacing j)
          (T.exact.physicalSpacing.spacing_pos j))
        (T.exact.sampling.latticeSteps j (t + 1)) ≤ δ } := by
  obtain ⟨J, hJ⟩ := H.volumeDominates t δ hδ
  exact ⟨J, fun j hj =>
    (latticeIRRatio_le_iff_thermodynamicIRDominance _ _ _).2 (hJ j hj)⟩

end SelectedThermodynamicIRPins

/-! ## Physical-volume growth implies the IR certificate

For a fixed positive physical separation `t+1`, it is enough that the sampled
distance does not overshoot `t+1` and that the actual linear extent
`a_j (L_j+1)` eventually dominates `(t+1)/δ`.  Positivity of `a_j` then
cancels it from

`a_j n_j ≤ t+1 ≤ a_j (δ (L_j+1))`,

leaving the required `n_j/(L_j+1) ≤ δ`. -/

/-- The physical-extent inequality at one scale, written so that the positive
target spacing is a common cancellable factor.  The corrected target pins
this spacing to the internal spacing of the same physical correlator family. -/
def physicalExtentDominatesAt
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu)
    (t j : Nat) (δ : Q') : Prop :=
  Q'.ofNat (t + 1) ≤
    T.exact.physicalSpacing.spacing j *
      (δ * Q'.ofNat
        ((T.uniform.uniformDecay.fam
          (T.exact.physicalSpacing.spacing j)
          (T.exact.physicalSpacing.spacing_pos j)).L + 1))

/-- The actual linear size `a_j (L_j+1)` of the selected physical-correlator
box.  Both the spacing and the lattice extent come from the exact same family
already pinned by the corrected target. -/
def selectedPhysicalLinearExtentAt
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (j : Nat) : Q' :=
  T.exact.physicalSpacing.spacing j *
    Q'.ofNat
      ((T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j)).L + 1)

/-- Cofinal divergence of the selected physical box's linear size.

This is the irreducible thermodynamic input stripped of the sampler time and
tolerance bookkeeping: every fixed rational physical length is eventually
contained in the same spacing-indexed correlator family.  The structure is
deliberately uninhabited. -/
structure SelectedPhysicalLinearExtentDivergence
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  eventuallyExceeds : forall R : Q',
    { J : Nat // forall j : Nat, J <= j ->
      R <= selectedPhysicalLinearExtentAt T j }

/-- A concrete sufficient schedule for physical-volume removal: at scale
index `j`, the selected physical box has linear size at least `j`.

Unlike the cofinal formulation above, this is a pointwise inequality that can
be targeted directly by a finite-volume construction. -/
structure SelectedPhysicalLinearExtentDiagonalGrowth
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  diagonalLowerBound : forall j : Nat,
    Q'.ofNat j <= selectedPhysicalLinearExtentAt T j

/-- A denominator-aware lattice volume schedule.  At scale `j`, it asks for
at least `j * den(a_j)` lattice units in the selected correlator's linear
extent.  This is a natural-number condition with no quotient arithmetic left
for a finite-volume producer to discharge. -/
structure SelectedLatticeExtentDenominatorSchedule
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  latticeExtentLowerBound : forall j : Nat,
    j * (T.exact.physicalSpacing.spacing j).den <=
      (T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j)).L + 1

namespace SelectedPhysicalLinearExtentDiagonalGrowth

/-- The denominator-aware lattice schedule implies the physical diagonal
bound.  Positivity of `a_j` gives `1 <= num(a_j)`, so

`j*den(a_j) <= L_j+1 <= num(a_j)*(L_j+1)`.

Cross multiplication is exactly `j <= a_j(L_j+1)`. -/
def ofLatticeDenominatorSchedule
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (H : SelectedLatticeExtentDenominatorSchedule T) :
    SelectedPhysicalLinearExtentDiagonalGrowth T where
  diagonalLowerBound := by
    intro j
    let a : Q' := T.exact.physicalSpacing.spacing j
    let extent : Nat :=
      (T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j)).L + 1
    have hschedule : j * a.den <= extent := H.latticeExtentLowerBound j
    have hscheduleInt : (j : Int) * (a.den : Int) <= (extent : Int) := by
      exact_mod_cast hschedule
    have hnumPos : (0 : Int) < a.num :=
      CReal.num_pos_of_pos (T.exact.physicalSpacing.spacing_pos j)
    have hnum : (1 : Int) <= a.num := by omega
    have hextentNonneg : (0 : Int) <= (extent : Int) := Int.natCast_nonneg _
    have hextentScaled : (extent : Int) <= a.num * (extent : Int) := by
      have := Int.mul_le_mul_of_nonneg_right hnum hextentNonneg
      simpa only [Int.one_mul] using this
    show (Q'.ofNat j).num *
        ((a * Q'.ofNat extent).den : Int) <=
      (a * Q'.ofNat extent).num * ((Q'.ofNat j).den : Int)
    simpa only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one] using
        (Int.le_trans hscheduleInt hextentScaled)

end SelectedPhysicalLinearExtentDiagonalGrowth

namespace SelectedPhysicalLinearExtentDivergence

/-- The diagonal lower bound `j <= a_j(L_j+1)` is cofinal because the natural
numbers dominate every rational. -/
def ofDiagonalGrowth
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (H : SelectedPhysicalLinearExtentDiagonalGrowth T) :
    SelectedPhysicalLinearExtentDivergence T where
  eventuallyExceeds := by
    intro R
    refine ⟨RegularCReal.qBound R, fun j hj => ?_⟩
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self R)
      (Q'.le_trans' _ _ _ (RegularCReal.abs_le_ofNat_qBound R)
        (Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hj)
          (H.diagonalLowerBound j)))

end SelectedPhysicalLinearExtentDivergence

/-- Constructive growth of the same physical correlator's linear extent,
together with a no-overshoot sampler bound.  This is a sufficient physical
form of thermodynamic removal and remains deliberately uninhabited. -/
structure SelectedPhysicalVolumeGrowthPins
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  sampledDistanceBound : forall (j t : Nat),
    T.exact.physicalSpacing.spacing j *
        Q'.ofNat (T.exact.sampling.latticeSteps j (t + 1)) ≤
      Q'.ofNat (t + 1)
  extentDominates : forall (t : Nat) (δ : Q'), (0 : Q') < δ ->
    { J : Nat // forall j : Nat, J ≤ j ->
      physicalExtentDominatesAt T t j δ }

namespace SelectedPhysicalVolumeGrowthPins

/-- Cofinal divergence of `a_j(L_j+1)`, together with the sampler's
no-overshoot theorem, supplies every time-and-tolerance physical-volume
window. -/
def ofLinearExtentDivergence
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (H : SelectedPhysicalLinearExtentDivergence T)
    (sampledDistanceBound : forall (j t : Nat),
      T.exact.physicalSpacing.spacing j *
          Q'.ofNat (T.exact.sampling.latticeSteps j (t + 1)) <=
        Q'.ofNat (t + 1)) :
    SelectedPhysicalVolumeGrowthPins T where
  sampledDistanceBound := sampledDistanceBound
  extentDominates := by
    intro t delta hdelta
    let target : Q' := Q'.ofNat (t + 1)
    let threshold : Q' := Q'.divPos target delta hdelta
    obtain ⟨J, hJ⟩ := H.eventuallyExceeds threshold
    refine ⟨J, fun j hj => ?_⟩
    let a : Q' := T.exact.physicalSpacing.spacing j
    let box : Q' := Q'.ofNat
      ((T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j)).L + 1)
    have hscaled : delta * threshold <= delta * (a * box) :=
      Q'.mul_le_mul_of_nonneg_left _ _ delta (hJ j hj) (Q'.le_of_lt hdelta)
    have hleft : (delta * threshold).eqv target := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv delta threshold) ?_
      exact Q'.divPos_mul_eqv target delta hdelta
    have hright : (delta * (a * box)).eqv (a * (delta * box)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv delta a box)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (delta * a) (a * delta) box
          (Q'.mul_comm_eqv delta a)) ?_
      exact Q'.mul_assoc_eqv a delta box
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- Physical linear-extent growth yields the denominator-free
thermodynamic IR certificate by cancellation of the positive spacing. -/
def thermodynamicIR
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) :
    SelectedThermodynamicIRPins T where
  volumeDominates := by
    intro t δ hδ
    obtain ⟨J, hJ⟩ := V.extentDominates t δ hδ
    refine ⟨J, fun j hj => ?_⟩
    let a : Q' := T.exact.physicalSpacing.spacing j
    let n : Nat := T.exact.sampling.latticeSteps j (t + 1)
    let P : PhysicalCorrelator := T.uniform.uniformDecay.fam
      (T.exact.physicalSpacing.spacing j)
      (T.exact.physicalSpacing.spacing_pos j)
    have hscaled : a * Q'.ofNat n ≤
        a * (δ * Q'.ofNat (P.L + 1)) :=
      Q'.le_trans' _ _ _ (V.sampledDistanceBound j t) (hJ j hj)
    have hquot : Q'.ofNat n ≤ δ * Q'.ofNat (P.L + 1) :=
      Q'.le_of_mul_le_mul_left hscaled
        (T.exact.physicalSpacing.spacing_pos j)
    have hcross :
        (Q'.ofNat n).num *
            ((δ * Q'.ofNat (P.L + 1)).den : Int) ≤
          (δ * Q'.ofNat (P.L + 1)).num *
            ((Q'.ofNat n).den : Int) := hquot
    show (n : Int) * (δ.den : Int) ≤
      δ.num * ((P.L + 1 : Nat) : Int)
    simpa only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one] using hcross

/-- No-overshoot physical sampling keeps the normalized exponent in the unit
interval.  The mass bound itself is read from the already-supplied exponent
data at spacing one, so no new mass ceiling is assumed. -/
theorem sampledNormalizedExponent_le_one
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t j k : Nat) :
    (sampledNormalizedExponent T t j).approx k ≤ (1 : Q') := by
  let U := T.uniform.uniformDecay
  let m := U.m.approx k
  let a := T.exact.physicalSpacing.spacing j
  let n := T.exact.sampling.latticeSteps j (t + 1)
  let c := Q'.invSucc t
  have hm0 : (0 : Q') ≤ m :=
    Q'.le_trans' _ _ _ ((U.expData (Q'.ofNat 1)).hpos k)
      (Q'.le_of_eqv (Q'.mul_one_eqv m))
  have hm1 : m ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv m)))
      ((U.expData (Q'.ofNat 1)).hle1 k)
  have hN0 : (0 : Q') ≤ Q'.ofNat (t + 1) := ExpNeg.ofNat_nonneg' _
  have hdist : a * Q'.ofNat n ≤ Q'.ofNat (t + 1) :=
    V.sampledDistanceBound j t
  have hmassDistance : m * (a * Q'.ofNat n) ≤ Q'.ofNat (t + 1) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ m hdist hm0) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right m 1 (Q'.ofNat (t + 1)) hm1 hN0) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.ofNat (t + 1)))
  have hscaled : c * (m * (a * Q'.ofNat n)) ≤
      c * Q'.ofNat (t + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ c hmassDistance (Q'.invSucc_nonneg t)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (sampledNormalizedExponent_approx_eqv_distance T t j k)) ?_
  refine Q'.le_trans' _ _ _ hscaled ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv c (Q'.ofNat (t + 1)))
      (Q'.ofNat_succ_mul_invSucc t))

/-- Fully constructed `ExpNegCData` for the normalized sampled exponent. -/
def sampledNormalizedExpData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t j : Nat) :
    CReal.ExpNegCData (sampledNormalizedExponent T t j) :=
  CReal.scaleData (sampledTimeChunkExponent T t j)
    (sampledTimeChunkExpData T t j)
    (T.exact.sampling.latticeSteps j (t + 1))
    (V.sampledNormalizedExponent_le_one t j)

/-- The exponential of the normalized sampled exponent. -/
def sampledNormalizedExpFactor
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t j : Nat) : CReal :=
  CReal.expNegCD (sampledNormalizedExponent T t j)
    (V.sampledNormalizedExpData t j)

/-- Exact chunking rewrites the variable lattice power as the fixed physical
time power of the normalized exponential.  This is purely algebraic once the
no-overshoot unit bound has supplied the two `ExpNegCData` packages. -/
theorem sampledPhysicalDecayFactor_equiv_chunkPower
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t j : Nat) :
    CReal.Equiv (sampledPhysicalDecayFactor T (t + 1) j)
      (CReal.cpow (V.sampledNormalizedExpFactor t j) (t + 1)) := by
  let U := T.uniform.uniformDecay
  let a := T.exact.physicalSpacing.spacing j
  let n := T.exact.sampling.latticeSteps j (t + 1)
  let v := sampledTimeChunkExponent T t j
  let dv := sampledTimeChunkExpData T t j
  let s := sampledNormalizedExponent T t j
  let ds := V.sampledNormalizedExpData t j
  let eV := CReal.expNegCD v dv
  have hbasePow : CReal.Equiv (CReal.cpow eV (t + 1))
      (CReal.expNegCD (CReal.scaleN (t + 1) v)
        (sampledTimeChunkDescentExpData T t j)) :=
    CReal.expNegCD_powerLaw v dv (t + 1)
      (sampledTimeChunk_descent_le_one T t j)
  have hdescentExp : CReal.Equiv
      (CReal.expNegCD (CReal.scaleN (t + 1) v)
        (sampledTimeChunkDescentExpData T t j))
      (CReal.expNegCD
        (CReal.mul U.m (CReal.ofQ' a)) (U.expData a)) :=
    CReal.expNegCD_pointwise_congr
      (CReal.scaleN (t + 1) v) (CReal.mul U.m (CReal.ofQ' a))
      (sampledTimeChunkDescentExpData T t j) (U.expData a)
      (sampledTimeChunk_descent_approx T t j)
  have hbase : CReal.Equiv
      (CReal.expNegCD (CReal.mul U.m (CReal.ofQ' a)) (U.expData a))
      (CReal.cpow eV (t + 1)) :=
    (CReal.Equiv.trans hbasePow hdescentExp).symm
  have hnormalized : CReal.Equiv (CReal.cpow eV n)
      (CReal.expNegCD s ds) :=
    CReal.expNegCD_powerLaw v dv n
      (V.sampledNormalizedExponent_le_one t j)
  change CReal.Equiv
    (CReal.cpow
      (CReal.expNegCD (CReal.mul U.m (CReal.ofQ' a)) (U.expData a)) n)
    (CReal.cpow (CReal.expNegCD s ds) (t + 1))
  refine CReal.Equiv.trans (CReal.cpow_equiv hbase n) ?_
  refine CReal.Equiv.trans (CReal.cpow_mul eV (t + 1) n) ?_
  rw [Nat.mul_comm (t + 1) n]
  refine CReal.Equiv.trans (CReal.cpow_mul eV n (t + 1)).symm ?_
  exact CReal.cpow_equiv hnormalized (t + 1)

/-- Continuity of `expNegCD` only on the normalized unit-interval exponent,
combined with fixed-power continuity and exact chunking, implies the original
physical-envelope limit.  This is the reduced analytic seam. -/
theorem positiveEnvelopeConverges_of_normalizedExpConverges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t : Nat)
    (hExp : CReal.ConvergesTo (V.sampledNormalizedExpFactor t)
      (stepFactor T.uniform.uniformDecay.m (Q'.ofNat 1)
        (T.uniform.uniformDecay.expData (Q'.ofNat 1)))) :
    CReal.ConvergesTo (sampledPhysicalDecayFactor T (t + 1))
      (exactMassContinuumDecayFactor T (t + 1)) := by
  let U := T.uniform.uniformDecay
  have hSeqBound : ∀ j k,
      Q'.abs ((V.sampledNormalizedExpFactor t j).approx k) ≤ Q'.ofNat 3 := by
    intro j k
    let d := V.sampledNormalizedExpData t j
    exact ExpNeg.expNegC_approx_le_three
      (sampledNormalizedExponent T t j) d.Mw d.hpos d.hle1
      d.hMw d.hMwmono k
  have hLimitBound : ∀ k,
      Q'.abs ((stepFactor U.m (Q'.ofNat 1)
        (U.expData (Q'.ofNat 1))).approx k) ≤ Q'.ofNat 3 := by
    intro k
    let d := U.expData (Q'.ofNat 1)
    exact ExpNeg.expNegC_approx_le_three
      (CReal.mul U.m (CReal.ofQ' (Q'.ofNat 1)))
      d.Mw d.hpos d.hle1 d.hMw d.hMwmono k
  have hPower := CReal.convergesTo_cpow_of_bound
    (Q'.ofNat 3) (by decide : (0 : Q') ≤ Q'.ofNat 3)
    hSeqBound hLimitBound hExp (t + 1)
  change CReal.ConvergesTo (sampledPhysicalDecayFactor T (t + 1))
    (CReal.cpow
      (stepFactor U.m (Q'.ofNat 1) (U.expData (Q'.ofNat 1))) (t + 1))
  exact YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (fun j => (V.sampledPhysicalDecayFactor_equiv_chunkPower t j).symm)
    hPower

/-- The normalized exponential factor converges without a residual continuity
assumption: `sampledNormalizedExponent_converges` supplies convergence of the
unit-interval exponents, and the generic constructive sequential-continuity
theorem for `expNegCD` transports it. -/
theorem sampledNormalizedExpFactor_converges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t : Nat) :
    CReal.ConvergesTo (V.sampledNormalizedExpFactor t)
      (stepFactor T.uniform.uniformDecay.m (Q'.ofNat 1)
        (T.uniform.uniformDecay.expData (Q'.ofNat 1))) :=
  CReal.convergesTo_expNegCD
    (fun j => V.sampledNormalizedExpData t j)
    (T.uniform.uniformDecay.expData (Q'.ofNat 1))
    (sampledNormalizedExponent_converges T t)

/-- Physical-volume no-overshoot plus the already-pinned distance limit now
imply the complete unweighted positive-separation envelope limit. -/
theorem positiveEnvelopeConverges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (V : SelectedPhysicalVolumeGrowthPins T) (t : Nat) :
    CReal.ConvergesTo (sampledPhysicalDecayFactor T (t + 1))
      (exactMassContinuumDecayFactor T (t + 1)) :=
  V.positiveEnvelopeConverges_of_normalizedExpConverges t
    (V.sampledNormalizedExpFactor_converges t)

end SelectedPhysicalVolumeGrowthPins

/-- Constructive UV and physical-volume windows for the concrete scaling ratio
already fixed by the uniform decay datum.  No time-zero error condition is
imposed: exponential clustering is an asymptotic positive-separation
statement. -/
structure SelectedPhysicalScalingWindows
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  uvWindow : forall (t : Nat) (δ : Q'), (0 : Q') < δ ->
    { J : Nat // forall j : Nat, J <= j ->
      latticeUVRatio (T.exact.sampling.latticeSteps j (t + 1)) <= δ }
  physicalVolume : SelectedPhysicalVolumeGrowthPins T

/-- The exact residual needed to put the target sampling inside the decay
window and identify the limit of its physical exponential envelope.  It is
deliberately uninhabited.

Every window field is Type-valued, so it carries a constructive cutoff rather
than merely asserting one in `Prop`. -/
structure ExactMassUniformDecayScalingWindow
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) : Type 2 where
  physicalWindows : SelectedPhysicalScalingWindows T

namespace ExactMassUniformDecayScalingWindow

/-- The complete positive-separation envelope limit is derived from the
physical window; it is no longer a field of the scaling residual. -/
theorem positiveEnvelopeConverges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (W : ExactMassUniformDecayScalingWindow T) (t : Nat) :
    CReal.ConvergesTo (sampledPhysicalDecayFactor T (t + 1))
      (exactMassContinuumDecayFactor T (t + 1)) :=
  W.physicalWindows.physicalVolume.positiveEnvelopeConverges t

/-- The concrete UV and IR windows give the original error-modulus window at
every positive separation. -/
def positiveRatioWindow
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (W : ExactMassUniformDecayScalingWindow T)
    (t : Nat) (δ : Q') (hδ : (0 : Q') < δ) :
    { J : Nat // forall j : Nat, J <= j ->
      physicalScalingRatio
        (T.uniform.uniformDecay.fam
          (T.exact.physicalSpacing.spacing j)
          (T.exact.physicalSpacing.spacing_pos j))
        (T.exact.sampling.latticeSteps j (t + 1)) <= δ } := by
  obtain ⟨Juv, hJuv⟩ := W.physicalWindows.uvWindow t δ hδ
  obtain ⟨Jir, hJir⟩ :=
    W.physicalWindows.physicalVolume.thermodynamicIR.irWindow t δ hδ
  refine ⟨max Juv Jir, fun j hj => ?_⟩
  have huv : latticeUVRatio
      (T.exact.sampling.latticeSteps j (t + 1)) <= δ :=
    hJuv j (Nat.le_trans (Nat.le_max_left _ _) hj)
  have hir : latticeIRRatio
      (T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j))
      (T.exact.sampling.latticeSteps j (t + 1)) <= δ :=
    hJir j (Nat.le_trans (Nat.le_max_right _ _) hj)
  exact (Q'.max'_le_iff' _ _ _).2 ⟨huv, hir⟩

/-- The error sampled in the target scaling window converges to zero.  The
upper estimate uses `err_vanish`; the lower estimate is the source-level sign
invariant of the error modulus. -/
theorem sampledDecayError_converges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (W : ExactMassUniformDecayScalingWindow T) (t : Nat) :
    CReal.ConvergesTo (sampledDecayError T (t + 1)) CReal.czero := by
  intro ε hε
  have hhalf : (0 : Q') < HalfPow.half * ε :=
    ExpNeg.half_mul_pos ε hε
  obtain ⟨δ, hδ, herr⟩ :=
    T.uniform.uniformDecay.err_vanish (HalfPow.half * ε) hhalf
  obtain ⟨J, hJ⟩ := W.positiveRatioWindow t δ hδ
  refine ⟨J, fun j hj => ?_⟩
  let r : Q' := physicalScalingRatio
    (T.uniform.uniformDecay.fam
      (T.exact.physicalSpacing.spacing j)
      (T.exact.physicalSpacing.spacing_pos j))
    (T.exact.sampling.latticeSteps j (t + 1))
  have hr0 : (0 : Q') <= r :=
    physicalScalingRatio_nonneg
      (T.uniform.uniformDecay.fam
        (T.exact.physicalSpacing.spacing j)
        (T.exact.physicalSpacing.spacing_pos j))
      (T.exact.sampling.latticeSteps j (t + 1))
  have hrδ : r <= δ := hJ j hj
  obtain ⟨Nupper, hupper⟩ :=
    herr r hr0 hrδ (HalfPow.half * ε) hhalf
  obtain ⟨Nlower, hlower⟩ :=
    T.uniform.uniformDecay.err_nonneg r ε hε
  refine ⟨max Nupper Nlower, fun n hn => ?_⟩
  have hnUpper : Nupper <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnLower : Nlower <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  constructor
  · have hu := hupper n hnUpper
    refine Q'.le_trans' _ _ _ hu (Q'.le_of_eqv ?_)
    exact Q'.eqv_trans _ _ _ (ExpNeg.two_halves ε)
      (Q'.eqv_symm (QPoly.q_zero_add_eqv ε))
  · exact hlower n hnLower

/-- Absolute values of the sampled physical family converge to the absolute
value of the same selected projective continuum correlator. -/
theorem sampledAbsoluteCorrelation_converges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu) (t : Nat) :
    CReal.ConvergesTo (sampledAbsoluteCorrelation T t)
      (CReal.abs (T.exact.projective.continuumCorr
        T.exact.projective.gapObservable t)) := by
  simpa [sampledAbsoluteCorrelation, CReal.abs_ofQ'] using
    CReal.convergesTo_abs (T.uniformSampledGapCorrelationConverges t)

/-- The fixed amplitude can be restored after the genuine exponential-factor
limit; scalar multiplication is constructively continuous. -/
theorem sampledWeightedEnvelope_converges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (W : ExactMassUniformDecayScalingWindow T) (t : Nat) :
    CReal.ConvergesTo (sampledWeightedEnvelope T (t + 1))
      (exactMassContinuumEnvelope T (t + 1)) := by
  simpa [sampledWeightedEnvelope, exactMassContinuumEnvelope] using
    CReal.convergesTo_const_mul T.uniform.uniformDecay.A
      (W.positiveEnvelopeConverges t)

/-- The complete right side of the sampled decay estimate converges to the
exact-mass continuum envelope: the scaling error disappears. -/
theorem sampledDecayRhs_converges
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (W : ExactMassUniformDecayScalingWindow T) (t : Nat) :
    CReal.ConvergesTo
      (fun j => CReal.add (sampledWeightedEnvelope T (t + 1) j)
        (sampledDecayError T (t + 1) j))
      (exactMassContinuumEnvelope T (t + 1)) := by
  have hadd := CReal.convergesTo_add
    (W.sampledWeightedEnvelope_converges t) (W.sampledDecayError_converges t)
  refine CReal.convergesTo_limit_congr hadd ?_
  exact SumOfSquares.Equiv_of_approx_eqv (fun n => by
    show ((exactMassContinuumEnvelope T (t + 1)).approx n + 0).eqv
      ((exactMassContinuumEnvelope T (t + 1)).approx n)
    exact Q'.eqv_of_eq (Q'.add_zero' _))

/-- The finite-spacing decay estimate passes to the selected continuum
correlator at the exact logarithmic physical mass.  This theorem consumes the
explicit scaling-window residual and proves the order transport; it does not
construct that residual. -/
theorem continuumExactMassDecay
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {T : ContinuumCorrectedExactMassTarget mu}
    (W : ExactMassUniformDecayScalingWindow T) (t : Nat) :
    CReal.leEv
      (CReal.abs (T.exact.projective.continuumCorr
        T.exact.projective.gapObservable (t + 1)))
      (exactMassContinuumEnvelope T (t + 1)) := by
  apply CReal.leEv_of_convergesTo_le
    (sampledAbsoluteCorrelation_converges T (t + 1))
    (W.sampledDecayRhs_converges t)
  intro j
  exact T.uniform.uniformDecay.decay
    (T.exact.physicalSpacing.spacing j)
    (T.exact.physicalSpacing.spacing_pos j)
    (T.exact.sampling.latticeSteps j (t + 1))

end ExactMassUniformDecayScalingWindow

end YMGap.Continuum.ContinuumExactMassScalingWindow

#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.sampledDecayError_converges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.positiveRatioWindow
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.floorLatticeUVRatio_le_spacing
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.sampledTimeChunk_descent
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.sampledTimeChunkDescentExpData
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.sampledNormalizedExponent_equiv_distance
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.sampledNormalizedExponent_converges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalLinearExtentDiagonalGrowth.ofLatticeDenominatorSchedule
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalLinearExtentDivergence.ofDiagonalGrowth
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.ofLinearExtentDivergence
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.sampledNormalizedExponent_le_one
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.sampledNormalizedExpData
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.sampledPhysicalDecayFactor_equiv_chunkPower
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.positiveEnvelopeConverges_of_normalizedExpConverges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.sampledNormalizedExpFactor_converges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.positiveEnvelopeConverges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.positiveEnvelopeConverges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.floorLatticeUVWindow
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.latticeIRRatio_le_iff_thermodynamicIRDominance
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedThermodynamicIRPins.irWindow
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.SelectedPhysicalVolumeGrowthPins.thermodynamicIR
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.sampledAbsoluteCorrelation_converges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.sampledWeightedEnvelope_converges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.sampledDecayRhs_converges
#print axioms YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow.continuumExactMassDecay
