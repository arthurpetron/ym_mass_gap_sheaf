# Same-carrier completed reflected pairing and physical time

Date: 2026-09-16. Classification: PROGRESS after `68c1cbc`.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian mass gap for
every compact simple group, on the SAME theory, within the constructive
axiom gate. This checkpoint concerns the selected fixed-width SU(2) action;
it does not complete that target.

## Result and causal argument

The original intrinsic reflected pairing now extends to the SAME Cauchy
quotient already carrying physical time. The extension is symmetric,
nonnegative on the diagonal and positive definite: its diagonal is zero
exactly at the embedded zero element. The fixed unit has diagonal one.
Completed time obeys the sum-of-times identity and constant-one diagonal
contraction. Every even-time mixed diagonal lies between zero and the
original diagonal. No completed linear structure is assumed in these proofs.

Expansion exposes the actual continuity estimate and the bounds/moduli
needed for the limit; contraction combines those inputs into one returned
scalar representative and then a well-defined quotient pairing.

1. For Cauchy representative X, take the supplied anchor index iX=X.modulus 1.
   The original coefficient cap CX at X.seq iX and the actual reflected
   squared-sum inequality give the eventual diagonal ceiling BX=2+2*CX.
   Difference-plus-anchor cancellation holds inside the pairing; the
   corresponding signed lists are not equated literally.
2. Sharp CS and the two-term bilinear difference identity prove actual
   pairing continuity. With two unchanged diagonal values bounded by B,
   squared-distance tolerance delta=epsilon^2/[8*(B+1)] gives two-sided
   pairing error epsilon. Physical-face guards remain in the subtype.
   Only generic scalar lemmas from the old plaquette module are reused.
3. Use B=max(BX,BY) and the maximum of the two anchor indices and both
   delta-moduli. This computes the outer Cauchy rate for B(X.seq n,Y.seq n).
   The existing reciprocal-index rate closure handles arbitrary supplied
   moduli; no monotonicity premise is introduced. It need not dominate the
   raw rate at the SAME tolerance: the proof uses a smaller sampled tolerance.
4. Each scalar term is the original ofQ'CauchySeq time limit. Its directed
   QMhat bound gives inner regularity epsilon.den. This is regularity of
   the reindexed CReal approximations, NOT a parameter-independent bound
   on raw finite-window convergence. The explicit outer and inner rates
   feed completeLimitFromRate. The returned representative also has a
   named QCauchy modulus
   epsilon |-> (HalfPow.half*(HalfPow.half*epsilon)).den.
5. Explicit moduli for close Cauchy representatives give a two-sided bound
   between their pairing sequences. Uniqueness of their constructed limits
   proves representative independence. Quotient.lift2 descends into RC;
   no representative is selected. Nonempty Close is eliminated only inside
   the propositional well-definedness proof, not to construct rate data.
6. Constant representatives recover the original intrinsic pairing.
   Symmetry, diagonal positivity and unit normalization pass through the
   same limits. Literal termwise physical advance gives completed
   B(T_r x,T_s y)=B(x,T_(r+s)y) and B(T_n x,T_n x)<=B(x,x).
   Thus B(x,T_(2n)x)=B(T_n x,T_n x)>=0. This is even-time positivity,
   not positivity of the one-step map.
7. A max-tail limit argument shows that the SAME outer rate bounds each
   late pairing term against its limit. If the completed diagonal vanishes,
   that rate constructs a Type-valued Close witness to the constant-zero
   sequence. Hence no additional null elements remain in the completed
   diagonal. This proof does not wait for completed bilinearity or use choice.
8. Fix the physical lag n and common chart
   H=max(radius x,radius(S^n y)). At boundary depth t, place the literal
   mirrored/advanced signed probe product in extent
   adjacentEvenExtent(width+t+H), starting at width+1 with t+(2*H+t)
   chain transitions. Every original finiteValue is exactly the diagonal
   window ratio, retaining the selected action and its partition. The
   original scalar stream inherits the existing window QCauchy modulus.
   Uniqueness identifies its returned CReal with the completed time
   correlator. Cauchy index, physical lag and finite boundary depth are
   separate parameters; the compact source polynomial stays fixed in t.

## Declaration evidence

All module paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `normBase`, `normCeiling` | `BF4ExactSlabFixedSpatialPairingBounds.lean:44`, `:49` | Computed anchor and eventual norm ceiling. |
| `diagonal_anchor_bound`, `diagonal_le_normCeiling` | `BF4ExactSlabFixedSpatialPairingBounds.lean:76`, `:103` | Actual reflected bounds, not new premises. |
| `pairing_small`, `pairing_difference_split`, `pairing_close` | `BF4ExactSlabFixedSpatialPairingContinuity.lean:55`, `:77`, `:95` | Actual CS and signed difference give explicit continuity. |
| `rawRate`, `pairSequence_raw_bound` | `BF4ExactSlabFixedSpatialPairingLimit.lean:50`, `:55` | Computed outer rate and its two-sided bound. |
| `pairRate`, `pairSequence_regular` | `BF4ExactSlabFixedSpatialPairingLimit.lean:79`, `:92` | Closed arbitrary rate and original scalar regularity. |
| `representativeInner`, `pairSequence_converges`, `representativeInnerCauchy` | `BF4ExactSlabFixedSpatialPairingLimit.lean:109`, `:114`, `:121` | Constructed limit and retained explicit modulus. |
| `closeRate`, `representativeInner_welldef` | `BF4ExactSlabFixedSpatialCompletedInner.lean:40`, `:71` | Explicit closeness and same-limit independence. |
| `completedInner`, `completedInner_embedSpan` | `BF4ExactSlabFixedSpatialCompletedInner.lean:89`, `:108` | Same-carrier RC pairing and original dense pin. |
| `completedInner_symm`, `completedInner_nonnegative`, `completedUnit_norm_one` | `BF4ExactSlabFixedSpatialCompletedInner.lean:122`, `:133`, `:138` | Symmetry, positive diagonal and normalized fixed unit. |
| `completedInner_time_sum`, `completedInner_time_balance` | `BF4ExactSlabFixedSpatialCompletedTimeForm.lean:58`, `:69` | Exact sum-of-times and symmetry identities. |
| `completedInner_time_contraction` | `BF4ExactSlabFixedSpatialCompletedTimeForm.lean:92` | Constant-one diagonal contraction on every completed element. |
| `completedInner_even_diagonal`, `completedInner_even_nonnegative`, `completedInner_even_le_identity` | `BF4ExactSlabFixedSpatialCompletedTimeForm.lean:101`, `:109`, `:114` | Even-time quadratic form between zero and identity. |
| `completedTime_correlator` | `BF4ExactSlabFixedSpatialCompletedTimeForm.lean:122` | Embedded time correlator is the same original intrinsic pairing. |
| `pairSequence_limit_close`, `closeZeroOfInnerZero` | `BF4ExactSlabFixedSpatialCompletedPosdef.lean:59`, `:75` | Existing rate constructs explicit closeness to zero. |
| `completedInner_posdef` | `BF4ExactSlabFixedSpatialCompletedPosdef.lean:99` | Zero completed diagonal iff embedded zero. |
| `chartRadius`, `sourcePolynomial`, `originalScalar` | `BF4ExactSlabFixedSpatialOriginalCorrelator.lean:61`, `:65`, `:90` | Fixed compact insertion and actual varying-placement finiteValue stream. |
| `originalScalar_pin`, `originalCauchy`, `originalCauchy_modulus` | `BF4ExactSlabFixedSpatialOriginalCorrelator.lean:102`, `:133`, `:149` | Original partition pin and inherited explicit Cauchy modulus. |
| `originalScalar_converges`, `originalScalar_limit`, `completedTime_originalCorrelator` | `BF4ExactSlabFixedSpatialOriginalCorrelator.lean:157`, `:173`, `:186` | Original finite expectations converge to exactly the completed physical correlator. |

## Scope and next causal frontier

All results keep rational 0<w<1, width and retained cutoff
K=headCutoff(w)+stage fixed. The selected original action, normalized
partition, reflected form, Cauchy carrier, time maps and unit remain the
same objects throughout. No old concrete plaquette completion is substituted.

The scalar ceiling depends on the representative's supplied modulus and
anchor. It is not one uniform bound over the completed carrier. The
epsilon.den inner regularity is not a raw thermodynamic/cutoff rate. The
time inequality has constant ONE, not q<1. No beta-uniform strict gap,
spacing calibration, Hamiltonian logarithm or mass estimate is asserted.

The original finite-correlator modulus is exactly
windowTimeModulus(hw0,hw1,width,polynomialCap(sourcePolynomial)). It depends
on nome, width and the actual source cap and is independent of late cutoff
stage in the displayed formula. Its physical lag enters through the named
source polynomial; no new lag-uniform claim is needed here. The original
observable is explicitly the product of placed mirrored/advanced spatial
probe spans, not an assertion about arbitrary coordinate polynomials.
No new reflection-image theorem is assumed by this pin.

The map named completedInner is now a positive-definite symmetric pairing
on the Cauchy quotient, but a full inner-product/Hilbert package still needs
completed vector operations and their laws, bilinearity, scalar extension
and metric completeness. The next bounded producer is actual addition and
rational scaling: prove d2(x+y,x'+y')<=2*d2(x,x')+2*d2(y,y') and the c^2
scaling identity, then instantiate BinaryQuadraticLipschitz and
ModulusContinuous at `lean/YMGap/Continuum/CRealSeminormCompletion.lean:397`
and `:340`. Their existing mapCauchy/completionMap constructions preserve
explicit moduli. Tolerance epsilon/(c*c+1) avoids division by a possibly
zero scalar. Descend algebraic laws through actual pointwise nullity, not
literal equality of signed-list presentations. Limit uniqueness then gives
completed bilinearity. These producers are still unimplemented here.

The fixed unit does not prove a nonconstant excitation or isolated vacuum.
Full gauge-observable completeness, a physical Hilbert/OS root, joint
cutoff/time passage, spatial/spacing control, a strict vacuum-complement
estimate with physical mass normalization, continuum QFT and all compact
simple groups remain open. No canonical field, literal hole, axiom or
analytic hypothesis changed.

## Focused verification

The seven modules below passed focused monitored checks with one worker and
a 20 GiB hard ceiling, each preceded by a fresh process/swap inspection.
All 61 public gates stay within {propext, Quot.sound}. Final logs contain
no error, warning, sorryAx or classical dependency. Local-notation dot syntax
and an omitted definitional-equality closure were repaired; no mathematical
hypotheses or resource limits were changed. No root/full-tree check or full
axiom audit was run.
Seven imports were added to the selective root; that is not a root-build claim.

| Module suffix | Gates | `/tmp/<full module name>.log` SHA-256 |
|---|---:|---|
| `PairingBounds` | 8 | `4a7714df548a0980ad98e8c9fda86f0ce5167e2aed9d920a347a11187f337c53` |
| `PairingContinuity` | 3 | `d3c1152e93f353e26d8c0a2cd0e32e87132505e513dcbb01d75b5d2cc2de224c` |
| `PairingLimit` | 13 | `9c75f069df99d10bca5f31f268f8f950b8da754bfee1e3bdb97940879cc01751` |
| `CompletedInner` | 12 | `a9b3bd1b54e8802affe89a90dd02f0dbaf869b36afc027120f297bf982a62cda` |
| `CompletedTimeForm` | 9 | `b05c5d61943606f8c729bcace65cb18247c77c6ad4aa7b3ca051a67ad969f484` |
| `CompletedPosdef` | 6 | `56a84dc04b45d5ba8314643c4a657650f746f78533a39579d92c730caee5b131` |
| `OriginalCorrelator` | 10 | `5cc809093f27526e65c9d2e035fdbb21b6678bda798bca0b88c7e169aeb9ac0c` |

Each suffix has prefix BF4ExactSlabFixedSpatial. Independent review checked
the computed ceilings and exact tolerance, correct unchanged slots,
arbitrary-modulus closure, original reindexed regularity, choice-free
descent, Type-valued zero-closeness witness, time balance, non-strict
even-time scope, fixed compact original insertion and unchanged partition.
Parallel agents wrote/reviewed disjoint pieces; only the
main agent compiled, serially. CI and capacity limits are unchanged. No
routine literature scan was performed.
