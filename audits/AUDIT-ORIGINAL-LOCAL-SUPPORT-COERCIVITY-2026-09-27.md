# Original conditional Dirichlet coercivity with support-only cost

Historical checkpoint: `bb6bbbd`. The subsequent
[completed local auxiliary construction](AUDIT-LOCAL-CHEBYSHEV-PRODUCER-2026-09-27.md)
supplies literal-local representatives for the actual Chebyshev orbit and
passes the estimate to its original covariance consumer. Its degree-dependent
cost does not prove asymptotic decay or a scaling-family bound.

## Checked result

For 0<w<1, every finite extent, K>=headCutoff(w), and every original-law
centered supported polynomial p literally local on a link list S of length
at most s, the proof constructs

    delta(w,s) = headFloor(w)^(6s) / prefixCap(w)^(6s) > 0
    delta(w,s) ||embed(p)||_original^2
      <= sum_i ||(I-P_i)embed(p)||_original^2.

The P_i are the actual completed conditional projections for the ORIGINAL
finite full action. No coercivity or successful finite-test premise is
assumed. The coefficient depends on nome and support-size budget, not extent,
late cutoff, location, degree or coefficients. The input is an embedded
literal-local polynomial, not an arbitrary completed or operationally
localized vector. This is a conditional-link dynamics bound, not an OS-time
transfer or physical Hamiltonian gap.

## Causal proof and exact source map

Write H for product Haar integration, B for the original product of faces
detached from S, b=H[B], m=headFloor(w)^(6s), and M=prefixCap(w)^(6s).
Let f_i=p-H_i p be the coordinate Haar fluctuation.

1. `weighted_fluctuation_le_difference`,
   `lean/YMGap/Continuum/SU2QuaternionWeightedHaarProjectionMinimum.lean:61`,
   proves H[B f_i^2] <= H[B(p-q)^2] when B and q omit coordinate i and B has
   its nonnegative certificate. This is weighted orthogonality and a
   nonnegative square, not an interacting tensorization assumption.
2. `fluctuation_linkLocal`, `fluctuation_zero_outside`,
   `background_independent_on_support`, and `probeMap_independent_selected`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportFluctuation.lean:58`, `:70`,
   `:91`, and `:107`, prove the required locality and independence. For
   i outside S, f_i is coefficientwise zero. For i inside S, B and every
   inverse probe omit i. The probe need not be local on S.
3. `support_collar_bounds`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportVariance.lean:177`,
   bounds the collar factors by m and M using its at-most-6s face count.
   `probe_residual_local_floor`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportResidualFloor.lean:78`,
   combines this with weighted minimality and exact H[B f_i^2]=b H[f_i^2].
   It proves m b H[f_i^2] <= ||p-probe(r)||_original^2 for EVERY exterior
   probe r. `conditional_residual_local_floor` (`:130`) passes the inequality
   through the actual inverse Cauchy row to ||(I-P_i)embed(p)||^2. The SAME b
   is retained for every link; no link-dependent exterior mass is summed.
4. `centered_norm_le_local_haar_variance` and
   `centered_norm_le_local_free_energy`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportHaarVariance.lean:77` and
   `:146`, subtract the explicit Haar mean, use ORIGINAL mean-zero
   orthogonality, compare the same touching factors from above, and apply
   Haar Efron--Stein. They give ||p||_original^2 <= M b sum_i H[f_i^2].
   Original and Haar centering are not identified.
5. `free_energy_schedule`,
   `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeCoercivity.lean:106`,
   is now public with its unchanged proof: the physical schedule counts
   every coordinate fluctuation exactly once. `free_energy_le_local_dirichlet`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportCoercivity.lean:87`, sums
   the residual estimates to m b E_free <= E_original.
6. `dense_local_coercivity_mul`
   (`lean/YMGap/Continuum/BF4ExactSlabLocalSupportCoercivity.lean:109`)
   combines m||p||^2 <= m M b E_free <= M E_original. There is no division
   by b and no lower floor for the whole volume. `dense_local_coercivity`
   (`lean/YMGap/Continuum/BF4ExactSlabLocalSupportCoercivity.lean:136`)
   divides only by the proved positive M and returns the displayed
   bound. `supportRatio` and `supportRatio_positive`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportVariance.lean:140` and
   `:144`, define the coefficient and prove strict positivity.

## Remaining frontier

- The local residual estimate requested after the static variance comparison
  is now proved for embedded literal-local inputs. This supersedes that
  missing-producer statement only in this scope.
- `EightLayerCone.Localized` for a completed auxiliary does not supply a
  literal-local polynomial/Cauchy representative here. That same-vector
  realization and the corresponding closed-limit estimate remain next.
- The coefficient can deteriorate with s and w. No uniformity in growing
  cones, changing coupling, beta or lattice spacing is asserted. A local
  estimate does not establish the scaling-family signed-cost target A03.
- No thermodynamic construction, physical-time identification, OS/QFT
  reconstruction, nontrivial continuum survival, positive physical mass,
  every-compact-simple-group extension or Clay closure is supplied.
  Canonical frontier fields and displayed chart markers are unchanged.

## Verification boundary

Seven focused checks passed through `scripts/safe_lean_build.py`, serialized
with one worker and a 20 GiB cap: WeightedHaarProjectionMinimum (1 printed
gate), LocalSupportFluctuation (6), LocalSupportVariance (8),
LocalSupportResidualFloor (2), LocalSupportHaarVariance (2),
FiniteVolumeCoercivity (7), and LocalSupportCoercivity (3).
All 29 printed gates use only {propext, Quot.sound}. Draft header, namespace
and rewrite elaboration errors were corrected before the final checks.
No new sorry, axiom, classical input, erased witness or frontier field.

Sol and Luna produced bounded independent proof components; Sol also
reviewed the common-background summation and final theorem's scope. No
parallel compiler was used. Every check finished in its initial call;
there was no live job requiring manual polling. The five-minute manual-poll
cadence and continuous automatic resource telemetry remain in force.
Root imports are registered but no root/full-tree build, audit/guard,
progress-metric script, routine literature scan or CI run was performed.
