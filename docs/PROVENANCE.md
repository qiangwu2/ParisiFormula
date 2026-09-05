# Dependencies and source provenance

## Active build dependencies

`lakefile.lean` declares two local libraries, `ParisiFormula` and `Targets`. Their
upstream dependencies are locked in `lake-manifest.json`:

| Dependency | Source | Locked revision |
|---|---|---|
| `mathlib` | `leanprover-community/mathlib4`, tag `v4.32.1` | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `QuantitativeStrictAT` | `njimaMath/research_public`, subdirectory `RSAT` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` |

`Lemmas.*` imports resolve to the RSAT dependency under
`.lake/packages/QuantitativeStrictAT/RSAT/`, not the historical root-level `Lemmas/`
copies. Neither `Lemmas/` nor `port/` is a local build target. The `main` selector in
the RSAT dependency declaration does not replace the pinned revision when reproducing
the checked-in manifest; `lake update` would deliberately refresh dependencies.

## Reuse inventory for the Talagrand lower bound

Search the locked dependency before developing new analytic machinery. The
following matches were checked in the active RSAT source, not the historical
copies. `Targets/GuerraAudit.lean` checks the completed local bridges and their
transitive dependencies for the standard Lean axioms only.

| Existing result | Local use or remaining adaptation |
|---|---|
| `AT.gtTerminal`, `AT.gtTerminal_zero`, `AT.deriv_gtTerminal_zero` | `coupledSite_eq_gtTerminal` bridges the paper's hyperbolic expression to RSAT's exponential expression; local normalization and derivative proofs now reuse RSAT. |
| `AT.sum_bool_pair_exp_eq_four_mul_exp_gtTerminal`, `AT.sum_pair_exp_sum_eq_prod_sum_exp` | Reused by the local one-site and N-site partition identities in `CoupledLambda.lean`. |
| `GTFrame.finiteStep`, `finiteStepD`, `step0_good`, `stepM_good`, `goodFam_fLbase` | `CoupledFiniteStep.lean` and `CoupledEndpoint.lean` iterate the existing transforms and regularity results. `TalagrandSection5.lean` specializes them to the actual inserted-level scalar `V` and its lambda derivative. No new dominated differentiation proof. |
| `AT.gtVectorStep`, `gtScalarStep`, `gtVectorStep_sum` | Directly reused for the N-site recursion and tensorization; integrability and positivity are discharged using `GoodFam`. Proved bridges identify the old shared step and the composition giving its independent step. |
| `AT.gtStateLogPartition`, `contDiff_gtStateLogPartition`, `fderiv_gtStateLogPartition_apply`, `fderiv_gtStateGibbs_apply` (`Bound/FiniteState.lean`) | Now used in `ConstrainedFiniteState.lean` on `AT.ConstrainedPair N u`, with an exact positive-Hamiltonian bridge and actual first/mixed second terminal derivatives. Full nested-cascade differentiation remains open. |
| `AT.gtCoefficientCLM` (`Bound/Comparison.lean`) | Defines the pair-disorder map `U ↦ (U(σ)+U(τ))` as an existing continuous linear map; no new finite-dimensional map construction needed. |
| `AT.pairOverlapMatrix_self`, `spin_sum_eq_mul_overlap`, `gtCovariance_remainder` (`Bound/Basic.lean`) | Reused in `CoupledCovariance.lean` for the constrained diagonal, independent/signed-shared field contractions, and entrywise square completion. The SK spectral contraction reuses the already proved local `sk_covariance_spectral_sum`. |
| `Finset.sum_range_by_parts`, `sum_range_sub` (Mathlib) | Reused in `SecondInterpolationAlgebra.lean` for the mass-weighted telescoping identity. The inserted correction is proved equal to the existing `2 * parisiCorrection` plus the split-level term in (5.9). |
| `AT.hasDerivAt_gtOrdinaryPressure_ibp`, `gtOrdinaryPressure_one_le_zero_add_shiftedDiagonalGap` (`Bound/Comparison.lean`) | Generic finite-state covariance interpolation, but for the ordinary expected log partition, not an arbitrary nested positive-mass cascade. Reuse where its pressure matches; extend only the missing cascade layer. |
| `hasDerivAt_mgf`, `integrable_pow_mul_exp_of_mem_interior_integrableExpSet` (Mathlib `MGFAnalytic`) | `ParisiMassDerivative.lean` proves the actual scalar mass derivative. Existing Gaussian linear-growth integrability makes the exponential-integrability domain all of `ℝ`; no new dominated-differentiation proof. |
| `Real.self_sub_one_le_mul_log` (Mathlib) | Nonnegativity of the genuine normalized tilt's entropy, hence scalar mass monotonicity. Integrability and density normalization are checked. |
| Local `Parisi.T_add_of_hasLinearGrowth`, Mathlib `integral_conv`, `gaussianReal_conv_gaussianReal` | `ParisiStepSemigroup.lean` adapts the existing nonzero-mass semigroup and proves the actual expectation branch at mass zero. Both variance endpoints are allowed. |
| Local `independentStepPi_add`, `sharedStepPi_diag`, `parisiStepPi_sum`, `coupledFieldCascade_eq_sum` | `TalagrandSection5Zero.lean` derives the actual zero-lambda factorization (5.18); the semigroup then restores the original recursion for (4.36), (5.19). |
| Local `hasDerivAt_parisiStepPi_param`, `hasDerivAt_tiltAvg_param_pi` | `CoupledCascadeDeriv.lean` adapts the first derivative through independent/shared levels and the tilted covariance rules, retaining the actual mass coefficient. The finite-state terminal supplies concrete derivative inputs. |
| Local `talagrand_proposition_2_5`, replica-weighted-tail conversion, and endpoint-safe convergence; Mathlib exponential asymptotics | `TalagrandOverlapTail.lean` sums over at most `N+1` attainable Ising overlaps and proves the full conditional concentration/convergence deduction. The uniform quadratic bound and positive first mass remain hypotheses. |

The final `AT.twoReplica_GT_bound` has RS smart-path hypotheses (one overlap
parameter, positive `β` and `h`, and an interior RS overlap). It cannot replace
the finite-RSB Theorem 2.4 as stated. This mismatch does **not** exclude its
generic supporting modules above. The generic half-step calculus may likewise
help extend the ordinary-pressure comparison, but has not yet been adapted.

No dependency revision was changed and no upstream source was copied or edited.
The general finite recursion presently proves λ-differentiation at fixed masses;
it does not assert the mass-variation estimates or identify the derivative with
Talagrand's `U′` in Lemma 5.8.

### Section 5 endpoint specialization

The coefficients were checked against the [original Annals paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v163-n1-p04.pdf),
pp. 252–253, equations (5.5)–(5.17). The paper's `k` is the local `k+1`.
For the left interval `q(r−1) ≤ u ≤ q(r)`, the inserted level is independent,
has mass `m`, and has frozen variance zero; outer shared masses are `m_p/2`.
The second interpolation is defined directly on standard Gaussian coordinates
using the combined variance of `Z + √(1−w)y`, with shared fields below `r` and
independent fields at/above `r`. Thus it does not require introducing and then
integrating out redundant Gaussian copies. The exact endpoint identities are
proved against the existing `constrainedPhi` and the explicit scalar recursion,
not assumed from a distributional identification.

`CoupledEndpoint.lean` reuses the existing interacting-step growth, order,
Fubini, and additive-constant results, together with RSAT's site tensorization.
`CoupledReindex.lean` supplies only algebraic changes of coordinates and deletion
of a zero-variance step. `TalagrandSecondInterpolation.lean` proves (5.8) and
(5.17) for this canonical construction. All are covered by axiom guards.
Theorem 3.1's nested-cascade derivative estimate is still missing; the ordinary
RSAT covariance comparison cannot be applied to this pressure without that extension.
The right-interval, negative-overlap, and general out-of-neighbor-interval
constructions remain separate work, as do the Section 4 optimality estimates.

### Covariance calculation and the remaining analytic gap

The calculation was checked against the same paper, pp. 239–241. The terminal
derivatives in `ConstrainedFiniteState.lean` are derivatives of the actual
`constrainedPairFieldBase`, not a separately postulated Gibbs family.
`constrainedPairSecond_SK_trace` contracts this Hessian with the actual abstract
SK spectral covariance. In contrast, `pairCovarianceExpression_eq` and `_le`
are deliberately statements about explicit normalized finite replica weights:
their expression has not been identified with `η′`. This is the remaining
nested differentiation/IBP obligation, not an assumption or relocated placeholder.

The local `hasDerivAt_parisiStepPi_param` and `hasDerivAt_tiltAvg_param_pi`
are now reused in `CoupledCascadeDeriv.lean`: first disorder derivatives
propagate through the entire actual paired cascade with fixed variances,
and tilted-observable derivatives retain the mass-weighted covariance term.
This is not yet the varying-variance derivative of the second interpolation;
full nested Hessian propagation and the Stein/replica identification remain open.
The RSAT half-step modules were inspected: they supply a single fixed half-mass
transform, not the arbitrary finite sequence needed here. Their final comparison
does not close the nested-cascade gap. Do not repeat the finite-state or
square-completion proofs already connected by this step.

### Scalar variation, baseline, and finite-overlap assembly

`ParisiMassDerivative.lean` differentiates one mass while its input function
is fixed, including every actual `parisiF` input. It does not assert the nested
Section 4 variation or stationarity identities. The derivative theorem assumes
nonzero mass; entropy integrability includes mass zero, and the separate scalar
semigroup covers zero mass without identifying it with the incorrect totalized
operator `Parisi.T 0`.

The zero-lambda formulas were independently checked against pp. 246 and 253
of the Annals paper: local forward index `p=k+2-j`, total depth `k+3`, and
split `k+3-r` give independent inserted/inner levels and shared outer levels.
`section4T` is the actual scalar nested integral, not half of `V` by definition.
Its Lean argument order is mass then variance, while the paper writes `T(v,m)`.
The outer mass-zero expectation and all split-variance endpoints are retained.

The Proposition 2.3 assembly follows p. 232. The bound is relative to `2ψ`,
not `2φ`: the threshold `2K(ψ−φ)+η` supplies the `η/K` deficit needed by
Proposition 2.5. Counting overlap values gives the sharper Ising factor `N+1`
(the paper uses the sufficient `2N+1`); no exponential spin-pair factor is lost.
The resulting fixed-scheme convergence is conditional on the uniform quadratic
estimate and `s.m 1 > 0`, not a proof of the remaining Theorem 2.4 or (2.19).

## Historical copies and local ports

All vendored files are Apache-2.0.  Original headers are retained unchanged.

| File in this repo | Origin | Path in origin | Commit | Edits |
|---|---|---|---|---|
| `Lemmas/SpinGlass/Calculus.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Calculus.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Defs.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Defs.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/gaussian_concentration.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/gaussian_concentration.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/GuerraBound.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/GuerraBound.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/Replicas.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/Replicas.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `Lemmas/SpinGlass/SKModel.lean` | njimaMath/research_public | `RSAT/Lemmas/SpinGlass/SKModel.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | none |
| `ParisiFormula/GuerraToninelli.lean` | njimaMath/research_public | `perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | 2 import lines + provenance header; proof repairs for Lean v4.32.1 (see below) |
| `ParisiFormula/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | provenance header and `Mathlib.MeasureTheory.Integral.Prod` import; compiled local port |
| `port/GuerraInterpolation.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraInterpolation.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraIBP.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraIBP.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraTrace.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraTrace.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/GuerraPipeline.lean` | or4nge19/SpinGlass | `SpinGlass/GuerraPipeline.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `port/ParisiOperator.lean` | or4nge19/SpinGlass | `SpinGlass/ParisiOperator.lean` | `d1342fdf0179e3e62c76a49d4eaad84e04c64fd6` | none (Lean 4.28; not built) |
| `lean-toolchain`, `lake-manifest.json`, `LICENSE` | njimaMath/research_public | `RSAT/` | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | initial source; manifest subsequently regenerated for this project's dependencies (see above) |

The RSAT core files (`Lemmas/SpinGlass/`) are themselves derived from or4nge19/SpinGlass;
RSAT's own NOTICE says so and is reproduced in our NOTICE.

Toolchains at the time of vendoring: RSAT and perceptronFixed used Lean v4.32.1 / v4.32.0
with matching Mathlib; or4nge19/SpinGlass used Lean v4.28.0-rc1 (hence the `port/` folder).

`ParisiFormula/ParisiOperatorGrowth.lean` is a local extension of the ported semigroup
law to linear-growth functions. The cascade files in `Targets/` and the local Stein
lemmas support the completed SK Theorem 2.1; they are not pending upstream ports.

## Post-vendoring repairs to `ParisiFormula/GuerraToninelli.lean`

The upstream file was verified against a slightly different Mathlib. These compatibility
repairs preserve the theorem statements:

* `cfgEquiv.left_inv` and `cfgJoin_cfgLeft_cfgRight` — `Fin.addCases_castAdd_natAdd` is now
  stated pointwise, and `simpa` cannot close the goal because the `simp` equation lemmas for
  `cfgLeft`/`cfgRight` are in applied form; `exact` (default transparency) does.
* `integrable_log_skZ`, the `hEnergy` continuity step — `simpa` normalised the goal into
  `Pi.add` form, which no longer matches `Continuous.add`; replaced by `simp only [skEnergy]`
  followed by `exact`.

The covariance comparison lemmas `cov_deriv_diag` and `cov_deriv_offdiag_nonpos` were
also made public for reuse.
