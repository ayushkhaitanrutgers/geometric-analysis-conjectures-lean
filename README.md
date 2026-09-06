# Geometric Analysis Conjectures: Solutions with Lean Certifications

This repository contains solutions (proofs, disproofs by explicit counterexample,
and one exact reduction) to problems from *One Hundred Potentially Tractable
Conjectures in Geometric Analysis*
([`geometric_analysis_100_conjectures.tex`](geometric_analysis_100_conjectures.tex)),
together with **Lean 4 formalizations certifying the proofs** against
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Solved problems

| # | Result | Paper (LaTeX) | Lean certification |
|---|--------|---------------|--------------------|
| 1 | **Counterexample** — a width-plateau counterexample to an index-$p$ conjecture for mean-curvature flow (round-sphere $p$-widths) | [`round_sphere_pwidth_counterexample.tex`](round_sphere_pwidth_counterexample.tex) | [`Lean-code/RoundSpherePWidth.lean`](Lean-code/RoundSpherePWidth.lean) |
| 2 | **Counterexample** — a positively curved counterexample to a CMC index–area bound | [`cmc_index_area_counterexample.tex`](cmc_index_area_counterexample.tex) | [`Lean-code/CmcIndexArea.lean`](Lean-code/CmcIndexArea.lean) |
| 3 | **Counterexample** — an explicit counterexample to a conjectured dimension-free Huisken-energy bound | [`explicit_huisken_energy_counterexample.tex`](explicit_huisken_energy_counterexample.tex) | [`Lean-code/HuiskenEnergy.lean`](Lean-code/HuiskenEnergy.lean) |
| 4 | **Counterexample** — intermediate $Q$-curvature positivity fails in dimension thirty | [`explicit_intermediate_q_curvature_counterexample.tex`](explicit_intermediate_q_curvature_counterexample.tex) | [`Lean-code/IntermediateQCurvature.lean`](Lean-code/IntermediateQCurvature.lean) |
| 5 | **Counterexample** — infinite-order contact does not force containment for nonintegral stationary varifolds | [`nonintegral_varifold_counterexample.tex`](nonintegral_varifold_counterexample.tex) | [`Lean-code/NonintegralVarifold.lean`](Lean-code/NonintegralVarifold.lean) |
| 6 | **Counterexample** — the omitted parameter $a=0$ in an affine-maximal Bernstein statement | [`affine_maximal_omitted_parameter.tex`](affine_maximal_omitted_parameter.tex) | [`Lean-code/AffineMaximalOmittedParameter.lean`](Lean-code/AffineMaximalOmittedParameter.lean) |
| 7 | **Proof** — eventual finiteness of critical Steklov lengths on hypersurfaces of revolution | [`eventual_finite_steklov_lengths.tex`](eventual_finite_steklov_lengths.tex) | [`Lean-code/SteklovLengths.lean`](Lean-code/SteklovLengths.lean) |
| 8 | **Reduction** — an exact reduction of the index-four conjecture for the critical spherical catenoid in $\mathbb{H}^3$ | [`exact_reduction.tex`](exact_reduction.tex) | [`Lean-code/ExactReduction.lean`](Lean-code/ExactReduction.lean) |
| 9 | **Proof/Counterexample** — a nonconvex hyperbolic obstacle with positive exterior Robin threshold | [`hyperbolic_exterior_robin_threshold.tex`](hyperbolic_exterior_robin_threshold.tex) | [`Lean-code/HyperbolicRobinThreshold.lean`](Lean-code/HyperbolicRobinThreshold.lean) |
| 10 | **Proof** — generic integer-order umbilics of analytic $W$-congruences | [`integer_w_congruence_genericity.tex`](integer_w_congruence_genericity.tex) | [`Lean-code/IntegerWCongruenceGenericity.lean`](Lean-code/IntegerWCongruenceGenericity.lean) |
| 11 | **Proof** — umbilics of analytic $W$-congruences with $m \notin \mathbb{N}$ are of type $A_\infty$ | [`noninteger_w_congruence.tex`](noninteger_w_congruence.tex) | [`Lean-code/NonintegerWCongruence.lean`](Lean-code/NonintegerWCongruence.lean) |
| 12 | **Proof** — all-order compatibility of the resonant Taylor equation at an umbilic of a $W$-congruence | [`w_congruence_all_order.tex`](w_congruence_all_order.tex) | [`Lean-code/WCongruenceAllOrder.lean`](Lean-code/WCongruenceAllOrder.lean) |
| 13 | **Proof** — BV compactness and positivity of magnetic Cheeger constants | [`magnetic_cheeger_positivity.tex`](magnetic_cheeger_positivity.tex) | [`Lean-code/MagneticCheeger.lean`](Lean-code/MagneticCheeger.lean) |

Note: `M5_round_sphere_pwidth_counterexample.tex` is a duplicate of
`round_sphere_pwidth_counterexample.tex` (stated in both files) and is covered by
the same Lean certification.

## The Lean certifications

Each paper has a corresponding file in [`Lean-code/`](Lean-code/) (~13,000 lines
total) that certifies its proofs as far as current Mathlib permits:

- **Toolchain**: Lean 4 (`leanprover/lean4:v4.30.0-rc2`, pinned in
  [`lean-toolchain`](lean-toolchain)) with a matching Mathlib. Every file begins
  with `import Mathlib` and compiles with **zero errors and zero `sorry`s**.
- **No extra axioms**: the files contain no `axiom` declarations, no
  `native_decide`, and no unsafe escape hatches; proofs rest only on Lean's
  kernel and Mathlib.
- **What is fully proved**: every computation the papers actually perform —
  closed-form derivatives and integrals, curvature and eigenvalue computations,
  Taylor/power-series expansions with all displayed coefficients, resonance
  arithmetic, rational certificates and inequalities, index/nullity counts, and
  the final contradictions or conclusions. Two files
  (`NonintegralVarifold.lean`, `AffineMaximalOmittedParameter.lean`) prove
  their papers **outright, with no standing hypotheses at all**.
- **What enters as hypotheses**: deep machinery absent from current Mathlib
  (Almgren–Pitts min–max, varifold first variation in general, BV compactness
  on manifolds, Cauchy–Kowalevski, elliptic regularity, manifold spectral
  theory) is packaged as *explicitly documented* structure fields or named
  hypotheses. Every such field's docstring cites the LaTeX statement it
  transcribes, and each file's module header gives the complete map
  theorem-by-theorem: fully proved vs. proved-from-hypotheses vs. not
  formalizable today.
- **Faithfulness audit**: beyond compilation, every (paper, Lean file) pair was
  checked by an LLM back-translation judge — the Lean statements are rendered
  back into literal mathematical English by one model and compared against the
  paper by an independent judge, with structured defect reporting (wrong
  quantifier, changed conclusion, missing hypothesis, …). All 13 pairs are
  judged faithful; the full audit is in
  [`comparator_report.md`](comparator_report.md) /
  [`comparator_report.json`](comparator_report.json), and the driver is
  [`scripts/comparator_audit.py`](scripts/comparator_audit.py).

### Checking the Lean files

The files are checked against Mathlib at the pinned toolchain. Two ways to
reproduce:

1. **Any Mathlib checkout** at `v4.30.0-rc2`: place a file where the Mathlib
   environment is visible and run `lake env lean <file>` from the Mathlib
   project root — each file is self-contained after `import Mathlib`.
2. **A [kimina-lean-server](https://github.com/project-numina/kimina-lean-server)**
   over the same Mathlib: [`scripts/check.py`](scripts/check.py) submits files
   to the server's warm REPL (`python3 scripts/check.py Lean-code/<file>.lean`),
   turning the ~3-minute cold `import Mathlib` into ~seconds per check.

## Repository layout

```
geometric_analysis_100_conjectures.tex   the source problem list
*.tex                                    the solution papers (LaTeX)
Lean-code/*.lean                         one Lean certification per paper
lean-toolchain                           pinned Lean version
scripts/check.py                         fast proof checker (kimina server client)
scripts/comparator_audit.py              tex ↔ Lean faithfulness audit driver
comparator_report.{md,json}              faithfulness audit results
```
