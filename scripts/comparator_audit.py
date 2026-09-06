#!/usr/bin/env python3
"""Faithfulness comparator over the repo's formalizations.

For each (paper.tex, Conjectures/X.lean) pair, runs the L2 back-translation
judge from ~/faithful-autoformalization in claude-cli subscription mode
(no API key, no downloads):
  1. back-translate the Lean file into literal English,
  2. an independent judge compares it against the tex and emits structured
     defects (wrong_quantifier, changed_conclusion, missing_hypothesis, ...).

Usage:
    python3 scripts/comparator_audit.py            # all pairs
    python3 scripts/comparator_audit.py CmcIndexArea   # one pair
Writes comparator_report.md + comparator_report.json in the repo root.
"""

import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path.home() / "faithful-autoformalization"))
import backtranslation_judge as btj  # noqa: E402

REPO = pathlib.Path(__file__).resolve().parent.parent
MODEL = "claude-cli:sonnet"

PAIRS = {
    "RoundSpherePWidth": "round_sphere_pwidth_counterexample.tex",
    "CmcIndexArea": "cmc_index_area_counterexample.tex",
    "HuiskenEnergy": "explicit_huisken_energy_counterexample.tex",
    "IntermediateQCurvature": "explicit_intermediate_q_curvature_counterexample.tex",
    "NonintegralVarifold": "nonintegral_varifold_counterexample.tex",
    "AffineMaximalOmittedParameter": "affine_maximal_omitted_parameter.tex",
    "SteklovLengths": "eventual_finite_steklov_lengths.tex",
    "ExactReduction": "exact_reduction.tex",
    "HyperbolicRobinThreshold": "hyperbolic_exterior_robin_threshold.tex",
    "IntegerWCongruenceGenericity": "integer_w_congruence_genericity.tex",
    "MagneticCheeger": "magnetic_cheeger_positivity.tex",
    "NonintegerWCongruence": "noninteger_w_congruence.tex",
    "WCongruenceAllOrder": "w_congruence_all_order.tex",
}

PROBLEM_PREFACE = (
    "The 'problem' below is a full LaTeX research paper. The candidate is a "
    "Lean 4 file intended to certify the paper's results as far as Mathlib "
    "permits: its headline theorems should faithfully capture the paper's "
    "main theorems, and where deep machinery is unavailable the file may "
    "package geometric inputs as explicitly documented hypotheses/structures "
    "(this is declared in the file and is NOT a defect by itself). Judge "
    "whether the Lean statements match the paper's claims: quantifiers, "
    "domains, constants, directions of inequalities, and conclusions; and "
    "whether any hypothesis package smuggles in the conclusion or is at risk "
    "of vacuity.\n\n----- PAPER -----\n"
)


def main() -> int:
    only = set(sys.argv[1:])
    results = {}
    for name, tex in PAIRS.items():
        if only and name not in only:
            continue
        lean_src = (REPO / "Conjectures" / f"{name}.lean").read_text()
        tex_src = (REPO / tex).read_text()
        print(f"[{name}] judging ({len(lean_src)}b lean vs {len(tex_src)}b tex)...",
              flush=True)
        v = btj.run_l2(
            None,
            PROBLEM_PREFACE + tex_src,
            lean_src,
            informalize_model=MODEL,
            judge_model=MODEL,
        )
        results[name] = {
            "faithful": v.faithful,
            "confidence": v.confidence,
            "parse_ok": v.parse_ok,
            "defects": [d.__dict__ for d in v.defects],
            "back_translation": v.back_translation,
        }
        flag = "FAITHFUL" if v.faithful else "DEFECTS"
        print(f"[{name}] -> {flag} (confidence={v.confidence}, "
              f"{len(v.defects)} defect(s))", flush=True)

    (REPO / "comparator_report.json").write_text(json.dumps(results, indent=1))
    lines = ["# Comparator (L2 back-translation judge) report\n"]
    for name, r in results.items():
        lines.append(f"## {name}: {'FAITHFUL' if r['faithful'] else 'DEFECTS FOUND'}"
                     f" (confidence: {r['confidence']})\n")
        for d in r["defects"]:
            lines.append(f"- **{d.get('kind', d.get('type', '?'))}**: "
                         f"{d.get('detail', d.get('description', ''))}")
        lines.append("")
    (REPO / "comparator_report.md").write_text("\n".join(lines))
    print("Wrote comparator_report.md / .json")
    bad = [n for n, r in results.items() if not r["faithful"]]
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
