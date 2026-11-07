# Refining Hardness after ETH

**Task-Relevant Distinctions and the Cost of Exact Counting**

Rohan Vinaik, November 2026.

DOI: [10.5281/zenodo.24040661](https://doi.org/10.5281/zenodo.24040661)

This repository holds a preprint, a four-page explanatory note, and the Lean 4
development that checks their stated results.

| Path | Contents |
| --- | --- |
| `paper/` | *Refining Hardness after ETH* (17 pages): PDF, standalone LaTeX and bibliography. |
| `note/` | *What Remains Hard after ETH?* (4 pages): the same set for the short note. |
| `lean_proofs/` | The Lean 4 project. `ETHResponse.lean` is the entry point; `ETHResponse/Audit.lean` is the axiom audit; `CORRESPONDENCE.md` maps the theorem endpoints to the manuscript. |

## What the paper proves

Two preprints, by OpenAI and by Claude, report deterministic algorithms that
count the satisfying assignments of fixed-width CNF formulas in time
$2^{O(n \log\log n / \sqrt{\log n})}$ up to polynomial factors. If their analyses
hold, the Exponential Time Hypothesis is false. The exponent still exceeds
$n^{1-\varepsilon}$ for every fixed $\varepsilon > 0$, so the successor question
is whether exact counting can gain a fixed power in its exponent. The public
form of that question is #SH, which the MIT Hardness Group has shown equivalent
to Weak #ETH (arXiv:2611.02650).

The paper gives a fully formalized finite analysis of the coordinate-swap
construction behind the OpenAI interpolation algorithm:

- The coordinate swaps have an exact spectrum, so the fixing condition imposes a
  rank requirement on every rational measurement map.
- Agreement with parity turns that requirement into a degree floor.
- Under the stated row and dimension budgets, the degree floor forces the
  complete clipped substitution enumeration to have size at least
  $2^{n \log_2\log_2 n / (4\sqrt{\log_2 n})}$ for $n \ge 2^{16}$, and
  eventually at least $2^{n^{1-\varepsilon}}$ for every fixed
  $\varepsilon > 0$.
- The measurement rows the source algorithm actually selects are constructed,
  their fixing-kernel property and exact row count are proved, and the bound is
  applied to them.

The result bounds the enumeration as the construction completes it. It is not a
lower bound for every algorithm that computes the count, and the unrestricted
counting hypothesis stays open. The upper bounds of the two source papers are
taken as their authors state them; this formalization has not re-verified them.

## Checking the Lean development

Lean and Mathlib are pinned to v4.28.0; `lake-manifest.json` records every
dependency revision. From `lean_proofs/`:

```sh
lake exe cache get
lake build
```

The default targets are `ETHResponse` and `ETHResponse.Audit`. The build treats
warnings as errors. The audit permits only `propext`, `Classical.choice` and
`Quot.sound`, and fails the build if any declaration in the mathematical
namespaces depends on `sorryAx` or on any other axiom. `AXIOM_REPORT.json`,
`BUILD_STATUS.json` and `BUILD.log` record the verified snapshot:

| Record | Value |
| --- | --- |
| Lean toolchain | leanprover/lean4:v4.28.0 |
| Mathlib revision | 8f9d9cff6bd728b17a24e163c9402775d9e6a365 |
| Project modules rebuilt from source | 28 |
| Declarations audited | 709 |
| Axioms used | propext, Classical.choice, Quot.sound |
| Build date | 2026-11-07 |

A clean build with the Mathlib cache takes a few minutes on a laptop.

## Rebuilding the documents

Each manuscript compiles on its own with pdfLaTeX, XeLaTeX or Tectonic; the
`.bbl` files are included, so no bibliography processor is required.

## Citing

See `CITATION.cff`.

```
Rohan Vinaik. Refining Hardness after ETH: Task-Relevant Distinctions and the
Cost of Exact Counting. Preprint, November 2026. https://doi.org/10.5281/zenodo.24040661
```

## Sources discussed

- OpenAI. *The Exponential Time Hypothesis Is False.* Preprint, October 2026.
  Source snapshot 42907c9e999cc00d6abe7a50bfc1023250edd1b9 in github.com/openai/math.
- Claude (Anthropic). *A 2^{o(n)} Time Algorithm for 3-SAT.* hexagon:2610.00577v1, October 2026.
- MIT Hardness Group, J. Brunner, E. D. Demaine, F. Frei, T. Gomez, M. Hecher,
  J. Li, J. Lynch. *ETH is Dead, Long Live SH.* arXiv:2611.02650, November 2026.

## License

The manuscripts (`paper/`, `note/`) are released under CC BY 4.0; see
`LICENSE-PAPER.md`. The Lean development (`lean_proofs/`) is released under
the MIT License; see `LICENSE`.
