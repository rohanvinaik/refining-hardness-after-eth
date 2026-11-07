# Public ETH-response proof slice

This project contains the formal results selected for the standalone ETH-response
paper. The entry point is `ETHResponse.lean`; `ETHResponse/Audit.lean` checks the
loaded declarations in the mathematical namespaces, including private helpers,
and their transitive axiom dependencies.
The named mathematical statements and their application hypotheses are recorded
in `CORRESPONDENCE.md`. No broad computational hypothesis is asserted as a proved
theorem by this artifact.

## Build

Lean and Mathlib are pinned to v4.28.0. Exact dependency revisions appear in
`lake-manifest.json`. From this proof project's directory:

```sh
lake exe cache get
lake build ETHResponse ETHResponse.Audit
```

The exported project's default `lake build` checks those same two targets.
Its configuration does not build the larger historical capstone. Dependencies
may be built from their pinned sources instead of using Mathlib's cache.

Only the selected local import closure is distributed. The direct roots are
`Observation`, `Observability`, `Transcript`, `Covering`, `SingletonCNF`,
`ReadAll`, `Simulation`, `Hermite`, `MeasurementRank`, `NearExponential`, and
`SelectedMeasurements`,
under `ExactSolution/`. Their genuine transitive dependencies are also present.
For example, `ReadAll` uses the operational policy machinery through `Discovery`,
and `Simulation` uses weighted union arguments through `Composition` and
`WeightedObservation`. Including those dependencies makes the export buildable;
it does not enlarge the paper's stated conclusions.

The full `ExactSolution.lean` capstone, its old audit, and the `Knowability` and
`Semantic` applications are excluded. The public audit rejects importing them.
Build caches, dependency directories, local links, and research downloads are
not part of the source export.

## Audit and receipts

The audit permits only propositional extensionality (`propext`), classical
choice (`Classical.choice`), and quotient soundness (`Quot.sound`). Named checks
also record axiom traces for the principal endpoints. Builds use warnings as
errors. Kernel checking establishes the formal conclusions under their stated
hypotheses; it does not verify that an external algorithm satisfies them.

The exporter computes a fresh declaration count for this selected environment.
No count from the larger development is a verification claim about this slice.

From the editable parent project, the public export command is:

```sh
python3 proofs/export.py --profile eth_response --verify --output-dir submission/lean_proofs
```

It builds the workspace targets and then a temporary project with all selected
project modules rebuilt. Both environments receive independent axiom probes.
Only pinned dependency caches are reused. `SOURCE_MANIFEST.json` records the
profile, import graph, source origins, byte counts, and hashes. `BUILD_STATUS.json`,
`AXIOM_REPORT.json`, and the sanitized `BUILD.log` identify the exact verified
snapshot. A source-only export makes no build claim. `--check` verifies an
existing snapshot and refreshes its ZIP without rebuilding it.

The exported README and correspondence file originate in `proofs/public/` in the
editable project. The export uses an independent Lake configuration with public
default targets. The manifest identifies that generated configuration; the build
receipt records and checks the original workspace configuration hash. A combined editable source bundle
retains the public documentation at both its workspace and standalone locations.

## Mathematical scope

The certificate results concern declared deterministic observations and tasks.
The singleton CNF example uses point observations; it is not a running-time
lower bound for explicitly supplied formulas. Reading all input bits gives the
acquisition ceiling while leaving internal computation uncharged.

The swap results concern the full history product, the actual coordinate swaps,
and a univariate polynomial fixing operator. Applications supply a rational
measurement map satisfying its fixing-kernel condition, its row budget, and
the stated dimension budget. The spectrum and rank identities are proved.
The resulting lower bounds apply to the defined clipped substitution sum.
They do not establish a lower bound for every algorithm computing the count.

The eventual theorem gives, for every positive real `eps`, a common threshold
beyond which every permitted parameter and measurement choice has substitution
count at least `2^(n^(1-eps))`. A separate theorem bounds that count by `3^n`.
These are statements about the declared enumeration family.

`SelectedMeasurements` constructs the actual local transpose-eigenvector rows
selected by the source interpolation procedure. It proves their relation to dual
coordinates, fixing kernel, exact row count, integer entries, and row-height
bound. Its application wrappers take a window and its tail budget; the kernel
condition is proved. A constructed parity interpolant has verified values,
degree and uniqueness, and interval wrappers also discharge those premises.
The numerical copied-row budget is checked. The global placement matrices,
formula reduction and full counting routine retain their separate source-level
analysis. The selected map is the local auxiliary map, not a per-group placed map.
