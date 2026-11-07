# Public theorem endpoints and application contracts

This file records mathematical endpoints rather than manuscript numbering.
All theorem names below have the prefix `ExactSolution`. Only their selected
source import closure is included by the `eth_response` profile.

| Selected module | Formal object |
| --- | --- |
| `Observation`, `Observability` | Finite task certificates, certificate minima including infinity, and observability as constancy on full-observation fibres. A decoder exists on realizable vectors; efficiency is not asserted. |
| `Transcript` | Actual deterministic policies and completed histories; replay gives `transcript_certificate` and `transcript_query_lower_bound`. |
| `Covering` | `cover_capacity` and `distinguishability_capacity_bound` derive certificate bounds from a finite witness set and an observation-capacity bound. |
| `SingletonCNF` | Actual width-bounded CNF syntax and semantics; singleton count and identity certificates have size `2^n`, whereas satisfiability has size one under the stated semantic comparison class. |
| `ReadAll` | `read_all_operational` reads every input bit, reconstructs the input, and then applies the task. Internal task computation is uncharged. |
| `Simulation` | `weighted_observation_simulation` transports certificate bounds through specified finite answer-vector decoders with explicit acquisition charges. |
| `Hermite` | `hermite_unique`, `hermite_nonunique`, and `hermite_value_at_zero_determined_iff` establish the ambient rational-polynomial information threshold, including a below-threshold counterexample. |
| `MeasurementRank/Basic` | Kernel containment bounds defect rank by measurement rank and row count. Diagonal and change-of-basis lemmas support the concrete application. |
| `SwapSpectrum` and its dependencies | Actual coordinate swaps, an explicit rational pair basis and tensor basis, exact multiplicities, polynomial action, and `swap_rank_eq_failure_mass`. |
| `MeasurementRank` | Actual rational linear measurements satisfying the fixing-kernel and row-budget contracts imply the degree floor. The dimension budget additionally implies the finite clipped-enumeration bound. |
| `NearExponential` | The existing explicit exponent eventually dominates `n^(1-eps)` for every `eps>0`; the actual-measurement wrapper retains all construction hypotheses. The clipped count is at most `3^n`. |
| `SelectedMeasurements/Rows` | Actual transpose-eigenvector measurements and normalized dual-coordinate measurements, positive scaling and equal kernels, exact rational basis entries, integrality and row height. |
| `SelectedMeasurements` | Constructed-map fixing, integer matrix, exact selected row count and tail normalization, interval interpolation and composed degree/finite/eventual application endpoints. Numerical copied-row accounting is separate from the unformalized global placement maps. |

## Concrete swap contract

`SwapSpectrum.History r Q` is `Fin Q → (Fin r × Fin r)`. Rational vectors are
functions on those histories, of dimension `r^(2*Q)`. `swapPi r Q s` swaps the
two labels at position `s`; `swapV0` is the product of those swaps and `swapW0`
is one half of the sum of `id-swapPi`. The actual operator is
`swapM0 r Q f = swapV0 r Q * Polynomial.aeval (swapW0 r Q) f`.

The application supplies

```text
C : (SwapSpectrum.History r Q → ℚ) →ₗ[ℚ] (Fin m → ℚ)
C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker
```

`MeasurementRank.kernel_defect_iff` identifies the second statement with
`∀ v, C v = 0 → swapM0 r Q f v = v`.

The rank identity and `MeasurementRank.swap_failure_mass_le_rows` together give

```text
r^(2*Q) * swapFailureMass f Q ((r-1)/(2*r)) ≤ m.
```

The numerical degree endpoint is
`MeasurementRank.swap_measurement_degree_floor`. Its premises are `r≥2`,
`Q>0`, `f.natDegree<R`, `tau≤1`, the fixing contract, and
`m≤r^(2*Q)*tau/(3*r)`. Its conclusion is `R≥1+5*sqrt(Q)/24`.

`MeasurementRank.swap_measurement_enumeration_floor` additionally assumes
`n≥65536` and `12*(r^(2*Q))²≤M≤3*n`. It concludes both `Q≤log₂(n)/4` and

```text
2^(n*log₂(log₂(n))/(4*sqrt(log₂(n))))
  ≤ enumerationCount n (substitutionOrder n R Q).
```

Here `substitutionOrder` is exactly `floor(3*n*R/Q)`, and `enumerationCount n q`
is the complete sum `∑ j=0..min(q,n), 2^j * choose n j`. The clipping and the
finite threshold are part of the checked statement. Matrix versions of the
measurement and enumeration conclusions are also included.

## Eventual exponent comparison

`enumeration_exponent_eventually_ge_power eps heps` assumes `eps>0` and proves
that the displayed explicit exponent eventually exceeds `n^(1-eps)`.
`swap_measurement_near_exponential_eventually` combines this with the actual
measurement theorem uniformly over all permitted parameters and maps.

`swap_measurement_near_exponential` gives the equivalent explicit-threshold
form `∃ N, ∀ n≥N, ...`. Its measurement, fixing, row-budget, and dimension-budget
premises remain present. `enumerationCount_le_three_pow n q` proves the
independent upper bound `enumerationCount n q≤3^n` for every natural `n,q`.

The artifact proves these mathematical implications. The external source's
full counting reduction, the satisfaction of its construction contracts, and
any broader complexity hypothesis have their separately stated scope.

## Constructed source-measurement application

The selected rows in Proposition 5.2 are the physical tensor eigenvectors whose
antisymmetric count is outside the retained window, transposed as rows. This
matches the proof of `lem:swaps-matrix` in the pinned OpenAI source. The
`measurement` map and `measurementMatrix` use those physical rows, not an
assumed coordinate oracle. `measurement_eq_scaled_dual` proves the nonzero
norm-squared scaling relating them to the normalized dual coordinates;
`measurement_ker_eq_dual` proves equality of kernels.

Principal endpoints, all under `ExactSolution.SelectedMeasurements`:

| Statement | Endpoint |
| --- | --- |
| Constructed kernel satisfies fixing | `measurement_fixing_kernel` |
| Matrix realizes the linear measurement map | `measurementMatrix_mulVecLin` |
| Entries are zero or either unit sign | `measurementMatrix_values` |
| Physical rows are an integer matrix's rational cast | `integerMeasurementMatrix_cast` |
| Integer row height is at most `r^(2*Q)` | `integerMeasurementMatrix_l1_le` |
| Exact selected row count is dimension times outside-window mass | `rowCount_eq_dimension_mul_tail` |
| Tail budget supplies row budget | `row_budget_of_tail` |
| Actual-map finite enumeration bound | `selected_measurement_enumeration_floor` |
| Uniform eventual bound with constructed map | `selected_measurement_near_exponential` |
| Parity interpolant values, degree and uniqueness | `parityInterpolant_agrees`, `parityInterpolant_natDegree_lt`, `eq_parityInterpolant` |
| Interval instance discharges polynomial and agreement inputs | `interval_measurement_enumeration_floor`, `interval_measurement_near_exponential` |
| Signed-window clipping and agreement transfer | `retainedSignedWindow`, `agreement_on_retainedSignedWindow` |
| Numerical total-row accounting | `placed_row_count_bound` |

The interval wrappers use an actual Lagrange interpolant on `Ico A (A+R)`, with
`R>0`. They retain the tail, row/dimension parameter budgets, and finite or
eventual size thresholds. The source's Newton/binomial expression is identified
mathematically by the same degree and interpolation values; its literal closed
formula is not separately formalized here.

In the bounded-occurrence clause branch the local condition is
`outsideWindowMass <= tau/(3*r)` and the dimension condition is
`12*D^2 <= M <= 3*n`. The numerical accounting theorem shows
`r*h*m <= 2*tau*n` from the local budget and `h*D <= 2*M`, with `tau>=0`.
It does not construct the source's repetition and group-restriction matrices,
or derive the local tail condition from a global total-row bound.
