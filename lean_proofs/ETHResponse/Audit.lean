import ETHResponse

/-!
# Axiom audit for the selected public proof development

Only declarations loaded by the public entry point are inspected. Every
declaration in either project namespace is checked, including definitions and
their transitive dependencies. The three standard logical axioms are allowed;
an admitted proof or any additional axiom fails the check.
-/

open Lean Elab Command in
elab "audit_eth_response" : command => do
  let env ← getEnv
  let forbiddenModules := #[`ExactSolution, `ExactSolution.Audit,
    `ExactSolution.Knowability, `ExactSolution.Semantic]
  for moduleName in env.header.moduleNames do
    if forbiddenModules.contains moduleName then
      throwError "Public entry point loaded excluded module {moduleName}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut exactCount := 0
  let mut responseCount := 0
  for (name, _) in env.constants.toList do
    let userName := (Lean.privateToUserName? name).getD name
    let isExact := (`ExactSolution).isPrefixOf userName
    let isResponse := (`ETHResponse).isPrefixOf userName
    if isExact || isResponse then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
      if isExact then exactCount := exactCount + 1
      if isResponse then responseCount := responseCount + 1
  unless exactCount > 0 do
    throwError "No ExactSolution declarations were loaded by the public entry point"
  logInfo m!"Public axiom audit passed for {exactCount + responseCount} loaded declarations ({exactCount} ExactSolution; {responseCount} ETHResponse)."

/-- info: 'ExactSolution.SingletonCNF.singleton_count_complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.SingletonCNF.singleton_count_complexity

/-- info: 'ExactSolution.transcript_query_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.transcript_query_lower_bound

/-- info: 'ExactSolution.read_all_operational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.read_all_operational

/-- info: 'ExactSolution.hermite_value_at_zero_determined_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.hermite_value_at_zero_determined_iff

/-- info: 'ExactSolution.SwapSpectrum.swap_rank_eq_failure_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.SwapSpectrum.swap_rank_eq_failure_mass

/-- info: 'ExactSolution.MeasurementRank.swap_measurement_degree_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.MeasurementRank.swap_measurement_degree_floor

/-- info: 'ExactSolution.MeasurementRank.swap_measurement_enumeration_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.MeasurementRank.swap_measurement_enumeration_floor

/-- info: 'ExactSolution.swap_measurement_near_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.swap_measurement_near_exponential

/-- info: 'ExactSolution.enumerationCount_le_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ExactSolution.enumerationCount_le_three_pow

/-- info: 'ExactSolution.SelectedMeasurements.measurement_fixing_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.measurement_fixing_kernel

/-- info: 'ExactSolution.SelectedMeasurements.rowCount_eq_dimension_mul_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.rowCount_eq_dimension_mul_tail

/-- info: 'ExactSolution.SelectedMeasurements.integerMeasurementMatrix_l1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.integerMeasurementMatrix_l1_le

/-- info: 'ExactSolution.SelectedMeasurements.placed_row_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.placed_row_count_bound

/-- info: 'ExactSolution.SelectedMeasurements.selected_measurement_degree_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.selected_measurement_degree_floor

/-- info: 'ExactSolution.SelectedMeasurements.signed_window_measurement_enumeration_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.signed_window_measurement_enumeration_floor

/-- info: 'ExactSolution.SelectedMeasurements.signed_window_measurement_near_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.signed_window_measurement_near_exponential

/-- info: 'ExactSolution.SelectedMeasurements.parityInterpolant_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.parityInterpolant_natDegree_lt

/-- info: 'ExactSolution.SelectedMeasurements.interval_measurement_near_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactSolution.SelectedMeasurements.interval_measurement_near_exponential

set_option maxHeartbeats 0 in
audit_eth_response
