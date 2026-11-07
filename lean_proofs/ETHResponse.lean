import ExactSolution.Observation
import ExactSolution.Observability
import ExactSolution.Transcript
import ExactSolution.Covering
import ExactSolution.SingletonCNF
import ExactSolution.ReadAll
import ExactSolution.Simulation
import ExactSolution.Hermite
import ExactSolution.MeasurementRank
import ExactSolution.NearExponential
import ExactSolution.SelectedMeasurements

/-!
# Public response proof entry point

The selected modules give the observation model, point-CNF separation,
operational transcript and explicit-input statements, observation simulation,
ambient Hermite threshold, and the concrete swap measurement and enumeration
chain. The near-exponential corollary retains the actual measurement and
dimension contracts of that specified family.

The selected transpose-eigenbasis construction proves the local fixing-kernel
condition from window agreement, counts its rows exactly, and bounds their
integer entries and absolute row sums. Its application endpoints retain the
tail and dimension budgets; external placement into variable groups is separate.

This entry point does not import the complete `ExactSolution` capstone or the
Knowability and Semantic applications. `ETHResponse.Audit` checks every loaded
declaration in the `ExactSolution` and `ETHResponse` namespaces.
-/
