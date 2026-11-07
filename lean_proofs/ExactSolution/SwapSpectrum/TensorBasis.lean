import ExactSolution.SwapSpectrum.PairBasis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! The actual coordinate swaps on the history-function space have the product
of the explicit pair bases as a basis. -/

namespace ExactSolution.SwapSpectrum

open scoped BigOperators

abbrev History (r Q : ℕ) := Fin Q → Pair r
abbrev EigenHistory (r Q : ℕ) := Fin Q → EigenIndex r

noncomputable def standardTensorBasis (r Q : ℕ) :
    Module.Basis (History r Q) ℚ (PiTensorProduct ℚ (fun _ : Fin Q => Pair r → ℚ)) :=
  Basis.piTensorProduct (fun _ : Fin Q => Pi.basisFun ℚ (Pair r))

noncomputable def tensorBasis (r Q : ℕ) :
    Module.Basis (EigenHistory r Q) ℚ (History r Q → ℚ) :=
  (Basis.piTensorProduct (fun _ : Fin Q => pairBasis r)).map
    (standardTensorBasis r Q).equivFun

theorem tensorBasis_apply (r Q : ℕ) (alpha : EigenHistory r Q) (h : History r Q) :
    tensorBasis r Q alpha h = ∏ s : Fin Q, pairBasis r (alpha s) (h s) := by
  simp [tensorBasis, standardTensorBasis, Module.Basis.equivFun_apply]

def swapAt {r Q : ℕ} (s : Fin Q) (h : History r Q) : History r Q :=
  Function.update h s (h s).swap

noncomputable def swapPi (r Q : ℕ) (s : Fin Q) : Module.End ℚ (History r Q → ℚ) where
  toFun x := fun h => x (swapAt s h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem swapPi_tensorBasis (r Q : ℕ) (s : Fin Q) (alpha : EigenHistory r Q) :
    swapPi r Q s (tensorBasis r Q alpha) = eigenSign (alpha s) • tensorBasis r Q alpha := by
  ext h
  change tensorBasis r Q alpha (swapAt s h) =
    eigenSign (alpha s) * tensorBasis r Q alpha h
  rw [tensorBasis_apply, tensorBasis_apply]
  have hrest : (∏ t ∈ (Finset.univ : Finset (Fin Q)) \ {s},
      pairBasis r (alpha t) (swapAt s h t)) =
      ∏ t ∈ (Finset.univ : Finset (Fin Q)) \ {s}, pairBasis r (alpha t) (h t) := by
    apply Finset.prod_congr rfl
    intro t ht
    have hts : t ≠ s := by simpa using (Finset.mem_sdiff.mp ht).2
    simp [swapAt, hts]
  have hlocal : pairBasis r (alpha s) (h s).swap =
      eigenSign (alpha s) * pairBasis r (alpha s) (h s) := by
    have hl := congrFun (pairBasis_eigen r (alpha s)) (h s)
    simpa [pairSwap, smul_eq_mul] using hl
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ s)
      (fun t => pairBasis r (alpha t) (swapAt s h t)),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ s)
      (fun t => pairBasis r (alpha t) (h t)), hrest]
  simp only [swapAt, Function.update_self]
  rw [hlocal]
  ring

end ExactSolution.SwapSpectrum
