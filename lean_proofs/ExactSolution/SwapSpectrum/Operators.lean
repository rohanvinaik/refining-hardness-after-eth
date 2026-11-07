import ExactSolution.SwapSpectrum.TensorBasis
import ExactSolution.MeasurementRank.Basic

/-! Actual products, sums, and polynomial evaluations of coordinate swaps. -/

namespace ExactSolution.SwapSpectrum

open scoped BigOperators
open Polynomial

noncomputable def swapV0 (r Q : ℕ) : Module.End ℚ (History r Q → ℚ) :=
  (List.ofFn (swapPi r Q)).prod

noncomputable def swapW0 (r Q : ℕ) : Module.End ℚ (History r Q → ℚ) :=
  (1 / 2 : ℚ) • ∑ s : Fin Q, (LinearMap.id - swapPi r Q s)

noncomputable def swapM0 (r Q : ℕ) (f : ℚ[X]) : Module.End ℚ (History r Q → ℚ) :=
  swapV0 r Q * Polynomial.aeval (swapW0 r Q) f

def signProduct {r Q : ℕ} (alpha : EigenHistory r Q) : ℚ :=
  ∏ s : Fin Q, eigenSign (alpha s)

def weightEigenvalue {r Q : ℕ} (alpha : EigenHistory r Q) : ℚ :=
  ∑ s : Fin Q, (1 - eigenSign (alpha s)) / 2

theorem indexed_prod_eigen {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    (T : ι → Module.End ℚ V) (d : ι → ℚ) (v : V)
    (heigen : ∀ i, T i v = d i • v) (l : List ι) :
    (l.map T).prod v = (l.map d).prod • v := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
      heigen, smul_smul]
    congr 1
    ring

theorem swapV0_tensorBasis (r Q : ℕ) (alpha : EigenHistory r Q) :
    swapV0 r Q (tensorBasis r Q alpha) =
      signProduct alpha • tensorBasis r Q alpha := by
  have h := indexed_prod_eigen (swapPi r Q) (fun s => eigenSign (alpha s))
    (tensorBasis r Q alpha) (fun s => swapPi_tensorBasis r Q s alpha)
    (List.ofFn (fun s : Fin Q => s))
  simpa [swapV0, signProduct, Function.comp_def, List.prod_ofFn] using h

theorem swapV0_apply (r Q : ℕ) (x : History r Q → ℚ) (h : History r Q) :
    swapV0 r Q x h = x (fun s => (h s).swap) := by
  let T : Module.End ℚ (History r Q → ℚ) :=
    { toFun := fun v h => v (fun s => (h s).swap)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT (alpha : EigenHistory r Q) :
      T (tensorBasis r Q alpha) = signProduct alpha • tensorBasis r Q alpha := by
    ext k
    change tensorBasis r Q alpha (fun s => (k s).swap) =
      signProduct alpha * tensorBasis r Q alpha k
    rw [tensorBasis_apply, tensorBasis_apply]
    have hl : ∀ s : Fin Q, pairBasis r (alpha s) (k s).swap =
        eigenSign (alpha s) * pairBasis r (alpha s) (k s) := by
      intro s
      simpa [pairSwap, smul_eq_mul] using
        congrFun (pairBasis_eigen r (alpha s)) (k s)
    simp_rw [hl]
    exact Finset.prod_mul_distrib
  have heq : swapV0 r Q = T := (tensorBasis r Q).ext fun alpha =>
    (swapV0_tensorBasis r Q alpha).trans (hT alpha).symm
  rw [heq]
  rfl

theorem swapW0_apply (r Q : ℕ) (x : History r Q → ℚ) (h : History r Q) :
    swapW0 r Q x h = (1 / 2 : ℚ) * ∑ s : Fin Q, (x h - x (swapAt s h)) := by
  simp [swapW0, swapPi]

theorem swapW0_tensorBasis (r Q : ℕ) (alpha : EigenHistory r Q) :
    swapW0 r Q (tensorBasis r Q alpha) =
      weightEigenvalue alpha • tensorBasis r Q alpha := by
  simp only [swapW0, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    LinearMap.id_apply, swapPi_tensorBasis]
  rw [Finset.smul_sum]
  have hterm : ∀ s : Fin Q,
      (1 / 2 : ℚ) • (tensorBasis r Q alpha -
          eigenSign (alpha s) • tensorBasis r Q alpha) =
        ((1 - eigenSign (alpha s)) / 2) • tensorBasis r Q alpha := by
    intro s
    have hsub : tensorBasis r Q alpha - eigenSign (alpha s) • tensorBasis r Q alpha =
        (1 - eigenSign (alpha s)) • tensorBasis r Q alpha := by
      rw [sub_smul, one_smul]
    rw [hsub, smul_smul]
    congr 1
    ring
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  rfl

theorem end_pow_apply_eigen {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (v : V) (c : ℚ) (h : T v = c • v) (n : ℕ) :
    (T ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, h, map_smul, ih, smul_smul, pow_succ]
    congr 1
    ring

theorem aeval_apply_eigen {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (v : V) (c : ℚ) (h : T v = c • v) (f : ℚ[X]) :
    Polynomial.aeval T f v = f.eval c • v := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply,
      end_pow_apply_eigen T v c h n]
    simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]

theorem swapM0_tensorBasis (r Q : ℕ) (f : ℚ[X]) (alpha : EigenHistory r Q) :
    swapM0 r Q f (tensorBasis r Q alpha) =
      (signProduct alpha * f.eval (weightEigenvalue alpha)) • tensorBasis r Q alpha := by
  rw [swapM0, Module.End.mul_apply,
    aeval_apply_eigen _ _ _ (swapW0_tensorBasis r Q alpha), map_smul,
    swapV0_tensorBasis, smul_smul]
  congr 1
  ring

theorem basis_diagonalization {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ V)
    (T : Module.End ℚ V) (d : ι → ℚ) (h : ∀ i, T (b i) = d i • b i) :
    b.equivFun.conj T = MeasurementRank.diagEnd d := by
  apply (Pi.basisFun ℚ ι).ext
  intro i
  have hback : b.equivFun.symm (Pi.basisFun ℚ ι i) = b i := by
    apply b.equivFun.injective
    ext j
    simp [Module.Basis.equivFun_self]
  ext j
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, hback, h, map_smul, Pi.smul_apply, smul_eq_mul,
    MeasurementRank.diagEnd_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Module.Basis.equivFun_self, hij, Ne.symm hij]

theorem swapM0_diagonalization (r Q : ℕ) (f : ℚ[X]) :
    (tensorBasis r Q).equivFun.conj (swapM0 r Q f) =
      MeasurementRank.diagEnd
        (fun alpha => signProduct alpha * f.eval (weightEigenvalue alpha)) :=
  basis_diagonalization _ _ _ (swapM0_tensorBasis r Q f)

theorem swap_rank_eq_eigen_history_count (r Q : ℕ) (f : ℚ[X]) :
    Module.finrank ℚ (LinearMap.id - swapM0 r Q f).range =
      (Finset.univ.filter fun alpha : EigenHistory r Q =>
        signProduct alpha * f.eval (weightEigenvalue alpha) ≠ 1).card :=
  MeasurementRank.finrank_defect_of_diagonalization _ _ _ (swapM0_diagonalization r Q f)

end ExactSolution.SwapSpectrum
