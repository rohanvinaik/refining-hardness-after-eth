import Mathlib

/-!
# Linear measurement rank bounds

If the zero-measurement subspace is fixed by an operator, its defect map
factors through the measured information. Rank-nullity bounds the defect rank
by the number of measurement rows. Independent diagonal and conjugation lemmas
support the concrete swap-spectrum application.
-/

namespace ExactSolution.MeasurementRank

theorem range_finrank_le_of_ker_le
    {V U W : Type*} [AddCommGroup V] [AddCommGroup U] [AddCommGroup W]
    [Module ℚ V] [Module ℚ U] [Module ℚ W] [FiniteDimensional ℚ V]
    (C : V →ₗ[ℚ] W) (N : V →ₗ[ℚ] U) (hker : C.ker ≤ N.ker) :
    Module.finrank ℚ N.range ≤ Module.finrank ℚ C.range := by
  have hk := Submodule.finrank_mono hker
  have hc := C.finrank_range_add_finrank_ker
  have hn := N.finrank_range_add_finrank_ker
  omega

theorem measurement_rows_ge_rank
    {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module ℚ V] [Module ℚ U] [FiniteDimensional ℚ V] {m : ℕ}
    (C : V →ₗ[ℚ] (Fin m → ℚ)) (N : V →ₗ[ℚ] U) (hker : C.ker ≤ N.ker) :
    Module.finrank ℚ N.range ≤ m := by
  calc
    Module.finrank ℚ N.range ≤ Module.finrank ℚ C.range :=
      range_finrank_le_of_ker_le C N hker
    _ ≤ Module.finrank ℚ (Fin m → ℚ) := Submodule.finrank_le _
    _ = m := by simp

theorem kernel_defect_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (C : V →ₗ[ℚ] (Fin m → ℚ)) (M : Module.End ℚ V) :
    C.ker ≤ (LinearMap.id - M).ker ↔ ∀ v, C v = 0 → M v = v := by
  constructor
  · intro h v hv
    have hn := h hv
    change v - M v = 0 at hn
    exact (sub_eq_zero.mp hn).symm
  · intro h v hv
    change v - M v = 0
    exact sub_eq_zero.mpr (h v hv).symm

theorem measurement_rows_ge_defectRank
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {m : ℕ}
    (C : V →ₗ[ℚ] (Fin m → ℚ)) (M : Module.End ℚ V)
    (hfixed : ∀ v, C v = 0 → M v = v) :
    Module.finrank ℚ (LinearMap.id - M).range ≤ m := by
  exact measurement_rows_ge_rank C (LinearMap.id - M) ((kernel_defect_iff C M).mpr hfixed)

def diagEnd {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℚ) :
    Module.End ℚ (ι → ℚ) := (Matrix.diagonal d).mulVecLin

@[simp] theorem diagEnd_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d v : ι → ℚ) (i : ι) : diagEnd d v i = d i * v i := by
  exact Matrix.mulVec_diagonal d v i

theorem finrank_range_diagEnd {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℚ) :
    Module.finrank ℚ (diagEnd d).range = (Finset.univ.filter fun i => d i ≠ 0).card := by
  change (Matrix.diagonal d).rank = _
  rw [Matrix.rank_diagonal]
  exact Fintype.card_subtype (fun i => d i ≠ 0)

theorem finrank_range_one_sub_diagEnd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℚ) :
    Module.finrank ℚ (LinearMap.id - diagEnd d).range =
      (Finset.univ.filter fun i => d i ≠ 1).card := by
  have h : LinearMap.id - diagEnd d = diagEnd (fun i => 1 - d i) := by
    ext v i
    simp
    ring
  rw [h, finrank_range_diagEnd]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hn heq
    apply hn
    rw [heq]
    norm_num
  · intro hn heq
    apply hn
    linarith

theorem finrank_range_conj
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W]
    (e : V ≃ₗ[ℚ] W) (N : Module.End ℚ V) :
    Module.finrank ℚ (e.conj N).range = Module.finrank ℚ N.range := by
  rw [LinearEquiv.conj_apply, LinearMap.range_comp_of_range_eq_top _ e.symm.range,
    LinearMap.range_comp, LinearEquiv.finrank_map_eq]

theorem finrank_defect_of_diagonalization
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (e : V ≃ₗ[ℚ] (ι → ℚ)) (M : Module.End ℚ V) (d : ι → ℚ)
    (hdiag : e.conj M = diagEnd d) :
    Module.finrank ℚ (LinearMap.id - M).range =
      (Finset.univ.filter fun i => d i ≠ 1).card := by
  have hid : e.conj (LinearMap.id : Module.End ℚ V) = LinearMap.id := by
    ext v
    simp [LinearEquiv.conj_apply]
  calc
    Module.finrank ℚ (LinearMap.id - M).range =
        Module.finrank ℚ (e.conj (LinearMap.id - M)).range :=
      (finrank_range_conj e _).symm
    _ = Module.finrank ℚ (LinearMap.id - diagEnd d).range := by rw [map_sub, hid, hdiag]
    _ = _ := finrank_range_one_sub_diagEnd d

end ExactSolution.MeasurementRank
