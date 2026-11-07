import Mathlib

/-!
# The clipped substitution enumeration

The count is the complete finite sum through `min q n`.  In particular, a
substitution order greater than `n` does not make the lower bound disappear.
-/

namespace ExactSolution

def enumerationCount (n q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min q n + 1), 2 ^ j * n.choose j

noncomputable def substitutionOrder (n R Q : ℕ) : ℕ :=
  Nat.floor (3 * (n : ℝ) * (R : ℝ) / (Q : ℝ))

theorem enumerationCount_ge_term {n q m : ℕ} (hm : m ≤ min q n) :
    2 ^ m * n.choose m ≤ enumerationCount n q := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (2 ^ j * n.choose j))
    (Finset.mem_range.mpr (by omega))

theorem enumerationCount_ge_choose {n q m : ℕ} (hm : m ≤ min q n) :
    n.choose m ≤ enumerationCount n q := by
  have hterm := enumerationCount_ge_term hm
  have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  nlinarith

private theorem choose_step (n m : ℕ) :
    ((m : ℝ) + 1) * ((n + 1).choose (m + 1) : ℝ) =
      ((n : ℝ) + 1) * (n.choose m : ℝ) := by
  have h := Nat.choose_mul (n := n + 1) (k := m + 1) (s := 1) (by omega)
  have hn : (m + 1) * (n + 1).choose (m + 1) = (n + 1) * n.choose m := by
    simpa [mul_comm] using h
  exact_mod_cast hn

theorem choose_lower_bound {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((n : ℝ) / (m : ℝ)) ^ m ≤ (n.choose m : ℝ) := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst m
      simp
    · cases n with
      | zero => omega
      | succ n =>
        have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
        have hmn' : m ≤ n := by omega
        have hi := ih (by omega) hmn'
        have hratio : ((n : ℝ) + 1) / ((m : ℝ) + 1) ≤ (n : ℝ) / (m : ℝ) := by
          apply (div_le_div_iff₀ (by positivity) hmpos).mpr
          have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn'
          nlinarith
        have ha : 0 ≤ ((n : ℝ) + 1) / ((m : ℝ) + 1) := by positivity
        have hrec : ((n + 1).choose (m + 1) : ℝ) =
            (((n : ℝ) + 1) / ((m : ℝ) + 1)) * (n.choose m : ℝ) := by
          field_simp
          nlinarith [choose_step n m]
        push_cast
        rw [pow_succ, hrec]
        calc
          _ ≤ ((n : ℝ) / (m : ℝ)) ^ m *
              (((n : ℝ) + 1) / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hratio m) ha
          _ ≤ (n.choose m : ℝ) * (((n : ℝ) + 1) / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hi ha
          _ = _ := by ring

theorem substitutionOrder_lower {n R Q : ℕ} {L : ℝ} (hQ : 0 < Q) (hL : 0 < L)
    (hQL : (Q : ℝ) ≤ L / 4)
    (hR : 1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ)) :
    (5 / 4 : ℝ) * n / Real.sqrt L - 1 ≤ (substitutionOrder n R Q : ℝ) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hsqQ := Real.sq_sqrt hQr.le
  have hsqL := Real.sq_sqrt hL.le
  have hsQ := Real.sqrt_nonneg (Q : ℝ)
  have hsL := Real.sqrt_nonneg L
  have ht : 2 * Real.sqrt Q ≤ Real.sqrt L := by nlinarith
  have hRlow : 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by linarith
  have hmulR := mul_le_mul_of_nonneg_right hRlow hsL
  have hmulS := mul_le_mul_of_nonneg_left ht hsQ
  have hcross : 5 * (Q : ℝ) ≤ 12 * (R : ℝ) * Real.sqrt L := by
    nlinarith [hmulR, hmulS]
  have hratio : 5 / (4 * Real.sqrt L) ≤ 3 * (R : ℝ) / (Q : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hQr).mpr
    nlinarith
  have hraw : (5 / 4 : ℝ) * n / Real.sqrt L ≤
      3 * (n : ℝ) * (R : ℝ) / (Q : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (n : ℝ) by positivity)
    convert h using 1 <;> ring
  have hf := Nat.lt_floor_add_one (3 * (n : ℝ) * (R : ℝ) / (Q : ℝ))
  unfold substitutionOrder
  linarith

theorem comparisonOrder_bounds {n q : ℕ} {L : ℝ} (hL : 16 ≤ L) (hLn : L ≤ n)
    (hq : (5 / 4 : ℝ) * n / Real.sqrt L - 1 ≤ (q : ℝ)) :
    let m := Nat.floor ((n : ℝ) / Real.sqrt L)
    1 ≤ m ∧ m ≤ min q n ∧
      (n : ℝ) / (2 * Real.sqrt L) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ (n : ℝ) / Real.sqrt L := by
  dsimp
  have hLp : 0 < L := by linarith
  have ht : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLp
  have htsq := Real.sq_sqrt hLp.le
  have ht4 : 4 ≤ Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hx : 0 ≤ (n : ℝ) / Real.sqrt L := by positivity
  have hx4 : 4 ≤ (n : ℝ) / Real.sqrt L := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hf := Nat.floor_le hx
  have hfl := Nat.lt_floor_add_one ((n : ℝ) / Real.sqrt L)
  have hmposR : (1 : ℝ) ≤ (Nat.floor ((n : ℝ) / Real.sqrt L) : ℝ) := by linarith
  have hmpos : 1 ≤ Nat.floor ((n : ℝ) / Real.sqrt L) := by exact_mod_cast hmposR
  have hxq : (n : ℝ) / Real.sqrt L ≤ (q : ℝ) := by
    linear_combination hq + (1 / 4 : ℝ) * hx4
  have hmq : Nat.floor ((n : ℝ) / Real.sqrt L) ≤ q := by
    exact_mod_cast hf.trans hxq
  have hxn : (n : ℝ) / Real.sqrt L ≤ (n : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    nlinarith
  have hmn : Nat.floor ((n : ℝ) / Real.sqrt L) ≤ n := Nat.floor_le_of_le hxn
  have hmhalf : (n : ℝ) / (2 * Real.sqrt L) ≤
      (Nat.floor ((n : ℝ) / Real.sqrt L) : ℝ) := by
    have h : (n : ℝ) / Real.sqrt L / 2 ≤
        (Nat.floor ((n : ℝ) / Real.sqrt L) : ℝ) := by linarith
    convert h using 1
    ring
  exact ⟨hmpos, le_min hmq hmn, hmhalf, hf⟩

theorem enumeration_lower_rpow {n q : ℕ} {L : ℝ} (hL : 16 ≤ L) (hLn : L ≤ n)
    (hq : (5 / 4 : ℝ) * n / Real.sqrt L - 1 ≤ (q : ℝ)) :
    (Real.sqrt L) ^ ((n : ℝ) / (2 * Real.sqrt L)) ≤ (enumerationCount n q : ℝ) := by
  let m := Nat.floor ((n : ℝ) / Real.sqrt L)
  obtain ⟨hmpos, hmclip, hmlow, hmup⟩ := comparisonOrder_bounds hL hLn hq
  have hmn : m ≤ n := le_trans hmclip (min_le_right _ _)
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hLp : 0 < L := by linarith
  have ht : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLp
  have ht4 : 4 ≤ Real.sqrt L := by
    nlinarith [Real.sq_sqrt hLp.le, Real.sqrt_nonneg L]
  have hratio : Real.sqrt L ≤ (n : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmr).mpr
    have h := (le_div_iff₀ ht).mp hmup
    nlinarith
  calc
    _ ≤ (Real.sqrt L) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hmlow
    _ ≤ ((n : ℝ) / (m : ℝ)) ^ (m : ℝ) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg L) hratio (by positivity)
    _ = ((n : ℝ) / (m : ℝ)) ^ m := Real.rpow_natCast _ _
    _ ≤ (n.choose m : ℝ) := choose_lower_bound hmpos hmn
    _ ≤ (enumerationCount n q : ℝ) := by
      exact_mod_cast enumerationCount_ge_choose hmclip

private theorem sqrt_rpow_identity {n : ℕ} {L : ℝ} (hL : 0 < L) :
    (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 L / (4 * Real.sqrt L)) =
      (Real.sqrt L) ^ ((n : ℝ) / (2 * Real.sqrt L)) := by
  have hbase := Real.rpow_logb (b := 2) (x := L) (by norm_num) (by norm_num) hL
  calc
    _ = (2 : ℝ) ^ (Real.logb 2 L * ((1 / 2 : ℝ) *
        ((n : ℝ) / (2 * Real.sqrt L)))) := by congr 1; ring
    _ = ((2 : ℝ) ^ Real.logb 2 L) ^ ((1 / 2 : ℝ) *
        ((n : ℝ) / (2 * Real.sqrt L))) := Real.rpow_mul (by norm_num) _ _
    _ = L ^ ((1 / 2 : ℝ) * ((n : ℝ) / (2 * Real.sqrt L))) := by rw [hbase]
    _ = (L ^ (1 / 2 : ℝ)) ^ ((n : ℝ) / (2 * Real.sqrt L)) :=
      Real.rpow_mul hL.le _ _
    _ = _ := by simp only [Real.sqrt_eq_rpow]

theorem enumeration_lower_exponential {n q : ℕ} {L : ℝ} (hL : 16 ≤ L) (hLn : L ≤ n)
    (hq : (5 / 4 : ℝ) * n / Real.sqrt L - 1 ≤ (q : ℝ)) :
    (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 L / (4 * Real.sqrt L)) ≤
      (enumerationCount n q : ℝ) := by
  rw [sqrt_rpow_identity (show 0 < L by linarith)]
  exact enumeration_lower_rpow hL hLn hq

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    nlinarith

theorem logTwo_bounds {n : ℕ} (hn : 65536 ≤ n) :
    16 ≤ Real.logb 2 (n : ℝ) ∧ Real.logb 2 (n : ℝ) ≤ (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  constructor
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hn0).mpr
    have hpow : (2 : ℝ) ^ (16 : ℝ) = 65536 := by norm_num
    rw [hpow]
    exact_mod_cast hn
  · apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hn0).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast nat_le_two_pow n

/-- The construction's dimension budget supplies the logarithmic bound on `Q`. -/
theorem dimension_budget_implies_Q_bound {r Q n : ℕ} {D M : ℝ}
    (hr : 2 ≤ r) (hD : D = (r : ℝ) ^ (2 * Q))
    (hbudget : 12 * D ^ 2 ≤ M) (hM : M ≤ 3 * (n : ℝ)) :
    (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 := by
  have hDn : D ^ 2 ≤ (n : ℝ) := by
    nlinarith [sq_nonneg D, show 0 ≤ (n : ℝ) by positivity]
  have hpow : (2 : ℝ) ^ (4 * Q) ≤ D ^ 2 := by
    calc
      _ ≤ (r : ℝ) ^ (4 * Q) :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hr) _
      _ = D ^ 2 := by
        rw [hD, ← pow_mul]
        congr 1
        omega
  have hn : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) (hpow.trans hDn)
  have hlog : ((4 * Q : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hn).mpr
    rw [Real.rpow_natCast]
    exact hpow.trans hDn
  push_cast at hlog
  linarith

/-- An explicit uniform lower bound on the construction's clipped enumeration. -/
theorem enumeration_floor_explicit {n R Q : ℕ} (hn : 65536 ≤ n) (hQ : 0 < Q)
    (hQL : (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4)
    (hR : 1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ)) :
    (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
      (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
        (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  obtain ⟨hL, hLn⟩ := logTwo_bounds hn
  apply enumeration_lower_exponential hL hLn
  exact substitutionOrder_lower hQ (by linarith) hQL hR

/-- This is `2^{Ω(n log log n / sqrt(log n))}` as a concrete eventual inequality. -/
theorem enumeration_floor_eventually :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R Q : ℕ, 0 < Q →
      (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 →
      1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) →
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
        (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
          (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (65536 : ℕ)] with n hn
  intro R Q hQ hQL hR
  exact enumeration_floor_explicit hn hQ hQL hR

end ExactSolution
