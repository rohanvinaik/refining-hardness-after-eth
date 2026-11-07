import Mathlib

/-!
# A uniform bound on binomial point masses

The proof uses thinning to a fair-coin distribution.  Every estimate concerns
the explicit binomial mass, including points outside its finite support.
-/

namespace ExactSolution

noncomputable def binomialMass (Q : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (Q.choose j : ℝ) * p ^ j * (1 - p) ^ (Q - j)

namespace Binomial

noncomputable def fairMass (m j : ℕ) : ℝ := (m.choose j : ℝ) / (2 : ℝ) ^ m

theorem mass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (Q j : ℕ) :
    0 ≤ binomialMass Q p j := by
  have hq : 0 ≤ 1 - p := by linarith
  unfold binomialMass
  positivity

theorem sum_mass (Q : ℕ) (p : ℝ) :
    (∑ m ∈ Finset.range (Q + 1), binomialMass Q p m) = 1 := by
  have h := add_pow p (1 - p) Q
  have hsum : ∀ m, binomialMass Q p m = p ^ m * (1 - p) ^ (Q - m) *
      (Q.choose m : ℝ) := by intro m; unfold binomialMass; ring
  simp_rw [hsum]
  simpa using h.symm

private theorem choose_step (Q m : ℕ) :
    (Q + 1 : ℝ) * (Q.choose m : ℝ) =
      (m + 1 : ℝ) * ((Q + 1).choose (m + 1) : ℝ) := by
  have h := Nat.choose_mul (n := Q + 1) (k := m + 1) (s := 1) (by omega)
  have hn : (Q + 1) * Q.choose m = (m + 1) * (Q + 1).choose (m + 1) := by
    simpa [mul_comm] using h.symm
  exact_mod_cast hn

theorem inverse_moment {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (Q : ℕ) :
    (∑ m ∈ Finset.range (Q + 1), binomialMass Q t m / ((m : ℝ) + 1)) ≤
      1 / (t * ((Q : ℝ) + 1)) := by
  have hentry (m : ℕ) :
      binomialMass Q t m / ((m : ℝ) + 1) * (t * ((Q : ℝ) + 1)) =
        binomialMass (Q + 1) t (m + 1) := by
    have hchoose := choose_step Q m
    unfold binomialMass
    rw [Nat.add_sub_add_right, pow_succ]
    field_simp
    linear_combination (1 - t) ^ (Q - m) * hchoose
  have hsum := sum_mass (Q + 1) t
  rw [Finset.sum_range_succ'] at hsum
  have hzero := mass_nonneg ht.le ht' (Q + 1) 0
  have htail : (∑ m ∈ Finset.range (Q + 1), binomialMass (Q + 1) t (m + 1)) ≤ 1 := by
    linarith
  apply (le_div_iff₀ (show 0 < t * ((Q : ℝ) + 1) by positivity)).mpr
  rw [Finset.sum_mul]
  simp_rw [hentry]
  exact htail

private theorem mixture_entry (Q m j : ℕ) (p : ℝ) :
    binomialMass Q (2 * p) m * fairMass m j =
      ((Q.choose m : ℝ) * (m.choose j : ℝ)) * p ^ m * (1 - 2 * p) ^ (Q - m) := by
  unfold binomialMass fairMass
  rw [mul_pow]
  field_simp

theorem mixture (Q j : ℕ) (p : ℝ) :
    binomialMass Q p j =
      ∑ m ∈ Finset.range (Q + 1), binomialMass Q (2 * p) m * fairMass m j := by
  simp_rw [mixture_entry]
  by_cases hj : j ≤ Q
  · have hlen : Q + 1 = j + (Q - j + 1) := by omega
    rw [hlen, Finset.sum_range_add]
    have hfront : (∑ m ∈ Finset.range j,
        ((Q.choose m : ℝ) * (m.choose j : ℝ)) * p ^ m * (1 - 2 * p) ^ (Q - m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmj : m < j := Finset.mem_range.mp hm
      simp [Nat.choose_eq_zero_of_lt hmj]
    rw [hfront, zero_add]
    have hentry (s : ℕ) :
        ((Q.choose (j + s) : ℝ) * ((j + s).choose j : ℝ)) * p ^ (j + s) *
            (1 - 2 * p) ^ (Q - (j + s)) =
          ((Q.choose j : ℝ) * p ^ j) *
            (p ^ s * (1 - 2 * p) ^ ((Q - j) - s) * ((Q - j).choose s : ℝ)) := by
      have hc := Nat.choose_mul (n := Q) (k := j + s) (s := j) (by omega)
      simp only [Nat.add_sub_cancel_left] at hc
      have hc' : (Q.choose (j + s) : ℝ) * ((j + s).choose j : ℝ) =
          (Q.choose j : ℝ) * ((Q - j).choose s : ℝ) := by
        exact_mod_cast hc
      have he : Q - (j + s) = (Q - j) - s := by omega
      rw [hc', he, pow_add]
      ring
    simp_rw [hentry, ← Finset.mul_sum, ← add_pow]
    unfold binomialMass
    congr 2
    ring
  · have hQj : Q < j := by omega
    have hleft : binomialMass Q p j = 0 := by
      simp [binomialMass, Nat.choose_eq_zero_of_lt hQj]
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have hmj : m < j := by have := Finset.mem_range.mp hm; omega
    simp [Nat.choose_eq_zero_of_lt hmj]

private noncomputable def centralMass (k : ℕ) : ℝ :=
  (k.centralBinom : ℝ) / (4 : ℝ) ^ k

private theorem centralMass_nonneg (k : ℕ) : 0 ≤ centralMass k := by
  unfold centralMass
  positivity

private theorem centralMass_step (k : ℕ) :
    (2 * (k : ℝ) + 2) * centralMass (k + 1) =
      (2 * (k : ℝ) + 1) * centralMass k := by
  have hrec : ((k : ℝ) + 1) * ((k + 1).centralBinom : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (k.centralBinom : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold centralMass
  rw [pow_succ]
  field_simp
  nlinarith [hrec]

private theorem centralMass_sq (k : ℕ) :
    (2 * (k : ℝ) + 1) * centralMass k ^ 2 ≤ 1 := by
  induction k with
  | zero => norm_num [centralMass]
  | succ k ih =>
    have hrec := centralMass_step k
    have hrec2 := congrArg (fun z : ℝ => z ^ 2) hrec
    have hfactor : 0 ≤ (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left ih hfactor
    have hpoly : (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) ≤
        (2 * (k : ℝ) + 2) ^ 2 := by nlinarith
    have hmain : (2 * (k : ℝ) + 2) ^ 2 *
        ((2 * (k : ℝ) + 3) * centralMass (k + 1) ^ 2) ≤
          (2 * (k : ℝ) + 2) ^ 2 := by
      calc
        _ = ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3)) *
            ((2 * (k : ℝ) + 1) * centralMass k ^ 2) := by
          nlinarith [congrArg (fun z : ℝ => (2 * (k : ℝ) + 3) * z) hrec2]
        _ ≤ ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3)) * 1 := hscaled
        _ ≤ (2 * (k : ℝ) + 2) ^ 2 := by simpa using hpoly
    have hpos : 0 < (2 * (k : ℝ) + 2) ^ 2 := by positivity
    have h := (mul_le_mul_iff_right₀ hpos).mp (show
        (2 * (k : ℝ) + 2) ^ 2 * ((2 * (k : ℝ) + 3) * centralMass (k + 1) ^ 2) ≤
          (2 * (k : ℝ) + 2) ^ 2 * 1 by simpa using hmain)
    push_cast
    nlinarith [h]

private theorem two_pow_even (k : ℕ) : (2 : ℝ) ^ (2 * k) = (4 : ℝ) ^ k := by
  rw [pow_mul]
  norm_num

private theorem fairMass_le_even (k j : ℕ) : fairMass (2 * k) j ≤ centralMass k := by
  have hc : ((2 * k).choose j : ℝ) ≤ (k.centralBinom : ℝ) := by
    exact_mod_cast Nat.choose_le_centralBinom j k
  unfold fairMass centralMass
  rw [two_pow_even]
  exact div_le_div_of_nonneg_right hc (by positivity)

private theorem centralBinom_odd (k : ℕ) :
    (k + 1).centralBinom = 2 * (2 * k + 1).choose k := by
  have hsymm : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := by
    have h := Nat.choose_symm (n := 2 * k + 1) (k := k) (by omega)
    have he : 2 * k + 1 - k = k + 1 := by omega
    simpa only [he] using h
  unfold Nat.centralBinom
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.choose_succ_succ', hsymm]
  omega

private theorem fairMass_le_odd (k j : ℕ) : fairMass (2 * k + 1) j ≤ centralMass (k + 1) := by
  have hc : ((2 * k + 1).choose j : ℝ) ≤ ((2 * k + 1).choose k : ℝ) := by
    have h := Nat.choose_le_middle j (2 * k + 1)
    have he : (2 * k + 1) / 2 = k := by omega
    rw [he] at h
    exact_mod_cast h
  have hmid : ((2 * k + 1).choose k : ℝ) / (2 : ℝ) ^ (2 * k + 1) =
      centralMass (k + 1) := by
    unfold centralMass
    rw [centralBinom_odd, Nat.cast_mul, Nat.cast_ofNat, pow_succ, pow_succ, two_pow_even]
    field_simp
    norm_num
  unfold fairMass
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans hmid.le

theorem fairMass_nonneg (m j : ℕ) : 0 ≤ fairMass m j := by
  unfold fairMass
  positivity

theorem fairMass_sq (m j : ℕ) : fairMass m j ^ 2 ≤ 1 / ((m : ℝ) + 1) := by
  let k := m / 2
  have hcase : m = 2 * k ∨ m = 2 * k + 1 := by dsimp [k]; omega
  rcases hcase with hm | hm
  · rw [hm]
    apply (le_div_iff₀ (show 0 < ((2 * k : ℕ) : ℝ) + 1 by positivity)).mpr
    have hsq := (sq_le_sq₀ (fairMass_nonneg (2 * k) j) (centralMass_nonneg k)).mpr
      (fairMass_le_even k j)
    have h := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 2 * (k : ℝ) + 1 by positivity)
    push_cast
    nlinarith [centralMass_sq k]
  · rw [hm]
    apply (le_div_iff₀ (show 0 < ((2 * k + 1 : ℕ) : ℝ) + 1 by positivity)).mpr
    have hsq := (sq_le_sq₀ (fairMass_nonneg (2 * k + 1) j)
      (centralMass_nonneg (k + 1))).mpr (fairMass_le_odd k j)
    have hc := centralMass_sq (k + 1)
    have h := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 2 * (k : ℝ) + 2 by positivity)
    have hcn : 0 ≤ centralMass (k + 1) ^ 2 := sq_nonneg _
    push_cast at hc ⊢
    nlinarith

theorem weighted_sum_sq_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * a i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * a i)
  have hleft : (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * a i)) =
      ∑ i ∈ s, w i * a i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = Real.sqrt (w i) ^ 2 * a i := by ring
      _ = w i * a i := by rw [Real.sq_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ s, Real.sqrt (w i) ^ 2) = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have hsecond : (∑ i ∈ s, (Real.sqrt (w i) * a i) ^ 2) =
      ∑ i ∈ s, w i * a i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  simpa only [hleft, hfirst, hsecond] using h

theorem mass_sq_le_inverse {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1 / 2) (Q j : ℕ) :
    binomialMass Q p j ^ 2 ≤ 1 / (2 * p * ((Q : ℝ) + 1)) := by
  have ht : 0 < 2 * p := by positivity
  have ht' : 2 * p ≤ 1 := by linarith
  have hw (m : ℕ) (_ : m ∈ Finset.range (Q + 1)) : 0 ≤ binomialMass Q (2 * p) m :=
    mass_nonneg ht.le ht' Q m
  have hcs := weighted_sum_sq_le (Finset.range (Q + 1))
    (binomialMass Q (2 * p)) (fun m => fairMass m j) hw
  rw [← mixture Q j p, sum_mass, one_mul] at hcs
  refine hcs.trans ?_
  calc
    (∑ m ∈ Finset.range (Q + 1), binomialMass Q (2 * p) m * fairMass m j ^ 2) ≤
        ∑ m ∈ Finset.range (Q + 1), binomialMass Q (2 * p) m / ((m : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left (fairMass_sq m j) (hw m hm)
    _ ≤ 1 / (2 * p * ((Q : ℝ) + 1)) := inverse_moment ht ht' Q

end Binomial

theorem binomial_mass_le {Q : ℕ} {p : ℝ} (hQ : 0 < Q)
    (hp : 1 / 4 ≤ p) (hp' : p ≤ 1 / 2) (j : ℕ) :
    binomialMass Q p j ≤ 2 / Real.sqrt Q := by
  have hp0 : 0 < p := by linarith
  have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hden : 0 < 2 * p * ((Q : ℝ) + 1) := by positivity
  have hsq := Binomial.mass_sq_le_inverse hp0 hp' Q j
  have hscaled := (le_div_iff₀ hden).mp hsq
  have hdenlower : ((Q : ℝ) + 1) / 2 ≤ 2 * p * ((Q : ℝ) + 1) := by
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hdenlower (sq_nonneg (binomialMass Q p j))
  have hstrong : binomialMass Q p j ^ 2 * ((Q : ℝ) + 1) ≤ 2 := by
    nlinarith [hweighted, hscaled]
  have hprod : (binomialMass Q p j * Real.sqrt Q) ^ 2 ≤ 4 := by
    rw [mul_pow, Real.sq_sqrt hQ0.le]
    nlinarith [hstrong, sq_nonneg (binomialMass Q p j)]
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hmass := Binomial.mass_nonneg hp0.le (show p ≤ 1 by linarith) Q j
  have hbound : binomialMass Q p j * Real.sqrt Q ≤ 2 :=
    (sq_le_sq₀ (mul_nonneg hmass hsqrt.le) (show (0 : ℝ) ≤ 2 by norm_num)).mp
      (by norm_num; exact hprod)
  exact (le_div_iff₀ hsqrt).mpr hbound

end ExactSolution
