-- import Mathlib
-- use #min_imports
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

theorem th (h : 2 = 2)
  : 2 = 2 :=
  by exact h

theorem th2
  : 2 = 2 :=
  by norm_num

theorem plus_comm : ∀ (a b : ℕ), a + b = b + a
  := by 
    intro a b
    have h := Nat.add_comm a b
    exact h

theorem alg : ∀ (a b c : ℕ), a * (b + c) = a * (c + b)
  := by
    intro a b c
    have h : b + c = c + b := by
      exact Nat.add_comm b c
    rw [h]

theorem alg' : ∀ (a b c d : ℕ),
  (c + d)^2 + c * (a + b)^2 = c^2 + d^2 + 2*c*d + c * a^2 + c * (b^2 + 2*a*b)
    := by
      intro a b c d
      ring

theorem ev10
  : Even 10 := by
    unfold Even
    use 5

theorem two_div_even :
    ∀ n : ℕ, Even n → 2 ∣ n := by
    intro n n_even
    unfold Even at n_even
    obtain ⟨r,hr⟩ := n_even
    have n_eq_2r : n = 2 * r := by
      rw [hr]
      ring
    rw [n_eq_2r]
    simp

#check two_div_even 10 ev10

theorem two_div_ten
  : 2 ∣ 10 := by
    have h := two_div_even 10 ev10
    exact h

def PrimeNum (n : ℕ) : Prop :=
  n ≥ 2 ∧ ∀ (m : ℕ), m ∣ n → m = 1 ∨ m = n

theorem notprime_1 : 
    ¬ PrimeNum 1 := by
      intro pr1
      unfold PrimeNum at pr1
      have ⟨h1, h2⟩ := pr1
      contradiction

theorem notprime_9 :
    ¬ PrimeNum 9 := by
      intro pr1
      unfold PrimeNum at pr1
      have ⟨hl, hr⟩ := pr1
      have hr_3 := hr 3
      have div : 3 ∣ 9 := by norm_num
      have or_case := hr_3 div
      rcases or_case with c1 | c2
      · contradiction
      · contradiction

theorem prime_5 :
    PrimeNum 5 := by
      unfold PrimeNum
      have hl : 5 ≥ 2 := by simp
      have hr : ∀ m : ℕ, m ∣ 5 → m = 1 ∨ m = 5 := by
        intro m m_div_5
        have h1 : 1 = 1 := by norm_num
        have h5 : 5 = 5 := by norm_num
        match m with
        | 0 => contradiction
        | 1 => exact Or.inl h1
        | 2 => contradiction
        | 3 => contradiction
        | 4 => contradiction
        | 5 => exact Or.inr h5
        | n + 6 => 
          have h6 : 5 < n + 6 := by norm_num
          have h_ := Nat.eq_zero_of_dvd_of_lt m_div_5 h6
          contradiction
      exact ⟨hl, hr⟩

#check Classical.em

#check irrational_sqrt_two

theorem irrat_pow_irrat_rat
  : ∃ (x y : ℝ), Irrational x ∧ Irrational y ∧ ¬ Irrational (x ^ y) := by
    have em := Classical.em (Irrational (√2 ^ √2))
    have irrat : Irrational √2 := by
      exact irrational_sqrt_two
    rcases em with hl | hr
    · use √2^√2, √2
      have hn : ((√2^√2) ^ √2) = 2 := by
        calc
          ((√2^√2) ^ √2) = √2 ^ (√2 * √2) := by
            have hx : 0 ≤ √2 := by simp only [Real.sqrt_nonneg]
            rw [Real.rpow_mul hx]
          _ = √2 ^ 2 := by
            rw [Real.mul_self_sqrt (by norm_num)]
            norm_num
          _ = 2 := by
            rw [Real.sq_sqrt]
            norm_num

      have rat : ¬ Irrational ((√2^√2) ^ √2) := by
        rw [hn]
        have h := Nat.not_irrational 2
        exact h
      exact ⟨hl, irrat, rat⟩
    · use √2, √2
      -- exact ⟨irrat, irrat, hr⟩
      
theorem infinites_prime
  : ∀ n : ℕ, ∃ p : Nat,
    Nat.Prime p ∧ p > n := by
      intro n
      have h_not_1 : n.factorial + 1 ≠ 1 := by
        have h := Nat.factorial_pos n
        linarith
      have prime_exist := Nat.exists_prime_and_dvd h_not_1
      obtain ⟨p, p_prime, p_dvd_nfac1⟩ := prime_exist

      use p 
      have p_notgreater : ¬ (p > n) → False := by 
        intro p_leq_n
        push_neg at p_leq_n
        have p_greater_1 : p > 1 := by
          have h := Nat.Prime.two_le p_prime
          linarith
        have p_dvd_nf : p ∣ n.factorial := by
          have h : p > 0 := by
            have h2 := p_greater_1
            linarith
          have h2 := Nat.dvd_factorial h p_leq_n
          exact h2
        have p_dvd_1 : p ∣ 1 := by
          have h := Nat.dvd_sub p_dvd_nfac1 p_dvd_nf
          have h2 : (n.factorial + 1) - n.factorial = 1 := by
            exact Nat.add_sub_cancel_left n.factorial 1
          rw [h2] at h
          exact h
        have f : 1 = 0 := by
          have h := Nat.eq_one_of_dvd_one p_dvd_1
          have h2 : 1 = 0 := by
            rw [h] at p_greater_1
            linarith
          exact h2
        contradiction
      have p_greater : p > n := by 
        have h := Classical.byContradiction p_notgreater
        exact h
      exact ⟨p_prime, p_greater⟩
#check infinites_prime

theorem example_3 (n : ℕ) (hn : n ≥ 4) : n ^ 3 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => linarith
  | succ k hk ih =>
    have h_3_gt_0 : 3 > 0 := by linarith
    have h_lt_pow_3 := Nat.mul_lt_mul_of_pos_left ih h_3_gt_0
    have h_t : 3 * 3 ^ k = 3 ^ (k + 1) := by ring
    rw [h_t] at h_lt_pow_3
    -- proof that (k + 1) ^ 3 < 3 * k ^ 3
    have h := calc
      (k + 1) ^ 3 = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by ring
      _ < k ^ 3 + k ^ 3 + k ^ 3 := by nlinarith
      _ = 3 * k ^ 3 := by ring
    exact Nat.lt_trans h h_lt_pow_3

theorem example_4 (n : ℕ) (hn : n ≥ 4) : Nat.factorial n > 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    ring_nf
    linarith
  | succ k hk ih => 
    unfold Nat.factorial
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    nlinarith

namespace TriangleNumber

def triangular_number (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), k

#eval triangular_number 20 -- expect 210

lemma closed_form_triangular (n : ℕ) : triangular_number n = n * (n + 1) / 2 := by 
  unfold triangular_number
  rw [Finset.sum_range_id (n + 1)]
  rw [Nat.add_sub_cancel]
  ring_nf

lemma odd_squared_minus_one_dvd_eight (n : ℕ) (h_odd : Odd n) : 8 ∣ n ^ 2 - 1 := by
  obtain ⟨p, rfl⟩ := Odd.exists_bit1 h_odd
  ring_nf
  have : 1 + p * 4 + p ^ 2 * 4 - 1 = p * 4 + p ^ 2 * 4 := by grind
  rw [this, ← Nat.add_mul]
  have : 8 = 2 * 4 := by ring
  rw [this, Nat.mul_dvd_mul_iff_right]
  · rw [Nat.pow_two, ← one_add_mul]
    have : Even p ∨ Even (1 + p) := by
      have : Odd p ↔  Even (1 + p) := by simp [Nat.add_comm 1 p, Nat.even_add_one]
      simpa [this] using Nat.even_or_odd p
    rcases this with hp | hp
    · exact Nat.dvd_mul_left_of_dvd (two_div_even p hp) (1 + p)
    · exact Nat.dvd_mul_right_of_dvd (two_div_even (1 + p) hp) p
  · linarith

-- P1:
-- theorem p1 (e : ℕ) (h0 : e > 0) (he : Odd e) : ∃ (k : ℕ), triangular_number k = (e ^ 2 - 1) / 8
end TriangleNumber

namespace TrigButEulerFunny

#check Complex.exp_mul_I

-- cos x from e^ix
lemma cos_x_from_exp_ix (x : Complex) :
    Complex.cos x = (Complex.exp (x * Complex.I) + Complex.exp (-x * Complex.I)) / 2 := by
      rw [Complex.exp_mul_I]
      rw [Complex.exp_mul_I]
      rw [Complex.sin_neg]
      rw [Complex.cos_neg]
      ring_nf

-- sin x from e^ix
lemma sin_x_from_exp_ix (x : Complex) :
    Complex.sin x = (Complex.exp (x * Complex.I) - Complex.exp (-x * Complex.I))
                    / (2 * Complex.I) := by
      rw [Complex.exp_mul_I]
      rw [Complex.exp_mul_I]
      rw [Complex.sin_neg]
      rw [Complex.cos_neg]
      ring_nf
      field_simp

-- tan x can be achieved by using the previous two proof. i skip because too lazy

-- sin^2 + cos^2 = 1
lemma sin_sq_add_cos_sq (x : Complex) :
    (Complex.sin x)^2 + (Complex.cos x)^2 = 1 := by
      rw [sin_x_from_exp_ix]
      rw [cos_x_from_exp_ix]
      field_simp
      simp
      ring_nf
      rw [<- Complex.exp_add]
      simp

-- sin 2*x = 2 sin x * cos x
lemma sin_two_x (x : Complex) :
    Complex.sin (2*x) = 2 * Complex.sin x * Complex.cos x := by
      rw [sin_x_from_exp_ix]
      rw [show 2 * x = x + x by ring]
      rw [sin_x_from_exp_ix]
      rw [cos_x_from_exp_ix]
      ring_nf
      have h: x * Complex.I * 2 = (x * Complex.I) + (x * Complex.I) := by ring
      rw [h]
      rw [Complex.exp_add]
      ring_nf
      have h2 : Complex.exp (-(x * Complex.I * 2)) = Complex.exp (-(x * Complex.I)) ^ 2 := by
        simp [h, Complex.exp_add]
        ring
      rw [h2]

end TrigButEulerFunny

-- let's try to reproduce arXiv:math/0211148 and arXiv:math/0508042
namespace EulerMascheroniTest

noncomputable def eulerMascheroniSeq (n : ℕ) := harmonic n - Real.log n

lemma eulerMascheroniSeq_one :
  eulerMascheroniSeq 1 = 1 := by
    rw [eulerMascheroniSeq]
    simp

noncomputable def γ := limUnder Filter.atTop eulerMascheroniSeq

noncomputable def eulerMascheroniSeq' (n : ℕ) := (-1)^(n-1) * eulerMascheroniSeq n

noncomputable def γ' (n : ℕ) := ((1/n) - Real.log ((n+1)/n))
noncomputable def ln4OverPiSeq (n : ℕ) := (-1)^(n-1) * γ' n

lemma ln_4_over_pi : Real.log (Real.pi / 4) = (∑' n, ln4OverPiSeq n) := by sorry

lemma γ_eq_sum : γ = (∑' n, γ' n) := by
  symm
  apply HasSum.tsum_eq
  unfold γ'
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · dsimp [γ]
    apply Filter.Tendsto.congr (f₁ := fun n ↦ harmonic (n - 1) - Real.log n)
    · intro n
      rw [Finset.sum_sub_distrib]
      congr
      · cases n with
        | zero =>
          simp
        | succ n =>
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero, div_zero, add_zero, Nat.add_one_sub_one]
          rw [harmonic_eq_sum_Icc]
          simp
          rw [<- Finset.Ico_add_one_right_eq_Icc]
          rw [Finset.sum_Ico_eq_sum_range]
          simp [add_comm]
      · sorry
    · sorry
  · intro n
    by_cases h : n = 0
    · rw [h]
      simp
    · rw [sub_nonneg]
      calc
        Real.log ((n + 1) / n)
        _ ≤ (n + 1) / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = 1 / n := by field_simp; ring

-- then proof that both of them equal to ∫∫ [0,1]^2 (1-x)/((1-xy)(-ln xy))
-- and we should get the first result: γ = ln (4/π)

end EulerMascheroniTest
