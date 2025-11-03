import Mathlib

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
