module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

noncomputable def infiniteSumTerm (n : ℕ) := ((1/n) - Real.log ((n+1)/n))

/- TODO: rewrite this entire proof because what the fuck have i done.
why didn't i digress the paper before writing AAAAAAAAAAAAAAAAA -/
lemma eulerMascheroniConstant_eq_sum :
    Real.eulerMascheroniConstant = (∑' n, infiniteSumTerm n) := by
  symm
  apply HasSum.tsum_eq
  unfold infiniteSumTerm
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · apply Filter.Tendsto.congr (f₁ := fun n ↦ harmonic (n - 1) - Real.log n)
    · intro n
      rw [Finset.sum_sub_distrib]
      congr
      · cases n with
        | zero => simp
        | succ n =>
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero, div_zero, add_zero, Nat.add_one_sub_one]
          rw [harmonic_eq_sum_Icc, <- Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
          simp [add_comm]
      · induction n with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_range_succ, <- ih]
          rcases n.eq_zero_or_pos with rfl | hn
          · simp
          · rw [Real.log_div]
            · simp
            · positivity 
            · positivity
    · have hshift :
        Filter.Tendsto (fun n : ℕ ↦ n - 1) Filter.atTop Filter.atTop :=
        Filter.tendsto_sub_atTop_nat 1
      have h :=
        Real.tendsto_harmonic_sub_log_add_one.comp hshift
      simp at h
      refine h.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnat : (n - 1) + 1 = n :=
        Nat.sub_add_cancel hn
      have hreal : (↑(n - 1) : ℝ) + 1 = (n : ℝ) := by
        simpa [Nat.cast_add] using congrArg (fun k : ℕ => (k : ℝ)) hnat
      simp [hreal]
  · intro n
    by_cases h : n = 0
    · rw [h]
      simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h
      have hlog : Real.log ((n + 1 : ℝ) / n) ≤ 1 / n := by
        calc
          Real.log ((n + 1 : ℝ) / n)
            ≤ (n + 1 : ℝ) / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = 1 / n := by
            field_simp
            ring
      exact sub_nonneg.mpr hlog
