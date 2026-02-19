module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
let's try to reproduce arXiv:math/0211148 and arXiv:math/0508042

Goal (arXiv:math/0211148):
- [x] Definition of the sequence in terms of harmonic and natural log
- [x] Definition of γ from sequence at infinite
- [ ] Proof of γ in terms of infinite sum
- [ ] natural log of 4/π in terms of "alternating" sequence
- [ ] Proof that γ = ln 4/π
-/

/-- definition of the sequence in terms of harmonic -/
-- noncomputable def eulerMascheroniSeq (n : ℕ) := if n = 0 then 2 else harmonic n - Real.log n
noncomputable def eulerMascheroniSeq (n : ℕ) := harmonic n - Real.log n

lemma eulerMascheroniSeq_one :
  eulerMascheroniSeq 1 = 1 := by
    rw [eulerMascheroniSeq]
    simp

/-- definition of the Euler's constant -/
noncomputable def γ := limUnder Filter.atTop eulerMascheroniSeq

-- i don't know why I defined this. Probably drunk on cafeine
noncomputable def eulerMascheroniSeq' (n : ℕ) := (-1)^(n-1) * eulerMascheroniSeq n

/-- definition of the inner of infinite sum -/
noncomputable def γ' (n : ℕ) := ((1/n) - Real.log ((n+1)/n))

/-- definition of the "alternating" sequence -/
noncomputable def ln4OverPiSeq (n : ℕ) := (-1)^(n-1) * γ' n

lemma ln_4_over_pi : Real.log (Real.pi / 4) = (∑' n, ln4OverPiSeq n) := by sorry

/- TODO: rewrite this entire proof because what the fuck have i done.
why didn't i digress the paper before writing AAAAAAAAAAAAAAAAA -/
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
    · unfold eulerMascheroniSeq 
      let s : ℕ → ℝ :=
        fun n => harmonic n - Real.log n
      have :
        (fun n => harmonic (n - 1) - Real.log n)
        =
        (fun n => s n - (1 : ℝ)/n) := by
        funext n
        cases n with
        | zero => simp [s]
        | succ k =>
            simp [s, harmonic_succ]
            ring
      rw [this]
      have hzero :
        Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n)
          Filter.atTop (nhds 0) := by
            simpa [one_div] using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      have hs :
        Filter.Tendsto s Filter.atTop
          (nhds (limUnder Filter.atTop s)) :=
        -- tendsto_nhds_limUnder γ_convergence
        sorry
      simpa using hs.sub hzero
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

-- then proof that both of them equal to ∫∫ [0,1]^2 (1-x)/((1-xy)(-ln xy))
-- and we should get the first result: γ = ln (4/π)
