import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

theorem digamma_gauss_theorem (x : ℚ) (h1 : x > 0) (h2 : x < 1) :
    Complex.digamma (x) =
      -Real.eulerMascheroniConstant - Real.log (2*x.den)
      - (Real.pi / 2) * Real.cot (x * Real.pi)
      + 2 * ∑ n ∈ Finset.Icc 1 (⌈(x.den : ℚ)/2⌉ - 1) ,
                  (Real.cos ((2 * Real.pi * x.num * n) / x.den)
                    * Real.log (Real.sin ((Real.pi * n) / x.den)))
    := by
      sorry

lemma digamma_one_fourth :
    Complex.digamma (1/4) = -Real.eulerMascheroniConstant -3 * Real.log 2 - Real.pi / 2 := by
      have this := digamma_gauss_theorem (1/4) (by norm_num) (by norm_num)
      simp at this
      ring_nf at this
      rw [show Real.log 8 = 3 * Real.log 2 by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num];
          exact Real.log_pow 2 3,
        Finset.Icc_self,
        Finset.sum_singleton] at this
      simp only [Int.sign] at this
      norm_cast at this
      ring_nf at this
      simp only [mul_one_div, Complex.cos_pi_div_two, zero_mul, mul_comm, add_zero] at this
      norm_cast at this
      rw [<-Real.tan_inv_eq_cot, Real.tan_pi_div_four] at this
      simp only [Rat.divInt] at this
      norm_cast at this
      rw [show Int.negSucc 0 = -1 by simp, show mkRat (-1) 2 = -(1/2) by ring] at this
      rw [show (1 : ℝ)⁻¹ = 1 by ring, inline.eq_1, mul_one] at this
      rw [show Real.pi * ((-(1 / 2) : ℚ) : ℝ) = -(Real.pi / 2) by ring] at this
      push_cast at this
      simp only [sub_eq_add_neg] at this
      simp only [sub_eq_add_neg]
      exact this

#check digamma_gauss_theorem
#check digamma_one_fourth
