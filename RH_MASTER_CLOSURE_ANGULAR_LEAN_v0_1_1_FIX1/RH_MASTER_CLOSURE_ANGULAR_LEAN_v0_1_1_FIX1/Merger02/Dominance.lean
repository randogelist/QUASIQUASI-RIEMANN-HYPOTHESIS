import Merger02.Growth

namespace Merger02
open Filter
open scoped Topology

/-- A normalized asymptotic expansion at one fixed interior phase. This
records exactly what pole subtraction and Cauchy estimates must supply. -/
def DominantExpansion (s : ℕ → ℂ) : Prop :=
  ∃ z A lam : ℂ, ‖z‖ ≤ 1 ∧ A ≠ 0 ∧ 1 < ‖lam‖ ∧
    Tendsto (fun N : ℕ =>
      ‖rowPolynomial s N z - A * lam ^ N‖ / ‖lam‖ ^ N)
      atTop (𝓝 0)

/-- The key 'every sufficiently large depth' conclusion, proved from a
single genuinely dominant expansion rather than from a limsup statement. -/
theorem dominantExpansion_implies_eventual_exponential
    {s : ℕ → ℂ} (h : DominantExpansion s) : EventualExponential (energy s) := by
  rcases h with ⟨z, A, lam, hz, hA, hlam, hlim⟩
  have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hhalf : 0 < ‖A‖ / 2 := by positivity
  have hL : 0 < ‖lam‖ := lt_trans zero_lt_one hlam
  have hev : ∀ᶠ N : ℕ in atTop,
      ‖rowPolynomial s N z - A * lam ^ N‖ / ‖lam‖ ^ N < ‖A‖ / 2 :=
    hlim.eventually (gt_mem_nhds hhalf)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨(‖A‖ / 2) ^ 2, ‖lam‖ ^ 2, by positivity, ?_, M, ?_⟩
  · nlinarith
  · intro N hN
    have hpow : 0 < ‖lam‖ ^ N := pow_pos hL N
    have herr : ‖rowPolynomial s N z - A * lam ^ N‖ <
        (‖A‖ / 2) * ‖lam‖ ^ N :=
      (div_lt_iff₀ hpow).1 (hM N hN)
    have htri : ‖A‖ * ‖lam‖ ^ N ≤
        ‖rowPolynomial s N z‖ + ‖rowPolynomial s N z - A * lam ^ N‖ := by
      calc
        ‖A‖ * ‖lam‖ ^ N = ‖A * lam ^ N‖ := by rw [norm_mul, norm_pow]
        _ = ‖rowPolynomial s N z - (rowPolynomial s N z - A * lam ^ N)‖ := by
          congr 1
          ring
        _ ≤ ‖rowPolynomial s N z‖ +
            ‖rowPolynomial s N z - A * lam ^ N‖ := norm_sub_le _ _
    have hlower : (‖A‖ / 2) * ‖lam‖ ^ N ≤ ‖rowPolynomial s N z‖ := by
      nlinarith
    have hleft : 0 ≤ (‖A‖ / 2) * ‖lam‖ ^ N := by positivity
    have hsquare : ((‖A‖ / 2) * ‖lam‖ ^ N) ^ 2 ≤
        ‖rowPolynomial s N z‖ ^ 2 := by
      nlinarith [norm_nonneg (rowPolynomial s N z)]
    have hident : (‖A‖ / 2) ^ 2 * (‖lam‖ ^ 2) ^ N =
        ((‖A‖ / 2) * ‖lam‖ ^ N) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hident]
    exact le_trans hsquare (rowPolynomial_norm_sq_le_energy s N hz)

/-- This is the remaining actual meromorphic-analytic FORMALIZATION target. -/
def ActualDominantExpansionStatement : Prop :=
  ∀ rho : ℂ, NontrivialZero rho → rho.re ≠ (1 / 2 : ℝ) →
    DominantExpansion actualJet

theorem actualGrowth_of_actualExpansion
    (hExpansion : ActualDominantExpansionStatement) : ActualPoleGrowthStatement := by
  intro rho hz hOff
  exact dominantExpansion_implies_eventual_exponential (hExpansion rho hz hOff)

/-- Still two explicit inputs: no assertion that the actual expansion has
already been constructed is made in this native source. -/
theorem US_ENERGY_IMPLIES_RH_GIVEN_DOMINANT_EXPANSION
    (hExpansion : ActualDominantExpansionStatement) (hUS : ActualUS) :
    _root_.RiemannHypothesis :=
  US_ENERGY_IMPLIES_RH_GIVEN_POLE_GROWTH (actualGrowth_of_actualExpansion hExpansion) hUS

end Merger02
