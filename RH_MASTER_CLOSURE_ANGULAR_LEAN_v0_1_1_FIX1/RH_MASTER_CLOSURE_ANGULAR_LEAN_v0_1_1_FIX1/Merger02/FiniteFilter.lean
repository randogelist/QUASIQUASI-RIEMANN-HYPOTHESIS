import Merger02.RowRefinement
import Merger02.Growth

/-!
A finite backward filter cannot hide exponential growth from the actual row
energy. Its coefficients may have either sign or be complex. The input is a
quantified coefficient estimate, not a declaration of the desired conclusion.
-/
namespace Merger02
open Filter
open scoped BigOperators Topology

noncomputable def filteredRow (s : ℕ → ℂ) (d : ℕ) (q : ℕ → ℂ)
    (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), q j * rowPolynomial s (N - j) z

noncomputable def filterMass (d : ℕ) (q : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), ‖q j‖

theorem filterMass_nonneg (d : ℕ) (q : ℕ → ℂ) : 0 ≤ filterMass d q := by
  unfold filterMass
  positivity

theorem filterMass_one_le {d : ℕ} {q : ℕ → ℂ} (hq : q 0 = 1) :
    1 ≤ filterMass d q := by
  have h := Finset.single_le_sum (f := fun j => ‖q j‖)
    (fun j _ => norm_nonneg (q j))
    (show 0 ∈ Finset.range (d + 1) by simp)
  simpa [filterMass, hq] using h

theorem filteredRow_norm_le_sqrt_energy (s : ℕ → ℂ) (d : ℕ) (q : ℕ → ℂ)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖filteredRow s d q N z‖ ≤ filterMass d q * Real.sqrt (energy s N) := by
  unfold filteredRow filterMass
  calc
    _ ≤ ∑ j ∈ Finset.range (d + 1), ‖q j * rowPolynomial s (N - j) z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (d + 1), ‖q j‖ * Real.sqrt (energy s N) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (earlier_rowPolynomial_norm_le_sqrt_energy s (Nat.sub_le N j) hz)
        (norm_nonneg (q j))
    _ = _ := by rw [Finset.sum_mul]

theorem filteredRow_norm_sq_le_energy (s : ℕ → ℂ) (d : ℕ) (q : ℕ → ℂ)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖filteredRow s d q N z‖ ^ 2 ≤ (filterMass d q) ^ 2 * energy s N := by
  have h := filteredRow_norm_le_sqrt_energy s d q N hz
  have h0 := filterMass_nonneg d q
  have h1 := Real.sqrt_nonneg (energy s N)
  have h2 := Real.sq_sqrt (energy_nonneg s N)
  have h3 : 0 ≤ filterMass d q * Real.sqrt (energy s N) := mul_nonneg h0 h1
  have hs : ‖filteredRow s d q N z‖ ^ 2 ≤
      (filterMass d q * Real.sqrt (energy s N)) ^ 2 := by
    nlinarith [norm_nonneg (filteredRow s d q N z)]
  simpa [mul_pow, h2] using hs

/-- The finite-filter analogue of the old single-dominant-pole expansion. -/
def FilteredExpansion (s : ℕ → ℂ) : Prop :=
  ∃ (z A lam : ℂ) (d : ℕ) (q : ℕ → ℂ),
    ‖z‖ ≤ 1 ∧ A ≠ 0 ∧ 1 < ‖lam‖ ∧ q 0 = 1 ∧
    Tendsto (fun N : ℕ =>
      ‖filteredRow s d q N z - A * lam ^ N‖ / ‖lam‖ ^ N) atTop (𝓝 0)

theorem filteredExpansion_implies_eventual_exponential
    {s : ℕ → ℂ} (h : FilteredExpansion s) : EventualExponential (energy s) := by
  rcases h with ⟨z, A, lam, d, q, hz, hA, hlam, hq, hlim⟩
  let L := filterMass d q
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (filterMass_one_le hq)
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hhalf : 0 < ‖A‖ / 2 := by positivity
  have hlam0 : 0 < ‖lam‖ := lt_trans zero_lt_one hlam
  have hev : ∀ᶠ N : ℕ in atTop,
      ‖filteredRow s d q N z - A * lam ^ N‖ / ‖lam‖ ^ N < ‖A‖ / 2 :=
    hlim.eventually (gt_mem_nhds hhalf)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨(‖A‖ / 2) ^ 2 / L ^ 2, ‖lam‖ ^ 2, by positivity, ?_, M, ?_⟩
  · nlinarith
  · intro N hN
    have hp : 0 < ‖lam‖ ^ N := pow_pos hlam0 N
    have herr : ‖filteredRow s d q N z - A * lam ^ N‖ <
        (‖A‖ / 2) * ‖lam‖ ^ N := (div_lt_iff₀ hp).mp (hM N hN)
    have htri : ‖A‖ * ‖lam‖ ^ N ≤
        ‖filteredRow s d q N z‖ + ‖filteredRow s d q N z - A * lam ^ N‖ := by
      calc
        _ = ‖A * lam ^ N‖ := by rw [norm_mul, norm_pow]
        _ = ‖filteredRow s d q N z - (filteredRow s d q N z - A * lam ^ N)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_sub_le _ _
    have hlower : (‖A‖ / 2) * ‖lam‖ ^ N ≤ ‖filteredRow s d q N z‖ := by
      linarith
    have hlow0 : 0 ≤ (‖A‖ / 2) * ‖lam‖ ^ N := by positivity
    have hsq : ((‖A‖ / 2) * ‖lam‖ ^ N) ^ 2 ≤
        ‖filteredRow s d q N z‖ ^ 2 := by
      nlinarith [norm_nonneg (filteredRow s d q N z)]
    have hen : ‖filteredRow s d q N z‖ ^ 2 ≤ L ^ 2 * energy s N :=
      filteredRow_norm_sq_le_energy s d q N hz
    have hpow : (‖lam‖ ^ 2) ^ N = (‖lam‖ ^ N) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    calc
      (‖A‖ / 2) ^ 2 / L ^ 2 * (‖lam‖ ^ 2) ^ N =
          ((‖A‖ / 2) * ‖lam‖ ^ N) ^ 2 / L ^ 2 := by
        rw [hpow, mul_pow]
        ring
      _ ≤ energy s N := (div_le_iff₀ hL2).mpr (by nlinarith [hsq, hen])

/-- Precise geometric remainder estimate which Cauchy's theorem must deliver.
The expansion and envelope are both tied to the unchanged sequence s. -/
def FiniteFilterEstimate (s : ℕ → ℂ) : Prop :=
  ∃ (z A lam : ℂ) (d : ℕ) (q : ℕ → ℂ) (M r : ℝ),
    ‖z‖ ≤ 1 ∧ A ≠ 0 ∧ 1 < ‖lam‖ ∧ q 0 = 1 ∧
    0 ≤ M ∧ 0 ≤ r ∧ r < ‖lam‖ ∧
    ∀ N : ℕ, d ≤ N → ‖filteredRow s d q N z - A * lam ^ N‖ ≤ M * r ^ N

theorem finiteFilterEstimate_implies_filteredExpansion {s : ℕ → ℂ}
    (h : FiniteFilterEstimate s) : FilteredExpansion s := by
  rcases h with ⟨z, A, lam, d, q, M, r, hz, hA, hlam, hq, hM, hr, hrL, herr⟩
  refine ⟨z, A, lam, d, q, hz, hA, hlam, hq, ?_⟩
  have hL : 0 < ‖lam‖ := lt_trans zero_lt_one hlam
  have hrat : 0 ≤ r / ‖lam‖ := div_nonneg hr hL.le
  have hrat1 : r / ‖lam‖ < 1 := (div_lt_one hL).mpr hrL
  have hgeo : Tendsto (fun N : ℕ => M * (r / ‖lam‖) ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hrat hrat1).const_mul M
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N => lt_of_lt_of_le ha
      (div_nonneg (norm_nonneg _) (pow_nonneg hL.le N)))
  · intro b hb
    have hev := hgeo.eventually (gt_mem_nhds hb)
    filter_upwards [eventually_ge_atTop d, hev] with N hNd hNb
    have hupper :
        ‖filteredRow s d q N z - A * lam ^ N‖ / ‖lam‖ ^ N ≤
          M * (r / ‖lam‖) ^ N := by
      calc
        _ ≤ (M * r ^ N) / ‖lam‖ ^ N :=
          div_le_div_of_nonneg_right (herr N hNd) (pow_nonneg hL.le N)
        _ = _ := by rw [div_pow]; ring
    exact lt_of_le_of_lt hupper hNb

theorem finiteFilterEstimate_implies_eventual_exponential {s : ℕ → ℂ}
    (h : FiniteFilterEstimate s) : EventualExponential (energy s) :=
  filteredExpansion_implies_eventual_exponential
    (finiteFilterEstimate_implies_filteredExpansion h)

/-- Unimplemented analytic coefficient-extraction statement. Its explicit
appearance in the conditional endpoint is mandatory until a proof is added. -/
def ActualFiniteFilterStatement : Prop :=
  ∀ rho : ℂ, NontrivialZero rho → rho.re ≠ (1 / 2 : ℝ) →
    FiniteFilterEstimate actualJet

theorem actualGrowth_of_actualFiniteFilter
    (hFilter : ActualFiniteFilterStatement) : ActualPoleGrowthStatement := by
  intro rho hz hOff
  exact finiteFilterEstimate_implies_eventual_exponential (hFilter rho hz hOff)

theorem US_ENERGY_IMPLIES_RH_GIVEN_FINITE_FILTER
    (hFilter : ActualFiniteFilterStatement) (hUS : ActualUS) :
    _root_.RiemannHypothesis :=
  US_ENERGY_IMPLIES_RH_GIVEN_POLE_GROWTH (actualGrowth_of_actualFiniteFilter hFilter) hUS

theorem NOT_RH_IMPLIES_NOT_US_GIVEN_FINITE_FILTER
    (hFilter : ActualFiniteFilterStatement) (hNotRH : ¬ _root_.RiemannHypothesis) :
    ¬ ActualUS :=
  fun hUS => hNotRH (US_ENERGY_IMPLIES_RH_GIVEN_FINITE_FILTER hFilter hUS)

end Merger02
