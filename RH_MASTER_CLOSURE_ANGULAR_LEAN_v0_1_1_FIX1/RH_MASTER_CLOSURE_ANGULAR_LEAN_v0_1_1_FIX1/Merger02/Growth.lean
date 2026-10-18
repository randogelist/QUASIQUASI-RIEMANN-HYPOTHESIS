import Merger02.Envelope

namespace Merger02
open Filter
open scoped Topology

/-- A real-base version of the cofinal finite-row condition. -/
def CofinalSubexponential (H : ℕ → ℝ) : Prop :=
  ∀ b : ℝ, 1 < b → ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ H N ≤ b ^ N

/-- Literal logarithmic condition from the forward-proof note. -/
def LogCofinalSubexponential (H : ℕ → ℝ) : Prop :=
  ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧
    Tendsto (fun j => Real.log (1 + H (n j)) / (n j : ℝ)) atTop (𝓝 0)

/-- The positive constant cannot be silently dropped. -/
def EventualExponential (H : ℕ → ℝ) : Prop :=
  ∃ c b : ℝ, 0 < c ∧ 1 < b ∧
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * b ^ N ≤ H N

/-- Every strictly smaller exponential eventually absorbs the prefactor. -/
theorem eventually_pow_lt_const_mul_pow
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, a ^ N < c * b ^ N := by
  have hb : 0 < b := lt_trans ha hab
  have hratio : 0 ≤ a / b := le_of_lt (div_pos ha hb)
  have hratio1 : a / b < 1 := (div_lt_one hb).2 hab
  have ht : Tendsto (fun N : ℕ => (a / b) ^ N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1
  have hev : ∀ᶠ N : ℕ in atTop, (a / b) ^ N < c :=
    ht.eventually (gt_mem_nhds hc)
  filter_upwards [hev] with N hN
  have hp : 0 < b ^ N := pow_pos hb N
  rw [div_pow] at hN
  exact (div_lt_iff₀ hp).1 hN

/-- Sparse upper bounds contradict growth at every sufficiently large depth. -/
theorem cofinal_excludes_eventual_exponential {H : ℕ → ℝ}
    (hUS : CofinalSubexponential H) : ¬ EventualExponential H := by
  rintro ⟨c, b, hc, hb, M, hM⟩
  let a : ℝ := (1 + b) / 2
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  have ha : 0 < a := lt_trans zero_lt_one ha1
  have hev := eventually_pow_lt_const_mul_pow ha hab hc
  obtain ⟨K, hK⟩ := (eventually_atTop.1 hev)
  obtain ⟨N, hN, hu⟩ := hUS a ha1 (max M K)
  have hMN : M ≤ N := le_trans (le_max_left _ _) hN
  have hKN : K ≤ N := le_trans (le_max_right _ _) hN
  exact (not_lt_of_ge (le_trans (hM N hMN) hu)) (hK N hKN)

/-- Converts the logarithmic input without changing the actual energy. -/
theorem logCofinal_implies_cofinal {H : ℕ → ℝ}
    (hH : ∀ N, 0 ≤ H N) (hUS : LogCofinalSubexponential H) :
    CofinalSubexponential H := by
  rcases hUS with ⟨n, hn, hlog⟩
  intro b hb M
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hsmall : ∀ᶠ j : ℕ in atTop,
      Real.log (1 + H (n j)) / (n j : ℝ) < Real.log b :=
    hlog.eventually (gt_mem_nhds hlogb)
  have hlarge : ∀ᶠ j : ℕ in atTop, max M 1 ≤ n j :=
    hn.eventually (eventually_ge_atTop (max M 1))
  obtain ⟨j, hj, hjlarge⟩ := (hsmall.and hlarge).exists
  have hM : M ≤ n j := le_trans (le_max_left _ _) hjlarge
  have hn1 : 1 ≤ n j := le_trans (le_max_right _ _) hjlarge
  have hnpos : 0 < (n j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hmul : Real.log (1 + H (n j)) < Real.log b * (n j : ℝ) :=
    (div_lt_iff₀ hnpos).1 hj
  have hbound : 1 + H (n j) < b ^ n j := by
    have hleft : 0 < 1 + H (n j) := by linarith [hH (n j)]
    have hright : 0 < b ^ n j := pow_pos hb0 _
    apply (Real.log_lt_log_iff hleft hright).1
    simpa [Real.log_pow, mul_comm] using hmul
  exact ⟨n j, hM, by linarith⟩

abbrev ActualUS : Prop := LogCofinalSubexponential actualEnergy
abbrev ActualUSRows : Prop := CofinalSubexponential actualEnergy

/-- This named proposition is an UNIMPLEMENTED analytic bridge in this
native package, not a theorem or a global declaration of an assumption. -/
def ActualPoleGrowthStatement : Prop :=
  ∀ rho : ℂ, NontrivialZero rho → rho.re ≠ (1 / 2 : ℝ) →
    EventualExponential actualEnergy

/-- Explicit two-input result. This is NOT the desired one-input theorem. -/
theorem US_ENERGY_IMPLIES_RH_GIVEN_POLE_GROWTH
    (hGrowth : ActualPoleGrowthStatement) (hUS : ActualUS) :
    _root_.RiemannHypothesis := by
  have hRows : ActualUSRows := logCofinal_implies_cofinal actualEnergy_nonneg hUS
  unfold _root_.RiemannHypothesis
  intro rho hz htrivial hneOne
  by_contra hOff
  exact cofinal_excludes_eventual_exponential hRows
    (hGrowth rho ⟨hz, htrivial, hneOne⟩ hOff)

end Merger02
