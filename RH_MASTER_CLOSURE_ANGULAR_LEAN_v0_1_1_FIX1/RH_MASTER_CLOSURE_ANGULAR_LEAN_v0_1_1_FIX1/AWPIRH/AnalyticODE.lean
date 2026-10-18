import Mathlib

/-!
A denominator-free analytic ODE cannot develop a zero from a nonzero anchor.
The proof uses vanishing orders, not an assumed global logarithm.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

theorem analytic_ode_nonvanishing
    {U : Set ℂ} (hopen : IsOpen U) (hconn : IsPreconnected U)
    {Y A : ℂ → ℂ} (hY : AnalyticOnNhd ℂ Y U) (hA : AnalyticOnNhd ℂ A U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hY₀ : Y z₀ ≠ 0)
    (hode : ∀ z ∈ U, deriv Y z = A z * Y z) :
    ∀ z ∈ U, Y z ≠ 0 := by
  intro z hz hzero
  have ho₀ : analyticOrderAt Y z₀ = 0 :=
    (hY z₀ hz₀).analyticOrderAt_eq_zero.mpr hY₀
  have hfin₀ : analyticOrderAt Y z₀ ≠ ⊤ := by simp [ho₀]
  have hfinite : analyticOrderAt Y z ≠ ⊤ :=
    hY.analyticOrderAt_ne_top_of_isPreconnected hconn hz₀ hz hfin₀
  have hd : analyticOrderAt (deriv Y) z + 1 = analyticOrderAt Y z := by
    simpa [hzero] using (hY z hz).analyticOrderAt_deriv_add_one
  have hevent : deriv Y =ᶠ[𝓝 z] (fun w => A w * Y w) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact hode w hw
  have hm : analyticOrderAt (deriv Y) z =
      analyticOrderAt A z + analyticOrderAt Y z := by
    calc
      _ = analyticOrderAt (fun w => A w * Y w) z := analyticOrderAt_congr hevent
      _ = _ := analyticOrderAt_mul (hA z hz) (hY z hz)
  have hle : analyticOrderAt Y z ≤ analyticOrderAt (deriv Y) z := by
    rw [hm]
    simpa using add_le_add_right
      (show (0 : ℕ∞) ≤ analyticOrderAt A z from bot_le) (analyticOrderAt Y z)
  have hbad : analyticOrderAt Y z + 1 ≤ analyticOrderAt Y z := by
    calc
      _ ≤ analyticOrderAt (deriv Y) z + 1 := add_le_add_left hle 1
      _ = _ := hd
  generalize hq : analyticOrderAt Y z = q at hbad hfinite
  lift q to ℕ using hfinite with n hn
  norm_cast at hbad
  omega

/-- A locally proved ODE extends after clearing the unknown function's denominator. -/
theorem analytic_local_ode_nonvanishing
    {U : Set ℂ} (hopen : IsOpen U) (hconn : IsPreconnected U)
    {Y A : ℂ → ℂ} (hY : AnalyticOnNhd ℂ Y U) (hA : AnalyticOnNhd ℂ A U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hY₀ : Y z₀ ≠ 0)
    (hlocal : ∀ᶠ z in 𝓝 z₀, deriv Y z + A z * Y z = 0) :
    ∀ z ∈ U, Y z ≠ 0 := by
  have hE : AnalyticOnNhd ℂ (fun z => deriv Y z + A z * Y z) U := by
    intro z hz
    exact (hY z hz).deriv.add ((hA z hz).mul (hY z hz))
  have hzero : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) U := by
    intro z hz
    exact analyticAt_const
  have heq : Set.EqOn (fun z => deriv Y z + A z * Y z) (fun _ => (0 : ℂ)) U :=
    hE.eqOn_of_preconnected_of_eventuallyEq hzero hconn hz₀ hlocal
  have hneg : AnalyticOnNhd ℂ (fun z => -A z) U := by
    intro z hz
    exact (hA z hz).neg
  apply analytic_ode_nonvanishing hopen hconn hY hneg hz₀ hY₀
  intro z hz
  have h := heq hz
  change deriv Y z = -A z * Y z
  linear_combination h

end AWPIRH
