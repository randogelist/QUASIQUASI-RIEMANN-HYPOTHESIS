import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A scalar little-o limit engine

This module proves an implication between explicitly supplied scalar analytic
inputs.  It does not identify `I`, the cutoff sum `S`, or the constants with a
native zeta-function construction, and does not assert the Riemann hypothesis.
-/

open Filter Asymptotics
open scoped Topology

namespace RHScalarLittleO

/-- Approach zero through positive real arguments. -/
def zeroRight : Filter ℝ := 𝓝[>] (0 : ℝ)

instance zeroRight_neBot : NeBot zeroRight := by
  unfold zeroRight
  infer_instance

theorem tendsto_id_zeroRight :
    Tendsto (fun r : ℝ => r) zeroRight (𝓝 0) := by
  change Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0)
  exact tendsto_id.mono_left nhdsWithin_le_nhds

theorem eventually_pos_zeroRight : ∀ᶠ r in zeroRight, 0 < r := by
  change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
  exact self_mem_nhdsWithin

/-- A finite limit for `I r / r` already implies that `I r` tends to zero. -/
theorem integral_tendsto_zero_of_normalized
    (I : ℝ → ℝ) (q : ℝ)
    (hI : Tendsto (fun r => I r / r) zeroRight (𝓝 (Real.pi * q))) :
    Tendsto I zeroRight (𝓝 0) := by
  have hprod : Tendsto (fun r => r * (I r / r)) zeroRight
      (𝓝 ((0 : ℝ) * (Real.pi * q))) :=
    tendsto_id_zeroRight.mul hI
  have heq : (fun r => r * (I r / r)) =ᶠ[zeroRight] I := by
    filter_upwards [eventually_pos_zeroRight] with r hr
    field_simp [ne_of_gt hr]
  have hlimit := Filter.Tendsto.congr' heq hprod
  simpa using hlimit

/-- The little-o residual and the normalized integral limit force cutoff saturation.

No convergence hypothesis on the cutoff function `S` is required.
-/
theorem cutoff_tendsto_of_normalized_integral_and_isLittleO
    (I S : ℝ → ℝ) (q : ℝ)
    (hI : Tendsto (fun r => I r / r) zeroRight (𝓝 (Real.pi * q)))
    (hLittleO : (fun r => I r - Real.pi * r * S r)
      =o[zeroRight] (fun r : ℝ => r)) :
    Tendsto S zeroRight (𝓝 q) := by
  have hquot : Tendsto (fun r => (I r - Real.pi * r * S r) / r)
      zeroRight (𝓝 0) := hLittleO.tendsto_div_nhds_zero
  have hproxy : Tendsto
      (fun r => ((I r / r) - ((I r - Real.pi * r * S r) / r)) / Real.pi)
      zeroRight (𝓝 ((Real.pi * q - 0) / Real.pi)) :=
    (hI.sub hquot).div tendsto_const_nhds Real.pi_ne_zero
  have heval : (Real.pi * q - 0) / Real.pi = q := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [heval] at hproxy
  have heq :
      (fun r => ((I r / r) - ((I r - Real.pi * r * S r) / r)) / Real.pi)
      =ᶠ[zeroRight] S := by
    filter_upwards [eventually_pos_zeroRight] with r hr
    field_simp [ne_of_gt hr, Real.pi_ne_zero]
    ring
  exact Filter.Tendsto.congr' heq hproxy

/-- The residual scalar `q - S r` therefore tends to zero. -/
theorem residual_tendsto_zero_of_normalized_integral_and_isLittleO
    (I S : ℝ → ℝ) (q : ℝ)
    (hI : Tendsto (fun r => I r / r) zeroRight (𝓝 (Real.pi * q)))
    (hLittleO : (fun r => I r - Real.pi * r * S r)
      =o[zeroRight] (fun r : ℝ => r)) :
    Tendsto (fun r => q - S r) zeroRight (𝓝 0) := by
  have hS := cutoff_tendsto_of_normalized_integral_and_isLittleO I S q hI hLittleO
  have hres : Tendsto (fun r => q - S r) zeroRight (𝓝 (q - q)) :=
    tendsto_const_nhds.sub hS
  simpa using hres

/-- An eventually linear integral tends to zero, without a little-o input. -/
theorem integral_tendsto_zero
    (I : ℝ → ℝ) (q : ℝ)
    (hI : I =ᶠ[zeroRight] fun r => Real.pi * r * q) :
    Tendsto I zeroRight (𝓝 0) := by
  have hlinear : Tendsto (fun r : ℝ => Real.pi * r * q)
      zeroRight (𝓝 (Real.pi * 0 * q)) :=
    (tendsto_const_nhds.mul tendsto_id_zeroRight).mul tendsto_const_nhds
  have hzero : Tendsto (fun r : ℝ => Real.pi * r * q)
      zeroRight (𝓝 0) := by simpa using hlinear
  exact Filter.Tendsto.congr' hI.symm hzero

/-- The normalized residual has the limit dictated by `hI` and `hS`. -/
theorem residual_div_tendsto
    (I S : ℝ → ℝ) (q SInf : ℝ)
    (hI : I =ᶠ[zeroRight] fun r => Real.pi * r * q)
    (hS : Tendsto S zeroRight (𝓝 SInf)) :
    Tendsto (fun r => (I r - Real.pi * r * S r) / r)
      zeroRight (𝓝 (Real.pi * (q - SInf))) := by
  have heq : (fun r => (I r - Real.pi * r * S r) / r)
      =ᶠ[zeroRight] (fun r => Real.pi * (q - S r)) := by
    filter_upwards [hI, eventually_pos_zeroRight] with r hir hr
    rw [hir]
    field_simp [ne_of_gt hr]
  have hlimit : Tendsto (fun r => Real.pi * (q - S r))
      zeroRight (𝓝 (Real.pi * (q - SInf))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hS)
  exact Filter.Tendsto.congr' heq.symm hlimit

/-- An actual Mathlib little-o hypothesis forces saturation of the cutoff sum. -/
theorem q_eq_SInf_of_isLittleO
    (I S : ℝ → ℝ) (q SInf : ℝ)
    (hI : I =ᶠ[zeroRight] fun r => Real.pi * r * q)
    (hS : Tendsto S zeroRight (𝓝 SInf))
    (hLittleO : (fun r => I r - Real.pi * r * S r)
      =o[zeroRight] (fun r : ℝ => r)) :
    q = SInf := by
  have hquot : Tendsto (fun r => (I r - Real.pi * r * S r) / r)
      zeroRight (𝓝 0) := hLittleO.tendsto_div_nhds_zero
  have hconstant : Real.pi * (q - SInf) = 0 :=
    tendsto_nhds_unique (residual_div_tendsto I S q SInf hI hS) hquot
  have hdiff : q - SInf = 0 :=
    (mul_eq_zero.mp hconstant).resolve_left Real.pi_ne_zero
  exact sub_eq_zero.mp hdiff

end RHScalarLittleO
