import AWPIRH.RowAnalytic
import AWPIRH.ProductGeometry
import AWPIRH.AnalyticODE

/-!
INCOMPLETE NATIVE ASSEMBLY -- this is NOT the requested premise-minimal theorem.
The two concrete analytic interfaces below are declared as propositions only.
No proof of either is supplied, neither is postulated, and neither is hidden in US.
This file demonstrates how the already implemented blocks connect once the
remaining analytic translations have been completed.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

/-- Native translation still pending: symmetric-product entire analyticity. -/
def ActualProductEntire : Prop :=
  AnalyticOnNhd ℂ symmetricProduct Set.univ

/--
Native translation still pending: actual Mellin-to-xi / all-depth Widder
identification and the finite row transform must prove this LOCAL identity.
This is the cleared local differential identity, not a global zero-free input.
-/
def ActualLocalRowODE : Prop :=
  ∀ η : ℂ, ‖η‖ = 1 →
    ∀ᶠ v in 𝓝 (0 : ℂ),
      deriv (fun w : ℂ => symmetricProduct (phaseMap η w)) v +
        (((η - 1) / (1 - v)) * rowAnalyticSum nativeCoefficients η v) *
          symmetricProduct (phaseMap η v) = 0

theorem phaseMap_analyticAt (η : ℂ) {v : ℂ} (hv : v ∈ unitDisc) :
    AnalyticAt ℂ (phaseMap η) v := by
  have hd := one_sub_ne_zero_of_mem_unitDisc hv
  unfold phaseMap
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact hd

/--
PARTIAL ASSEMBLY with both extra parameters deliberately visible.
This is not AWPIRH_US_IMPLIES_MATHLIB_RH and must not be reported as that theorem.
-/
theorem MATHLIB_RH_OF_US_AND_TWO_ANALYTIC_BINDINGS
    (hUS : US_AWPI)
    (hEntire : ActualProductEntire)
    (hLocal : ActualLocalRowODE) :
    _root_.RiemannHypothesis := by
  apply MATHLIB_RH_OF_PRODUCT_NONVANISHING
  intro r hr
  obtain ⟨η, v, hη, hv, hmap⟩ := phase_cover hr
  let Y : ℂ → ℂ := fun w => symmetricProduct (phaseMap η w)
  let A : ℂ → ℂ := fun w =>
    ((η - 1) / (1 - w)) * rowAnalyticSum nativeCoefficients η w
  have hY : AnalyticOnNhd ℂ Y unitDisc := by
    intro w hw
    have hp : AnalyticAt ℂ symmetricProduct (phaseMap η w) :=
      hEntire _ (Set.mem_univ _)
    exact AnalyticAt.fun_comp (g := symmetricProduct) (f := phaseMap η)
      (x := w) hp (phaseMap_analyticAt η hw)
  have hrow := US_AWPI_IMPLIES_ACTUAL_ROW_ANALYTIC hUS (le_of_eq hη)
  have hA : AnalyticOnNhd ℂ A unitDisc := by
    intro w hw
    have hden := one_sub_ne_zero_of_mem_unitDisc hw
    have hfrac : AnalyticAt ℂ (fun u : ℂ => (η - 1) / (1 - u)) w := by
      apply AnalyticAt.div
      · exact analyticAt_const
      · fun_prop
      · exact hden
    exact hfrac.mul (hrow w hw)
  have hY0 : Y 0 ≠ 0 := by simp [Y]
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hconn : IsPreconnected unitDisc := (convex_ball (0 : ℂ) 1).isPreconnected
  have hopen : IsOpen unitDisc := Metric.isOpen_ball
  have hevent : ∀ᶠ w in 𝓝 (0 : ℂ), deriv Y w + A w * Y w = 0 :=
    hLocal η hη
  have hnv := analytic_local_ode_nonvanishing hopen hconn hY hA h0 hY0 hevent v hv
  simpa [Y, hmap] using hnv

end AWPIRH
