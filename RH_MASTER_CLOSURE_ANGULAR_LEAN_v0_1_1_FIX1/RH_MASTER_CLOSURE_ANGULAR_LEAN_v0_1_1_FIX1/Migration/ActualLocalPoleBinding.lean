import Merger02.LocalPole
import Migration.DirectXiBinding

namespace Merger04.LocalPole

open Complex Filter
open scoped Topology
open NativeSoloboloNegativity Merger04.Migration

/-- The Merger_02 actual xi is definitionally the same actual xi used by the
    direct Widder branch.  This theorem makes the cross-branch identification
    explicit in the dependency graph. -/
theorem MERGER02_ACTUAL_XI_EQ_CURRENT_XI (s : ℂ) :
    Merger02.actualXi s = xiEntire s := by
  rfl

/-- Likewise for the centered xi functions. -/
theorem MERGER02_CENTERED_XI_EQ_CURRENT_CENTERED_XI (w : ℂ) :
    Merger02.centeredXi w = NativeSolobolo.mathlibCenteredXi w := by
  rfl

/-- Likewise for the principal-branch slit-theta used in the local pole proof. -/
theorem MERGER02_THETA_EQ_CURRENT_SLIT_THETA (z : ℂ) :
    Merger02.theta z = NativeSolobolo.mathlibSlitTheta z := by
  rfl

/-- Negating Mathlib's literal RH statement produces an actual nontrivial
    zeta zero off the critical line.  No project zero interface is used. -/
theorem NOT_RH_GIVES_OFFLINE_NONTRIVIAL_ZERO
    (hnot : ¬ _root_.RiemannHypothesis) :
    ∃ rho : ℂ, Merger02.NontrivialZero rho ∧ rho.re ≠ (1 / 2 : ℝ) := by
  unfold _root_.RiemannHypothesis at hnot
  push_neg at hnot
  rcases hnot with ⟨rho, hz, htriv, hone, hoff⟩
  have htriv' : ¬ ∃ n : ℕ, rho = -2 * ((n : ℂ) + 1) := by
    intro hex
    rcases hex with ⟨n, hn⟩
    exact htriv n hn
  exact ⟨rho, ⟨hz, htriv', hone⟩, hoff⟩

/-- A compact local certificate: one actual off-line zero gives one genuine
    simple pole of the actual Xi/Cayley generating function in the open disk.
    Multiplicity of the underlying theta zero is already absorbed into `A`. -/
structure ActualXiInteriorSimplePole where
  rho : ℂ
  nontrivialZero : Merger02.NontrivialZero rho
  offLine : rho.re ≠ (1 / 2 : ℝ)
  phase : ℂ
  pole : ℂ
  residue : ℂ
  remainder : ℂ → ℂ
  phase_norm : ‖phase‖ = 1
  phase_ne_one : phase ≠ 1
  pole_ne_zero : pole ≠ 0
  pole_in_disk : ‖pole‖ < 1
  inverse_expands : 1 < ‖pole⁻¹‖
  residue_ne_zero : residue ≠ 0
  remainder_analytic : AnalyticAt ℂ remainder pole
  local_principal_part :
    ∀ᶠ u in 𝓝[≠] pole,
      Merger02.rawGenerating phase u = residue / (u - pole) + remainder u

/-- !!! Actual off-line zero -> actual interior simple Cayley pole.
    This discharges the zero-selection and local meromorphic-factorization
    part of the previous global channel interface. -/
theorem OFFLINE_ZERO_GIVES_ACTUAL_XI_INTERIOR_SIMPLE_POLE
    {rho : ℂ} (hz : Merger02.NontrivialZero rho)
    (hoff : rho.re ≠ (1 / 2 : ℝ)) :
    ∃ P : ActualXiInteriorSimplePole, P.rho = rho := by
  rcases Merger02.actual_offline_simple_pole hz hoff with
    ⟨z, v, A, R, hzNorm, hz1, hv0, hv, hinv, hA, hR, hlocal⟩
  refine ⟨{
    rho := rho
    nontrivialZero := hz
    offLine := hoff
    phase := z
    pole := v
    residue := A
    remainder := R
    phase_norm := hzNorm
    phase_ne_one := hz1
    pole_ne_zero := hv0
    pole_in_disk := hv
    inverse_expands := hinv
    residue_ne_zero := hA
    remainder_analytic := hR
    local_principal_part := hlocal
  }, rfl⟩

/-- !!! Failure of Mathlib RH produces the literal local pole certificate. -/
theorem NOT_RH_GIVES_ACTUAL_XI_INTERIOR_SIMPLE_POLE
    (hnot : ¬ _root_.RiemannHypothesis) :
    ∃ P : ActualXiInteriorSimplePole, True := by
  rcases NOT_RH_GIVES_OFFLINE_NONTRIVIAL_ZERO hnot with ⟨rho, hz, hoff⟩
  rcases OFFLINE_ZERO_GIVES_ACTUAL_XI_INTERIOR_SIMPLE_POLE hz hoff with ⟨P, _⟩
  exact ⟨P, trivial⟩

end Merger04.LocalPole
