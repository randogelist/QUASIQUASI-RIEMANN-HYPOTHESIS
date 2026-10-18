import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Actual Mathlib xi, not an arbitrary RH proposition or model zero predicate.
The completion and nonvanishing proofs adapt the supplied native archives.
-/

set_option autoImplicit false
noncomputable section
namespace AWPIRH

def xi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

def centeredXi (w : ℂ) : ℂ := xi ((1 / 2 : ℂ) + w)

def NontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧ s ≠ 1

theorem xi_differentiable : Differentiable ℂ xi := by
  intro s
  have hL : DifferentiableAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀ s
  unfold xi
  fun_prop

theorem xi_reflection (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem centeredXi_differentiable : Differentiable ℂ centeredXi := by
  intro w
  unfold centeredXi
  exact (xi_differentiable ((1 / 2 : ℂ) + w)).comp w (by fun_prop)

theorem centeredXi_even (w : ℂ) : centeredXi (-w) = centeredXi w := by
  unfold centeredXi
  have h := xi_reflection ((1 / 2 : ℂ) + w)
  convert h using 1 <;> ring

theorem nontrivialZero_ne_zero {s : ℂ} (hs : NontrivialZero s) : s ≠ 0 := by
  intro h
  have hz := hs.1
  rw [h, riemannZeta_zero] at hz
  norm_num at hz

theorem gammaR_ne_zero_of_nontrivialZero {s : ℂ} (hs : NontrivialZero s) :
    s.Gammaℝ ≠ 0 := by
  intro hGamma
  rcases Complex.Gammaℝ_eq_zero_iff.mp hGamma with ⟨n, hn⟩
  cases n with
  | zero =>
      have hs0 : s = 0 := by simpa using hn
      exact nontrivialZero_ne_zero hs hs0
  | succ n =>
      apply hs.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ, neg_mul] using hn

theorem completedZeta_zero_of_nontrivialZero {s : ℂ} (hs : NontrivialZero s) :
    completedRiemannZeta s = 0 := by
  have hs0 := nontrivialZero_ne_zero hs
  have hg := gammaR_ne_zero_of_nontrivialZero hs
  have hd : completedRiemannZeta s / s.Gammaℝ = 0 := by
    calc
      _ = riemannZeta s := (riemannZeta_def_of_ne_zero hs0).symm
      _ = 0 := hs.1
  exact (div_eq_zero_iff.mp hd).resolve_right hg

theorem xi_eq_completed {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold xi
  field_simp [hs0, h1s]
  <;> ring

theorem xi_zero_of_nontrivialZero {s : ℂ} (hs : NontrivialZero s) : xi s = 0 := by
  rw [xi_eq_completed (nontrivialZero_ne_zero hs) hs.2.2,
    completedZeta_zero_of_nontrivialZero hs]
  simp

theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    norm_num [xi]
  · have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    intro hxi
    apply hzeta
    rw [riemannZeta_eq_mul_completedRiemannZeta₀]
    have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
      simpa [xi] using hxi
    have h1ms : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hnum : s * completedRiemannZeta₀ s - 1 - s / (1 - s) = 0 := by
      calc
        _ = -(1 + s * (s - 1) * completedRiemannZeta₀ s) / (1 - s) := by
          field_simp [h1ms]
          <;> ring
        _ = 0 := by rw [hraw]; simp
    rw [hnum]
    simp

/-- Pointwise even descent; global analyticity is a separate implementation block. -/
def theta (z : ℂ) : ℂ := centeredXi (Complex.sqrt z)

theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  simpa [Complex.sqrt] using Complex.cpow_ofNat_inv_pow z 2

theorem theta_square (w : ℂ) : theta (w ^ 2) = centeredXi w := by
  have hsq : (Complex.sqrt (w ^ 2)) ^ 2 = w ^ 2 := complex_sqrt_sq _
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · simp [theta, h]
  · simpa [theta, h] using centeredXi_even w

theorem theta_one : theta 1 = xi (3 / 2 : ℂ) := by
  have h : (1 / 2 : ℂ) + 1 = 3 / 2 := by ring
  simpa [theta, centeredXi] using congrArg xi h

theorem theta_one_ne_zero : theta 1 ≠ 0 := by
  rw [theta_one]
  apply xi_ne_zero_of_one_le_re
  norm_num

theorem theta_zero_of_nontrivialZero {s : ℂ} (hs : NontrivialZero s) :
    theta ((s - 1 / 2) ^ 2) = 0 := by
  rw [theta_square]
  have hshift : (1 / 2 : ℂ) + (s - 1 / 2) = s := by ring
  simpa [centeredXi, hshift] using xi_zero_of_nontrivialZero hs

end AWPIRH
