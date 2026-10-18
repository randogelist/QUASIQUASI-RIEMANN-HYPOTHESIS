import Mathlib

/-!
Merger_01: the literal native input for the v0.5 forward theorem.
No analytic identification or closing theorem is placed inside US_AWPI.
All integrals use Mathlib's total Bochner integral; convergence and binding
are separate mathematical statements, not fields of these definitions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace AWPIRH

def nativeDensity (t : ℝ) : ℝ :=
  (Real.exp t * (t - 1) + 1) / (Real.exp t - 1) ^ 2

def nativeMellin (s : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0,
    Complex.exp ((s - 1) * (Real.log t : ℂ)) * (nativeDensity t : ℂ)

def nativeCompletion (s : ℂ) : ℂ :=
  s * (Real.sqrt Real.pi : ℂ) /
    (Complex.exp (s * (Real.log (2 * Real.sqrt Real.pi) : ℂ)) *
      Complex.Gamma ((s + 1) / 2))

def nativeXi (s : ℂ) : ℂ := nativeCompletion s * nativeMellin s

def nativeFreeEnergy (y : ℝ) : ℝ :=
  Real.log ((nativeXi ((1 / 2 + Real.exp (y / 2) : ℝ) : ℂ)).re)

def nativeBase (y : ℝ) : ℝ :=
  4 * deriv (deriv nativeFreeEnergy) y

/-- The log-anchor form of the unnormalized Widder recurrence. -/
def nativeWidder : ℕ → ℝ → ℝ
  | 0 => nativeBase
  | n + 1 => fun y =>
      2 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
        (((n : ℝ) + 1) ^ 2 * nativeWidder n y -
          deriv (deriv (nativeWidder n)) y)

/-- Fixed anchor a=1 is y=0. These coefficients are not free data. -/
def nativeCoefficients (n : ℕ) : ℂ := (nativeWidder n 0 : ℂ)

/-- Exact signed Bernstein cell, with the original binomial normalization. -/
def bernsteinCell (c : ℕ → ℂ) (N j : ℕ) : ℂ :=
  (N.choose j : ℂ) *
    ∑ k ∈ Finset.range (N - j + 1),
      (-1 : ℂ) ^ k * ((N - j).choose k : ℂ) * c (j + k)

def bernsteinEnergy (c : ℕ → ℂ) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) *
    ∑ j ∈ Finset.range (N + 1), ‖bernsteinCell c N j‖ ^ 2

def rowPolynomial (c : ℕ → ℂ) (N : ℕ) (η : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), bernsteinCell c N j * η ^ j

def SubexponentialEnergy (c : ℕ → ℂ) : Prop :=
  Tendsto (fun N : ℕ => Real.log (1 + bernsteinEnergy c N) / (N : ℝ))
    atTop (𝓝 0)

/-- Only the native energy-growth assertion. No bridge or RH conjunct. -/
def US_AWPI : Prop := SubexponentialEnergy nativeCoefficients

@[simp] theorem nativeWidder_zero (y : ℝ) :
    nativeWidder 0 y = nativeBase y := rfl

@[simp] theorem nativeWidder_succ (n : ℕ) (y : ℝ) :
    nativeWidder (n + 1) y =
      2 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
        (((n : ℝ) + 1) ^ 2 * nativeWidder n y -
          deriv (deriv (nativeWidder n)) y) := rfl

@[simp] theorem bernsteinCell_diagonal (c : ℕ → ℂ) (N : ℕ) :
    bernsteinCell c N N = c N := by
  simp [bernsteinCell]

@[simp] theorem bernsteinCell_zero (c : ℕ → ℂ) :
    bernsteinCell c 0 0 = c 0 := by simp [bernsteinCell]

@[simp] theorem bernsteinEnergy_zero (c : ℕ → ℂ) :
    bernsteinEnergy c 0 = ‖c 0‖ ^ 2 := by
  simp [bernsteinEnergy, bernsteinCell]

@[simp] theorem rowPolynomial_zero (c : ℕ → ℂ) (η : ℂ) :
    rowPolynomial c 0 η = c 0 := by
  simp [rowPolynomial, bernsteinCell]

theorem bernsteinEnergy_nonneg (c : ℕ → ℂ) (N : ℕ) :
    0 ≤ bernsteinEnergy c N := by
  unfold bernsteinEnergy
  positivity

theorem US_AWPI_unfold :
    US_AWPI ↔ Tendsto
      (fun N : ℕ => Real.log (1 + bernsteinEnergy nativeCoefficients N) / (N : ℝ))
      atTop (𝓝 0) := Iff.rfl

end AWPIRH
