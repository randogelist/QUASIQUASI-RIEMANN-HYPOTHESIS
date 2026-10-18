import Core.ActualThetaCayley

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo

/-- ! Exact square of the imaginary Cayley displacement. -/
theorem CAYLEY_IMAG_MAGNITUDE_SQ
    (a r : ℝ)
    (ha : 0 ≤ a)
    (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    (cayleyImagMagnitude a r) ^ 2 = 4 * a ^ 2 * r * (1 - r) := by
  unfold cayleyImagMagnitude
  have hnonneg : 0 ≤ (a * r) * (a * (1 - r)) := by
    positivity
  calc
    (2 * Real.sqrt ((a * r) * (a * (1 - r)))) ^ 2
        = 4 * (Real.sqrt ((a * r) * (a * (1 - r)))) ^ 2 := by ring
    _ = 4 * ((a * r) * (a * (1 - r))) := by
      rw [Real.sq_sqrt hnonneg]
    _ = 4 * a ^ 2 * r * (1 - r) := by ring

/-- !! Sum of the two Cayley conjugate points. -/
theorem CAYLEY_PAIR_SUM
    (a r : ℝ) :
    cayleyPointPlus a r + cayleyPointMinus a r =
      ((2 * a * (1 - 2 * r) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [cayleyPointPlus, cayleyPointMinus]
    ring
  · simp [cayleyPointPlus, cayleyPointMinus]

/-- !! Product of the two Cayley conjugate points. -/
theorem CAYLEY_PAIR_PRODUCT
    (a r : ℝ)
    (ha : 0 ≤ a)
    (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    cayleyPointPlus a r * cayleyPointMinus a r =
      ((a ^ 2 : ℝ) : ℂ) := by
  have hi := CAYLEY_IMAG_MAGNITUDE_SQ a r ha hr0 hr1
  apply Complex.ext
  · change
      (a * (1 - 2 * r)) * (a * (1 - 2 * r)) -
          cayleyImagMagnitude a r * (-cayleyImagMagnitude a r) = a ^ 2
    nlinarith
  · change
      (a * (1 - 2 * r)) * (-cayleyImagMagnitude a r) +
          cayleyImagMagnitude a r * (a * (1 - 2 * r)) = 0
    ring

/--
!!! QUADRATIC CAYLEY KERNEL IDENTITY.
The square-root parametrization disappears after multiplying the conjugate
factors.  This is the root-free denominator used by the local jet expansion.
-/
theorem CAYLEY_QUADRATIC_KERNEL_IDENTITY
    (a r : ℝ)
    (ha : 0 ≤ a)
    (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1)
    (z : ℂ) :
    (z - cayleyPointPlus a r) * (z - cayleyPointMinus a r) =
      (z - (a : ℂ)) ^ 2 + ((4 * a * r : ℝ) : ℂ) * z := by
  have hs := CAYLEY_PAIR_SUM a r
  have hp := CAYLEY_PAIR_PRODUCT a r ha hr0 hr1
  calc
    (z - cayleyPointPlus a r) * (z - cayleyPointMinus a r)
        = z ^ 2 - z * (cayleyPointPlus a r + cayleyPointMinus a r) +
            cayleyPointPlus a r * cayleyPointMinus a r := by ring
    _ = z ^ 2 - z * (((2 * a * (1 - 2 * r) : ℝ) : ℂ)) +
            (((a ^ 2 : ℝ) : ℂ)) := by rw [hs, hp]
    _ = (z - (a : ℂ)) ^ 2 + ((4 * a * r : ℝ) : ℂ) * z := by
      push_cast
      ring

/-- Complex Cayley eigenvalue attached to one logarithmic-derivative channel. -/
noncomputable def cayleyChannelQ (a : ℝ) (t : ℂ) : ℂ :=
  (4 * (a : ℂ) * t) / (((a : ℂ) + t) ^ 2)

/-- Root-free transfer of the simple logarithmic-derivative channel 1/(z+t). -/
noncomputable def cayleyChannelTransfer (a r : ℝ) (t : ℂ) : ℂ :=
  (4 * (a : ℂ) * t) /
    ((((a : ℂ) + t) ^ 2) - ((4 * a * r : ℝ) : ℂ) * t)

/--
!!! SINGLE CHANNEL -> GEOMETRIC CAYLEY RESOLVENT.
Whenever the displayed denominators are nonzero, the root-free channel is
exactly q/(1-rq).
-/
theorem CAYLEY_CHANNEL_TRANSFER_EQ_GEOMETRIC
    (a r : ℝ) (t : ℂ)
    (hat : (a : ℂ) + t ≠ 0)
    (hden : (((a : ℂ) + t) ^ 2) - ((4 * a * r : ℝ) : ℂ) * t ≠ 0) :
    cayleyChannelTransfer a r t =
      cayleyChannelQ a t / (1 - (r : ℂ) * cayleyChannelQ a t) := by
  unfold cayleyChannelTransfer cayleyChannelQ
  have hbase : (((a : ℂ) + t) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 hat
  have hden_eq :
      (((a : ℂ) + t) ^ 2) - ((4 * a * r : ℝ) : ℂ) * t =
        (((a : ℂ) + t) ^ 2) - (r : ℂ) * (4 * (a : ℂ) * t) := by
    push_cast
    ring
  have hden' :
      (((a : ℂ) + t) ^ 2) - (r : ℂ) * (4 * (a : ℂ) * t) ≠ 0 := by
    rw [← hden_eq]
    exact hden
  have hone :
      1 - (r : ℂ) *
          ((4 * (a : ℂ) * t) / (((a : ℂ) + t) ^ 2)) ≠ 0 := by
    intro hz
    have hzero :
        (((a : ℂ) + t) ^ 2) - (r : ℂ) * (4 * (a : ℂ) * t) = 0 := by
      calc
        (((a : ℂ) + t) ^ 2) - (r : ℂ) * (4 * (a : ℂ) * t) =
            (((a : ℂ) + t) ^ 2) *
              (1 - (r : ℂ) *
                ((4 * (a : ℂ) * t) / (((a : ℂ) + t) ^ 2))) := by
              field_simp [hbase]
        _ = 0 := by rw [hz]; ring
    exact hden' hzero
  rw [hden_eq]
  field_simp [hbase, hden', hone]

/-- The exact nth geometric jet coefficient of one channel. -/
noncomputable def cayleyChannelCoeff (a : ℝ) (t : ℂ) (n : Nat) : ℂ :=
  (cayleyChannelQ a t) ^ (n + 1)

/-- ! Channel jets advance by one multiplication with the Cayley eigenvalue. -/
theorem CAYLEY_CHANNEL_COEFF_STEP
    (a : ℝ) (t : ℂ) (n : Nat) :
    cayleyChannelCoeff a t (n + 1) =
      cayleyChannelQ a t * cayleyChannelCoeff a t n := by
  unfold cayleyChannelCoeff
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  ring

end NativeSolobolo.Derivations.Geometry
