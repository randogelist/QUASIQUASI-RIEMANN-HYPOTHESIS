import Mathlib

/-!
Local product calculus.  These lemmas transport explicit differentiable
factorizations; they do not assert a factorization or an implicit curve exists.
The multiplicity is written `k + 1`, so it is always positive.
-/

noncomputable section
namespace AngularRegularity

/-- Derivative of a nonnegative local zero-factor model, in reduced form. -/
theorem local_factor_hasDerivAt
    {H D : ℝ → ℝ} {x h d : ℝ}
    (hH : HasDerivAt H h x) (hD : HasDerivAt D d x) (k : ℕ) :
    HasDerivAt (fun y => H y * D y ^ (k + 1))
      (D x ^ k * (((k + 1 : ℕ) : ℝ) * H x * d + D x * h)) x := by
  have hraw :
      HasDerivAt (fun y => H y * D y ^ (k + 1))
        (h * D x ^ (k + 1) +
          H x * (((k + 1 : ℕ) : ℝ) * D x ^ ((k + 1) - 1) * d)) x :=
    hH.mul (hD.pow (k + 1))
  have hcoef :
      h * D x ^ (k + 1) +
          H x * (((k + 1 : ℕ) : ℝ) * D x ^ ((k + 1) - 1) * d) =
        D x ^ k * (((k + 1 : ℕ) : ℝ) * H x * d + D x * h) := by
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  rw [hcoef] at hraw
  exact hraw

theorem local_factor_deriv
    {H D : ℝ → ℝ} {x h d : ℝ}
    (hH : HasDerivAt H h x) (hD : HasDerivAt D d x) (k : ℕ) :
    deriv (fun y => H y * D y ^ (k + 1)) x =
      D x ^ k * (((k + 1 : ℕ) : ℝ) * H x * d + D x * h) :=
  (local_factor_hasDerivAt hH hD k).deriv

/-- At a zero of the reduced slope, its positive prefactor cannot change
the sign of its derivative. -/
theorem reduced_slope_hasDerivAt
    {D J : ℝ → ℝ} {x d j : ℝ}
    (hD : HasDerivAt D d x) (hJ : HasDerivAt J j x)
    (hzero : J x = 0) (k : ℕ) :
    HasDerivAt (fun y => D y ^ k * J y) (D x ^ k * j) x := by
  have hraw :
      HasDerivAt (fun y => D y ^ k * J y)
        (((k : ℝ) * D x ^ (k - 1) * d) * J x + D x ^ k * j) x :=
    (hD.pow k).mul hJ
  rw [hzero, mul_zero, zero_add] at hraw
  exact hraw

theorem reduced_slope_deriv_pos
    {D J : ℝ → ℝ} {x d j : ℝ}
    (hD : HasDerivAt D d x) (hJ : HasDerivAt J j x)
    (hzero : J x = 0) (hpos : 0 < D x) (hj : 0 < j) (k : ℕ) :
    0 < deriv (fun y => D y ^ k * J y) x := by
  rw [(reduced_slope_hasDerivAt hD hJ hzero k).deriv]
  exact mul_pos (pow_pos hpos k) hj

theorem local_factor_pos
    {H D : ℝ → ℝ} {x : ℝ} (hH : 0 < H x) (hD : 0 < D x) (k : ℕ) :
    0 < H x * D x ^ (k + 1) :=
  mul_pos hH (pow_pos hD (k + 1))

/-- A reduced stationary point is also a stationary point of the full slope. -/
theorem reduced_stationary_implies_stationary
    {D J : ℝ → ℝ} {x : ℝ} (hzero : J x = 0) (k : ℕ) :
    D x ^ k * J x = 0 := by
  rw [hzero, mul_zero]

/-- Away from D=0, no stationary points are lost by the reduction. -/
theorem reduced_stationary_iff
    {D J : ℝ → ℝ} {x : ℝ} (hD : D x ≠ 0) (k : ℕ) :
    D x ^ k * J x = 0 ↔ J x = 0 := by
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero k hD)
  · intro h
    rw [h, mul_zero]

end AngularRegularity
