import Core.Observable

namespace NativeSolobolo

/--
The centered Theta-zero corresponding to beta + i gamma.
This is the literal z = (rho - 1/2)^2 coordinate.
-/
def CenteredXiGeometry.thetaZeroPoint
    (X : CenteredXiGeometry) (z : X.Zero) : ℂ :=
  Complex.mk
    (X.beta z ^ 2 - X.gamma z ^ 2)
    (2 * X.beta z * X.gamma z)

/--
Actual centered-Theta data used by the direct Cayley observable.
`thetaPrime` is carried explicitly because the finite value of the observable is
built from theta'/theta.  The pole proof itself only needs `theta_zero`.
-/
structure CenteredThetaData where
  geometry : CenteredXiGeometry
  theta : ℂ → ℂ
  thetaPrime : ℂ → ℂ
  theta_zero : ∀ z : geometry.Zero,
    theta (geometry.thetaZeroPoint z) = 0

/-- Positive imaginary magnitude of the conjugate Cayley pair. -/
noncomputable def cayleyImagMagnitude (a r : ℝ) : ℝ :=
  2 * Real.sqrt ((a * r) * (a * (1 - r)))

/-- Upper member of the Cayley conjugate pair at anchor a and radius r. -/
noncomputable def cayleyPointPlus (a r : ℝ) : ℂ :=
  Complex.mk (a * (1 - 2 * r)) (cayleyImagMagnitude a r)

/-- Lower member of the Cayley conjugate pair at anchor a and radius r. -/
noncomputable def cayleyPointMinus (a r : ℝ) : ℂ :=
  Complex.mk (a * (1 - 2 * r)) (-cayleyImagMagnitude a r)

/--
!!! ACTUAL THETA/GP CAYLEY OBSERVABLE
At nonzero denominators this is the dual-Lowner/Cayley observable
  4 a * [ w R(w) - z R(z) ] / (w-z),  R = theta'/theta,
on the conjugate pair z = z_+, w = z_-.
At a theta zero the observable is recorded as `none`, i.e. a genuine pole point.
-/
noncomputable def actualThetaCayleyObservable
    (T : CenteredThetaData) : GPObservable ℂ where
  eval a r :=
    let zp := cayleyPointPlus a r
    let zm := cayleyPointMinus a r
    if hzero : T.theta zp = 0 ∨ T.theta zm = 0 then
      none
    else
      let Rp := T.thetaPrime zp / T.theta zp
      let Rm := T.thetaPrime zm / T.theta zm
      some ((4 * (a : ℂ)) * ((zm * Rm - zp * Rp) / (zm - zp)))

end NativeSolobolo

namespace NativeSolobolo

/--
Exact logarithmic metric gauge for the Cayley disk:
  r = sin^2(eta/2),   0 <= eta < pi.
-/
noncomputable def cayleyRadiusAtMetricDepth (eta : ℝ) : ℝ :=
  (Real.sin (eta / 2)) ^ 2

/-- Inverse metric depth attached to an interior Cayley radius. -/
noncomputable def metricDepthOfCayleyRadius (r : ℝ) : ℝ :=
  2 * Real.arcsin (Real.sqrt r)

/--
Actual Cayley regularity at metric depth eta: at every positive anchor, the
literal theta'/theta Cayley observable is finite at r = sin^2(eta/2).
-/
def ActualCayleyMetricRegularAt (T : CenteredThetaData) (eta : ℝ) : Prop :=
  ∀ a : ℝ, PositiveAnchor a →
    (actualThetaCayleyObservable T).eval a (cayleyRadiusAtMetricDepth eta) ≠ none

end NativeSolobolo
