import Derivations.Geometry.PositiveAnchorNonvanishing
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace NativeSolobolo

open Complex

/--
!!! Quarter-shifted actual theta gauge.
Every positive new anchor `a > 0` samples the already-proved zero-free old
anchor `a + 1/4 >= 1/4`.
-/
noncomputable def quarterShiftTheta (z : ℂ) : ℂ :=
  mathlibSlitTheta (z + (1 / 4 : ℂ))

/-- !!! The quarter-shifted actual theta is zero-free at every positive anchor. -/
theorem QUARTER_SHIFT_THETA_NE_ZERO_POSITIVE
    {a : ℝ} (ha : PositiveAnchor a) :
    quarterShiftTheta (a : ℂ) ≠ 0 := by
  have hpos : PositiveAnchor (a + (1 / 4 : ℝ)) := by
    dsimp [PositiveAnchor] at ha ⊢
    linarith
  have hq : (1 / 4 : ℝ) ≤ a + (1 / 4 : ℝ) := by
    dsimp [PositiveAnchor] at ha
    linarith
  have h := NativeSolobolo.Derivations.Geometry.MATHLIB_SLIT_THETA_NE_ZERO_ANCHOR_GE_QUARTER
    hpos hq
  simpa [quarterShiftTheta] using h

/-- !! Quarter-shifted theta is analytic at every positive anchor. -/
theorem QUARTER_SHIFT_THETA_ANALYTIC_AT_POSITIVE
    {a : ℝ} (ha : PositiveAnchor a) :
    AnalyticAt ℂ quarterShiftTheta (a : ℂ) := by
  have hpos : PositiveAnchor (a + (1 / 4 : ℝ)) := by
    dsimp [PositiveAnchor] at ha ⊢
    linarith
  have hmemReal : (((a + (1 / 4 : ℝ) : ℝ) : ℂ)) ∈ Complex.slitPlane :=
    POSITIVE_ANCHOR_MEM_SLIT_PLANE hpos
  have hmem : ((a : ℂ) + (1 / 4 : ℂ)) ∈ Complex.slitPlane := by
    simpa using hmemReal
  have htheta : AnalyticAt ℂ mathlibSlitTheta ((a : ℂ) + (1 / 4 : ℂ)) :=
    MATHLIB_SLIT_THETA_ANALYTIC_ON_NHD _ hmem
  have hadd : AnalyticAt ℂ (fun z : ℂ => z + (1 / 4 : ℂ)) (a : ℂ) := by
    exact analyticAt_id.fun_add analyticAt_const
  change AnalyticAt ℂ
    (fun z : ℂ => mathlibSlitTheta (z + (1 / 4 : ℂ)))
    (a : ℂ)
  exact AnalyticAt.fun_comp
    (g := mathlibSlitTheta)
    (f := fun z : ℂ => z + (1 / 4 : ℂ))
    (x := (a : ℂ))
    htheta hadd

/--
The dimensionless angular-disc parameter.  `w = 0` is the positive anchor and
`w = ±1` reaches the negative-real boundary.  The factor `pi` makes the
critical metric radius literally one.
-/
noncomputable def quarterShiftAnglePoint (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) * w)

@[simp] theorem QUARTER_SHIFT_ANGLE_POINT_ZERO (a : ℝ) :
    quarterShiftAnglePoint a 0 = (a : ℂ) := by
  simp [quarterShiftAnglePoint]

/-- !! The angular-disc point map is analytic at the origin. -/
theorem QUARTER_SHIFT_ANGLE_POINT_ANALYTIC_AT_ZERO (a : ℝ) :
    AnalyticAt ℂ (quarterShiftAnglePoint a) 0 := by
  have hid : AnalyticAt ℂ (id : ℂ → ℂ) 0 := analyticAt_id
  have hc : AnalyticAt ℂ (fun _w : ℂ => Complex.I * (Real.pi : ℂ)) 0 :=
    analyticAt_const
  have hlin0 := hc.fun_mul hid
  have hlin :
      AnalyticAt ℂ (fun w : ℂ => (Complex.I * (Real.pi : ℂ)) * w) 0 := by
    simpa [id_eq] using hlin0
  have hexp0 :
      AnalyticAt ℂ
        (Complex.exp ∘ (fun w : ℂ => (Complex.I * (Real.pi : ℂ)) * w)) 0 :=
    analyticAt_cexp.comp hlin
  have hexp :
      AnalyticAt ℂ
        (fun w : ℂ => Complex.exp ((Complex.I * (Real.pi : ℂ)) * w)) 0 := by
    simpa [Function.comp_def] using hexp0
  have ha : AnalyticAt ℂ (fun _w : ℂ => (a : ℂ)) 0 := analyticAt_const
  have hprod :
      AnalyticAt ℂ
        (fun w : ℂ => (a : ℂ) * Complex.exp ((Complex.I * (Real.pi : ℂ)) * w))
        0 :=
    ha.fun_mul hexp
  change AnalyticAt ℂ
    (fun w : ℂ => (a : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) * w))
    0
  simpa [mul_assoc] using hprod

/-- Actual quarter-shifted theta pulled back to the angular unit-disc gauge. -/
noncomputable def quarterShiftAngleTheta (a : ℝ) (w : ℂ) : ℂ :=
  quarterShiftTheta (quarterShiftAnglePoint a w)

/-- !! The pulled-back actual theta is analytic at the disc origin. -/
theorem QUARTER_SHIFT_ANGLE_THETA_ANALYTIC_AT_ZERO
    {a : ℝ} (ha : PositiveAnchor a) :
    AnalyticAt ℂ (quarterShiftAngleTheta a) 0 := by
  have htheta : AnalyticAt ℂ quarterShiftTheta (a : ℂ) :=
    QUARTER_SHIFT_THETA_ANALYTIC_AT_POSITIVE ha
  have htheta0 :
      AnalyticAt ℂ quarterShiftTheta (quarterShiftAnglePoint a 0) := by
    simpa using htheta
  have hpoint : AnalyticAt ℂ (quarterShiftAnglePoint a) 0 :=
    QUARTER_SHIFT_ANGLE_POINT_ANALYTIC_AT_ZERO a
  change AnalyticAt ℂ
    (fun w : ℂ => quarterShiftTheta (quarterShiftAnglePoint a w))
    0
  exact AnalyticAt.fun_comp
    (g := quarterShiftTheta)
    (f := quarterShiftAnglePoint a)
    (x := (0 : ℂ))
    htheta0 hpoint

/-- !!! The pulled-back theta is nonzero at the disc origin. -/
theorem QUARTER_SHIFT_ANGLE_THETA_NE_ZERO_AT_ZERO
    {a : ℝ} (ha : PositiveAnchor a) :
    quarterShiftAngleTheta a 0 ≠ 0 := by
  simpa [quarterShiftAngleTheta] using QUARTER_SHIFT_THETA_NE_ZERO_POSITIVE ha

/--
Actual reciprocal theta germ in the angular unit-disc gauge.  This is the
clean local object whose singularities are exactly translated theta zeros.
-/
noncomputable def quarterShiftAngleReciprocal (a : ℝ) (w : ℂ) : ℂ :=
  (quarterShiftAngleTheta a w)⁻¹

/-- !!! The actual reciprocal angular germ is analytic at zero for every positive anchor. -/
theorem QUARTER_SHIFT_ANGLE_RECIPROCAL_ANALYTIC_AT_ZERO
    {a : ℝ} (ha : PositiveAnchor a) :
    AnalyticAt ℂ (quarterShiftAngleReciprocal a) 0 := by
  have htheta := QUARTER_SHIFT_ANGLE_THETA_ANALYTIC_AT_ZERO ha
  have hne := QUARTER_SHIFT_ANGLE_THETA_NE_ZERO_AT_ZERO ha
  unfold quarterShiftAngleReciprocal
  exact htheta.fun_inv hne

/--
Canonical Taylor series of the literal actual reciprocal germ.  No coefficient
identification hypothesis is present: these are definitionally the iterated
complex derivatives of the actual mathlib xi/theta object.
-/
noncomputable def quarterShiftAngleReciprocalSeries (a : ℝ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n : Nat =>
      iteratedDeriv n (quarterShiftAngleReciprocal a) 0 / (n.factorial : ℂ))

/--
!!! ACTUAL LOCAL-JET IDENTIFICATION IN THE ANGULAR DISC GAUGE.
The canonical derivative series is literally a power series for the actual
quarter-shifted reciprocal theta germ at the positive anchor.
-/
theorem ACTUAL_QUARTER_SHIFT_ANGLE_RECIPROCAL_HAS_FPOWER_SERIES_AT_ZERO
    {a : ℝ} (ha : PositiveAnchor a) :
    HasFPowerSeriesAt
      (quarterShiftAngleReciprocal a)
      (quarterShiftAngleReciprocalSeries a)
      0 := by
  simpa [quarterShiftAngleReciprocalSeries] using
    (QUARTER_SHIFT_ANGLE_RECIPROCAL_ANALYTIC_AT_ZERO ha).hasFPowerSeriesAt

/-- !! In particular the actual reciprocal germ has a positive Taylor radius. -/
theorem ACTUAL_QUARTER_SHIFT_ANGLE_RECIPROCAL_SERIES_RADIUS_POS
    {a : ℝ} (ha : PositiveAnchor a) :
    0 < (quarterShiftAngleReciprocalSeries a).radius := by
  exact (ACTUAL_QUARTER_SHIFT_ANGLE_RECIPROCAL_HAS_FPOWER_SERIES_AT_ZERO ha).radius_pos

end NativeSolobolo
