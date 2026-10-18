import GeneralizedCharacter

namespace GPBKQRKernel

/-- The signed Cayley coordinate of the reciprocal scale gain. -/
noncomputable def cayleyCoordinate (sigma : ℝ) : ℝ :=
  (phaseFreeGain sigma - 1) / (phaseFreeGain sigma + 1)

/-- The nonnegative, reflection-invariant Cayley defect. -/
noncomputable def cayleyDefect (sigma : ℝ) : ℝ :=
  (cayleyCoordinate sigma) ^ 2

/-- The contraction constructed directly from the Cayley defect. -/
noncomputable def cayleyContraction (sigma : ℝ) : ℝ :=
  1 - cayleyDefect sigma

/-- Concrete scalar energy used by the constructed Cayley step. -/
def scalarEnergy (x : ℝ) : ℝ := x ^ 2

/-- Concrete Cayley contraction step on the scalar energy space. -/
noncomputable def cayleyStep (sigma x : ℝ) : ℝ :=
  Real.sqrt (cayleyContraction sigma) * x

/-- The Cayley denominator is positive, hence nonzero, without a premise. -/
theorem phaseFreeGain_add_one_pos (sigma : ℝ) :
    0 < phaseFreeGain sigma + 1 := by
  linarith [phaseFreeGain_pos sigma]

/-- Reflection makes the signed Cayley coordinate odd. -/
theorem cayleyCoordinate_reflect (sigma : ℝ) :
    cayleyCoordinate (reflect sigma) = -cayleyCoordinate sigma := by
  unfold cayleyCoordinate
  rw [phaseFreeGain_reflect]
  let g := phaseFreeGain sigma
  have hg : 0 < g := by
    dsimp [g]
    exact phaseFreeGain_pos sigma
  have hgne : g ≠ 0 := ne_of_gt hg
  have hsum : g + 1 ≠ 0 := by linarith
  have hinvsum : g⁻¹ + 1 ≠ 0 := by
    have hginv : 0 < g⁻¹ := inv_pos.mpr hg
    linarith
  change (g⁻¹ - 1) / (g⁻¹ + 1) = -((g - 1) / (g + 1))
  field_simp [hgne, hsum, hinvsum]
  ring

/-- The Cayley defect is nonnegative by construction. -/
theorem cayleyDefect_nonneg (sigma : ℝ) : 0 ≤ cayleyDefect sigma := by
  unfold cayleyDefect
  positivity

/-- The defect is invariant under reflection. -/
theorem cayleyDefect_reflect (sigma : ℝ) :
    cayleyDefect (reflect sigma) = cayleyDefect sigma := by
  unfold cayleyDefect
  rw [cayleyCoordinate_reflect]
  ring

/-- The Cayley construction is exactly the previously derived symmetric contraction. -/
theorem cayleyContraction_eq_symmetricContraction (sigma : ℝ) :
    cayleyContraction sigma = symmetricContraction sigma := by
  unfold cayleyContraction cayleyDefect cayleyCoordinate
  have h := one_sub_symmetricContraction sigma
  linarith

/-- Exact rational formula of the constructed Cayley contraction. -/
theorem cayleyContraction_formula (sigma : ℝ) :
    cayleyContraction sigma =
      4 * phaseFreeGain sigma / (1 + phaseFreeGain sigma) ^ 2 := by
  rw [cayleyContraction_eq_symmetricContraction]
  rfl

/-- The constructed Cayley contraction is strictly positive. -/
theorem cayleyContraction_pos (sigma : ℝ) :
    0 < cayleyContraction sigma := by
  rw [cayleyContraction_eq_symmetricContraction]
  exact symmetricContraction_pos sigma

/-- The constructed Cayley contraction is at most one. -/
theorem cayleyContraction_le_one (sigma : ℝ) :
    cayleyContraction sigma ≤ 1 := by
  rw [cayleyContraction_eq_symmetricContraction]
  exact symmetricContraction_le_one sigma

/-- Exact Cayley defect identity. -/
theorem one_sub_cayleyContraction (sigma : ℝ) :
    1 - cayleyContraction sigma = cayleyDefect sigma := by
  unfold cayleyContraction
  ring

/-- Reflection leaves the constructed contraction unchanged. -/
theorem cayleyContraction_reflect (sigma : ℝ) :
    cayleyContraction (reflect sigma) = cayleyContraction sigma := by
  calc
    cayleyContraction (reflect sigma) =
        symmetricContraction (reflect sigma) :=
      cayleyContraction_eq_symmetricContraction _
    _ = symmetricContraction sigma := symmetricContraction_reflect sigma
    _ = cayleyContraction sigma :=
      (cayleyContraction_eq_symmetricContraction sigma).symm

/-- The signed Cayley coordinate vanishes exactly at the center. -/
theorem cayleyCoordinate_eq_zero_iff (sigma : ℝ) :
    cayleyCoordinate sigma = 0 ↔ sigma = (1 / 2 : ℝ) := by
  constructor
  · intro h
    unfold cayleyCoordinate at h
    have hden : phaseFreeGain sigma + 1 ≠ 0 :=
      ne_of_gt (phaseFreeGain_add_one_pos sigma)
    have hnum : phaseFreeGain sigma - 1 = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right hden
    have hg : phaseFreeGain sigma = 1 := sub_eq_zero.mp hnum
    exact (phaseFreeGain_eq_one_iff sigma).1 hg
  · intro hs
    have hg : phaseFreeGain sigma = 1 :=
      (phaseFreeGain_eq_one_iff sigma).2 hs
    simp [cayleyCoordinate, hg]

/-- The nonnegative Cayley defect vanishes exactly at the center. -/
theorem cayleyDefect_eq_zero_iff (sigma : ℝ) :
    cayleyDefect sigma = 0 ↔ sigma = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have hc : cayleyCoordinate sigma = 0 := by
      unfold cayleyDefect at h
      nlinarith [sq_nonneg (cayleyCoordinate sigma)]
    exact (cayleyCoordinate_eq_zero_iff sigma).1 hc
  · intro hs
    have hc : cayleyCoordinate sigma = 0 :=
      (cayleyCoordinate_eq_zero_iff sigma).2 hs
    simp [cayleyDefect, hc]

/-- The constructed contraction saturates exactly at the center. -/
theorem cayleyContraction_eq_one_iff (sigma : ℝ) :
    cayleyContraction sigma = 1 ↔ sigma = (1 / 2 : ℝ) := by
  rw [cayleyContraction_eq_symmetricContraction]
  exact symmetricContraction_eq_one_iff sigma

/-- The constructed contraction is the exact reciprocal of the dual Cayley value. -/
theorem cayleyContraction_mul_dualCayleyEigenvalue (sigma : ℝ) :
    cayleyContraction sigma * dualCayleyEigenvalue sigma = 1 := by
  rw [cayleyContraction_eq_symmetricContraction]
  exact symmetricContraction_mul_dualCayleyEigenvalue sigma

/-- Scalar energy is nonnegative. -/
theorem scalarEnergy_nonneg (x : ℝ) : 0 ≤ scalarEnergy x := by
  unfold scalarEnergy
  positivity

/-- Exact energy scaling of the explicitly constructed Cayley step. -/
theorem cayleyStep_energy (sigma x : ℝ) :
    scalarEnergy (cayleyStep sigma x) =
      cayleyContraction sigma * scalarEnergy x := by
  have hq : 0 ≤ cayleyContraction sigma :=
    le_of_lt (cayleyContraction_pos sigma)
  unfold scalarEnergy cayleyStep
  rw [mul_pow, Real.sq_sqrt hq]

/-- The explicitly constructed Cayley step is contractive in scalar energy. -/
theorem cayleyStep_contractive (sigma x : ℝ) :
    scalarEnergy (cayleyStep sigma x) ≤ scalarEnergy x := by
  rw [cayleyStep_energy]
  have hx : 0 ≤ scalarEnergy x := scalarEnergy_nonneg x
  have hq : cayleyContraction sigma ≤ 1 := cayleyContraction_le_one sigma
  nlinarith

/-- The exact energy loss is the Cayley defect times the incoming energy. -/
theorem cayleyStep_energy_defect (sigma x : ℝ) :
    scalarEnergy x - scalarEnergy (cayleyStep sigma x) =
      cayleyDefect sigma * scalarEnergy x := by
  rw [cayleyStep_energy]
  unfold cayleyContraction
  ring

/-- On the canonical unit state, energy preservation occurs exactly at the center. -/
theorem cayleyStep_unit_saturates_iff_center (sigma : ℝ) :
    scalarEnergy (cayleyStep sigma 1) = scalarEnergy 1 ↔
      sigma = (1 / 2 : ℝ) := by
  rw [cayleyStep_energy]
  have hunit : scalarEnergy (1 : ℝ) = 1 := by
    norm_num [scalarEnergy]
  rw [hunit, mul_one]
  exact cayleyContraction_eq_one_iff sigma

/-- A premise-free certificate collecting the whole constructed Cayley layer. -/
theorem cayleyConstruction_certificate (sigma : ℝ) :
    0 < cayleyContraction sigma ∧
    cayleyContraction sigma ≤ 1 ∧
    1 - cayleyContraction sigma = cayleyDefect sigma ∧
    cayleyContraction sigma * dualCayleyEigenvalue sigma = 1 := by
  exact ⟨cayleyContraction_pos sigma,
    cayleyContraction_le_one sigma,
    one_sub_cayleyContraction sigma,
    cayleyContraction_mul_dualCayleyEigenvalue sigma⟩

end GPBKQRKernel
