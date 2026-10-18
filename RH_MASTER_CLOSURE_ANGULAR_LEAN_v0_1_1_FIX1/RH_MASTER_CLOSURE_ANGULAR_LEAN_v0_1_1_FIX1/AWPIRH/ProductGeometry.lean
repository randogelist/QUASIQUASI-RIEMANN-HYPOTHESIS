import AWPIRH.XiCore
import AWPIRH.PhaseGeometry

set_option autoImplicit false
noncomputable section
namespace AWPIRH

def rootPlus (r : ℂ) : ℂ :=
  1 - 2 * r + Complex.sqrt ((1 - 2 * r) ^ 2 - 1)

def rootMinus (r : ℂ) : ℂ :=
  1 - 2 * r - Complex.sqrt ((1 - 2 * r) ^ 2 - 1)

/-- Literal symmetric product. No analytic property is embedded in the definition. -/
def symmetricProduct (r : ℂ) : ℂ :=
  theta (rootPlus r) * theta (rootMinus r) / (theta 1) ^ 2

@[simp] theorem rootPlus_zero : rootPlus 0 = 1 := by simp [rootPlus]
@[simp] theorem rootMinus_zero : rootMinus 0 = 1 := by simp [rootMinus]

@[simp] theorem symmetricProduct_zero : symmetricProduct 0 = 1 := by
  simp only [symmetricProduct, rootPlus_zero, rootMinus_zero]
  rw [← pow_two]
  exact div_self (pow_ne_zero 2 theta_one_ne_zero)

theorem quadratic_factorization (r z : ℂ) :
    (z - rootPlus r) * (z - rootMinus r) =
      z ^ 2 - 2 * (1 - 2 * r) * z + 1 := by
  have hsq := complex_sqrt_sq ((1 - 2 * r) ^ 2 - 1)
  unfold rootPlus rootMinus
  linear_combination -hsq

theorem symmetricProduct_zero_of_quadratic_root {r z : ℂ}
    (hz : z ^ 2 - 2 * (1 - 2 * r) * z + 1 = 0)
    (ht : theta z = 0) : symmetricProduct r = 0 := by
  have hprod : (z - rootPlus r) * (z - rootMinus r) = 0 := by
    rw [quadratic_factorization, hz]
  rcases mul_eq_zero.mp hprod with h | h
  · have hroot : z = rootPlus r := sub_eq_zero.mp h
    have hzero : theta (rootPlus r) = 0 := by simpa [hroot] using ht
    simp [symmetricProduct, hzero]
  · have hroot : z = rootMinus r := sub_eq_zero.mp h
    have hzero : theta (rootMinus r) = 0 := by simpa [hroot] using ht
    simp [symmetricProduct, hzero]

def zeroImage (z : ℂ) : ℂ := -(1 - z) ^ 2 / (4 * z)

theorem zeroImage_quadratic {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 - 2 * (1 - 2 * zeroImage z) * z + 1 = 0 := by
  unfold zeroImage
  field_simp [hz]
  <;> ring

theorem offLine_zero_gives_product_zero {s : ℂ}
    (hs : NontrivialZero s) (hoff : s.re ≠ 1 / 2) :
    ∃ r : ℂ, OffRay r ∧ symmetricProduct r = 0 := by
  let w : ℂ := s - 1 / 2
  let z : ℂ := w ^ 2
  have hwre : w.re ≠ 0 := by
    dsimp [w]
    simpa using sub_ne_zero.mpr hoff
  have hw : w ≠ 0 := by
    intro h
    apply hwre
    simp [h]
  have hz : z ≠ 0 := pow_ne_zero 2 hw
  have hquad := zeroImage_quadratic hz
  have ht : theta z = 0 := by
    simpa [z, w] using theta_zero_of_nontrivialZero hs
  refine ⟨zeroImage z, ?_, symmetricProduct_zero_of_quadratic_root hquad ht⟩
  intro hr
  have hneg := root_on_ray_is_negative hr hquad
  exact hwre (re_eq_zero_of_square_negative hneg.1 hneg.2)

/-- Fully actual geometric terminal implication; no abstract RH model. -/
theorem MATHLIB_RH_OF_PRODUCT_NONVANISHING
    (hP : ∀ r : ℂ, OffRay r → symmetricProduct r ≠ 0) :
    _root_.RiemannHypothesis := by
  intro s hz htriv h1
  by_contra hoff
  have hs : NontrivialZero s := ⟨hz, htriv, h1⟩
  obtain ⟨r, hr, hzero⟩ := offLine_zero_gives_product_zero hs hoff
  exact hP r hr hzero

end AWPIRH
