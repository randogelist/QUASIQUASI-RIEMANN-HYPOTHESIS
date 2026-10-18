import AWPIRH.WidderCongruence

/-!
Reduction of the sole v0.8.4 coefficient binding to two intrinsic analytic germs.
This module does NOT assert either germ.  It proves all real-derivative/Widder
propagation once the literal native completion is identified with actual xi near
the fixed anchor, and keeps the independent product-side coefficient identity
visible rather than hiding it in US_AWPI.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

/-- The fixed log-anchor parametrization; `anchorPoint 0 = 3/2`. -/
def anchorPoint (y : ℝ) : ℂ :=
  ((1 / 2 + Real.exp (y / 2) : ℝ) : ℂ)

@[simp] theorem anchorPoint_zero : anchorPoint 0 = (3 / 2 : ℂ) := by
  norm_num [anchorPoint]

/-- Actual Mathlib-xi free energy in the SAME real-log convention as NativeInput. -/
def xiFreeEnergy (y : ℝ) : ℝ :=
  Real.log ((xi (anchorPoint y)).re)

def xiBase (y : ℝ) : ℝ :=
  4 * deriv (deriv xiFreeEnergy) y

def xiWidder (n : ℕ) : ℝ → ℝ :=
  logWidderTower xiBase n

/-- Literal native-Mellin completion equals the actual Mathlib xi germ at the anchor. -/
def NativeXiAnchorGerm : Prop :=
  (fun y : ℝ => nativeXi (anchorPoint y)) =ᶠ[𝓝 (0 : ℝ)]
    (fun y : ℝ => xi (anchorPoint y))

/-- The independent product-side statement after the xi germ is fixed. -/
def XiWidderProductCoefficientIdentity : Prop :=
  ∀ n : ℕ, (xiWidder n 0 : ℂ) = productLogCoefficients n

/-- Native xi germ equality gives free-energy germ equality without sign assumptions. -/
theorem nativeFreeEnergy_eventuallyEq_xiFreeEnergy
    (hXi : NativeXiAnchorGerm) :
    nativeFreeEnergy =ᶠ[𝓝 (0 : ℝ)] xiFreeEnergy := by
  filter_upwards [hXi] with y hy
  unfold nativeFreeEnergy xiFreeEnergy anchorPoint at *
  exact congrArg (fun z : ℂ => Real.log z.re) hy

/-- Two real derivatives preserve the germ equality, hence so does the base curvature. -/
theorem nativeBase_eventuallyEq_xiBase
    (hXi : NativeXiAnchorGerm) :
    nativeBase =ᶠ[𝓝 (0 : ℝ)] xiBase := by
  have hfree := nativeFreeEnergy_eventuallyEq_xiFreeEnergy hXi
  have h2 : deriv (deriv nativeFreeEnergy) =ᶠ[𝓝 (0 : ℝ)]
      deriv (deriv xiFreeEnergy) := hfree.deriv.deriv
  filter_upwards [h2] with y hy
  unfold nativeBase xiBase
  rw [hy]

/-- The entire native Widder tower is therefore fixed by the xi germ. -/
theorem nativeWidder_eventuallyEq_xiWidder
    (hXi : NativeXiAnchorGerm) (n : ℕ) :
    nativeWidder n =ᶠ[𝓝 (0 : ℝ)] xiWidder n := by
  rw [nativeWidder_eq_logWidderTower]
  exact logWidderTower_eventuallyEq (nativeBase_eventuallyEq_xiBase hXi) n

/-- At the fixed anchor this is equality of the original native coefficient and xi-Widder value. -/
theorem nativeCoefficient_eq_xiWidder
    (hXi : NativeXiAnchorGerm) (n : ℕ) :
    nativeCoefficients n = (xiWidder n 0 : ℂ) := by
  have h0 : nativeWidder n 0 = xiWidder n 0 :=
    (nativeWidder_eventuallyEq_xiWidder hXi n).self_of_nhds
  unfold nativeCoefficients
  exact congrArg (fun x : ℝ => (x : ℂ)) h0

/-- The old monolithic coefficient binding follows from the two sharp germ statements. -/
theorem NATIVE_PRODUCT_COEFFICIENT_IDENTITY_OF_GERMS
    (hXi : NativeXiAnchorGerm)
    (hProd : XiWidderProductCoefficientIdentity) :
    NativeProductCoefficientIdentity := by
  intro n
  rw [nativeCoefficient_eq_xiWidder hXi n]
  exact hProd n

/-- Forward assembly after the coefficient binding has been decomposed. -/
theorem MATHLIB_RH_OF_US_AND_NATIVE_GERMS
    (hUS : US_AWPI)
    (hXi : NativeXiAnchorGerm)
    (hProd : XiWidderProductCoefficientIdentity) :
    _root_.RiemannHypothesis := by
  exact MATHLIB_RH_OF_US_AND_COEFFICIENT_IDENTITY hUS
    (NATIVE_PRODUCT_COEFFICIENT_IDENTITY_OF_GERMS hXi hProd)

end AWPIRH
