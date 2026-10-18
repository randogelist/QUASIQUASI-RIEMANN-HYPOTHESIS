import AWPIRH.Assembly
import AWPIRH.ProductLogGerm

/-!
One fewer analytic input than the v0.6.4 passing assembly.
The original definitions and old assembly remain unchanged.
The local native/Widder row identity is still an explicit input.
-/
set_option autoImplicit false
noncomputable section
namespace AWPIRH

/-- The formerly supplied entire-product input is now a proved declaration. -/
theorem ACTUAL_PRODUCT_ENTIRE : ActualProductEntire :=
  symmetricProduct_entire

/-- Forward assembly with only the remaining actual local row identity supplied. -/
theorem MATHLIB_RH_OF_US_AND_LOCAL_ROW_ODE
    (hUS : US_AWPI)
    (hLocal : ActualLocalRowODE) :
    _root_.RiemannHypothesis := by
  exact MATHLIB_RH_OF_US_AND_TWO_ANALYTIC_BINDINGS hUS ACTUAL_PRODUCT_ENTIRE hLocal

end AWPIRH
