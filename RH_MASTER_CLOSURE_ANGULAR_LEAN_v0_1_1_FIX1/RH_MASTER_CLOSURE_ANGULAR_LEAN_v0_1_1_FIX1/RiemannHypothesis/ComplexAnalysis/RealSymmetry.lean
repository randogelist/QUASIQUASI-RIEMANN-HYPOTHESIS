/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Data.Complex.Basic

/-!
# Real symmetry / conjugation lemmas

Generic lemmas about complex conjugation used by the engine. Isolated here
so `RealZeros.Engine` can import this without pulling in the full
`LogDerivative` or `PoleProbe` files.
-/

namespace OverflowResidueRH

open Complex

/-- `(star z).im = -z.im` — the `Star`-side restatement of `Complex.conj_im`. -/
theorem complex_star_im (ρ : ℂ) : (star ρ).im = -ρ.im := by
  change (starRingEnd ℂ ρ).im = -ρ.im
  exact Complex.conj_im ρ

end OverflowResidueRH
