import Merger02.Actual

namespace Merger02

/-- The algebra underlying the transported meromorphic pole. -/
theorem mobius_denominator_identity (t z v : ℂ) :
    (1 - z * v) + t * (1 - v) = (1 + t) - (z + t) * v := by
  ring

/-- Cross-multiplied single-pole transport, before any nonzero division. -/
theorem single_pole_transport_numerator (m t z v : ℂ) :
    m * ((1 - z * v) * (1 + t) - ((1 - z * v) + t * (1 - v))) =
      m * t * (1 - z) * v := by
  ring

/-- Exact denominator difference explaining strict amplification. -/
theorem amplification_gap_identity (beta gamma : ℝ) :
    (1 + beta ^ 2 + gamma ^ 2) ^ 2 -
      ((1 + gamma ^ 2 - beta ^ 2) ^ 2 + (2 * beta * gamma) ^ 2) =
        4 * beta ^ 2 := by
  ring

/-- For a nonzero horizontal displacement the ratio is strictly above one,
provided the anchor denominator is nonzero. -/
theorem amplification_sq_gt_one
    (beta gamma : ℝ) (hb : beta ≠ 0)
    (hd : 0 < (1 + gamma ^ 2 - beta ^ 2) ^ 2 + (2 * beta * gamma) ^ 2) :
    1 < (1 + beta ^ 2 + gamma ^ 2) ^ 2 /
      ((1 + gamma ^ 2 - beta ^ 2) ^ 2 + (2 * beta * gamma) ^ 2) := by
  apply (one_lt_div hd).2
  have hsq : 0 < beta ^ 2 := sq_pos_of_ne_zero hb
  nlinarith [amplification_gap_identity beta gamma]

end Merger02
