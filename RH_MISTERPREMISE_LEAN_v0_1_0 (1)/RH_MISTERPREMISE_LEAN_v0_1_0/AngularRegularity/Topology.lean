import MisterPremise.MathlibImports

/-!
# Topology of angular derivative signals

These are generic calculus and topology statements. They do not identify a
negative derivative with a zero of the profile. Every continuity, sign, and
positive-profile hypothesis used below is explicit.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AngularRegularity

/-- On an open parameter domain, a continuous strict-negative signal has an
open negative region. -/
theorem negative_region_isOpen
    {A : ℝ → ℝ → ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D)
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) D) :
    IsOpen {p : ℝ × ℝ | p ∈ D ∧ A p.1 p.2 < 0} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hDnhds : D ∈ 𝓝 p := hD.mem_nhds hp.1
  have hAt : ContinuousAt (fun q : ℝ × ℝ => A q.1 q.2) p :=
    (hA p hp.1).continuousAt hDnhds
  have hneg : ∀ᶠ q : ℝ × ℝ in 𝓝 p, A q.1 q.2 < 0 :=
    hAt.eventually (isOpen_Iio.mem_nhds hp.2)
  filter_upwards [hDnhds, hneg] with q hqD hqneg
  exact ⟨hqD, hqneg⟩

/-- A fixed angular witness with strictly negative signal persists at nearby
radii. The conclusion concerns that signal, not zeros of the profile. -/
theorem negative_witness_eventually
    {A : ℝ → ℝ → ℝ} {r₀ c : ℝ}
    (hA : ContinuousAt (fun r : ℝ => A r c) r₀)
    (hneg : A r₀ c < 0) :
    ∀ᶠ r : ℝ in 𝓝 r₀, A r c < 0 :=
  hA.eventually (isOpen_Iio.mem_nhds hneg)

/-- Metric form of persistence of one strict-negative angular witness. -/
theorem negative_witness_neighborhood
    {A : ℝ → ℝ → ℝ} {r₀ c : ℝ}
    (hA : ContinuousAt (fun r : ℝ => A r c) r₀)
    (hneg : A r₀ c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, dist r r₀ < ε → A r c < 0 := by
  exact Metric.eventually_nhds_iff.mp (negative_witness_eventually hA hneg)

/-- Both radial perturbations retain the same strict-negative witness. -/
theorem negative_witness_two_sided
    {A : ℝ → ℝ → ℝ} {r₀ c : ℝ}
    (hA : ContinuousAt (fun r : ℝ => A r c) r₀)
    (hneg : A r₀ c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε →
      A (r₀ - δ) c < 0 ∧ A (r₀ + δ) c < 0 := by
  obtain ⟨ε, hε, hball⟩ := negative_witness_neighborhood hA hneg
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  have hminus : dist (r₀ - δ) r₀ = |δ| := by
    rw [Real.dist_eq]
    have heq : r₀ - δ - r₀ = -δ := by ring
    rw [heq, abs_neg]
  have hplus : dist (r₀ + δ) r₀ = |δ| := by
    rw [Real.dist_eq]
    have heq : r₀ + δ - r₀ = δ := by ring
    rw [heq]
  exact ⟨hball (r₀ - δ) (by simpa only [hminus] using hδ),
    hball (r₀ + δ) (by simpa only [hplus] using hδ)⟩

/-- An interior zero of a nonnegative slice is a stationary point. The total
derivative formulation needs no extra differentiability premise: Fermat's
theorem applies when it exists, and Lean's total derivative is zero otherwise. -/
theorem derivative_eq_zero_of_nonnegative_zero
    {P : ℝ → ℝ → ℝ} {r a b x : ℝ}
    (hx : x ∈ Ioo a b)
    (hP : ∀ y ∈ Icc a b, 0 ≤ P r y)
    (hzero : P r x = 0) :
    deriv (P r) x = 0 := by
  have hlocal : ∀ᶠ y : ℝ in 𝓝 x, y ∈ Icc a b :=
    Icc_mem_nhds hx.1 hx.2
  have hmin : IsLocalMin (P r) x := by
    filter_upwards [hlocal] with y hy
    rw [hzero]
    exact hP y hy
  exact hmin.deriv_eq_zero

/-- A continuous signal with strict opposite signs at the endpoints has a
zero strictly inside the interval. -/
theorem exists_interior_zero_of_sign_bracket
    {A : ℝ → ℝ → ℝ} {r a b : ℝ}
    (hab : a < b)
    (hA : ContinuousOn (A r) (Icc a b))
    (hleft : A r a < 0)
    (hright : 0 < A r b) :
    ∃ x ∈ Ioo a b, A r x = 0 := by
  have htarget : (0 : ℝ) ∈ Icc (A r a) (A r b) :=
    ⟨hleft.le, hright.le⟩
  obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc hab.le hA htarget
  have hxa : x ≠ a := by
    intro h
    subst x
    exact (ne_of_lt hleft) hzero
  have hxb : x ≠ b := by
    intro h
    subst x
    exact (ne_of_gt hright) hzero
  exact ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),
    lt_of_le_of_ne hx.2 hxb⟩, hzero⟩

/-- A derivative sign bracket on a strictly positive slice produces a
positive stationary point. Strict positivity is supplied as an explicit gap
hypothesis; it is not inferred from continuity or from the sign bracket. -/
theorem exists_positive_stationary_of_sign_bracket
    {P : ℝ → ℝ → ℝ} {r a b : ℝ}
    (hab : a < b)
    (hderiv : ContinuousOn (deriv (P r)) (Icc a b))
    (hleft : deriv (P r) a < 0)
    (hright : 0 < deriv (P r) b)
    (hpositive : ∀ x ∈ Icc a b, 0 < P r x) :
    ∃ x ∈ Ioo a b, 0 < P r x ∧ deriv (P r) x = 0 := by
  obtain ⟨x, hx, hzero⟩ := exists_interior_zero_of_sign_bracket
    (A := fun r x => deriv (P r) x) hab hderiv hleft hright
  exact ⟨x, hx, hpositive x ⟨hx.1.le, hx.2.le⟩, hzero⟩

end AngularRegularity
