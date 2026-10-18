import MisterPremise.MathlibImports

/-!
# Isolation of zero radii

For a nonzero entire function, only finitely many zeros lie in a compact set.
Consequently, the moduli of its zeros have a gap around every fixed radius,
except possibly for zeros having exactly that radius. In particular, existence
of a zero on one circle does not propagate to nearby circles.

The proofs below use no RH or angular-sign hypothesis. The intermediate finite
set statement is exposed separately so the compactness step can be audited.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AngularRegularity

/-- A circle of radius `r` contains a zero of `f`. This includes all angles. -/
def zeroRadius (f : ℂ → ℂ) (r : ℝ) : Prop :=
  ∃ z : ℂ, f z = 0 ∧ ‖z‖ = r

/-- All zero radii sufficiently close to `r₀` equal `r₀` itself. -/
def radiusGap (f : ℂ → ℂ) (r₀ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ z : ℂ, f z = 0 → |‖z‖ - r₀| < ε → ‖z‖ = r₀

/-- A finite collection of points has only finitely many radii, so it has a
positive radial separation from any fixed radius after that radius is removed.
Repeated points or repeated moduli cause no problem. -/
theorem finite_points_radius_gap (S : Finset ℂ) (r₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ S, |‖z‖ - r₀| < ε → ‖z‖ = r₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro z hz
      simp at hz
  | @insert a S ha ih =>
      obtain ⟨ε, hε, hgap⟩ := ih
      by_cases hsame : ‖a‖ = r₀
      · refine ⟨ε, hε, ?_⟩
        intro z hz hclose
        rcases Finset.mem_insert.mp hz with hza | hzS
        · subst z
          exact hsame
        · exact hgap z hzS hclose
      · have hapos : 0 < |‖a‖ - r₀| :=
          abs_pos.mpr (sub_ne_zero.mpr hsame)
        refine ⟨min ε |‖a‖ - r₀|, lt_min_iff.mpr ⟨hε, hapos⟩, ?_⟩
        intro z hz hclose
        rcases Finset.mem_insert.mp hz with hza | hzS
        · subst z
          exact False.elim ((lt_irrefl |‖a‖ - r₀|)
            (lt_of_lt_of_le hclose (min_le_right _ _)))
        · exact hgap z hzS (lt_of_lt_of_le hclose (min_le_left _ _))

/-- Entire analyticity and one nonzero value imply finiteness of the zero set
inside every compact subset of the complex plane. -/
theorem zeros_in_compact_finite
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ a : ℂ, f a ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | f z = 0 ∧ z ∈ K}.Finite := by
  have hcod : {z : ℂ | f z ≠ 0} ∈ Filter.codiscreteWithin Set.univ := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
        isPreconnected_univ with hzero | hnonzero
    · obtain ⟨a, ha⟩ := hne
      exact False.elim (ha (hzero (Set.mem_univ a)))
    · exact hnonzero
  have hKcod : {z : ℂ | f z ≠ 0} ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K) hcod
  have hfinite := hK.finite_sdiff_of_mem_codiscreteWithin hKcod
  apply hfinite.subset
  intro z hz
  exact ⟨hz.2, fun hnotzero => hnotzero hz.1⟩

/-- Concrete disk version of compact zero finiteness. The bound `R` need not be
positive; if it is negative the set is empty. -/
theorem zeros_in_disk_finite
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ a : ℂ, f a ≠ 0) (R : ℝ) :
    {z : ℂ | f z = 0 ∧ ‖z‖ ≤ R}.Finite := by
  have hfinite := zeros_in_compact_finite hf hne (isCompact_closedBall (0 : ℂ) R)
  apply hfinite.subset
  intro z hz
  refine ⟨hz.1, ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2

/-- Finitely many zeros in one sufficiently large disk already suffice for
radial isolation. The finite hypothesis is the only input in this lemma. -/
theorem radiusGap_of_finite_disk_zeros
    {f : ℂ → ℂ} {r₀ : ℝ}
    (hfinite : {z : ℂ | f z = 0 ∧ ‖z‖ ≤ r₀ + 1}.Finite) :
    radiusGap f r₀ := by
  classical
  obtain ⟨ε, hε, hgap⟩ := finite_points_radius_gap hfinite.toFinset r₀
  refine ⟨min ε 1, lt_min_iff.mpr ⟨hε, by norm_num⟩, ?_⟩
  intro z hz hclose
  have habs : |‖z‖ - r₀| < 1 :=
    lt_of_lt_of_le hclose (min_le_right _ _)
  have hbound : ‖z‖ ≤ r₀ + 1 := by
    have hu := (abs_lt.mp habs).2
    linarith
  have hzS : z ∈ hfinite.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hz, hbound⟩
  exact hgap z hzS (lt_of_lt_of_le hclose (min_le_left _ _))

/-- Full analytic radius-isolation theorem. This does not assume that `r₀` is
itself a zero radius. -/
theorem radiusGap_of_analytic_nonzero
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ a : ℂ, f a ≠ 0) (r₀ : ℝ) :
    radiusGap f r₀ :=
  radiusGap_of_finite_disk_zeros (zeros_in_disk_finite hf hne (r₀ + 1))

/-- A radial gap excludes zeros on every nearby circle with a different
radius. -/
theorem no_nearby_zeroRadius_of_radiusGap
    {f : ℂ → ℂ} {r₀ : ℝ} (hgap : radiusGap f r₀) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, |r - r₀| < ε → r ≠ r₀ → ¬ zeroRadius f r := by
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, ?_⟩
  intro r hclose hne hr
  obtain ⟨z, hz, hzr⟩ := hr
  apply hne
  have heq := hgap z hz (by simpa only [hzr] using hclose)
  simpa only [hzr] using heq

/-- Both sufficiently small, nonzero radial perturbations contain no zeros.
This is consistent with persistence of a negative angular derivative. -/
theorem no_zeroRadius_two_sided_of_analytic_nonzero
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ a : ℂ, f a ≠ 0) (r₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ¬ zeroRadius f (r₀ - δ) ∧ ¬ zeroRadius f (r₀ + δ) := by
  obtain ⟨ε, hε, hgap⟩ := no_nearby_zeroRadius_of_radiusGap
    (radiusGap_of_analytic_nonzero hf hne r₀)
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε
  have hminus : |r₀ - δ - r₀| < ε := by
    have heq : r₀ - δ - r₀ = -δ := by ring
    simpa only [heq, abs_neg, abs_of_pos hδ] using hδε
  have hplus : |r₀ + δ - r₀| < ε := by
    have heq : r₀ + δ - r₀ = δ := by ring
    simpa only [heq, abs_of_pos hδ] using hδε
  exact ⟨hgap (r₀ - δ) hminus (by linarith),
    hgap (r₀ + δ) hplus (by linarith)⟩

end AngularRegularity
