import Migration.FrozenBinding
import Bridge.XiWidderIdentification

namespace Merger04.Migration

open Filter Merger04.Regularization
open scoped Topology
open NativeSoloboloNegativity

noncomputable section

/-- The migration's endpoint-safe xi is exactly twice the standard xi normalization
    used by the negativity branch.  The scalar 2 disappears from logarithmic
    derivatives and hence from every Widder moment. -/
theorem ENTIRE_XI_EQ_TWO_XI_ENTIRE (s : ℂ) :
    entireXi s = 2 * xiEntire s := by
  unfold entireXi xiEntire NativeSolobolo.mathlibXi
  ring

/-- Real centered slices differ only by the harmless factor 2. -/
theorem ENTIRE_REAL_SLICE_EQ_TWO_XI_REAL_SLICE (x : ℝ) :
    realSlice entireXi x = 2 * xiRealSlice x := by
  unfold realSlice xiRealSlice
  have hs : (((x + (1 / 2 : ℝ) : ℝ) : ℂ)) =
      (1 / 2 : ℂ) + (x : ℂ) := by
    push_cast
    ring
  rw [hs, ENTIRE_XI_EQ_TWO_XI_ENTIRE]
  simp

/-- Multiplying xi by the nonzero constant 2 does not change theta'/theta. -/
theorem ENTIRE_CENTERED_R_EQ_XI_R (a : ℝ) :
    centeredR entireXi a = xiR a := by
  have hslice : realSlice entireXi = (fun x : ℝ => 2 * xiRealSlice x) := by
    funext x
    exact ENTIRE_REAL_SLICE_EQ_TWO_XI_REAL_SLICE x
  have hd : deriv (realSlice entireXi) (Real.sqrt a) =
      2 * deriv xiRealSlice (Real.sqrt a) := by
    rw [hslice, deriv_const_mul_field]
  have hv : realSlice entireXi (Real.sqrt a) =
      2 * xiRealSlice (Real.sqrt a) :=
    ENTIRE_REAL_SLICE_EQ_TWO_XI_REAL_SLICE (Real.sqrt a)
  unfold centeredR xiR
  dsimp
  rw [hd, hv]
  let x : ℝ := Real.sqrt a
  let d : ℝ := deriv xiRealSlice (Real.sqrt a)
  let f : ℝ := xiRealSlice (Real.sqrt a)
  change (2 * d) / (2 * x * (2 * f)) = d / (2 * x * f)
  have hden : 2 * x * (2 * f) = 2 * (2 * x * f) := by ring
  rw [hden]
  by_cases h : 2 * x * f = 0
  · simp [h]
  · field_simp [h]

/-- Therefore the two depth-zero moments are literally equal as functions. -/
theorem ENTIRE_BASE_MOMENT_EQ_XI_WIDDER_BASE :
    baseMoment entireXi = xiWidderBase := by
  funext a
  unfold baseMoment xiWidderBase
  have hr : (fun t : ℝ => t * centeredR entireXi t) =
      (fun t : ℝ => t * xiR t) := by
    funext t
    rw [ENTIRE_CENTERED_R_EQ_XI_R]
  rw [hr]

/-- The migration's D^2 is the same Euler-square appearing in the direct tower. -/
theorem SCALE_D2_EQ_EULER_SQUARE
    {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) :
    scaleD2 f a =
      a * deriv f a + a ^ 2 * deriv (deriv f) a := by
  change NativeSoloboloNegativity.eulerD
      (NativeSoloboloNegativity.eulerD f) a =
        a * deriv f a + a ^ 2 * deriv (deriv f) a
  exact NativeSoloboloNegativity.EULER_D_SQUARE hf

/-- On analytic germs the two displayed Widder-step formulas coincide. -/
theorem MIGRATION_STEP_EQ_NEGATIVITY_STEP
    (n : ℕ) {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) :
    step n f a = NativeSoloboloNegativity.widderStep n f a := by
  have hD2 := SCALE_D2_EQ_EULER_SQUARE hf
  unfold step NativeSoloboloNegativity.widderStep
  rw [hD2]
  push_cast
  ring

/-- The direct Rodrigues expression is analytic wherever R is analytic. -/
theorem DIRECT_SCALED_ANALYTIC_ON
    {U : Set ℝ} {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    AnalyticOnNhd ℝ (widderDirectScaled R n) U := by
  intro a ha
  have hprod : AnalyticOnNhd ℝ (fun t : ℝ => t ^ (n + 1) * R t) U := by
    intro b hb
    exact (analyticAt_id.pow (n + 1)).mul (hR b hb)
  have hjet := ANALYTIC_ITERATED_DERIV_ON hprod (2 * n + 1)
  unfold widderDirectScaled widderWeight widderRodriguesJet
  exact (analyticAt_id.pow (n + 1)).mul
    (analyticAt_const.mul (hjet a ha))

/-- Direct Widder formula equals the migration recurrence on any open analytic
    R-domain.  This is the normalization bridge needed to reuse the negativity
    layer without changing frozen US. -/
theorem MIGRATION_DIRECT_EQUALS_TOWER_ON_OPEN
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    Set.EqOn (widderDirectScaled R n)
      (tower (widderBaseOf R) n) U := by
  induction n with
  | zero =>
      intro a ha
      exact WIDDER_DIRECT_SCALED_ZERO R a
  | succ n ih =>
      intro a ha
      have hlocal : widderDirectScaled R n =ᶠ[𝓝 a]
          tower (widderBaseOf R) n := by
        filter_upwards [hU.mem_nhds ha] with b hb
        exact ih hb
      have hstepCongr := STEP_EVENTUALLY_EQ n hlocal
      calc
        widderDirectScaled R (n + 1) a =
            NativeSoloboloNegativity.widderStep n
              (widderDirectScaled R n) a :=
          WIDDER_DIRECT_SCALED_STEP hU hR n ha
        _ = step n (widderDirectScaled R n) a := by
          symm
          exact MIGRATION_STEP_EQ_NEGATIVITY_STEP n
            (DIRECT_SCALED_ANALYTIC_ON hR n a ha)
        _ = step n (tower (widderBaseOf R) n) a :=
          hstepCongr.eq_of_nhds
        _ = tower (widderBaseOf R) (n + 1) a := rfl

/-- Actual endpoint-safe migration moments equal the independently defined
    direct Xi-Widder formula at every regular positive anchor. -/
theorem REGULARIZED_MOMENT_EQ_XI_DIRECT_ON_REGULAR_ANCHORS
    (a : ℝ) (ha : a ∈ xiRegularAnchors) (n : ℕ) :
    moment entireXi a n = xiWidderDirect a n := by
  have hbase : baseMoment entireXi = widderBaseOf xiR := by
    rw [ENTIRE_BASE_MOMENT_EQ_XI_WIDDER_BASE]
    rfl
  calc
    moment entireXi a n = tower (baseMoment entireXi) n a := rfl
    _ = tower (widderBaseOf xiR) n a := by rw [hbase]
    _ = widderDirectScaled xiR n a := by
      symm
      exact MIGRATION_DIRECT_EQUALS_TOWER_ON_OPEN
        XI_REGULAR_ANCHORS_OPEN XI_R_ANALYTIC_ON_REGULAR_ANCHORS n ha
    _ = xiWidderDirect a n := XI_DIRECT_SCALED_EQ_DIRECT a n

/-- Transport direct spectral peak data to the exact regularized profile used
    by the frozen-US migration. -/
def directPeakDataToRegularized
    (P : ChannelPeakData xiWidderDirect)
    (hreg : ∀ᶠ n : ℕ in atTop, P.anchor n ∈ xiRegularAnchors) :
    ChannelPeakData (fun a n => moment entireXi a n) :=
  P.transferMoments (by
    filter_upwards [hreg] with n hn
    exact (REGULARIZED_MOMENT_EQ_XI_DIRECT_ON_REGULAR_ANCHORS
      (P.anchor n) hn n).symm)

/-- A regular base anchor plus convergence of the tuned anchors is enough for
    eventual regularity, so no all-positive-anchor nonvanishing theorem is needed. -/
theorem DIRECT_PEAK_DATA_GIVE_REGULARIZED_EVENTUAL_NEGATIVITY
    (P : ChannelPeakData xiWidderDirect)
    (hbase : P.baseAnchor ∈ xiRegularAnchors) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∃ a : ℝ, 0 < a ∧ moment entireXi a n < 0 := by
  have hreg : ∀ᶠ n : ℕ in atTop, P.anchor n ∈ xiRegularAnchors :=
    P.anchorLimit.eventually (XI_REGULAR_ANCHORS_OPEN.mem_nhds hbase)
  exact PEAK_DATA_GIVE_EVENTUAL_NEGATIVE_ANCHORS
    (directPeakDataToRegularized P hreg)

/-- The regularized cofinal positivity predicate excludes the transported
    eventual-negative channel obstruction. -/
theorem REGULARIZED_US_EXCLUDES_DIRECT_PEAK_DATA
    (hUS : RegularizedUS)
    (P : ChannelPeakData xiWidderDirect)
    (hbase : P.baseAnchor ∈ xiRegularAnchors) : False := by
  rcases DIRECT_PEAK_DATA_GIVE_REGULARIZED_EVENTUAL_NEGATIVITY P hbase with
    ⟨K, hneg⟩
  rcases hUS K with ⟨N, hKN, hN⟩
  rcases hneg N hKN with ⟨a, ha, hlt⟩
  exact (not_lt_of_ge (hN a ha)) hlt

end
end Merger04.Migration
