import Mathlib

namespace NativeSoloboloNegativity

open Filter
open scoped Topology

/-- Finitely many convergent channels below M have one eventual bound below M. -/
theorem FINITE_CHANNELS_HAVE_UNIFORM_GAP
    (f : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M)
    (hlim : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (c j)))
    (hstrict : ∀ j, c j < M) (K : ℕ) :
    ∃ eta : ℝ, 0 ≤ eta ∧ eta < M ∧
      ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j < K → f n j ≤ eta := by
  induction K with
  | zero =>
      refine ⟨M / 2, (half_pos hM).le, ?_, ?_⟩
      · linarith
      · exact Filter.Eventually.of_forall (by intro n j hj; omega)
  | succ K ih =>
      rcases ih with ⟨eta, he0, heM, he⟩
      let d : ℝ := (c K + M) / 2
      have hcd : c K < d := by dsimp [d]; linarith [hstrict K]
      have hdM : d < M := by dsimp [d]; linarith [hstrict K]
      have hnew : ∀ᶠ n : ℕ in atTop, f n K < d :=
        (hlim K).eventually (gt_mem_nhds hcd)
      refine ⟨max eta d, le_trans he0 (le_max_left _ _),
        max_lt_iff.mpr ⟨heM, hdM⟩, ?_⟩
      filter_upwards [he, hnew] with n hn hnd
      intro j hj
      by_cases hjK : j < K
      · exact le_trans (hn j hjK) (le_max_left _ _)
      · have hjEq : j = K := by omega
        subst j
        exact le_trans hnd.le (le_max_right _ _)

/-- A finite-head/vanishing-tail argument derives a gap uniform in both depth
    and the countable complement. This fills in the compactness step in the
    paper argument; uniformity is not merely asserted. -/
theorem UNIFORM_GAP_FROM_VANISHING_ENVELOPE
    (f : ℕ → ℕ → ℝ) (c envelope : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M)
    (hlim : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (c j)))
    (hstrict : ∀ j, c j < M)
    (henvelope : ∀ n j, f n j ≤ envelope j)
    (henvelopeLim : Tendsto envelope atTop (𝓝 0)) :
    ∃ eta : ℝ, 0 ≤ eta ∧ eta < M ∧
      ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, f n j ≤ eta := by
  have htail : ∀ᶠ j : ℕ in atTop, envelope j < M / 2 :=
    henvelopeLim.eventually (gt_mem_nhds (half_pos hM))
  rcases Filter.eventually_atTop.1 htail with ⟨K, hK⟩
  rcases FINITE_CHANNELS_HAVE_UNIFORM_GAP f c M hM hlim hstrict K with
    ⟨eta, he0, heM, he⟩
  refine ⟨max eta (M / 2), le_trans he0 (le_max_left _ _),
    max_lt_iff.mpr ⟨heM, by linarith⟩, ?_⟩
  filter_upwards [he] with n hn
  intro j
  by_cases hj : j < K
  · exact le_trans (hn j hj) (le_max_left _ _)
  · have hKj : K ≤ j := by omega
    exact le_trans (henvelope n j)
      (le_trans (hK j hKj).le (le_max_right _ _))

end NativeSoloboloNegativity
