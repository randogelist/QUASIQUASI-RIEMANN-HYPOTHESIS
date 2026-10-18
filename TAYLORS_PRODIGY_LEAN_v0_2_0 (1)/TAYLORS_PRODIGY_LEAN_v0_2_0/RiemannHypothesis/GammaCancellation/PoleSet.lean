/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.Ring

/-!
# GammaCancellation.PoleSet

The Γ-pole set of the complex Gamma function and its completed-ξ pullback, together
with the topological facts the Γ-cancellation bridge depends on.

`Γ(z)` has simple poles exactly at the non-positive integers `z ∈ {0, -1, -2, …}`.
The raw completed-ξ function carries a `Γ(s/2)` factor, so its Γ-singularities sit at
`s/2 ∈ {0, -1, -2, …}`, i.e. `s ∈ {0, -2, -4, …}`. This module names

* `gammaPoleSet` — the set `{-n : n ∈ ℕ}` of Γ poles in `ℂ`;
* `completedXiGammaPolePullbackSet` — its pullback under `s ↦ s/2`;

and proves the two topological inputs the bridge needs:

* `isClosed_gammaPoleSet` — `gammaPoleSet` is closed in `ℂ`;
* `gammaPoleAvoidingNeighborhoodSource` — every point off the pole set has an open
  neighborhood that avoids it (discreteness, packaged as data).
-/

namespace OverflowResidueRH

/-- **Γ pole set**: complex points `-n` for `n : ℕ` (where `Γ` has poles). -/
def gammaPoleSet : Set ℂ :=
  {z : ℂ | ∃ n : ℕ, z = -((n : ℂ))}

/-- **Completed-ξ Γ-pole pullback**: `s` such that `Γ(s/2)` is at a pole. -/
def completedXiGammaPolePullbackSet : Set ℂ :=
  {s : ℂ | s / 2 ∈ gammaPoleSet}

/-- ⭐ **PROVED — `gammaPoleSet` membership unfold.** -/
theorem mem_gammaPoleSet_iff (z : ℂ) :
    z ∈ gammaPoleSet ↔ ∃ n : ℕ, z = -((n : ℂ)) := Iff.rfl

/-- ⭐ **PROVED — pullback membership unfold.** -/
theorem mem_completedXiGammaPolePullbackSet_iff (s : ℂ) :
    s ∈ completedXiGammaPolePullbackSet ↔ s / 2 ∈ gammaPoleSet := Iff.rfl

/-- 📦 **`GammaPoleAvoidingNeighborhoodSource`** — every `s` with
`s/2 ∉ gammaPoleSet` has an open neighborhood where `w/2 ∉ gammaPoleSet`
for all `w`. The topological discreteness claim, packaged as data. -/
structure GammaPoleAvoidingNeighborhoodSource : Prop where
  exists_avoiding_nhds :
    ∀ s : ℂ,
      s / 2 ∉ gammaPoleSet →
      ∃ U : Set ℂ,
        IsOpen U ∧ s ∈ U ∧
        (∀ w ∈ U, w / 2 ∉ gammaPoleSet)

/-- 📦 **`IsClosedGammaPoleSetSource`** — topological discreteness
of `gammaPoleSet`, packaged as a target. -/
structure IsClosedGammaPoleSetSource : Prop where
  isClosed : IsClosed gammaPoleSet

/-- 🌟🌟🌟 **PROVED — `GammaPoleAvoidingNeighborhoodSource` from
`IsClosed gammaPoleSet`.** Closed complement + preimage of open
under continuous `w ↦ w/2`. -/
theorem GammaPoleAvoidingNeighborhoodSource.of_isClosed
    (H : IsClosedGammaPoleSetSource) :
    GammaPoleAvoidingNeighborhoodSource := by
  refine ⟨?_⟩
  intro s hs
  refine ⟨{w : ℂ | w / 2 ∉ gammaPoleSet}, ?_, hs, ?_⟩
  · have hcont : Continuous (fun w : ℂ => w / 2) :=
      continuous_id.div_const _
    exact (H.isClosed.isOpen_compl).preimage hcont
  · intro w hw
    exact hw

/-- ⭐ **PROVED — `‖(n : ℂ)‖ = n` for natural `n`.** -/
theorem norm_natCast_complex (n : ℕ) : ‖(n : ℂ)‖ = n := by
  simp

/-- ⭐ **PROVED — `‖-((n : ℂ))‖ = n`.** -/
theorem norm_neg_natCast_complex (n : ℕ) : ‖-((n : ℂ))‖ = n := by
  rw [norm_neg, norm_natCast_complex]

/-- 🌟🌟🌟🌟 **PROVED — `gammaPoleSet` is closed in ℂ.** -/
theorem isClosed_gammaPoleSet : IsClosed gammaPoleSet := by
  -- Step 1: `gammaPoleSet = -·⁻¹ Set.range ((↑) : ℕ → ℂ)`.
  have h_eq : gammaPoleSet = Neg.neg ⁻¹' Set.range ((↑) : ℕ → ℂ) := by
    ext z
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simp [hn]
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have : -((n : ℂ)) = z := by rw [hn]; ring
      exact this.symm
  rw [h_eq]
  refine IsClosed.preimage continuous_neg ?_
  -- Step 2: `Set.range ((↑) : ℕ → ℂ) = (Im⁻¹{0}) ∩ (Re⁻¹ Set.range ((↑) : ℕ → ℝ))`.
  have h_re_im :
      Set.range ((↑) : ℕ → ℂ)
        = (Complex.im ⁻¹' ({0} : Set ℝ)) ∩
          (Complex.re ⁻¹' Set.range ((↑) : ℕ → ℝ)) := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨?_, n, ?_⟩
      · simp
      · simp
    · rintro ⟨him, n, hre⟩
      refine ⟨n, ?_⟩
      apply Complex.ext
      · -- goal: ((n : ℂ)).re = z.re
        have h3 : ((n : ℂ)).re = (n : ℝ) := by simp
        exact h3.trans hre
      · -- goal: ((n : ℂ)).im = z.im
        have h4 : ((n : ℂ)).im = 0 := by simp
        exact h4.trans him.symm
  rw [h_re_im]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_singleton.preimage Complex.continuous_im
  · exact Nat.isClosedEmbedding_coe_real.isClosed_range.preimage
      Complex.continuous_re

/-- 🌟🌟 **PROVED unconditionally.** -/
theorem isClosedGammaPoleSetSource :
    IsClosedGammaPoleSetSource :=
  ⟨isClosed_gammaPoleSet⟩

/-- 🌟🌟 **PROVED unconditionally — `GammaPoleAvoidingNeighborhoodSource`.** -/
theorem gammaPoleAvoidingNeighborhoodSource :
    GammaPoleAvoidingNeighborhoodSource :=
  GammaPoleAvoidingNeighborhoodSource.of_isClosed isClosedGammaPoleSetSource

end OverflowResidueRH
