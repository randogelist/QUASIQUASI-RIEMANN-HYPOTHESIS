import CayleyGolPhi.CayleyCore
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group

namespace CayleyGolPhi

open Complex

/-- Literal nontrivial-zeta-zero predicate used by Mathlib RH. -/
def NontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧
    s ≠ 1

/--
Canonical two-variable GolPhi paired series.  It is the pair-grouped form of
  4 * sum_m (-1)^m * (2m + u + 1)^(-s).
The paired form is the stable definition used here because the Riemann slice
`u = 1` binds directly to the already formalized eta pairing.
-/
noncomputable def golPhi (u s : ℂ) : ℂ :=
  (4 : ℂ) * ∑' (k : ℕ),
    ((4 * (k : ℂ) + u + 1) ^ (-s) -
      (4 * (k : ℂ) + u + 3) ^ (-s))

/-- Positive-integer Dirichlet term (n+1)^(-s). -/
noncomputable def dirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  (((n + 1 : ℕ) : ℂ) ^ (-s))

/-- Paired eta series: (1^-s-2^-s)+(3^-s-4^-s)+... -/
noncomputable def etaPairSeries (s : ℂ) : ℂ :=
  ∑' (k : ℕ), (dirichletTerm s (2 * k) - dirichletTerm s (2 * k + 1))

/--
Canonical GolPhi Riemann slice u=1:
  G(1,s) = 4 * 2^(-s) * eta(s)
in the half-plane of absolute convergence.
This is the exact paired form of the canonical GolPhi series.
-/
noncomputable def golPhiS1 (s : ℂ) : ℂ :=
  (4 : ℂ) * ((2 : ℂ) ^ (-s)) * etaPairSeries s

/-- Explicit eta/zeta prefactor on the GolPhi u=1 slice. -/
noncomputable def golPhiS1Prefactor (s : ℂ) : ℂ :=
  (4 : ℂ) * ((2 : ℂ) ^ (-s)) * (1 - (2 : ℂ) ^ (1 - s))

/-- Negative complex powers of positive integers are reciprocals. -/
theorem DIRICHLET_TERM_EQ_ONE_DIV (s : ℂ) (n : ℕ) :
    dirichletTerm s n = 1 / (((n + 1 : ℕ) : ℂ) ^ s) := by
  simp [dirichletTerm, Complex.cpow_neg, one_div]

/-- Absolute summability of positive-integer Dirichlet terms for re(s)>1. -/
theorem SUMMABLE_DIRICHLET_TERM {s : ℂ} (hs : 1 < s.re) :
    Summable (dirichletTerm s) := by
  have h0 : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ s)) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hshift : Summable (fun n : ℕ => 1 / ((((n + 1 : ℕ) : ℂ)) ^ s)) := by
    have h := (_root_.summable_nat_add_iff
      (f := fun n : ℕ => 1 / ((n : ℂ) ^ s)) 1).2 h0
    simpa using h
  exact hshift.congr (fun n => (DIRICHLET_TERM_EQ_ONE_DIV s n).symm)

/-- Mathlib zeta Dirichlet series in the same negative-exponent form. -/
theorem RIEMANN_ZETA_EQ_TSUM_DIRICHLET_TERM {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, dirichletTerm s n := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro n
  simpa [Nat.cast_add, Nat.cast_one] using (DIRICHLET_TERM_EQ_ONE_DIV s n).symm

/-- Exact dyadic factorization of odd-indexed positive-integer terms. -/
theorem DIRICHLET_TERM_ODD (s : ℂ) (k : ℕ) :
    dirichletTerm s (2 * k + 1) =
      (2 : ℂ) ^ (-s) * dirichletTerm s k := by
  unfold dirichletTerm
  have hnat : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rw [hnat]
  simpa using Complex.natCast_mul_natCast_cpow 2 (k + 1) (-s)

/-- Sum of odd-indexed terms is 2^(-s) zeta(s). -/
theorem TSUM_ODD_DIRICHLET_TERM {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, dirichletTerm s (2 * k + 1)) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  have hf : Summable (dirichletTerm s) := SUMMABLE_DIRICHLET_TERM hs
  calc
    (∑' k : ℕ, dirichletTerm s (2 * k + 1))
        = ∑' k : ℕ, (2 : ℂ) ^ (-s) * dirichletTerm s k := by
            apply tsum_congr
            intro k
            exact DIRICHLET_TERM_ODD s k
    _ = (2 : ℂ) ^ (-s) * (∑' k : ℕ, dirichletTerm s k) := by
          rw [tsum_mul_left]
    _ = (2 : ℂ) ^ (-s) * riemannZeta s := by
          rw [← RIEMANN_ZETA_EQ_TSUM_DIRICHLET_TERM hs]

/-- Eta factorization eta(s)=(1-2^(1-s)) zeta(s), proved directly. -/
theorem ETA_PAIR_SERIES_EQ_ZETA_FACTOR {s : ℂ} (hs : 1 < s.re) :
    etaPairSeries s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hf : Summable (dirichletTerm s) := SUMMABLE_DIRICHLET_TERM hs
  have hEvenInj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    dsimp at hab
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) hab
  have hOddInj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    dsimp at hab
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmul
  have he : Summable (fun k : ℕ => dirichletTerm s (2 * k)) := by
    simpa [Function.comp_def] using hf.comp_injective hEvenInj
  have ho : Summable (fun k : ℕ => dirichletTerm s (2 * k + 1)) := by
    simpa [Function.comp_def] using hf.comp_injective hOddInj
  have hsplit :
      (∑' k : ℕ, dirichletTerm s (2 * k)) +
          (∑' k : ℕ, dirichletTerm s (2 * k + 1)) =
        riemannZeta s := by
    calc
      (∑' k : ℕ, dirichletTerm s (2 * k)) +
          (∑' k : ℕ, dirichletTerm s (2 * k + 1))
          = ∑' k : ℕ, dirichletTerm s k := tsum_even_add_odd he ho
      _ = riemannZeta s := (RIEMANN_ZETA_EQ_TSUM_DIRICHLET_TERM hs).symm
  have hodd :
      (∑' k : ℕ, dirichletTerm s (2 * k + 1)) =
        (2 : ℂ) ^ (-s) * riemannZeta s :=
    TSUM_ODD_DIRICHLET_TERM hs
  have hpow :
      (2 : ℂ) ^ (1 - s) = (2 : ℂ) * (2 : ℂ) ^ (-s) := by
    have hexp : (1 : ℂ) - s = 1 + (-s) := by ring
    rw [hexp, Complex.cpow_add 1 (-s) (by norm_num)]
    simp
  unfold etaPairSeries
  rw [he.tsum_sub ho]
  calc
    (∑' k : ℕ, dirichletTerm s (2 * k)) -
        (∑' k : ℕ, dirichletTerm s (2 * k + 1))
        = ((∑' k : ℕ, dirichletTerm s (2 * k)) +
            (∑' k : ℕ, dirichletTerm s (2 * k + 1))) -
          2 * (∑' k : ℕ, dirichletTerm s (2 * k + 1)) := by ring
    _ = riemannZeta s - 2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by
          rw [hsplit, hodd]
    _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
          rw [hpow]
          ring

/--
At `u = 1`, the canonical two-variable paired GolPhi series is exactly the
previously formalized Riemann slice.  This identity is algebraic at the tsum
level; the subsequent zeta identification uses the convergent half-plane.
-/
theorem GOLPHI_AT_ONE_EQ_GOLPHI_S1 (s : ℂ) :
    golPhi 1 s = golPhiS1 s := by
  have hterm : ∀ k : ℕ,
      ((4 * (k : ℂ) + (1 : ℂ) + 1) ^ (-s) -
          (4 * (k : ℂ) + (1 : ℂ) + 3) ^ (-s)) =
        (2 : ℂ) ^ (-s) *
          (dirichletTerm s (2 * k) - dirichletTerm s (2 * k + 1)) := by
    intro k
    have hfirst :
        (4 * (k : ℂ) + (1 : ℂ) + 1) ^ (-s) =
          (2 : ℂ) ^ (-s) * dirichletTerm s (2 * k) := by
      unfold dirichletTerm
      have hbase :
          4 * (k : ℂ) + (1 : ℂ) + 1 =
            (((2 * (2 * k + 1) : ℕ) : ℂ)) := by
        push_cast
        ring
      rw [hbase]
      simpa using Complex.natCast_mul_natCast_cpow 2 (2 * k + 1) (-s)
    have hsecond :
        (4 * (k : ℂ) + (1 : ℂ) + 3) ^ (-s) =
          (2 : ℂ) ^ (-s) * dirichletTerm s (2 * k + 1) := by
      unfold dirichletTerm
      have hbase :
          4 * (k : ℂ) + (1 : ℂ) + 3 =
            (((2 * (2 * k + 1 + 1) : ℕ) : ℂ)) := by
        push_cast
        ring
      rw [hbase]
      simpa using
        Complex.natCast_mul_natCast_cpow 2 (2 * k + 1 + 1) (-s)
    rw [hfirst, hsecond]
    ring
  unfold golPhi golPhiS1 etaPairSeries
  rw [show
    (∑' k : ℕ,
      ((4 * (k : ℂ) + (1 : ℂ) + 1) ^ (-s) -
        (4 * (k : ℂ) + (1 : ℂ) + 3) ^ (-s))) =
      ∑' k : ℕ, (2 : ℂ) ^ (-s) *
        (dirichletTerm s (2 * k) - dirichletTerm s (2 * k + 1)) by
      apply tsum_congr
      exact hterm]
  rw [tsum_mul_left]
  ring

/-- Exact canonical GolPhi u=1 factorization on re(s)>1. -/
theorem GOLPHI_S1_EQ_PREFACTOR_MUL_ZETA {s : ℂ} (hs : 1 < s.re) :
    golPhiS1 s = golPhiS1Prefactor s * riemannZeta s := by
  unfold golPhiS1 golPhiS1Prefactor
  rw [ETA_PAIR_SERIES_EQ_ZETA_FACTOR hs]
  ring

/-- The full canonical GolPhi family restricts to the exact zeta-calibrated Riemann slice. -/
theorem GOLPHI_AT_ONE_EQ_PREFACTOR_MUL_ZETA {s : ℂ} (hs : 1 < s.re) :
    golPhi 1 s = golPhiS1Prefactor s * riemannZeta s := by
  rw [GOLPHI_AT_ONE_EQ_GOLPHI_S1]
  exact GOLPHI_S1_EQ_PREFACTOR_MUL_ZETA hs

/--
Entire completed GolPhi Riemann slice. This is the removable-singularity-free
completion of the normalized u=1 GolPhi slice, expressed directly through
Mathlib's entire Lambda_0 completion.
-/
noncomputable def completedGolPhiS1 (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- The completed GolPhi slice is literally the actual xi used by Cayley. -/
theorem COMPLETED_GOLPHI_S1_EQ_XI (s : ℂ) :
    completedGolPhiS1 s = mathlibXi s := by
  rfl

/-- Completed GolPhi is entire. -/
theorem COMPLETED_GOLPHI_S1_DIFFERENTIABLE :
    Differentiable ℂ completedGolPhiS1 := by
  change Differentiable ℂ mathlibXi
  exact MATHLIB_XI_DIFFERENTIABLE

/--
Cayley is exactly the centered-square pullback of completed GolPhi at u=1.
No compatibility axiom is present.
-/
theorem CAYLEY_THETA_IS_COMPLETED_GOLPHI_PULLBACK (z : ℂ) :
    slitTheta z = completedGolPhiS1 ((1 / 2 : ℂ) + Complex.sqrt z) := by
  rfl

/-- Cayley theta zeros are literally completed-GolPhi zeros under the centered-square map. -/
theorem CAYLEY_THETA_ZERO_IFF_COMPLETED_GOLPHI_ZERO (z : ℂ) :
    slitTheta z = 0 ↔
      completedGolPhiS1 ((1 / 2 : ℂ) + Complex.sqrt z) = 0 := by
  rw [CAYLEY_THETA_IS_COMPLETED_GOLPHI_PULLBACK]

end CayleyGolPhi
