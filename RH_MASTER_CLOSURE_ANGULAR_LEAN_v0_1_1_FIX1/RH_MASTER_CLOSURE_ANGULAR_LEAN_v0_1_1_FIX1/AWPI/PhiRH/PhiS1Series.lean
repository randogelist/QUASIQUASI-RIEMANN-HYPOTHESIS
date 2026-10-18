import AWPI.PhiRH.S1Prefactor
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group

namespace AWPI.PhiRH.PhiS1Series

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.NativeZetaSupport
open AWPI.PhiRH.S1Prefactor
open AWPI.PhiRH.ShiftedSliceFrontier
open AWPI.PhiRH.TransverseFrontier
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.ActivityFrontier

/-- The positive-integer Dirichlet term `(n+1)^(-s)`.  This is definitionally
    equivalent to `1 / (n+1)^s`, but the negative-exponent form makes the
    dyadic odd-subsequence factorization exact by `natCast_mul_natCast_cpow`. -/
noncomputable def dirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  (((n + 1 : ℕ) : ℂ) ^ (-s))

/-- The paired alternating Dirichlet series

      (1^-s - 2^-s) + (3^-s - 4^-s) + ... .

    On `re s > 1` it is absolutely summable and equals the ordinary eta
    series.  Pairing mirrors the even/odd cell split in the supplied Phi
    construction and avoids any conditional-rearrangement issue. -/
noncomputable def etaPairSeries (s : ℂ) : ℂ :=
  ∑' (k : ℕ), (dirichletTerm s (2 * k) - dirichletTerm s (2 * k + 1))

/-- Concrete u=1 Phi cell-series value: `4 * 2^(-s)` times the paired eta
    series.  This is the complex form of the supplied u=1 cell formula. -/
noncomputable def phiS1CellSeries (s : ℂ) : ℂ :=
  (4 : ℂ) * ((2 : ℂ) ^ (-s)) * etaPairSeries s

/-- Negative complex powers of positive integers agree with reciprocal positive
    powers. -/
theorem dirichletTerm_eq_one_div (s : ℂ) (n : ℕ) :
    dirichletTerm s n = 1 / (((n + 1 : ℕ) : ℂ) ^ s) := by
  simp [dirichletTerm, Complex.cpow_neg, one_div]

/-- Absolute summability of the positive-integer Dirichlet terms in the
    half-plane `re s > 1`. -/
theorem summable_dirichletTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (dirichletTerm s) := by
  have h0 : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ s)) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hshift : Summable (fun n : ℕ => 1 / ((((n + 1 : ℕ) : ℂ)) ^ s)) := by
    have h := (_root_.summable_nat_add_iff
      (f := fun n : ℕ => 1 / ((n : ℂ) ^ s)) 1).2 h0
    simpa using h
  exact hshift.congr (fun n => (dirichletTerm_eq_one_div s n).symm)

/-- Mathlib's native zeta Dirichlet series, rewritten in negative-exponent
    form. -/
theorem riemannZeta_eq_tsum_dirichletTerm {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, dirichletTerm s n := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro n
  simpa [Nat.cast_add, Nat.cast_one] using (dirichletTerm_eq_one_div s n).symm

/-- Exact dyadic factorization of the odd-indexed positive-integer terms. -/
theorem dirichletTerm_odd (s : ℂ) (k : ℕ) :
    dirichletTerm s (2 * k + 1) =
      (2 : ℂ) ^ (-s) * dirichletTerm s k := by
  unfold dirichletTerm
  have hnat : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rw [hnat]
  simpa using Complex.natCast_mul_natCast_cpow 2 (k + 1) (-s)

/-- The sum of the odd-indexed positive-integer terms is `2^(-s) ζ(s)`. -/
theorem tsum_odd_dirichletTerm {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, dirichletTerm s (2 * k + 1)) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  have hf : Summable (dirichletTerm s) := summable_dirichletTerm hs
  calc
    (∑' k : ℕ, dirichletTerm s (2 * k + 1))
        = ∑' k : ℕ, (2 : ℂ) ^ (-s) * dirichletTerm s k := by
            apply tsum_congr
            intro k
            exact dirichletTerm_odd s k
    _ = (2 : ℂ) ^ (-s) * (∑' k : ℕ, dirichletTerm s k) := by
          rw [tsum_mul_left]
    _ = (2 : ℂ) ^ (-s) * riemannZeta s := by
          rw [← riemannZeta_eq_tsum_dirichletTerm hs]

/-- Dirichlet eta factorization on the absolute-convergence half-plane:

      eta(s) = (1 - 2^(1-s)) zeta(s).

    This is proved directly from Mathlib's native zeta Dirichlet series and
    the even/odd decomposition; it is proved rather than taken as a project premise. -/
theorem etaPairSeries_eq_zeta_factor {s : ℂ} (hs : 1 < s.re) :
    etaPairSeries s =
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hf : Summable (dirichletTerm s) := summable_dirichletTerm hs
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
    simpa [Function.comp_def] using
      hf.comp_injective hEvenInj
  have ho : Summable (fun k : ℕ => dirichletTerm s (2 * k + 1)) := by
    simpa [Function.comp_def] using
      hf.comp_injective hOddInj
  have hsplit :
      (∑' k : ℕ, dirichletTerm s (2 * k)) +
          (∑' k : ℕ, dirichletTerm s (2 * k + 1)) =
        riemannZeta s := by
    calc
      (∑' k : ℕ, dirichletTerm s (2 * k)) +
          (∑' k : ℕ, dirichletTerm s (2 * k + 1))
          = ∑' k : ℕ, dirichletTerm s k := tsum_even_add_odd he ho
      _ = riemannZeta s := (riemannZeta_eq_tsum_dirichletTerm hs).symm
  have hodd :
      (∑' k : ℕ, dirichletTerm s (2 * k + 1)) =
        (2 : ℂ) ^ (-s) * riemannZeta s :=
    tsum_odd_dirichletTerm hs
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
    _ = riemannZeta s -
          2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by rw [hsplit, hodd]
    _ = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
          rw [hpow]
          ring

/-- The concrete u=1 Phi cell series satisfies the exact S1 Phi-zeta value
    factorization on `re s > 1`. -/
theorem phiS1CellSeries_eq_s1Prefactor_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    phiS1CellSeries s = s1Prefactor s * riemannZeta s := by
  unfold phiS1CellSeries s1Prefactor
  rw [etaPairSeries_eq_zeta_factor hs]
  ring

/-- At the shifted point of every nontrivial zeta zero, the concrete u=1 cell
    series has the required S1 factorization. -/
theorem shifted_phiS1CellSeries_factorization
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    phiS1CellSeries (rho + 1) =
      s1Prefactor (rho + 1) * riemannZeta (rho + 1) := by
  have hre : 0 < rho.re := nontrivialZetaZero_re_pos rho hz
  have hs : 1 < (rho + 1).re := by
    simpa using add_lt_add_right hre 1
  exact phiS1CellSeries_eq_s1Prefactor_mul_zeta hs

/-- The old Phi-zeta value-identity frontier is reduced to a strictly narrower
    construction-binding statement: the project's u=1 Phi value agrees with
    the concrete cell series supplied by its own cell formula. -/
theorem shiftedSlice_nonzero_of_phiS1CellSeries_binding
    (phiS1 : ℂ → ℂ)
    (rho : ℂ) (hz : NontrivialZetaZero rho)
    (hbind : phiS1 (rho + 1) = phiS1CellSeries (rho + 1)) :
    phiS1 (rho + 1) ≠ 0 := by
  apply shiftedSlice_nonzero_of_phi_zeta_value_identity phiS1 rho hz
  calc
    phiS1 (rho + 1) = phiS1CellSeries (rho + 1) := hbind
    _ = s1Prefactor (rho + 1) * riemannZeta (rho + 1) :=
      shifted_phiS1CellSeries_factorization rho hz

/-- Native RH closure with the S1 eta-zeta analytic factorization proved.
    The shifted branch now assumes only that the project's Phi slice is the
    concrete cell-series value. -/
theorem MATHLIB_RH_OF_SEVEN_PHI_CELL_SERIES_FRONTIER_LEAVES
    (phiS1 : ℂ → ℂ)
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (phiS1CellSeriesBinding :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiS1 (rho + 1) = phiS1CellSeries (rho + 1))
    (transverseNorm2_identity :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiTransverseJet rho = rhoNorm2 rho * shiftedPhiNorm2 phiS1 rho)
    (plusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → plusJetScale rho ≠ 0)
    (minusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → minusJetScale rho ≠ 0)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetPlus plusJetScale phiTransverseJet rho) ^ 2 -
            (boundJetPlus plusJetScale phiTransverseJet rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetMinus minusJetScale phiTransverseJet rho) ^ 2 -
            (boundJetMinus minusJetScale phiTransverseJet rho) ^ 2 ≤
          -(finiteMinusSquare n rho) ^ 2 +
            actualKQMinusSource n rho.re rho.im *
              actualKQMinusSource n rho.re rho.im)
    (jointTailDecay :
      ∀ (rho : ℂ) (eps : ℝ), NontrivialZetaZero rho → 0 < eps →
        ∃ n : ℕ,
          actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im ≤ eps ∧
          actualKQMinusSource n rho.re rho.im *
              actualKQMinusSource n rho.re rho.im ≤ eps) :
    RiemannHypothesis := by
  apply MATHLIB_RH_OF_SEVEN_PHI_ZETA_FRONTIER_LEAVES
    phiS1 phiTransverseJet plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho hz
    calc
      phiS1 (rho + 1) = phiS1CellSeries (rho + 1) := phiS1CellSeriesBinding rho hz
      _ = s1Prefactor (rho + 1) * riemannZeta (rho + 1) :=
        shifted_phiS1CellSeries_factorization rho hz
  · exact transverseNorm2_identity
  · exact plusBindingScale_nonzero
  · exact minusBindingScale_nonzero
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.PhiS1Series
