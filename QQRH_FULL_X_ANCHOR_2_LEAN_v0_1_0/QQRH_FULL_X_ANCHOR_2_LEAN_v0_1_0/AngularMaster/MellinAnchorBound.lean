import AngularMaster.MellinEndpointBound
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open MeasureTheory Set Real
open OverflowResidueRH

namespace AngularMaster

/-- A two-exponential majorant of a negative power, sharp to first order at one. -/
theorem rpow_neg_le_exp_majorant {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x) :
    x ^ (-a) ≤ 1 - a / (a + 1) +
      a / (a + 1) * exp (-(a + 1) * (x - 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  let f : ℝ → ℝ := fun y => y ^ (-a) - a / (a + 1) * exp (-(a + 1) * (y - 1))
  have hd (y : ℝ) (hy : 1 ≤ y) :
      HasDerivAt f (-a * y ^ (-a - 1) + a * exp (-(a + 1) * (y - 1))) y := by
    have hy0 : y ≠ 0 := ne_of_gt (zero_lt_one.trans_le hy)
    convert! (Real.hasDerivAt_rpow_const (x := y) (p := -a) (Or.inl hy0)).sub
      (((((hasDerivAt_id y).sub_const 1).const_mul (-(a + 1))).exp).const_mul (a / (a + 1))) using 1 <;>
      try simp only [f, id_eq]
    all_goals try rfl
    all_goals field_simp
    all_goals ring
  have hm : AntitoneOn f (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy1 : 1 ≤ y := interior_subset hy
      have hy0 : 0 < y := zero_lt_one.trans_le hy1
      rw [(hd y hy1).deriv]
      have he : exp (-(a + 1) * (y - 1)) ≤ y ^ (-a - 1) := by
        rw [Real.rpow_def_of_pos hy0]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonpos_left (Real.log_le_sub_one_of_pos hy0)
          (show -(a + 1) ≤ 0 by linarith)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left he ha]
  have hh := hm (show (1 : ℝ) ∈ Ici 1 by simp) hx hx
  dsimp [f] at hh
  simp only [Real.one_rpow, sub_self, mul_zero, exp_zero, mul_one] at hh
  linarith

/-- Retaining a negative Mellin weight improves the exponential endpoint bound. -/
theorem integral_Ioi_one_rpow_neg_exp_le {a p : ℝ} (ha : 0 ≤ a) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 1, x ^ (-a) * exp (-(p * x))) ≤
      exp (-p) / p * (1 - a / (p + a + 1)) := by
  let b := a + 1
  have hb : 0 < b := by dsimp [b]; linarith
  have hpb : 0 < p + b := add_pos hp hb
  have hint : IntegrableOn (fun x : ℝ => x ^ (-a) * exp (-(p * x))) (Ioi 1) :=
    integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat 0 hp (by simp; linarith)
  have heint (q : ℝ) (hq : 0 < q) :
      IntegrableOn (fun x : ℝ => exp (-(q * x))) (Ioi 1) := by
    simpa only [neg_mul, IntegrableOn] using
      (integrableOn_exp_mul_Ioi (a := -q) (by linarith) 1)
  let g : ℝ → ℝ := fun x => (1 - a / b) * exp (-(p * x)) +
    (a / b * exp b) * exp (-((p + b) * x))
  have hgint : IntegrableOn g (Ioi 1) :=
    ((heint p hp).const_mul (1 - a / b)).add
      ((heint (p + b) hpb).const_mul (a / b * exp b))
  have hpoint (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      x ^ (-a) * exp (-(p * x)) ≤ g x := by
    calc
      _ ≤ (1 - a / b + a / b * exp (-b * (x - 1))) * exp (-(p * x)) :=
        mul_le_mul_of_nonneg_right (rpow_neg_le_exp_majorant ha hx.le) (exp_nonneg _)
      _ = g x := by
        dsimp [g]
        rw [add_mul, mul_assoc]
        congr 1
        rw [← exp_add, mul_assoc, ← exp_add]
        congr 2
        ring
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, g x :=
      setIntegral_mono_on hint hgint measurableSet_Ioi hpoint
    _ = (1 - a / b) * (exp (-p) / p) +
        (a / b * exp b) * (exp (-(p + b)) / (p + b)) := by
      rw [integral_add ((heint p hp).const_mul _) ((heint (p + b) hpb).const_mul _)]
      rw [integral_const_mul, integral_const_mul,
        integral_Ioi_one_exp_neg_mul hp, integral_Ioi_one_exp_neg_mul hpb]
    _ = exp (-p) / p * (1 - a / (p + a + 1)) := by
      have he : exp b * exp (-(p + b)) = exp (-p) := by
        rw [← exp_add]
        congr 1
        ring
      calc
        _ = (1 - a / b) * (exp (-p) / p) + a / b * (exp (-p) / (p + b)) := by
          rw [← mul_div_assoc, mul_assoc, ← mul_div_assoc, he]
        _ = _ := by
          dsimp [b]
          field_simp
          <;> ring

end AngularMaster
