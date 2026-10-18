import Derivations.Widder.DirectTower
import Mathlib

namespace NativeSoloboloNegativity

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Hausdorff-signed forward differences, copied in its minimal recursive form.
    `hausdorffDiff c n k = (-1)^k Δ^k c_n`. -/
def hausdorffDiff (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | n, 0 => c n
  | n, Nat.succ k => hausdorffDiff c n k - hausdorffDiff c (n + 1) k

@[simp] theorem HAUSDORFF_DIFF_ZERO (c : ℕ → ℝ) (n : ℕ) :
    hausdorffDiff c n 0 = c n := rfl

@[simp] theorem HAUSDORFF_DIFF_SUCC (c : ℕ → ℝ) (n k : ℕ) :
    hausdorffDiff c n (k + 1) =
      hausdorffDiff c n k - hausdorffDiff c (n + 1) k := by
  change hausdorffDiff c n (Nat.succ k) = _
  rfl

/-- Exact Pascal/Hopf split. No positivity assumption is used. -/
theorem HAUSDORFF_DIFF_SPLIT (c : ℕ → ℝ) (n k : ℕ) :
    hausdorffDiff c n k =
      hausdorffDiff c (n + 1) k + hausdorffDiff c n (k + 1) := by
  rw [HAUSDORFF_DIFF_SUCC]
  ring

/-- Factorial/sign normalization of the derivative jet. -/
def jetWeight (n : ℕ) : ℝ :=
  (-1 : ℝ)^n / (n.factorial : ℝ)

/-- The normalized resolvent derivative jet
    d_a(n)=(-1)^n a^(n+1) R^(n)(a)/n!. -/
def normalizedJet (R : ℝ → ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  jetWeight n * (a^(n + 1) * iteratedDeriv n R a)

/-- The actual Hausdorff cell of the normalized derivative jet. -/
def jetHausdorffCell (R : ℝ → ℝ) (n k : ℕ) (a : ℝ) : ℝ :=
  hausdorffDiff (fun m : ℕ => normalizedJet R m a) n k

/-- Near-central cell H(N,N+1). -/
def centralHausdorffCell (R : ℝ → ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  jetHausdorffCell R N (N + 1) a

/-- The central cell in the exact Widder normalization. -/
def centralWidderMoment (R : ℝ → ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  (4 : ℝ)^(N + 1) * centralHausdorffCell R N a

@[simp] theorem JET_HAUSDORFF_CELL_ZERO (R : ℝ → ℝ) (n : ℕ) (a : ℝ) :
    jetHausdorffCell R n 0 a = normalizedJet R n a := rfl

@[simp] theorem JET_HAUSDORFF_CELL_SUCC
    (R : ℝ → ℝ) (n k : ℕ) (a : ℝ) :
    jetHausdorffCell R n (k + 1) a =
      jetHausdorffCell R n k a - jetHausdorffCell R (n + 1) k a := by
  change hausdorffDiff (fun m : ℕ => normalizedJet R m a) n (k + 1) = _
  exact HAUSDORFF_DIFF_SUCC _ n k

/-- The jet weights obey the exact factorial/sign step. -/
theorem JET_WEIGHT_SUCC (n : ℕ) :
    jetWeight (n + 1) = -jetWeight n / (((n + 1 : ℕ) : ℝ)) := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hfac : ((n + 1).factorial : ℝ) =
      (((n + 1 : ℕ) : ℝ)) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast <;> rfl
  unfold jetWeight
  rw [hfac, pow_succ]
  field_simp [hn, Nat.factorial_ne_zero] <;> ring

/-- Every normalized derivative jet is analytic on the same open analytic domain. -/
theorem NORMALIZED_JET_ANALYTIC_ON
    {U : Set ℝ} {R : ℝ → ℝ} (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    AnalyticOnNhd ℝ (normalizedJet R n) U := by
  intro a ha
  unfold normalizedJet
  exact analyticAt_const.mul
    ((analyticAt_id.pow (n + 1)).mul (ANALYTIC_ITERATED_DERIV_ON hR n a ha))

/-- D of the n-th normalized derivative jet is exactly its first Hausdorff payment. -/
theorem EULER_NORMALIZED_JET
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) {a : ℝ} (ha : a ∈ U) :
    eulerD (normalizedJet R n) a =
      (((n + 1 : ℕ) : ℝ)) *
        (normalizedJet R n a - normalizedJet R (n + 1) a) := by
  have hfn : AnalyticAt ℝ (iteratedDeriv n R) a :=
    ANALYTIC_ITERATED_DERIV_ON hR n a ha
  have hprod : AnalyticAt ℝ
      (fun t : ℝ => t^(n + 1) * iteratedDeriv n R t) a :=
    (analyticAt_id.pow (n + 1)).mul hfn
  have hconst := EULER_D_CONST_MUL (jetWeight n)
    (f := fun t : ℝ => t^(n + 1) * iteratedDeriv n R t) (a := a) hprod
  have hpower := EULER_D_POWER_MUL (n + 1)
    (f := iteratedDeriv n R) (a := a) hfn
  have hEn : eulerD (iteratedDeriv n R) a =
      a * iteratedDeriv (n + 1) R a := by
    unfold eulerD
    rw [← iteratedDeriv_succ]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  change eulerD
      (fun t : ℝ => jetWeight n * (t^(n + 1) * iteratedDeriv n R t)) a = _
  rw [hconst, hpower, hEn]
  unfold normalizedJet
  rw [JET_WEIGHT_SUCC]
  field_simp [hn]
  ring

/-- Euler differentiation is additive over subtraction at analytic points. -/
theorem EULER_D_SUB {f g : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) (hg : AnalyticAt ℝ g a) :
    eulerD (fun t : ℝ => f t - g t) a = eulerD f a - eulerD g a := by
  have hd : deriv (fun t : ℝ => f t - g t) a = deriv f a - deriv g a :=
    (hf.differentiableAt.hasDerivAt.sub hg.differentiableAt.hasDerivAt).deriv
  unfold eulerD
  rw [hd]
  ring

/-- Every finite Hausdorff cell of the jet is analytic on the same domain. -/
theorem JET_HAUSDORFF_CELL_ANALYTIC_ON
    {U : Set ℝ} {R : ℝ → ℝ} (hR : AnalyticOnNhd ℝ R U) (n k : ℕ) :
    AnalyticOnNhd ℝ (jetHausdorffCell R n k) U := by
  induction k generalizing n with
  | zero =>
      change AnalyticOnNhd ℝ (normalizedJet R n) U
      exact NORMALIZED_JET_ANALYTIC_ON hR n
  | succ k ih =>
      intro a ha
      have h0 := ih n a ha
      have h1 := ih (n + 1) a ha
      change AnalyticAt ℝ
        (fun t : ℝ => jetHausdorffCell R n k t -
          jetHausdorffCell R (n + 1) k t) a
      exact h0.sub h1

/-- !!! Differential-Pascal law for every normalized jet cell:
    D H(n,k)=(n+1)H(n,k)-(n+k+1)H(n+1,k). -/
theorem EULER_JET_HAUSDORFF_CELL
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n k : ℕ) {a : ℝ} (ha : a ∈ U) :
    eulerD (jetHausdorffCell R n k) a =
      (((n + 1 : ℕ) : ℝ)) * jetHausdorffCell R n k a -
      (((n + k + 1 : ℕ) : ℝ)) * jetHausdorffCell R (n + 1) k a := by
  induction k generalizing n with
  | zero =>
      change eulerD (normalizedJet R n) a =
        (((n + 1 : ℕ) : ℝ)) * normalizedJet R n a -
          (((n + 1 : ℕ) : ℝ)) * normalizedJet R (n + 1) a
      rw [EULER_NORMALIZED_JET hU hR n ha]
      ring
  | succ k ih =>
      have h0 := JET_HAUSDORFF_CELL_ANALYTIC_ON hR n k a ha
      have h1 := JET_HAUSDORFF_CELL_ANALYTIC_ON hR (n + 1) k a ha
      calc
        eulerD (jetHausdorffCell R n (k + 1)) a =
            eulerD (fun t : ℝ => jetHausdorffCell R n k t -
              jetHausdorffCell R (n + 1) k t) a := by rfl
        _ = eulerD (jetHausdorffCell R n k) a -
              eulerD (jetHausdorffCell R (n + 1) k) a :=
          EULER_D_SUB h0 h1
        _ = (((n + 1 : ℕ) : ℝ)) * jetHausdorffCell R n (k + 1) a -
              (((n + (k + 1) + 1 : ℕ) : ℝ)) *
                jetHausdorffCell R (n + 1) (k + 1) a := by
          rw [ih n, ih (n + 1),
            JET_HAUSDORFF_CELL_SUCC, JET_HAUSDORFF_CELL_SUCC]
          push_cast
          ring

/-- Second Euler derivative of any jet cell, derived from the first-order law. -/
theorem EULER_SQUARE_JET_HAUSDORFF_CELL
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n k : ℕ) {a : ℝ} (ha : a ∈ U) :
    eulerD (eulerD (jetHausdorffCell R n k)) a =
      (((n + 1 : ℕ) : ℝ))^2 * jetHausdorffCell R n k a -
      (((n + k + 1 : ℕ) : ℝ)) * (((2 * n + 3 : ℕ) : ℝ)) *
        jetHausdorffCell R (n + 1) k a +
      (((n + k + 1 : ℕ) : ℝ)) * (((n + k + 2 : ℕ) : ℝ)) *
        jetHausdorffCell R (n + 2) k a := by
  let A : ℝ := (((n + 1 : ℕ) : ℝ))
  let B : ℝ := (((n + k + 1 : ℕ) : ℝ))
  have hEq : Set.EqOn
      (eulerD (jetHausdorffCell R n k))
      (fun t : ℝ => A * jetHausdorffCell R n k t -
        B * jetHausdorffCell R (n + 1) k t) U := by
    intro b hb
    dsimp [A, B]
    exact EULER_JET_HAUSDORFF_CELL hU hR n k hb
  have hdEq := LOCAL_DERIV_CONGR hU hEq ha
  have h0 := JET_HAUSDORFF_CELL_ANALYTIC_ON hR n k a ha
  have h1 := JET_HAUSDORFF_CELL_ANALYTIC_ON hR (n + 1) k a ha
  have hA0 : AnalyticAt ℝ (fun t : ℝ => A * jetHausdorffCell R n k t) a :=
    analyticAt_const.mul h0
  have hB1 : AnalyticAt ℝ (fun t : ℝ => B * jetHausdorffCell R (n + 1) k t) a :=
    analyticAt_const.mul h1
  have htransport :
      eulerD (eulerD (jetHausdorffCell R n k)) a =
        eulerD (fun t : ℝ => A * jetHausdorffCell R n k t -
          B * jetHausdorffCell R (n + 1) k t) a := by
    unfold eulerD
    exact congrArg (fun z : ℝ => a * z) hdEq
  rw [htransport, EULER_D_SUB hA0 hB1,
    EULER_D_CONST_MUL A h0, EULER_D_CONST_MUL B h1,
    EULER_JET_HAUSDORFF_CELL hU hR n k ha,
    EULER_JET_HAUSDORFF_CELL hU hR (n + 1) k ha]
  dsimp [A, B]
  push_cast
  ring

/-- !!! Central diagonal second-order identity. This is the exact Widder
    recurrence before multiplying by 4^(N+1). -/
theorem CENTRAL_HAUSDORFF_SECOND_ORDER
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) {a : ℝ} (ha : a ∈ U) :
    2 * (((n + 1 : ℕ) : ℝ)) * (2 * (((n + 1 : ℕ) : ℝ)) + 1) *
        centralHausdorffCell R (n + 1) a =
      (((n + 1 : ℕ) : ℝ))^2 * centralHausdorffCell R n a -
        eulerD (eulerD (centralHausdorffCell R n)) a := by
  unfold centralHausdorffCell
  rw [EULER_SQUARE_JET_HAUSDORFF_CELL hU hR n (n + 1) ha,
    JET_HAUSDORFF_CELL_SUCC]
  push_cast
  ring

/-- Euler-square commutes with multiplication by a scalar, with no hidden
    differentiability assumption because scalar differentiation is exact. -/
theorem EULER_SQUARE_CONST_MUL (c : ℝ) (f : ℝ → ℝ) (a : ℝ) :
    eulerD (eulerD (fun t : ℝ => c * f t)) a =
      c * eulerD (eulerD f) a := by
  have hfun : eulerD (fun t : ℝ => c * f t) =
      (fun t : ℝ => c * eulerD f t) := by
    funext t
    unfold eulerD
    rw [deriv_const_mul_field]
    ring
  rw [hfun]
  unfold eulerD
  rw [deriv_const_mul_field]
  ring

/-- Existing Widder step expressed in Euler-square form. -/
theorem WIDDER_STEP_EQ_EULER
    {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) (n : ℕ) :
    widderStep n f a =
      2 / ((((n + 1 : ℕ) : ℝ)) *
        (2 * (((n + 1 : ℕ) : ℝ)) + 1)) *
      ((((n + 1 : ℕ) : ℝ))^2 * f a - eulerD (eulerD f) a) := by
  rw [EULER_D_SQUARE hf]
  unfold widderStep
  ring

/-- The central Widder-normalized cell is analytic on every analytic domain. -/
theorem CENTRAL_WIDDER_MOMENT_ANALYTIC_ON
    {U : Set ℝ} {R : ℝ → ℝ} (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    AnalyticOnNhd ℝ (centralWidderMoment R n) U := by
  intro a ha
  unfold centralWidderMoment centralHausdorffCell
  exact analyticAt_const.mul
    (JET_HAUSDORFF_CELL_ANALYTIC_ON hR n (n + 1) a ha)

/-- Depth zero central cell is exactly the existing Widder base. -/
theorem CENTRAL_WIDDER_ZERO_EQ_BASE
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) {a : ℝ} (ha : a ∈ U) :
    centralWidderMoment R 0 a = widderBaseOf R a := by
  have hRa := hR a ha
  have hd : deriv (fun t : ℝ => t * R t) a = R a + a * deriv R a := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id a).fun_mul hRa.differentiableAt.hasDerivAt).deriv
  unfold centralWidderMoment centralHausdorffCell jetHausdorffCell
  simp only [hausdorffDiff, normalizedJet, jetWeight, iteratedDeriv_zero,
    iteratedDeriv_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    div_one, pow_zero, pow_one, one_mul]
  unfold widderBaseOf
  rw [hd]
  rw [iteratedDeriv_one]
  ring

/-- !!! Central Hausdorff cell obeys exactly the existing all-depth Widder step. -/
theorem CENTRAL_WIDDER_STEP
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) {a : ℝ} (ha : a ∈ U) :
    centralWidderMoment R (n + 1) a =
      widderStep n (centralWidderMoment R n) a := by
  have hcell := CENTRAL_HAUSDORFF_SECOND_ORDER hU hR n ha
  have hcm := CENTRAL_WIDDER_MOMENT_ANALYTIC_ON hR n a ha
  have hsq : eulerD (eulerD (centralWidderMoment R n)) a =
      (4 : ℝ)^(n + 1) *
        eulerD (eulerD (centralHausdorffCell R n)) a := by
    unfold centralWidderMoment
    exact EULER_SQUARE_CONST_MUL ((4 : ℝ)^(n + 1))
      (centralHausdorffCell R n) a
  rw [WIDDER_STEP_EQ_EULER hcm n, hsq]
  change (4 : ℝ)^(n + 2) * centralHausdorffCell R (n + 1) a = _
  unfold centralWidderMoment
  have hpow : (4 : ℝ)^(n + 2) = (4 : ℝ)^(n + 1) * 4 := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  rw [hpow]
  have hfactor :
      (((n + 1 : ℕ) : ℝ))^2 *
          ((4 : ℝ)^(n + 1) * centralHausdorffCell R n a) -
        (4 : ℝ)^(n + 1) *
          eulerD (eulerD (centralHausdorffCell R n)) a =
      (4 : ℝ)^(n + 1) *
        ((((n + 1 : ℕ) : ℝ))^2 * centralHausdorffCell R n a -
          eulerD (eulerD (centralHausdorffCell R n)) a) := by
    ring
  rw [hfactor, ← hcell]
  have hden :
      (((n + 1 : ℕ) : ℝ)) *
        (2 * (((n + 1 : ℕ) : ℝ)) + 1) ≠ 0 := by
    positivity
  field_simp [hden]
  ring

/-- !!! The whole near-central Hausdorff diagonal equals the recursively generated
    Widder tower on every open analytic domain. -/
theorem CENTRAL_WIDDER_EQUALS_TOWER_ON_OPEN
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    Set.EqOn (centralWidderMoment R n) (widderTower (widderBaseOf R) n) U := by
  induction n with
  | zero =>
      intro a ha
      exact CENTRAL_WIDDER_ZERO_EQ_BASE hU hR ha
  | succ n ih =>
      intro a ha
      calc
        centralWidderMoment R (n + 1) a =
            widderStep n (centralWidderMoment R n) a :=
          CENTRAL_WIDDER_STEP hU hR n ha
        _ = widderStep n (widderTower (widderBaseOf R) n) a :=
          WIDDER_STEP_CONGR_ON_OPEN hU ih n ha
        _ = widderTower (widderBaseOf R) (n + 1) a := rfl

/-- !!! Hence the independently defined direct Rodrigues expression is exactly
    4^(N+1) times the near-central Hausdorff cell. -/
theorem WIDDER_DIRECT_EQ_CENTRAL_HAUSDORFF_ON_OPEN
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    Set.EqOn (widderDirectScaled R n) (centralWidderMoment R n) U := by
  intro a ha
  calc
    widderDirectScaled R n a = widderTower (widderBaseOf R) n a :=
      WIDDER_DIRECT_EQUALS_TOWER_ON_OPEN hU hR n ha
    _ = centralWidderMoment R n a :=
      (CENTRAL_WIDDER_EQUALS_TOWER_ON_OPEN hU hR n ha).symm

end
end NativeSoloboloNegativity
