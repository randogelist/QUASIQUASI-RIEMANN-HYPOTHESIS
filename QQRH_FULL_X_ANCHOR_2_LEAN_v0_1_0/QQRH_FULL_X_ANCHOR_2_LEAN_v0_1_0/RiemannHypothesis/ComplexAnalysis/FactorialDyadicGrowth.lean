/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.MellinGrowth

/-!
# From factorial envelopes to dyadic order-one growth

`MellinTwoSidedExponentialDecay.norm_mellin_le_factorial` produces bounds
whose variable part has the form

`C * (B ^ (N + 1) * N!)`.

When the auxiliary integer `N` is at most affine-linear in a dyadic radius,
this file absorbs the factorial envelope into an order-one exponential.  The
main pointwise estimate is

`C * (B ^ (N + 1) * N!) <= exp (A * (m + 1) * 2 ^ m)`,

under `N <= K * 2 ^ m + K`.  Here `A` is an explicit nonnegative constant
depending only on `C`, `B`, and `K`.  The estimate holds for every `m`, so in
particular it supplies the eventual estimate needed on dyadic circles.

Both natural powers and `Real.rpow` at natural exponents are supported.  The
latter is the notation used by the Mellin-growth theorem.  The final two
structures package the conversion so that a later boundary-value argument
only has to provide a factorial envelope and an index bound.
-/

namespace OverflowResidueRH

open Real

/-! ## Elementary estimates -/

/-- A deliberately coarse bound which is convenient for absorbing ordinary
powers into an exponential. -/
theorem nonneg_pow_le_exp_mul_nat (x : Real) (hx : 0 <= x) (n : Nat) :
    x ^ n <= Real.exp (x * n) := by
  have hxexp : x <= Real.exp x := by
    linarith [Real.add_one_le_exp x]
  calc
    x ^ n <= (Real.exp x) ^ n := pow_le_pow_left₀ hx hxexp n
    _ = Real.exp (x * n) := by
      rw [<- Real.exp_nat_mul]
      congr 1
      ring

/-- Replace an affine dyadic index bound by a pure dyadic bound.  The slack
factor `2 * K + 1` is chosen so that the statement also covers `m = 0`. -/
theorem affineDyadicIndex_le_pureDyadic {K m N : Nat}
    (hN : N <= K * 2 ^ m + K) :
    N <= (2 * K + 1) * 2 ^ m := by
  have hK : K <= K * 2 ^ m :=
    Nat.le_mul_of_pos_right K (by positivity)
  calc
    N <= K * 2 ^ m + K := hN
    _ <= K * 2 ^ m + K * 2 ^ m := Nat.add_le_add_left hK _
    _ = (2 * K) * 2 ^ m := by ring
    _ <= (2 * K + 1) * 2 ^ m := by
      gcongr
      omega

/-- A natural number bounded by `D * 2 ^ m` is bounded by an exponential
whose logarithm is linear in `m`. -/
theorem natCast_le_exp_of_le_dyadic (D m N : Nat)
    (hN : N <= D * 2 ^ m) :
    (N : Real) <= Real.exp (((D : Real) + 2) * (m + 1)) := by
  have hDexp : (D : Real) <= Real.exp D := by
    linarith [Real.add_one_le_exp (D : Real)]
  have htwo : (2 : Real) ^ m <= Real.exp ((2 : Real) * m) :=
    nonneg_pow_le_exp_mul_nat 2 (by norm_num) m
  have hcast : (N : Real) <= (D : Real) * (2 : Real) ^ m := by
    exact_mod_cast hN
  calc
    (N : Real) <= (D : Real) * (2 : Real) ^ m := hcast
    _ <= Real.exp D * Real.exp ((2 : Real) * m) :=
      mul_le_mul hDexp htwo (by positivity) (by positivity)
    _ = Real.exp ((D : Real) + 2 * m) := by rw [<- Real.exp_add]
    _ <= Real.exp (((D : Real) + 2) * (m + 1)) := by
      apply Real.exp_le_exp.mpr
      have hD0 : 0 <= (D : Real) := Nat.cast_nonneg D
      have hm0 : 0 <= (m : Real) := Nat.cast_nonneg m
      nlinarith

/-- The factorial part of a pure dyadic index envelope has dyadic order-one
growth.  The proof only uses `N! <= N ^ N`; sharper Stirling estimates are not
needed for the downstream order statement. -/
theorem factorial_le_exp_of_le_dyadic (D m N : Nat)
    (hN : N <= D * 2 ^ m) :
    (N.factorial : Real) <=
      Real.exp (((D : Real) + 2) * D *
        (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
  have hfact : (N.factorial : Real) <= (N : Real) ^ N := by
    exact_mod_cast N.factorial_le_pow
  have hbase := natCast_le_exp_of_le_dyadic D m N hN
  have hpow : (N : Real) ^ N <=
      (Real.exp (((D : Real) + 2) * (m + 1))) ^ N :=
    pow_le_pow_left₀ (Nat.cast_nonneg N) hbase N
  have hNcast : (N : Real) <= (D : Real) * (2 : Real) ^ m := by
    exact_mod_cast hN
  calc
    (N.factorial : Real) <= (N : Real) ^ N := hfact
    _ <= (Real.exp (((D : Real) + 2) * (m + 1))) ^ N := hpow
    _ = Real.exp ((((D : Real) + 2) * (m + 1)) * N) := by
      rw [<- Real.exp_nat_mul]
      congr 1
      ring
    _ <= Real.exp ((((D : Real) + 2) * (m + 1)) *
          ((D : Real) * (2 : Real) ^ m)) := by
      apply Real.exp_le_exp.mpr
      gcongr
    _ = Real.exp (((D : Real) + 2) * D *
          (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
      congr 1
      push_cast
      ring

/-- The ordinary-power part of the factorial envelope has dyadic order-one
growth when the exponent has a pure dyadic bound. -/
theorem pow_succ_le_exp_of_le_dyadic (B : Real) (hB : 0 <= B)
    (D m N : Nat) (hN : N <= D * 2 ^ m) :
    B ^ (N + 1) <=
      Real.exp ((B * (D + 1)) *
        (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
  have hpow := nonneg_pow_le_exp_mul_nat B hB (N + 1)
  have hone : 1 <= 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
  have hN1 : N + 1 <= (D + 1) * 2 ^ m := by
    calc
      N + 1 <= D * 2 ^ m + 1 := Nat.add_le_add_right hN 1
      _ <= D * 2 ^ m + 2 ^ m := Nat.add_le_add_left hone _
      _ = (D + 1) * 2 ^ m := by ring
  have hN1cast : ((N + 1 : Nat) : Real) <=
      ((D + 1 : Nat) : Real) * (2 : Real) ^ m := by
    exact_mod_cast hN1
  calc
    B ^ (N + 1) <= Real.exp (B * (((N + 1 : Nat) : Real))) := hpow
    _ <= Real.exp (B * (((D + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hN1cast hB
    _ <= Real.exp ((B * (D + 1)) *
          (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
      apply Real.exp_le_exp.mpr
      have hm1 : (1 : Real) <= ((m + 1 : Nat) : Real) := by norm_num
      calc
        B * (((D + 1 : Nat) : Real) * (2 : Real) ^ m) =
            (B * ((D + 1 : Nat) : Real)) * 1 * (2 : Real) ^ m := by ring
        _ <= (B * ((D + 1 : Nat) : Real)) *
            ((m + 1 : Nat) : Real) * (2 : Real) ^ m := by
          gcongr
        _ = (B * (D + 1)) *
            (((m + 1 : Nat) : Real) * (2 : Real) ^ m) := by
          push_cast
          ring

/-- A nonnegative constant can be absorbed into the same dyadic exponential
without introducing a separate additive constant. -/
theorem le_exp_dyadic_self (C : Real) (hC : 0 <= C) (m : Nat) :
    C <= Real.exp (C *
      (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
  have hself : C <= Real.exp C := by
    linarith [Real.add_one_le_exp C]
  apply hself.trans
  apply Real.exp_le_exp.mpr
  have ht : (1 : Real) <=
      ((m + 1 : Nat) : Real) * (2 : Real) ^ m := by
    have hm : (1 : Real) <= ((m + 1 : Nat) : Real) := by norm_num
    have hp : (1 : Real) <= (2 : Real) ^ m := by
      exact_mod_cast Nat.one_le_pow m 2 (by norm_num)
    nlinarith
  calc
    C = C * 1 := by ring
    _ <= C * (((m + 1 : Nat) : Real) * (2 : Real) ^ m) :=
      mul_le_mul_of_nonneg_left ht hC

/-! ## The pointwise factorial-to-dyadic bridge -/

/-- An explicit rate which absorbs a factorial envelope. -/
def factorialDyadicGrowthRate (C B : Real) (K : Nat) : Real :=
  let D : Real := 2 * K + 1
  C + B * (D + 1) + (D + 2) * D

/-- The explicit factorial-to-dyadic rate is nonnegative when the original
envelope constants are nonnegative. -/
theorem factorialDyadicGrowthRate_nonneg (C B : Real) (K : Nat)
    (hC : 0 <= C) (hB : 0 <= B) :
    0 <= factorialDyadicGrowthRate C B K := by
  dsimp [factorialDyadicGrowthRate]
  positivity

/-- Natural-power form of the factorial-to-dyadic bridge.  This is stronger
than an eventual estimate: it holds for every natural `m`. -/
theorem mul_pow_factorial_le_exp_dyadic
    (C B : Real) (hC : 0 <= C) (hB : 0 <= B)
    (K m N : Nat) (hN : N <= K * 2 ^ m + K) :
    C * B ^ (N + 1) * (N.factorial : Real) <=
      Real.exp (factorialDyadicGrowthRate C B K *
        (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
  let D : Nat := 2 * K + 1
  have hND : N <= D * 2 ^ m := affineDyadicIndex_le_pureDyadic hN
  let t : Real := ((m + 1 : Nat) : Real) * (2 : Real) ^ m
  have hconst : C <= Real.exp (C * t) := le_exp_dyadic_self C hC m
  have hpower : B ^ (N + 1) <=
      Real.exp ((B * (D + 1)) * t) :=
    pow_succ_le_exp_of_le_dyadic B hB D m N hND
  have hfact : (N.factorial : Real) <=
      Real.exp ((((D : Real) + 2) * D) * t) :=
    factorial_le_exp_of_le_dyadic D m N hND
  calc
    C * B ^ (N + 1) * (N.factorial : Real) <=
        Real.exp (C * t) * Real.exp ((B * (D + 1)) * t) *
          Real.exp ((((D : Real) + 2) * D) * t) := by
      gcongr
    _ = Real.exp (factorialDyadicGrowthRate C B K *
          (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
      rw [<- Real.exp_add, <- Real.exp_add]
      congr 1
      dsimp [factorialDyadicGrowthRate, D, t]
      push_cast
      ring

/-- `Real.rpow` form of the bridge.  This is the form that applies directly
to `MellinTwoSidedExponentialDecay.norm_mellin_le_factorial`. -/
theorem mul_rpow_factorial_le_exp_dyadic
    (C B : Real) (hC : 0 <= C) (hB : 0 <= B)
    (K m N : Nat) (hN : N <= K * 2 ^ m + K) :
    C * (B ^ (((N + 1 : Nat) : Real)) * (N.factorial : Real)) <=
      Real.exp (factorialDyadicGrowthRate C B K *
        (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
  rw [Real.rpow_natCast]
  simpa only [mul_assoc] using
    mul_pow_factorial_le_exp_dyadic C B hC hB K m N hN

/-- Direct dyadic-order corollary of the factorial Mellin bound.  The
hypotheses `hupper` and `hlower` are exactly those of
`MellinTwoSidedExponentialDecay.norm_mellin_le_factorial`; `hN` is the only
new arithmetic input. -/
theorem MellinTwoSidedExponentialDecay.norm_mellin_le_exp_dyadic
    {f : Real -> Complex} (H : MellinTwoSidedExponentialDecay f)
    (s : Complex) (K m N : Nat)
    (hupper : s.re - 1 <= N)
    (hlower : -(N : Real) - 2 <= s.re - 1 - H.k)
    (hconv : MellinConvergent f s)
    (hN : N <= K * 2 ^ m + K) :
    ‖mellin f s‖ <=
      Real.exp (factorialDyadicGrowthRate (2 * H.A) (1 / H.p) K *
        (((m + 1 : Nat) : Real) * (2 : Real) ^ m)) := by
  refine (H.norm_mellin_le_factorial s N hupper hlower hconv).trans ?_
  simpa only [Nat.cast_add, Nat.cast_one] using
    (mul_rpow_factorial_le_exp_dyadic
      (2 * H.A) (1 / H.p)
      (mul_nonneg (by norm_num) H.A_nonneg)
      (div_nonneg (by norm_num) H.p_pos.le) K m N hN)

/-- Existential-facing version of the main theorem.  It records exactly the
usual eventual-growth interface while retaining nonnegativity of both output
constants. -/
theorem exists_factorialDyadic_orderOne_bound
    (C B : Real) (hC : 0 <= C) (hB : 0 <= B) (K lower : Nat) :
    ∃ A A0 : Real, 0 <= A ∧ 0 <= A0 ∧
      ∀ m N : Nat, lower <= m -> N <= K * 2 ^ m + K ->
        C * (B ^ (((N + 1 : Nat) : Real)) * (N.factorial : Real)) <=
          Real.exp (A * (((m + 1 : Nat) : Real) * (2 : Real) ^ m) + A0) := by
  refine ⟨factorialDyadicGrowthRate C B K, 0,
    factorialDyadicGrowthRate_nonneg C B K hC hB, le_rfl, ?_⟩
  intro m N _ hN
  simpa using mul_rpow_factorial_le_exp_dyadic C B hC hB K m N hN

/-! ## Reusable eventual-growth packages -/

/-- A generic dyadic order-one upper bound for a real-valued sequence. -/
structure DyadicOrderOneGrowthData (u : Nat -> Real) : Type where
  lower : Nat
  A : Real
  A0 : Real
  A_nonneg : 0 <= A
  A0_nonneg : 0 <= A0
  bound : forall m : Nat, lower <= m ->
    u m <= Real.exp (A * (((m + 1 : Nat) : Real) * (2 : Real) ^ m) + A0)

/-- Data obtained after a Mellin or contour estimate has reduced a sequence
to a factorial envelope with a dyadically bounded auxiliary index.  The power
is written as `Real.rpow` to match `MellinGrowth.lean`. -/
structure FactorialDyadicEnvelopeData (u : Nat -> Real) : Type where
  lower : Nat
  index : Nat -> Nat
  C : Real
  B : Real
  K : Nat
  C_nonneg : 0 <= C
  B_nonneg : 0 <= B
  index_le : forall m : Nat, lower <= m -> index m <= K * 2 ^ m + K
  envelope_le : forall m : Nat, lower <= m ->
    u m <= C *
      (B ^ (((index m + 1 : Nat) : Real)) * ((index m).factorial : Real))

/-- A factorial envelope with affine-dyadic index growth canonically yields a
dyadic order-one growth package. -/
def FactorialDyadicEnvelopeData.toDyadicOrderOneGrowthData
    {u : Nat -> Real} (H : FactorialDyadicEnvelopeData u) :
    DyadicOrderOneGrowthData u where
  lower := H.lower
  A := factorialDyadicGrowthRate H.C H.B H.K
  A0 := 0
  A_nonneg := factorialDyadicGrowthRate_nonneg
    H.C H.B H.K H.C_nonneg H.B_nonneg
  A0_nonneg := le_rfl
  bound := by
    intro m hm
    refine (H.envelope_le m hm).trans ?_
    simpa using mul_rpow_factorial_le_exp_dyadic
      H.C H.B H.C_nonneg H.B_nonneg H.K m (H.index m) (H.index_le m hm)

end OverflowResidueRH
