# FIX1

Reported failure: `AWPIRH/NativeCompletionReduction.lean:52`, in
`two_sqrt_pi_cpow`.

The expected complex-power base is the complex cast of the real product
`2 * sqrt(pi)`. The available multiplication theorem has the product of the
two complex casts. FIX1 inserts `rw [Complex.ofReal_mul]` immediately before
the existing theorem application.

- Exactly one mathematical source file changes, by one proof line.
- All theorem statements and all 2,460 public audit entries are unchanged.
- The 1,835 theorem/lemma source count is unchanged.
- All 11 FIX9 baseline source modules are unchanged.
- Static validation passed; FIX1 compilation and audit rerun remain pending.
- The original v0.1.0 Windows run failed at the above point. No pass beyond
  that point is inferred from its log.
