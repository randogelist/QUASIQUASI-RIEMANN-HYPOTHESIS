import AngularMaster.ActualProfile
import AngularMaster.ProductLimit
import AngularMaster.ProductValueLimit
import AngularMaster.ActualHadamard
import AngularMaster.RadialExtension

/-!
# Unconditional equivalence of native RH and the frozen angular Master

The actual xi factorization is imported as a proved theorem and transported
in `ActualHadamard.lean`. No product bridge is an extra theorem parameter.
Neither RH nor the Master condition itself is proved by this equivalence.
-/

noncomputable section
namespace AngularMaster

theorem theta_zeros_iff_actual_derivative_nonnegative :
    ThetaZerosNonpositive ↔ DerivativeNonnegative actualProfile := by
  constructor
  · intro hz
    exact derivativeNonnegative_of_profileMaster
      (actual_profileMaster_of_native_RH (native_RH_iff_theta_zeros_nonpositive.mpr hz))
  · intro hd
    exact native_RH_iff_theta_zeros_nonpositive.mp
      (native_RH_of_actual_derivative_nonnegative hd)

theorem actual_derivative_nonnegative_iff_profileMaster :
    DerivativeNonnegative actualProfile ↔ ProfileMaster actualProfile := by
  constructor
  · intro hd
    have hz := native_RH_iff_theta_zeros_nonpositive.mp
      (native_RH_of_actual_derivative_nonnegative hd)
    exact actual_profileMaster_of_native_RH (native_RH_iff_theta_zeros_nonpositive.mpr hz)
  · exact derivativeNonnegative_of_profileMaster

/-- Native RH is equivalent to the actual angular Master, without extra premises. -/
theorem native_RH_iff_actual_profileMaster :
    _root_.RiemannHypothesis ↔ ProfileMaster actualProfile := by
  calc
    _root_.RiemannHypothesis ↔ XiZerosCritical :=
      native_RH_iff_xi_zeros_critical
    _ ↔ ThetaZerosNonpositive := xi_zeros_critical_iff_theta_zeros_nonpositive
    _ ↔ DerivativeNonnegative actualProfile :=
      theta_zeros_iff_actual_derivative_nonnegative
    _ ↔ ProfileMaster actualProfile :=
      actual_derivative_nonnegative_iff_profileMaster

/-- Normalization does not alter either sign condition. This total-derivative
identity needs no separate endpoint differentiability assumption. -/
theorem actual_profileMaster_iff_logMaster
    {ε : ℝ} {S : ℝ → ℝ} (hε : 0 < ε) (hS : NormalizerPositive S) :
    ProfileMaster actualProfile ↔ LogMaster ε S actualProfile := by
  exact (logMaster_iff_profileMaster_total hε hS
    (fun r hr x => actualProfile_nonnegative_all r x)).symm

theorem native_RH_iff_actual_logMaster
    {ε : ℝ} {S : ℝ → ℝ} (hε : 0 < ε) (hS : NormalizerPositive S) :
    _root_.RiemannHypothesis ↔ LogMaster ε S actualProfile :=
  (native_RH_iff_actual_profileMaster).trans
    (actual_profileMaster_iff_logMaster hε hS)

/-- Exact frozen Riemann normalization. There is no denominator-nonvanishing
hypothesis: the forward direction obtains it from RH, and the reverse direction
uses the proved dense-radius extension. -/
theorem native_RH_iff_frozenLogMaster
    {ε : ℝ} (hε : 0 < ε) :
    _root_.RiemannHypothesis ↔ frozenLogMaster ε := by
  constructor
  · intro hRH
    exact (actual_profileMaster_iff_logMaster hε
      (frozenNormalizer_positive_of_native_RH hRH)).mp
        ((native_RH_iff_actual_profileMaster).mp hRH)
  · exact frozen_logMaster_implies_native_RH hε

theorem actual_profileMaster_iff_frozenLogMaster
    {ε : ℝ} (hε : 0 < ε) :
    ProfileMaster actualProfile ↔ frozenLogMaster ε := by
  constructor
  · intro h
    have hS := frozenNormalizer_positive_of_native_RH
      (actual_profileMaster_implies_native_RH h)
    exact (actual_profileMaster_iff_logMaster hε hS).mp h
  · intro h
    have hS := frozenNormalizer_positive_of_native_RH
      (frozen_logMaster_implies_native_RH hε h)
    exact (actual_profileMaster_iff_logMaster hε hS).mpr h

/-- The positive logarithmic parameter does not change the frozen Master.
No auxiliary analytic hypotheses are needed. -/
theorem frozenLogMaster_epsilon_invariant
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    frozenLogMaster ε ↔ frozenLogMaster δ :=
  (actual_profileMaster_iff_frozenLogMaster hε).symm.trans
    (actual_profileMaster_iff_frozenLogMaster hδ)

/-- One fixed positive epsilon suffices for the unconditional equivalence. -/
theorem FROZEN_RH_MASTER_EQUIVALENCE :
    _root_.RiemannHypothesis ↔ frozenLogMaster (1 / 2) :=
  native_RH_iff_frozenLogMaster (by norm_num)

/-- The requested final theorem, with no auxiliary analytic parameter. -/
theorem RH_iff_Master :
    _root_.RiemannHypothesis ↔ frozenLogMaster (1 / 2) :=
  FROZEN_RH_MASTER_EQUIVALENCE

/-- The raw Master is precisely the conjunction of the two frozen conditions. -/
theorem RH_iff_Sub_1_and_Sub_2 :
    _root_.RiemannHypothesis ↔
      AngularMinimum actualProfile ∧ BoundaryNonnegative actualProfile :=
  native_RH_iff_actual_profileMaster

/-- The complete displayed RH-to-RH chain through the exact frozen object.
Every intermediate equivalence is proved, without asserting that RH holds. -/
theorem RH_TO_RH_FROZEN_MASTER_CHAIN :
    _root_.RiemannHypothesis ↔ _root_.RiemannHypothesis := by
  calc
    _root_.RiemannHypothesis ↔ XiZerosCritical := native_RH_iff_xi_zeros_critical
    _ ↔ ThetaZerosNonpositive := xi_zeros_critical_iff_theta_zeros_nonpositive
    _ ↔ DerivativeNonnegative actualProfile :=
      theta_zeros_iff_actual_derivative_nonnegative
    _ ↔ ProfileMaster actualProfile :=
      actual_derivative_nonnegative_iff_profileMaster
    _ ↔ frozenLogMaster (1 / 2) :=
      actual_profileMaster_iff_frozenLogMaster (by norm_num)
    _ ↔ _root_.RiemannHypothesis := (FROZEN_RH_MASTER_EQUIVALENCE).symm

/-- The requested single coherent chain, including the exponential/log Master.
The classical actual-theta product step is now a proved lemma. -/
theorem RH_TO_RH_LOG_MASTER_CHAIN
    {ε : ℝ} {S : ℝ → ℝ} (hε : 0 < ε) (hS : NormalizerPositive S) :
    _root_.RiemannHypothesis ↔ _root_.RiemannHypothesis := by
  calc
    _root_.RiemannHypothesis ↔ XiZerosCritical :=
      native_RH_iff_xi_zeros_critical
    _ ↔ ThetaZerosNonpositive := xi_zeros_critical_iff_theta_zeros_nonpositive
    _ ↔ DerivativeNonnegative actualProfile :=
      theta_zeros_iff_actual_derivative_nonnegative
    _ ↔ ProfileMaster actualProfile :=
      actual_derivative_nonnegative_iff_profileMaster
    _ ↔ LogMaster ε S actualProfile := actual_profileMaster_iff_logMaster hε hS
    _ ↔ _root_.RiemannHypothesis :=
      (native_RH_iff_actual_logMaster hε hS).symm

/-- The literal round trip requested by the user. The endpoint `RH ↔ RH` is
tautological; the named intermediate equivalences carry the mathematical content.
It is not a proof of RH. -/
theorem RH_TO_RH_COHERENT_CHAIN :
    _root_.RiemannHypothesis ↔ _root_.RiemannHypothesis := by
  calc
    _root_.RiemannHypothesis ↔ XiZerosCritical :=
      native_RH_iff_xi_zeros_critical
    _ ↔ ThetaZerosNonpositive := xi_zeros_critical_iff_theta_zeros_nonpositive
    _ ↔ DerivativeNonnegative actualProfile :=
      theta_zeros_iff_actual_derivative_nonnegative
    _ ↔ ProfileMaster actualProfile :=
      actual_derivative_nonnegative_iff_profileMaster
    _ ↔ _root_.RiemannHypothesis :=
      (native_RH_iff_actual_profileMaster).symm

end AngularMaster
