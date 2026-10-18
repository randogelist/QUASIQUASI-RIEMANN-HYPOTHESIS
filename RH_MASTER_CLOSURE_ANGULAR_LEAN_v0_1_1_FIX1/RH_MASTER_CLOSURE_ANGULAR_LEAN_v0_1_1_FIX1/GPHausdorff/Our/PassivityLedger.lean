import GPHausdorff.Core.FiniteDifference

namespace GPHausdorff.Our

open scoped BigOperators

/-- !!! Exact horizontal storage-payment ledger.
For every depth `m`, the initial Hausdorff storage equals the residual storage
plus the accumulated one-step payments.  Pure algebra: no literature axioms. -/
theorem hdiff_storage_ledger (c : ℕ → ℝ) (n k m : ℕ) :
    hdiff c n k =
      hdiff c (n + m) k +
        Finset.sum (Finset.range m) (fun j => hdiff c (n + j) (k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        hdiff c n k =
            hdiff c (n + m) k +
              Finset.sum (Finset.range m) (fun j => hdiff c (n + j) (k + 1)) := ih
        _ =
            (hdiff c ((n + m) + 1) k + hdiff c (n + m) (k + 1)) +
              Finset.sum (Finset.range m) (fun j => hdiff c (n + j) (k + 1)) := by
              rw [hdiff_split c (n + m) k]
        _ =
            hdiff c (n + (m + 1)) k +
              Finset.sum (Finset.range (m + 1)) (fun j => hdiff c (n + j) (k + 1)) := by
              rw [Finset.sum_range_succ]
              have hn : (n + m) + 1 = n + (m + 1) := by omega
              rw [hn]
              ring

/-- !!! Exact vertical storage-payment ledger. -/
theorem hdiff_vertical_ledger (c : ℕ → ℝ) (n k m : ℕ) :
    hdiff c n k =
      hdiff c n (k + m) +
        Finset.sum (Finset.range m) (fun j => hdiff c (n + 1) (k + j)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        hdiff c n k =
            hdiff c n (k + m) +
              Finset.sum (Finset.range m) (fun j => hdiff c (n + 1) (k + j)) := ih
        _ =
            (hdiff c (n + 1) (k + m) + hdiff c n ((k + m) + 1)) +
              Finset.sum (Finset.range m) (fun j => hdiff c (n + 1) (k + j)) := by
              rw [hdiff_split c n (k + m)]
        _ =
            hdiff c n (k + (m + 1)) +
              Finset.sum (Finset.range (m + 1)) (fun j => hdiff c (n + 1) (k + j)) := by
              rw [Finset.sum_range_succ]
              have hk : (k + m) + 1 = k + (m + 1) := by omega
              rw [hk]
              ring

/-- !! Under Hausdorff positivity, storage can only decrease along `n`. -/
theorem hausdorff_storage_monotone_n {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n k m : ℕ) :
    hdiff c (n + m) k ≤ hdiff c n k := by
  have hid := hdiff_storage_ledger c n k m
  have hsum :
      0 ≤ Finset.sum (Finset.range m) (fun j => hdiff c (n + j) (k + 1)) := by
    exact Finset.sum_nonneg (fun j _ => h (n + j) (k + 1))
  linarith

/-- !! Under Hausdorff positivity, storage can only decrease along difference order `k`. -/
theorem hausdorff_storage_monotone_k {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n k m : ℕ) :
    hdiff c n (k + m) ≤ hdiff c n k := by
  have hid := hdiff_vertical_ledger c n k m
  have hsum :
      0 ≤ Finset.sum (Finset.range m) (fun j => hdiff c (n + 1) (k + j)) := by
    exact Finset.sum_nonneg (fun j _ => h (n + 1) (k + j))
  linarith

/-- !! The total horizontal payment is bounded by the initial storage. -/
theorem hausdorff_total_payment_bound {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n k m : ℕ) :
    (Finset.sum (Finset.range m) (fun j => hdiff c (n + j) (k + 1))) ≤ hdiff c n k := by
  have hid := hdiff_storage_ledger c n k m
  have hres : 0 ≤ hdiff c (n + m) k := h (n + m) k
  linarith

/-- !! Every higher finite difference is bounded above by its zeroth-order storage. -/
theorem hausdorff_hdiff_le_c {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n k : ℕ) :
    hdiff c n k ≤ c n := by
  have hm := hausdorff_storage_monotone_k h n 0 k
  simpa using hm

/-- ! A Hausdorff-positive sequence is antitone. -/
theorem hausdorff_c_antitone_offset {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n m : ℕ) :
    c (n + m) ≤ c n := by
  have hm := hausdorff_storage_monotone_n h n 0 m
  simpa using hm

end GPHausdorff.Our
