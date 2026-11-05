import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicDelayedBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DelayedShellCertificate

/-! From logarithmic shell contraction and a dyadic budget to a shell certificate.
The dyadic iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open Set Metric

/-- The dyadic bootstrap and ambient cell bounds produce the finite shell
certificate, with no geometric assumptions beyond the stopping index. -/
theorem delayed_dyadic_shell_certificate
    {m : ℤ → ℤ → ℕ} {ε ρ t D B δ K α R R₀ S s c : ℝ}
    {η : ℝ → ℂ} {Λ : Set ℂ}
    (Θ : ℕ → Set ℤ) (O : ℕ → ℝ) (n N : ℕ)
    (hOeq : O = fun k => ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b)
    (hε : 0 < ε) (ht : 0 < t) (hη : Continuous η)
    (hD : 0 ≤ D) (hR : 0 < R) (hR₀ : 0 ≤ R₀)
    (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 < c)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hinit : Θ 0 = cellVertices ε η Λ) (hzero : (0 : ℤ) ∈ Θ 0)
    (hΛ : Λ ⊆ closedBall 0 R₀) (hmargin : δ + R₀ < ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D)
    (hshell : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (delayedShellRadius O K α R k) (fillCells ε η (Θ k))))
    (h0 : O 0 ≤ S) (htarget : S * (1 / 2 : ℝ) ^ N ≤ B)
    (hcut : ∀ k < n, (∀ i < k, O (i + 1) ≤ O i) →
      (c / 8) * delayedShellRadius O K α R k ≤ 1)
    (hcontract : ∀ k < n, B < O k →
      (∑ j ∈ Finset.range k, delayedShellRadius O K α R j) +
        ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ O j) →
      O (k + 1) ≤ (1 - s / (1 +
        |Real.log ((c / 8) * delayedShellRadius O K α R k)|) ^ 2) * O k)
    (hbudget :
      let a := (c / 8) * (S * K * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      let C := 2 / s + 2
      let A := 1 + |Real.log a|
      let L := |Real.log q|
      let H := (N : ℝ) * C * (A + L * (N : ℝ)) ^ 2
      delayedShellRadius O K α R 0 +
        ((S * K) ^ α * C * ((A + L) ^ 2 *
          ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) + R * H) +
        (H + 1) * (2 * D) ≤ δ)
    (hn :
      let a := (c / 8) * (S * K * (1 / 2 : ℝ)) ^ α
      let q := (1 / 2 : ℝ) ^ α
      (N : ℝ) * (2 / s + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n) :
    ∃ (T : ℕ → Set ℤ) (r : ℕ → ℝ) (τ : ℕ) (d : ℝ),
      0 ≤ d ∧ (∀ k < τ, 0 < r k) ∧ (0 : ℤ) ∈ T 0 ∧
      T 0 ⊆ cellVertices ε η Λ ∧
      (∀ k < τ, T (k + 1) = cellVertices ε η (thickening (r k) (fillCells ε η (T k)))) ∧
      (∀ k ≤ τ, ∀ a ∈ vClosure m (T k), diam (cell ε η a) ≤ d) ∧
      (∀ a ∈ vBoundary m (T τ), stoppedOdometer m ε η ρ t a ≤ B) ∧
      (∑ k ∈ Finset.range τ, r k) + ((τ : ℝ) + 1) * (2 * d) ≤ δ := by
  have hO : ∀ k ≤ n, 0 ≤ O k := by
    intro k _
    rw [hOeq]
    exact Real.iSup_nonneg fun b => stoppedOdometer_nonneg hε ht b
  obtain ⟨τ, hτ, hbound, _, hcost⟩ :=
    exists_threshold_of_delayed_dyadic_bootstrap O S K α R s c D B δ n N
      hS hK hα hR.le hs hs1 hc hD h0 hO htarget hcut hcontract hbudget hn
  subst O
  exact delayed_shell_certificate_of_ambient_bounds Θ n hε.le hη hD hR hR₀ hlf hadj
    hinit hzero hΛ hmargin hfin hsize hshell ⟨τ, hτ, hbound, hcost⟩

end MatedCRT.Sec7
