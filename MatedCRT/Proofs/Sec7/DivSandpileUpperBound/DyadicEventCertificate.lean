import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ComponentLogShellIteration
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DelayedDyadicCertificate

/-! A shell certificate from the mass and logarithmic survival good events.
The iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- Under the good events and the delayed dyadic budget, the stopped odometer
admits the finite shell certificate used in the upper bound. -/
theorem delayed_dyadic_certificate_of_mass_and_log_survival_events
    {m : ℤ → ℤ → ℕ} {ε ρ t R₀ R D c K C β βₘ s₀ s₁ s₂ ω₀ dd B δ F S : ℝ}
    {η : ℝ → ℂ} {Λ : Set ℂ} (Θ : ℕ → Set ℤ) (r O : ℕ → ℝ) (n N : ℕ)
    (hOeq : O = fun k => ⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b)
    (hr_eq : r = delayedShellRadius O (ε * K) (1 / β) F)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : ω₀ ≤ βₘ)
    (ht : 0 < t) (hc : 0 < c) (hc' : c ≤ 1)
    (hs₂0 : 0 < s₂) (hs₂ : s₂ ≤ 1)
    (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀) (hR : R ≤ ρ)
    (hF : 0 < F) (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hzero : (0 : ℤ) ∈ Θ 0) (hinit : Θ 0 = cellVertices ε η Λ) (hΛ : Λ ⊆ closedBall 0 R₀)
    (hball : ball 0 s₀ ⊆ fillCells ε η (Θ 0))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hslack : δ + R₀ < R)
    (hK : 0 < K) (hC : 0 ≤ C) (hβ : 0 < β) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hmargins : ∀ k < n,
      (∀ j < k, (⨆ b : vBoundary m (Θ (j + 1)), stoppedOdometer m ε η ρ t b) ≤
        (⨆ b : vBoundary m (Θ j), stoppedOdometer m ε η ρ t b)) →
      D ≤ r k / 2 ∧ r k + R ≤ ρ ∧
      R + r k / 4 + D < ρ / 2 ∧
      R + (((c / 8) * r k + D) + r k / 4) + D + r k / 4 ≤ ρ ∧
      10 * ε ^ ω₀ ≤ (c / 8) * r k ∧ (c / 8) * r k ≤ dd)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D)
    (hmass : ∀ T : Set ℤ, T ⊆ cellVertices ε η (ball 0 ρ) → IsVConnected m T →
      (0 : ℤ) ∈ T → ∀ (s : ℝ) (z : ℂ), 0 < s → ε ^ βₘ ≤ s →
      cellVertices ε η (ball z s) ⊆ cellVertices ε η (ball 0 ρ) \ T →
      ((cellVertices ε η (ball z (c * s)) ∩ matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤
        C * ⨆ b : vBoundary m T, stoppedOdometer m ε η ρ t b)
    (hodo : ∀ U : Set ℤ, U ⊆ cellVertices ε η (ball 0 ρ) \ {0} →
      ∀ b ∈ U, stoppedOdometer m ε η ρ t b ≤
      (⨆ a : vBoundary m U, stoppedOdometer m ε η ρ t a) *
        (srwLaw m b {x | vExitTime U x <
          vHitTime (U \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hgood : ∀ u : ℝ, 10 * ε ^ ω₀ ≤ u → u ≤ dd → ∀ T : Set ℤ,
      closure (fillCells ε η T) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε η T →
      ∀ A ⊆ cellVertices ε η (thickening u (fillCells ε η T)) \ T,
        (∀ z : ℂ, ((A ∩ cellVertices ε η (ball z u)).ncard : ℝ) < s₁ * u ^ β / ε) →
        ∀ a ∈ cellVertices ε η (frontier (thickening (u / 2) (fillCells ε η T))),
          srwLaw m a {x | ∀ j : ℕ,
            (j : ℕ∞) < vExitTime (cellVertices ε η (thickening u (fillCells ε η T)) \ T) x →
            x j ∈ A} ≤ ENNReal.ofReal (1 - s₂ / (1 + |Real.log u|) ^ 2))
    (hdd : dd ≤ 1) (hS : 0 < S) (h0 : O 0 ≤ S)
    (htarget : S * (1 / 2 : ℝ) ^ N ≤ B)
    (hbudget :
      let a := (c / 8) * (S * (ε * K) * (1 / 2 : ℝ)) ^ (1 / β)
      let q := (1 / 2 : ℝ) ^ (1 / β)
      let C' := 2 / s₂ + 2
      let A := 1 + |Real.log a|
      let L := |Real.log q|
      let H := (N : ℝ) * C' * (A + L * (N : ℝ)) ^ 2
      r 0 + ((S * (ε * K)) ^ (1 / β) * C' * ((A + L) ^ 2 *
        ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * q ^ j) + F * H) +
        (H + 1) * (2 * D) ≤ δ)
    (hn :
      let a := (c / 8) * (S * (ε * K) * (1 / 2 : ℝ)) ^ (1 / β)
      let q := (1 / 2 : ℝ) ^ (1 / β)
      (N : ℝ) * (2 / s₂ + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n) :
    ∃ (T : ℕ → Set ℤ) (r : ℕ → ℝ) (τ : ℕ) (d : ℝ),
      0 ≤ d ∧ (∀ k < τ, 0 < r k) ∧ (0 : ℤ) ∈ T 0 ∧
      T 0 ⊆ cellVertices ε η Λ ∧
      (∀ k < τ, T (k + 1) = cellVertices ε η (thickening (r k) (fillCells ε η (T k)))) ∧
      (∀ k ≤ τ, ∀ a ∈ vClosure m (T k), diam (cell ε η a) ≤ d) ∧
      (∀ a ∈ vBoundary m (T τ), stoppedOdometer m ε η ρ t a ≤ B) ∧
      (∑ k ∈ Finset.range τ, r k) + ((τ : ℝ) + 1) * (2 * d) ≤ δ := by
  have hr : ∀ k < n, 0 < r k := by
    intro k _
    rw [hr_eq]
    exact delayedShellRadius_pos O (ε * K) (1 / β) F hF k
  have hfirst : ((⨆ b : vBoundary m (Θ 0), stoppedOdometer m ε η ρ t b) * ε * K) ^
      (1 / β) ≤ r 0 := by
    rw [hr_eq, hOeq]
    simpa only [mul_assoc] using
      (delayedShellRadius_bounds (fun k => ⨆ b : vBoundary m (Θ k),
        stoppedOdometer m ε η ρ t b) (ε * K) (1 / β) F).1
  have hshift : ∀ k < n,
      ((⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) * ε * K) ^ (1 / β) ≤
        r (k + 1) := by
    intro k _
    rw [hr_eq, hOeq]
    simpa only [mul_assoc] using
      (delayedShellRadius_bounds (fun k => ⨆ b : vBoundary m (Θ k),
        stoppedOdometer m ε η ρ t b) (ε * K) (1 / β) F).2.1 k
  have hinit' : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀) := by
    rw [hinit]
    exact cellVertices_mono hΛ
  have hcontract := iterated_shell_contracts_of_mass_and_log_survival_events_of_component
    (B := B) Θ r n hε hε1 hω ht hc hc' hs₂0.le hs₂ hη hD hR₀ hR hr hsymm hlf hsucc hadj
    hfin hlap hzero hinit' hball hstep hslack hK.le hC hβ hs₁ hcoeff hfirst hshift
    hmargins hsize hmass hodo hgood
  apply delayed_dyadic_shell_certificate (α := 1 / β) (K := ε * K) (s := s₂) Θ O n N hOeq hε ht hη hD hF hR₀
    hS (mul_pos hε hK) (by positivity) hs₂0 hs₂ hc hlf hadj hinit hzero hΛ
    (by linarith) hfin hsize
  · simpa only [← hr_eq] using hstep
  · exact h0
  · exact htarget
  · intro k hk hprev
    have hp : ∀ j < k, (⨆ b : vBoundary m (Θ (j + 1)), stoppedOdometer m ε η ρ t b) ≤
        ⨆ b : vBoundary m (Θ j), stoppedOdometer m ε η ρ t b := by
      simpa only [hOeq] using hprev
    have hh := (hmargins k hk hp).2.2.2.2.2
    rw [← hr_eq]
    exact hh.trans hdd
  · rw [← hr_eq]
    simpa only [hOeq] using hcontract
  · simpa only [← hr_eq] using hbudget
  · exact hn

end MatedCRT.Sec7
