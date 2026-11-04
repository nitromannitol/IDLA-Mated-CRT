import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellSequence
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusSlack

/-! Simultaneous shell contraction on the mass and survival events. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- The two good events give contraction at each active connected shell whose
preceding shells satisfy the ambient budget. -/
theorem iterated_shell_contracts_of_mass_and_survival_events
    {m : ℤ → ℤ → ℕ} {ε ρ t R₀ R D c K C β βₘ s₀ s₁ s₂ ω₀ dd B δ : ℝ}
    {η : ℝ → ℂ} (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : ω₀ ≤ βₘ)
    (ht : 0 < t) (hc : 0 < c) (hc' : c ≤ 1)
    (hs₂ : s₂ ≤ 1) (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀) (hR : R ≤ ρ)
    (hr : ∀ k < n, 0 < r k) (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hconn : ∀ k < n, IsVConnected m (Θ k))
    (hzero : (0 : ℤ) ∈ Θ 0) (hinit : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hball : ball 0 s₀ ⊆ fillCells ε η (Θ 0))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hslack : δ + R₀ < R)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 < β) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hrad : ∀ k < n, B < (⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) →
      ((⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) * ε * K) ^ (1 / β) ≤ r k)
    (hmargins : ∀ k < n, D ≤ r k / 2 ∧ r k + R ≤ ρ ∧
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
            x j ∈ A} ≤ ENNReal.ofReal (1 - s₂)) :
    ∀ k < n, B < (⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (⨆ b : vBoundary m (Θ (k + 1)), stoppedOdometer m ε η ρ t b) ≤
      (1 - s₂) * (⨆ b : vBoundary m (Θ k), stoppedOdometer m ε η ρ t b) := by
  have hsizeR : ∀ a ∈ cellVertices ε η (ball 0 R), diam (cell ε η a) ≤ D :=
    fun a ha => hsize a (cellVertices_mono (ball_subset_ball hR) ha)
  intro k hk hactive hbudget
  have hgeom := iterated_shell_admissibility_of_total_budget Θ r k hε.le hη hD hR₀
    (fun j hj => hr j (by omega)) hadj hinit hzero hball
    (fun j hj => hstep j (by omega)) (by linarith) hsizeR
  obtain ⟨hfill, _, hzero', hball'⟩ := hgeom k le_rfl
  obtain ⟨hDr, hambient, hclosure, hmargin, hmin, hmax⟩ := hmargins k hk
  have hmassMin : ε ^ βₘ ≤ r k / 4 :=
    shell_mass_test_above_scale hε hε1 hω hc' (hr k hk).le hmin
  have hcontract := shell_boundary_contracts_of_mass_and_survival_events
    hε ht (hr k hk) hc hc' hs₂ hDr hη hsymm hlf hsucc hadj hfin hlap (hconn k hk)
    hzero' hK hC hβ hs₁ hcoeff (hrad k hk hactive) hfill hball' hambient hclosure
    hmargin hmin hmax hmassMin hsize hmass hodo hgood
  rw [hstep k hk]
  simpa only [mul_comm] using hcontract

end MatedCRT.Sec7
