import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellEvents
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Escape

/-! Shell contraction via the component of the source. The one-shell argument
is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- The connected mass estimate also holds for a finite shell containing the
source: its source component has boundary contained in the shell boundary. -/
theorem mass_bound_of_origin_component
    {m : ℤ → ℤ → ℕ} {ε ρ t C c βₘ : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (ht : 0 < t) (hC : 0 ≤ C)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (T : Set ℤ) (hTfin : T.Finite)
    (hmass : ∀ T : Set ℤ, T ⊆ cellVertices ε η (ball 0 ρ) → IsVConnected m T →
      (0 : ℤ) ∈ T → ∀ (s : ℝ) (z : ℂ), 0 < s → ε ^ βₘ ≤ s →
      cellVertices ε η (ball z s) ⊆ cellVertices ε η (ball 0 ρ) \ T →
      ((cellVertices ε η (ball z (c * s)) ∩ matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤
        C * ⨆ b : vBoundary m T, stoppedOdometer m ε η ρ t b)
    (hTsub : T ⊆ cellVertices ε η (ball 0 ρ))
    (h0 : (0 : ℤ) ∈ T) (s : ℝ) (z : ℂ) (hs : 0 < s) (hscale : ε ^ βₘ ≤ s)
    (hball : cellVertices ε η (ball z s) ⊆ cellVertices ε η (ball 0 ρ) \ T) :
    ((cellVertices ε η (ball z (c * s)) ∩ matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤
      C * ⨆ b : vBoundary m T, stoppedOdometer m ε η ρ t b := by
  have hsub : vComponent m T 0 ⊆ T := vComponent_subset h0
  have hbsub : vBoundary m (vComponent m T 0) ⊆ vBoundary m T := by
    intro b hb
    have hbT := not_mem_of_mem_vBoundary_vComponent h0 hb
    obtain ⟨_, a, ha, hab⟩ := hb
    exact ⟨hbT, a, hsub ha, hab⟩
  have := (vBoundary_finite hlf hTfin).to_subtype
  have hbdd : BddAbove (range fun b : vBoundary m T => stoppedOdometer m ε η ρ t b) :=
    (Set.finite_range _).bddAbove
  have hsup : (⨆ b : vBoundary m (vComponent m T 0), stoppedOdometer m ε η ρ t b) ≤
      ⨆ b : vBoundary m T, stoppedOdometer m ε η ρ t b := by
    apply Real.iSup_le
    · intro b
      exact le_ciSup hbdd ⟨b.1, hbsub b.2⟩
    · exact Real.iSup_nonneg fun b => stoppedOdometer_nonneg hε ht b
  have hball' : cellVertices ε η (ball z s) ⊆
      cellVertices ε η (ball 0 ρ) \ vComponent m T 0 := by
    intro a ha
    exact ⟨(hball ha).1, fun ha' => (hball ha).2 (hsub ha')⟩
  exact (hmass (vComponent m T 0) (hsub.trans hTsub) (isVConnected_vComponent hsymm)
    self_mem_vComponent s z hs hscale hball').trans (mul_le_mul_of_nonneg_left hsup hC)

/-- On the good events of Lemmas 6.8 and 7.2, a shell contracts
once its scale and the ambient geometric margins are admissible. -/
theorem shell_boundary_contracts_of_mass_and_survival_events_of_component
    {m : ℤ → ℤ → ℕ} {ε ρ t r R D c K C β βₘ s₀ s₁ s₂ ω₀ dd : ℝ}
    {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hr : 0 < r) (hc : 0 < c) (hc' : c ≤ 1)
    (hs₂ : s₂ ≤ 1) (hD : D ≤ r / 2) (hη : Continuous η)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (h0 : (0 : ℤ) ∈ Θ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 < β) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hradius : ((⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b) * ε * K) ^ (1 / β) ≤ r)
    (hΘball : fillCells ε η Θ ⊆ ball 0 R) (hball : ball 0 s₀ ⊆ fillCells ε η Θ)
    (hambient : r + R ≤ ρ)
    (hclosure : R + r / 4 + D < ρ / 2)
    (hmargin : R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ)
    (hmin : 10 * ε ^ ω₀ ≤ (c / 8) * r) (hmax : (c / 8) * r ≤ dd)
    (hmassMin : ε ^ βₘ ≤ r / 4)
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
    (hgood : ∀ u : ℝ, u = (c / 8) * r → 10 * ε ^ ω₀ ≤ u → u ≤ dd → ∀ T : Set ℤ,
      closure (fillCells ε η T) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε η T →
      ∀ A ⊆ cellVertices ε η (thickening u (fillCells ε η T)) \ T,
        (∀ z : ℂ, ((A ∩ cellVertices ε η (ball z u)).ncard : ℝ) < s₁ * u ^ β / ε) →
        ∀ a ∈ cellVertices ε η (frontier (thickening (u / 2) (fillCells ε η T))),
          srwLaw m a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε η (thickening u (fillCells ε η T)) \ T) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂)) :
    (⨆ b : vBoundary m (cellVertices ε η (thickening r (fillCells ε η Θ))),
      stoppedOdometer m ε η ρ t b) ≤
      (⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b) * (1 - s₂) := by
  obtain ⟨hΘsub, hΘfin, hnextfin, hI, hΛfin, hdiam⟩ :=
    shell_geometric_inputs_of_ambient (m := m) (t := t) hε.le hr.le hΘball hambient hfin hsize
  have hO : 0 ≤ ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b :=
    Real.iSup_nonneg fun b => stoppedOdometer_nonneg hε ht b
  exact shell_boundary_contracts_of_good_event hε ht hr hc hc' hs₂ hD hη hsymm hlf hsucc hadj
    hfin hΛfin hlap hΘfin h0 hO rfl hK hC hβ hs₁ hcoeff hradius hΘball hball hI hdiam
    hclosure hmargin (fun w hw => mass_bound_of_origin_component hε ht hC hsymm hlf Θ hΘfin hmass hΘsub h0 (r / 4) w (by linarith) hmassMin hw)
    hmin hmax hnextfin hodo hgood


end MatedCRT.Sec7
