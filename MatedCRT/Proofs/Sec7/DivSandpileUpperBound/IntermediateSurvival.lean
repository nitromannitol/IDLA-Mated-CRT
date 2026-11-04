import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.IntermediateContraction

/-! The intermediate annulus satisfies the survival estimate on the good event. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- The good event of Lemma 6.8 gives the survival bound for occupied vertices
in the intermediate annulus, using the strict local count estimate. -/
theorem intermediate_annulus_survival_of_good_event
    {m : ℤ → ℤ → ℕ} {ε ρ r R D c O K C β s₀ s₁ s₂ ω₀ dd : ℝ}
    {η : ℝ → ℂ} {Λ Θ : Set ℤ}
    (hη : Continuous η) (hΛ : Λ.Finite)
    (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hr : 0 < r) (hβ : 0 < β) (hc : 0 < c) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hradius : (O * ε * K) ^ (1 / β) ≤ r)
    (hΘ : fillCells ε η Θ ⊆ ball 0 R)
    (hball : ball 0 s₀ ⊆ fillCells ε η Θ)
    (hI : ∀ a ∈ cellVertices ε η (thickening (r / 4) (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hdiam : ∀ a ∈ Λ, diam (cell ε η a) ≤ D)
    (hclosure : R + r / 4 + D < ρ / 2)
    (hmargin : R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ)
    (hmass : ∀ w : ℂ,
      cellVertices ε η (ball w (r / 4)) ⊆ cellVertices ε η (ball 0 ρ) \ Θ →
      ((cellVertices ε η (ball w (c * (r / 4))) ∩ Λ).ncard : ℝ) ≤ C * O)
    (hmin : 10 * ε ^ ω₀ ≤ (c / 8) * r) (hmax : (c / 8) * r ≤ dd)
    (hgood : ∀ u : ℝ, 10 * ε ^ ω₀ ≤ u → u ≤ dd → ∀ T : Set ℤ,
      closure (fillCells ε η T) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε η T →
      ∀ A ⊆ cellVertices ε η (thickening u (fillCells ε η T)) \ T,
        (∀ z : ℂ, ((A ∩ cellVertices ε η (ball z u)).ncard : ℝ) < s₁ * u ^ β / ε) →
        ∀ a ∈ cellVertices ε η (frontier (thickening (u / 2) (fillCells ε η T))),
          srwLaw m a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε η (thickening u (fillCells ε η T)) \ T) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂)) :
    ∀ b ∈ cellVertices ε η (frontier (thickening (((c / 8) * r) / 2)
      (fillCells ε η (cellVertices ε η (thickening (r / 4) (fillCells ε η Θ)))))),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime
        (cellVertices ε η (thickening ((c / 8) * r)
          (fillCells ε η (cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))))) \
          cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))) x →
        x n ∈ (cellVertices ε η (thickening ((c / 8) * r)
          (fillCells ε η (cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))))) \
          cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))) ∩ Λ} ≤ ENNReal.ofReal (1 - s₂) := by
  let I := cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))
  let B := cellVertices ε η (thickening ((c / 8) * r) (fillCells ε η I)) \ I
  have hcount : ∀ z : ℂ, (((B ∩ Λ) ∩ cellVertices ε η (ball z ((c / 8) * r))).ncard : ℝ) <
      s₁ * ((c / 8) * r) ^ β / ε := by
    apply intermediate_annulus_local_count_lt hη hΛ (inter_subset_right : B ∩ Λ ⊆ Λ)
      hO hε hK hC hr hβ hc hs₁ hcoeff hradius hΘ hI
    · exact inter_subset_left
    · intro a ha
      exact hdiam a ha.2
    · exact hmargin
    · exact hmass
  have hclose : closure (fillCells ε η I) ⊆ ball 0 (ρ / 2) :=
    closure_fill_intermediate_subset_ball hη hΘ hI hclosure
  have hballI : ball 0 s₀ ⊆ fillCells ε η I :=
    hball.trans (fillCells_subset_fill_intermediate (by linarith : 0 < r / 4))
  exact hgood ((c / 8) * r) hmin hmax I hclose hballI (B ∩ Λ) inter_subset_left hcount

end MatedCRT.Sec7
