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

/-- The intermediate annulus is admissible for the stopped-odometer
estimate whenever the thickening and cell-diameter errors fit in the ambient
ball. The origin belongs to the filled intermediate shell. -/
theorem intermediate_annulus_subset_ambient_sdiff_origin
    {ε ρ s v R D : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 ≤ ε) (hs : 0 < s) (hη : Continuous η) (h0 : (0 : ℤ) ∈ Θ)
    (hΘ : fillCells ε η Θ ⊆ ball 0 R)
    (hdiam : ∀ a ∈ cellVertices ε η (thickening s (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hmargin : R + (v + D + s) ≤ ρ) :
    cellVertices ε η (thickening v
      (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ))))) \
      cellVertices ε η (thickening s (fillCells ε η Θ)) ⊆
      cellVertices ε η (ball 0 ρ) \ {0} := by
  have h0I : (0 : ℤ) ∈ cellVertices ε η (thickening s (fillCells ε η Θ)) := by
    refine ⟨vertexPoint ε η 0, vertexPoint_mem_cell hε η 0, ?_⟩
    exact self_subset_thickening hs _
      (mem_iUnion₂.mpr ⟨0, h0, vertexPoint_mem_cell hε η 0⟩)
  have hcontain : thickening v
      (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ)))) ⊆ ball 0 ρ := by
    refine (thickening_fill_intermediate_subset hη Subset.rfl hdiam).trans ?_
    refine (thickening_subset_of_subset (v + D + s) hΘ).trans ?_
    exact (Metric.thickening_ball 0 (v + D + s) R).trans
      (ball_subset_ball (by linarith))
  intro a ha
  exact ⟨cellVertices_mono hcontain ha.1, by simpa using (ne_of_mem_of_not_mem h0I ha.2).symm⟩

/-- The stopped-odometer estimate applies almost surely to every intermediate
annulus satisfying the ambient margin. -/
theorem intermediate_annulus_odometer_bound_ae
    (𝒮 : SpaceFillingSLEModel) (hodo : OdometerBoundMassStmt 𝒮)
    (γ ρ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε t s v R D : ℝ, 0 < ε → 0 < t → 0 < s →
      Continuous (S.η ω) → ∀ Θ : Set ℤ, (0 : ℤ) ∈ Θ →
      fillCells ε (S.η ω) Θ ⊆ ball 0 R →
      (∀ a ∈ cellVertices ε (S.η ω) (thickening s (fillCells ε (S.η ω) Θ)),
        diam (cell ε (S.η ω) a) ≤ D) → R + (v + D + s) ≤ ρ →
      ∀ b ∈ cellVertices ε (S.η ω) (thickening v
        (fillCells ε (S.η ω) (cellVertices ε (S.η ω)
          (thickening s (fillCells ε (S.η ω) Θ))))) \
        cellVertices ε (S.η ω) (thickening s (fillCells ε (S.η ω) Θ)),
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤
        (⨆ c : vBoundary (S.mult ε ω)
          (cellVertices ε (S.η ω) (thickening v
            (fillCells ε (S.η ω) (cellVertices ε (S.η ω)
              (thickening s (fillCells ε (S.η ω) Θ))))) \
            cellVertices ε (S.η ω) (thickening s (fillCells ε (S.η ω) Θ))),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) *
        (srwLaw (S.mult ε ω) b {x |
          vExitTime (cellVertices ε (S.η ω) (thickening v
            (fillCells ε (S.η ω) (cellVertices ε (S.η ω)
              (thickening s (fillCells ε (S.η ω) Θ))))) \
            cellVertices ε (S.η ω) (thickening s (fillCells ε (S.η ω) Θ))) x <
          vHitTime ((cellVertices ε (S.η ω) (thickening v
            (fillCells ε (S.η ω) (cellVertices ε (S.η ω)
              (thickening s (fillCells ε (S.η ω) Θ))))) \
            cellVertices ε (S.η ω) (thickening s (fillCells ε (S.η ω) Θ))) \
            matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) x}).toReal := by
  filter_upwards [hodo γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hω
  intro ε t s v R D hε ht hs hη Θ h0 hΘ hdiam hmargin
  apply hω ε t hε ht
  exact intermediate_annulus_subset_ambient_sdiff_origin hε.le hs hη h0 hΘ hdiam hmargin

end MatedCRT.Sec7
