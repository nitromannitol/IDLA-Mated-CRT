import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.IntermediateSurvival

/-! One-shell contraction using the admissible intermediate annulus. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- A positive shell expansion contains every vertex of the preceding shell. -/
theorem subset_cellVertices_thickening_fill
    {ε r : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ} (hε : 0 ≤ ε) (hr : 0 < r) :
    Θ ⊆ cellVertices ε η (thickening r (fillCells ε η Θ)) := by
  intro a ha
  refine ⟨vertexPoint ε η a, vertexPoint_mem_cell hε η a, ?_⟩
  exact self_subset_thickening hr _ (mem_iUnion₂.mpr ⟨a, ha, vertexPoint_mem_cell hε η a⟩)

/-- Each iterated shell contains the initial shell and hence its filled cells. -/
theorem initial_fill_subset_iterated_shell
    {ε : ℝ} {η : ℝ → ℂ} (Θ : ℕ → Set ℤ) (r : ℕ → ℝ)
    (hε : 0 ≤ ε) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, Θ (k + 1) = cellVertices ε η (thickening (r k) (fillCells ε η (Θ k))))
    (n : ℕ) : fillCells ε η (Θ 0) ⊆ fillCells ε η (Θ n) := by
  have hsub : ∀ n, Θ 0 ⊆ Θ n := by
    intro n
    induction n with
    | zero => exact Subset.rfl
    | succ n ih =>
      rw [hstep n]
      exact ih.trans (subset_cellVertices_thickening_fill hε (hr n))
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨a, hsub n ha, hza⟩

/-- A shell expansion is finite if it remains in a ball whose cells are finite. -/
theorem finite_cellVertices_thickening_fill_of_ball
    {ε ρ r R : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hΘ : fillCells ε η Θ ⊆ ball 0 R) (hmargin : r + R ≤ ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite) :
    (cellVertices ε η (thickening r (fillCells ε η Θ))).Finite := by
  apply hfin.subset
  apply cellVertices_mono
  exact (thickening_subset_of_subset r hΘ).trans
    ((Metric.thickening_ball 0 r R).trans ((ball_subset_ball hmargin).trans ball_subset_closedBall))

/-- The geometric and stopped-odometer conditions imply contraction across
one shell once the intermediate-annulus survival estimate holds. -/
theorem shell_boundary_contracts_of_survival_bound
    {m : ℤ → ℤ → ℕ} {ε ρ t q s v r R D : ℝ} {η : ℝ → ℂ}
    {Θ I B : Set ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hq : 0 ≤ q) (hs : 0 < s) (hv : 0 < v)
    (hη : Continuous η)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ)
    (hI : I = cellVertices ε η (thickening s (fillCells ε η Θ)))
    (hB : B = cellVertices ε η (thickening v (fillCells ε η I)) \ I)
    (hΘball : fillCells ε η Θ ⊆ ball 0 R)
    (hdiam : ∀ a ∈ I, diam (cell ε η a) ≤ D)
    (hambient : R + (v + D + s) ≤ ρ)
    (hbudget : v / 2 + D + s ≤ r)
    (hnextfin : (cellVertices ε η (thickening r (fillCells ε η Θ))).Finite)
    (hodo : ∀ U : Set ℤ, U ⊆ cellVertices ε η (ball 0 ρ) \ {0} →
      ∀ b ∈ U, stoppedOdometer m ε η ρ t b ≤
      (⨆ c : vBoundary m U, stoppedOdometer m ε η ρ t c) *
        (srwLaw m b {x | vExitTime U x <
          vHitTime (U \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hprob : ∀ b ∈ cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I))),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x →
        x n ∈ B ∩ matedDiscreteCluster m ε η ρ t} ≤ ENNReal.ofReal q) :
    (⨆ b : vBoundary m (cellVertices ε η (thickening r (fillCells ε η Θ))),
      stoppedOdometer m ε η ρ t b) ≤
      (⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b) * q := by
  have hdiamI : ∀ a ∈ cellVertices ε η (thickening s (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D := by simpa [hI] using hdiam
  have hnext := intermediate_inner_subset_next_shell hη hdiamI hbudget
  have hinner : (cellVertices ε η (thickening (v / 2) (fillCells ε η I)) \
      cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I)))).Finite := by
    apply hnextfin.subset
    simpa [hI] using hnext
  have hinner0 : (0 : ℤ) ∈ cellVertices ε η (thickening (v / 2) (fillCells ε η I)) \
      cellVertices ε η (frontier (thickening (v / 2) (fillCells ε η I))) := by
    simpa [hI] using intermediate_inner_contains_zero hε.le hs hv h0
  have hBambient : B ⊆ cellVertices ε η (ball 0 ρ) \ {0} := by
    rw [hB, hI]
    exact intermediate_annulus_subset_ambient_sdiff_origin hε.le hs hη h0 hΘball hdiamI hambient
  apply intermediate_annulus_boundary_contracts hε ht hq hs hv hη hsymm hlf hsucc hadj hfin
    hlap hΘ h0 hI hB hinner hinner0
  · simpa [hI] using hnext
  · exact hodo B hBambient
  · exact hprob

/-- A single shell contracts on the survival good event when the local mass
bound and the explicit geometric margins hold. -/
theorem shell_boundary_contracts_of_good_event
    {m : ℤ → ℤ → ℕ} {ε ρ t r R D c O K C β s₀ s₁ s₂ ω₀ dd : ℝ}
    {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 < ε) (ht : 0 < t) (hr : 0 < r) (hc : 0 < c) (hc' : c ≤ 1)
    (hs₂ : s₂ ≤ 1) (hD : D ≤ r / 2) (hη : Continuous η)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hΛfin : (matedDiscreteCluster m ε η ρ t).Finite)
    (hlap : ∀ a ∈ matedDiscreteCluster m ε η ρ t, a ≠ 0 →
      matedLaplacian m (stoppedOdometer m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹)
    (hΘ : Θ.Finite) (h0 : (0 : ℤ) ∈ Θ)
    (hO : 0 ≤ O) (hOeq : O = ⨆ b : vBoundary m Θ, stoppedOdometer m ε η ρ t b)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 < β) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hradius : (O * ε * K) ^ (1 / β) ≤ r)
    (hΘball : fillCells ε η Θ ⊆ ball 0 R) (hball : ball 0 s₀ ⊆ fillCells ε η Θ)
    (hI : ∀ a ∈ cellVertices ε η (thickening (r / 4) (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hdiam : ∀ a ∈ matedDiscreteCluster m ε η ρ t, diam (cell ε η a) ≤ D)
    (hclosure : R + r / 4 + D < ρ / 2)
    (hmargin : R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ)
    (hmass : ∀ w : ℂ,
      cellVertices ε η (ball w (r / 4)) ⊆ cellVertices ε η (ball 0 ρ) \ Θ →
      ((cellVertices ε η (ball w (c * (r / 4))) ∩
        matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤ C * O)
    (hmin : 10 * ε ^ ω₀ ≤ (c / 8) * r) (hmax : (c / 8) * r ≤ dd)
    (hnextfin : (cellVertices ε η (thickening r (fillCells ε η Θ))).Finite)
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
          srwLaw m a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε η (thickening u (fillCells ε η T)) \ T) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂)) :
    (⨆ b : vBoundary m (cellVertices ε η (thickening r (fillCells ε η Θ))),
      stoppedOdometer m ε η ρ t b) ≤ O * (1 - s₂) := by
  let I := cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))
  let B := cellVertices ε η (thickening ((c / 8) * r) (fillCells ε η I)) \ I
  have hambient : R + (((c / 8) * r) + D + r / 4) ≤ ρ := by
    have hDnonneg : 0 ≤ D := by
      have h0I : (0 : ℤ) ∈ I := by
        refine ⟨vertexPoint ε η 0, vertexPoint_mem_cell hε.le η 0, ?_⟩
        exact self_subset_thickening (by linarith : 0 < r / 4) _
          (mem_iUnion₂.mpr ⟨0, h0, vertexPoint_mem_cell hε.le η 0⟩)
      exact diam_nonneg.trans (hI 0 h0I)
    linarith
  have hprob := intermediate_annulus_survival_of_good_event hη hΛfin hO hε hK hC hr hβ hc hs₁
    hcoeff hradius hΘball hball hI hdiam hclosure hmargin hmass hmin hmax hgood
  have hcontract := shell_boundary_contracts_of_survival_bound (I := I) (B := B)
    hε ht (by linarith : 0 ≤ 1 - s₂) (by linarith : 0 < r / 4)
    (by positivity : 0 < (c / 8) * r) hη hsymm hlf hsucc hadj hfin hlap hΘ h0
    rfl rfl hΘball hI hambient (intermediate_radius_budget hr.le hc' hD) hnextfin hodo hprob
  simpa [hOeq] using hcontract

end MatedCRT.Sec7
