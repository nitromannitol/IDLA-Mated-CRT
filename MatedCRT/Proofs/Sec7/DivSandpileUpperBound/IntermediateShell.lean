import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusSlack

/-! Geometry of the intermediate shell used for the survival estimate. -/

namespace MatedCRT.Sec7

open Set Metric

/-- Thickening and then filling all meeting cells preserves the previous
filled shell. -/
theorem fillCells_subset_fill_intermediate
    {ε s : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ} (hs : 0 < s) :
    fillCells ε η Θ ⊆
      fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ))) := by
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  have haI : a ∈ cellVertices ε η (thickening s (fillCells ε η Θ)) :=
    ⟨z, hza, self_subset_thickening hs _ (mem_iUnion₂.mpr ⟨a, ha, hza⟩)⟩
  exact mem_iUnion₂.mpr ⟨a, haI, hza⟩

/-- A strict ambient margin puts the closure of the filled intermediate
shell inside the ball required by the survival estimate. -/
theorem closure_fill_intermediate_subset_ball
    {ε s R D ρ : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hη : Continuous η) (hΘ : fillCells ε η Θ ⊆ ball 0 R)
    (hdiam : ∀ a ∈ cellVertices ε η (thickening s (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hmargin : R + s + D < ρ / 2) :
    closure (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ)))) ⊆
      ball 0 (ρ / 2) := by
  have hfill : fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ))) ⊆
      ball 0 (R + s + D) := by
    have h := fillCells_subset_ball_of_thickened_shell (s := 0) hη hΘ Subset.rfl hdiam
      (show R + s + D + 0 ≤ R + s + D by linarith)
    simpa using h
  exact (closure_mono hfill).trans (closure_ball_subset_closedBall.trans (closedBall_subset_ball hmargin))

/-- A thickening of the filled intermediate shell is contained in a
thickening of the preceding shell, with one cell-diameter error. -/
theorem thickening_fill_intermediate_subset
    {ε s v D : ℝ} {η : ℝ → ℂ} {Θ I : Set ℤ}
    (hη : Continuous η)
    (hI : I ⊆ cellVertices ε η (thickening s (fillCells ε η Θ)))
    (hdiam : ∀ a ∈ I, diam (cell ε η a) ≤ D) :
    thickening v (fillCells ε η I) ⊆ thickening (v + D + s) (fillCells ε η Θ) := by
  intro z hz
  obtain ⟨y, hyI, hzy⟩ := Metric.mem_thickening_iff.mp hz
  obtain ⟨a, haI, hya⟩ := mem_iUnion₂.mp hyI
  obtain ⟨p, hpa, hp⟩ := hI haI
  obtain ⟨x, hxΘ, hpx⟩ := Metric.mem_thickening_iff.mp hp
  have hyp : dist y p ≤ D :=
    (dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded hya hpa).trans (hdiam a haI)
  refine Metric.mem_thickening_iff.mpr ⟨x, hxΘ, ?_⟩
  linarith [dist_triangle z y p, dist_triangle z p x]

/-- The graph annulus around the intermediate shell lies in the outer
thickening of the previous filled shell and avoids its inner cells. -/
theorem intermediate_annulus_geometry
    {ε s v D : ℝ} {η : ℝ → ℂ} {Θ A : Set ℤ}
    (hη : Continuous η)
    (hdiam : ∀ a ∈ cellVertices ε η (thickening s (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hA : A ⊆ cellVertices ε η (thickening v
      (fillCells ε η (cellVertices ε η (thickening s (fillCells ε η Θ))))) \
        cellVertices ε η (thickening s (fillCells ε η Θ))) :
    A ⊆ (cellVertices ε η (thickening s (fillCells ε η Θ)))ᶜ ∧
    A ⊆ cellVertices ε η (thickening (v + D + s) (fillCells ε η Θ)) := by
  constructor
  · intro a ha
    exact (hA ha).2
  · intro a ha
    exact cellVertices_mono (thickening_fill_intermediate_subset hη Subset.rfl hdiam) (hA ha).1

/-- The actual intermediate-shell annulus satisfies the strict small-mass
condition at radius `c r / 8` when its cells and the intermediate cells obey
the diameter bound. -/
theorem intermediate_annulus_local_count_lt
    {ε ρ r R D c O K β s₁ C : ℝ} {η : ℝ → ℂ} {A Λ Θ : Set ℤ}
    (hη : Continuous η) (hΛ : Λ.Finite) (hAΛ : A ⊆ Λ)
    (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hr : 0 < r) (hβ : 0 < β) (hc : 0 < c) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hradius : (O * ε * K) ^ (1 / β) ≤ r)
    (hΘ : fillCells ε η Θ ⊆ ball 0 R)
    (hI : ∀ a ∈ cellVertices ε η (thickening (r / 4) (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D)
    (hA : A ⊆ cellVertices ε η (thickening ((c / 8) * r)
      (fillCells ε η (cellVertices ε η (thickening (r / 4) (fillCells ε η Θ))))) \
        cellVertices ε η (thickening (r / 4) (fillCells ε η Θ)))
    (hdiam : ∀ a ∈ A, diam (cell ε η a) ≤ D)
    (hmargin : R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ)
    (hmass : ∀ w : ℂ,
      cellVertices ε η (ball w (r / 4)) ⊆ cellVertices ε η (ball 0 ρ) \ Θ →
      ((cellVertices ε η (ball w (c * (r / 4))) ∩ Λ).ncard : ℝ) ≤ C * O) :
    ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z ((c / 8) * r))).ncard : ℝ) <
      s₁ * ((c / 8) * r) ^ β / ε := by
  obtain ⟨hinner, houter⟩ := intermediate_annulus_geometry hη hI hA
  exact shell_local_count_lt_of_radius hη hΛ hAΛ hO hε hK hC hr hβ hc hs₁
    hcoeff hradius hΘ hinner houter hdiam hmargin hmass

end MatedCRT.Sec7
