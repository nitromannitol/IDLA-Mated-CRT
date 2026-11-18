import MatedCRT.FirstPass.Derived.AreaCellMeshEventually

/-! # A bounded set absorbing the cell-mesh condition of the shifted area-cell transfers

The shifted area-cell transfers assume that every cell of `areaCellConfig` meeting a set
`Wmesh` (after rescaling by `scale`) has diameter at most `d`, and that `Wmesh` contains the closed
balls of radius `scale * d` around the points of a given bounded set `U₁`. For an area
parametrized proper curve and mesh parameters tending to `0`, a bounded such set exists, and the
cell condition holds for all large indices. -/
set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric ReflectedGMS.GMS

/-- For a bounded set `U₁` of the plane, a rescaling `scale > 0` and a scale `d > 0`, the closed
`scale * d`-thickening `Wmesh` of `U₁` contains the closed balls of radius `scale * d` around the
points of `U₁`, and for all large indices every cell of `areaCellConfig` that meets the preimage of
`Wmesh` under the rescaling has diameter at most `d`. -/
theorem exists_meshSet_eventually_diam_cell_le {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (m : ℕ → ℤ → ℤ → ℕ) {U₁ : Set ReflectedGMS.Plane} (hU₁ : Bornology.IsBounded U₁)
    {scale : ℝ} (hscale : 0 < scale) {d : ℝ} (hd : 0 < d) :
    ∃ Wmesh : Set ReflectedGMS.Plane,
      Bornology.IsBounded Wmesh ∧
      (∀ x ∈ U₁, Metric.closedBall x (scale * d) ⊆ Wmesh) ∧
      ∀ᶠ n in atTop, ∀ K : (areaCellConfig h (hε n) (m n)).cells,
        (∃ z ∈ (K.1 : Set ReflectedGMS.Plane), scale • z ∈ Wmesh) →
          Metric.diam (K.1 : Set ReflectedGMS.Plane) ≤ d := by
  have hW : Bornology.IsBounded (Metric.cthickening (scale * d) U₁) := hU₁.cthickening
  have hpre : Bornology.IsBounded ((fun z : ReflectedGMS.Plane => scale • z) ⁻¹'
      Metric.cthickening (scale * d) U₁) := by
    rw [Set.preimage_smul₀ hscale.ne']
    exact hW.smul₀ _
  refine ⟨Metric.cthickening (scale * d) U₁, hW,
    fun x hx => Metric.closedBall_subset_cthickening hx _, ?_⟩
  filter_upwards [eventually_areaCellConfig_diam_le_of_meeting h hp hε hε0 m hpre hd]
    with n hn K hK
  obtain ⟨z, hzK, hzW⟩ := hK
  exact hn K ⟨z, hzK, hzW⟩

end MatedCRT
