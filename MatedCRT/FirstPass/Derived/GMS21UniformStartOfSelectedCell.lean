import MatedCRT.FirstPass.Derived.GMS21UniformStartOfReciprocalMesh
import MatedCRT.FirstPass.Derived.ExclusiveCellStartTransfer

/-!
# The uniform-start invariance principle from the selected-cell comparison at variable radii

Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, in the plane case starts the walk on the mated-CRT map of
cell mass `1/n` at the smallest vertex `x^n_z` whose cell contains the point `z`, compares the unstopped interpolated
walk with planar Brownian motion from `z`, and measures the distance of curves by the local metric (2.2), whose
smallness gives closeness of the two curves stopped at their exit times from `B_r(0)` for some radius `r` of every
interval (`MatedCRT.LocalCurveMetricPick.exists_cmpEDist_stopAtExit_lt_of_dLoc_lt`). The good set
`uniformStartSelectedData ε ρ R κ` records this comparison at mesh `ε`, uniformly over `z ∈ closedBall 0 ρ`, with
closeness at some radius `r > R`, as a set of (continuous curve, edge multiplicities) data.

Off a null set of every valid environment, the selected-cell comparison at the larger radius `R + 1` and the inner
radius `ρ' = (ρ + R) / 2` gives the comparison of `GMS21UniformStartInput` at the fixed radius `R`, from every vertex
embedded in `closedBall 0 ρ`: the transfer from a variable larger radius
(`StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le_variable`) and the transfer from selected cells to all
embedded vertices (`vertex_start_bound_of_selected`, through points lying in exactly one cell).

## Main results

* `uniformStartSelectedData`: the selected-cell good set at mesh `ε`.
* `MatedCRTEnv.IsValid.ae_mem_uniformStartGood_of_selected`: the almost sure inclusion of good events.
* `uniformReciprocal_of_selected_reference`: the uniform bound at the reciprocal meshes from the law-level selected
  bound on one reference environment.
* `gms21UniformStartInput_of_selected_reference`: `GMS21UniformStartInput 𝒮` from the normalized law, the closure
  properties and the law-level selected-cell bound at the cell masses `1/n` on one reference environment.
* `uniformStartSelectedBallData`, `MatedCRTEnv.IsValid.ae_mem_uniformStartGood_of_selectedBall`,
  `uniformReciprocal_of_selectedBall_reference`, `gms21UniformStartInput_of_selectedBall_reference`: the same with
  the walk and the Brownian motion stopped at their exits from the ball `B_R(0)`, the comparison established in the
  proof of Gwynne–Miller–Sheffield, Theorem 3.4, case 1.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- The selected-cell good set at mesh `ε` on the data space of (continuous curve, edge multiplicities): for every
point `z ∈ closedBall 0 ρ` and every set `T` of paths, the walk of the multiplicities `d.2` from the smallest vertex
whose cell contains `z`, embedded by `d.1(ε ·)` and interpolated, lies in `T` with probability at most `κ` plus the
probability that planar Brownian motion from `z` is, for some radius `r > R`, within `cmpEDist`-distance `κ` of `T`
after both curves are stopped at their exit times from `B_r(0)`. -/
def uniformStartSelectedData (ε ρ R κ : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ T : Set (ℝ≥0 → ℂ),
    srwLaw d.2 (vertexOf ε d.1 z) {w | interpolatedWalk ε d.1 1 w ∈ T} ≤
      planarBrownianMotion z {b | ∃ g ∈ T, ∃ r : ℝ, R < r ∧
        cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal κ} +
        ENNReal.ofReal κ}

/-- **Selected cells at variable radii give all vertices at the fixed radius.** Let `0 < ρ < R` and `κ > 0`. There
is `δ > 0` such that for every valid environment `S`, every measurable continuous version `η'` of its curve and every
mesh `ε > 0`, almost surely, if `(η', S.mult ε)` lies in `uniformStartSelectedData ε ((ρ + R) / 2) (R + 1) δ`, then
the good event of `GMS21UniformStartInput` at mesh `ε` with parameters `ρ, R, κ` holds. -/
theorem exists_ae_mem_uniformStartGood_of_selected {ρ R κ : ℝ} (hρR : ρ < R) (hκ : 0 < κ) :
    ∃ δ > 0, ∀ {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω},
      S.IsValid 𝒮 γ → ∀ {η' : Ω → C(ℝ, ℂ)}, (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) → ∀ {ε : ℝ}, 0 < ε →
      ∀ᵐ ω ∂S.P, (η' ω, S.mult ε ω) ∈ uniformStartSelectedData ε ((ρ + R) / 2) (R + 1) δ →
        ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (S.mult ε ω) x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint ε (S.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ := by
  have hρρ' : ρ < (ρ + R) / 2 := by linarith
  have hρ'R : (ρ + R) / 2 < R := by linarith
  have hκ2 : 0 < κ / 2 := half_pos hκ
  obtain ⟨δ, hδ, hvar⟩ :=
    StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le_variable (Ω' := ℕ → ℤ) hρ'R one_pos hκ2 hκ2
  refine ⟨δ, hδ, ?_⟩
  intro 𝒮 γ Ω _ S hS η' hη' ε hε
  filter_upwards [hη', hS.isAreaParametrized] with ω hω hap hsel
  have hsel' : ∀ z ∈ closedBall (0 : ℂ) ((ρ + R) / 2), ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)
          {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal (κ / 2)} +
          ENNReal.ofReal (κ / 2) := by
    intro z hz A
    refine hvar z hz (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z))
      (fun w => interpolatedWalk ε (S.η ω) 1 w)
      (fun w => continuous_interpolatedWalk ε 1 (S.η ω) w) (fun T => ?_) A
    have h := hsel z hz T
    simp only [hω] at h
    exact h
  intro x hx A
  have hbound := vertex_start_bound_of_selected hap hε hρρ' hρ'R (ENNReal.ofReal_pos.2 hκ2)
    (ENNReal.ofReal_pos.2 hκ2)
    (fun k A => srwLaw (S.mult ε ω) k
      {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A})
    (ENNReal.ofReal (κ / 2)) (ENNReal.ofReal (κ / 2)) hsel' x hx A
  have hhalf : ENNReal.ofReal (κ / 2) + ENNReal.ofReal (κ / 2) = ENNReal.ofReal κ := by
    rw [← ENNReal.ofReal_add hκ2.le hκ2.le, add_halves]
  rw [hhalf] at hbound
  exact hbound

/-- **The uniform reciprocal-mesh bound from the selected-cell bound on one reference environment.** If `𝒮` has
normalized law `ν` and, for each `0 < γ < 2`, some model `𝒮₀` with law `ν` has a valid environment `S₀` with a
measurable continuous version `η₀` of its curve such that for all `0 < ρ < R` and `κ, θ > 0` the law of
`(η₀, S₀.mult (1/n))` gives mass at most `θ` to the complement of `uniformStartSelectedData (1/n) ρ R κ` for all
large `n`, then the failure probability of the comparison of `GMS21UniformStartInput` at the mesh `1/n` is at most
`θ` in every valid environment of `𝒮`, for all large `n` independent of the environment. -/
theorem uniformReciprocal_of_selected_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        S.P {ω | ∀ x : ℤ, vertexPoint (1 / (n : ℝ)) (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (S.mult (1 / (n : ℝ)) ω) x
              {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (1 / (n : ℝ)) (S.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint (1 / (n : ℝ)) (S.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ}ᶜ ≤ ENNReal.ofReal θ := by
  intro γ hγ0 hγ2 R ρ hρ hρR κ hκ θ hθ
  obtain ⟨𝒮₀, hν₀, Ω₀, _, S₀, hS₀, η₀, hη₀m, hη₀, hbd⟩ := hRef γ hγ0 hγ2
  obtain ⟨δ, hδ, hae⟩ := exists_ae_mem_uniformStartGood_of_selected hρR hκ
  obtain ⟨N, hN⟩ := hbd (R + 1) ((ρ + R) / 2) (by linarith) (by linarith) δ hδ θ hθ
  refine ⟨max N 1, fun n hn Ω _ S hS => ?_⟩
  have hn0 : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    positivity
  obtain ⟨η', hη'm, hη'⟩ := hS.exists_curveVersion
  have hD : Measurable fun ω => (η' ω, S.mult (1 / (n : ℝ)) ω) :=
    hη'm.prodMk (hS.measurable_mult_array _)
  refine le_trans (measure_mono_ae (t := (fun ω => (η' ω, S.mult (1 / (n : ℝ)) ω)) ⁻¹'
      (uniformStartSelectedData (1 / (n : ℝ)) ((ρ + R) / 2) (R + 1) δ)ᶜ) ?_)
    ((Measure.le_map_apply hD.aemeasurable _).trans ?_)
  · filter_upwards [hae hS hη' hn0] with ω hω
    intro hbad hsel
    exact hbad (hω hsel)
  · rw [map_curveVersion_mult_eq_of_valid h1 hν₀ hγ0 hγ2 hS hS₀ hη'm hη' hη₀m hη₀ (1 / (n : ℝ))]
    exact hN n (le_of_max_le_left hn)

/-- **The uniform-start invariance principle from the selected-cell comparison on one reference environment.** Let
`𝒮` have normalized space-filling SLE law `ν` and the closure properties `SLEModelClosureInput 𝒮`. Suppose that for
each `0 < γ < 2` some model `𝒮₀` with the same law `ν` has a valid environment `S₀` (on any carrier) with a measurable
continuous version `η₀` of its curve, such that for all `0 < ρ < R` and `κ, θ > 0`, for all large `n` the law of
`(η₀, S₀.mult (1/n))` gives mass at most `θ` to the complement of `uniformStartSelectedData (1/n) ρ R κ`
(Gwynne–Miller–Sheffield, arXiv:1705.11161, Theorem 3.4, plane case: cell masses `1/n`, the smallest cell containing
the start, the unstopped walk, closeness at some radius beyond `R` as given by the local metric (2.2)). Then
`GMS21UniformStartInput 𝒮`. -/
theorem gms21UniformStartInput_of_selected_reference {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    GMS21UniformStartInput 𝒮 :=
  gms21UniformStartInput_of_uniform_reciprocal h2 (uniformReciprocal_of_selected_reference h1 hRef)

/-- The selected-cell good set at mesh `ε` and the fixed radius `R`: for every point `z ∈ closedBall 0 ρ` and every
set `A` of paths, the walk of `d.2` from the smallest vertex whose cell contains `z`, embedded by `d.1(ε ·)`,
interpolated and stopped at its exit time from `B_R(0)`, lies in `A` with probability at most `κ` plus the
probability that planar Brownian motion from `z`, stopped at its exit time from `B_R(0)`, is within
`cmpEDist`-distance `κ` of `A`. This is the comparison established in the proof of Gwynne–Miller–Sheffield
(arXiv:1705.11161), Theorem 3.4, case 1 (the walk and the Brownian motion stopped at their exits from a ball). -/
def uniformStartSelectedBallData (ε ρ R κ : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ A : Set (ℝ≥0 → ℂ),
    srwLaw d.2 (vertexOf ε d.1 z) {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε d.1 1 w) ∈ A} ≤
      planarBrownianMotion z {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ}

/-- **Selected cells at the fixed radius give all vertices.** For `0 < ρ < R`, `κ > 0`, every valid environment `S`,
every measurable continuous version `η'` of its curve and every mesh `ε > 0`, almost surely, if `(η', S.mult ε)` lies
in `uniformStartSelectedBallData ε ((ρ + R) / 2) R (κ / 2)`, then the good event of `GMS21UniformStartInput` at mesh
`ε` with parameters `ρ, R, κ` holds. -/
theorem MatedCRTEnv.IsValid.ae_mem_uniformStartGood_of_selectedBall {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε ρ R κ : ℝ} (hε : 0 < ε) (hρR : ρ < R) (hκ : 0 < κ) :
    ∀ᵐ ω ∂S.P, (η' ω, S.mult ε ω) ∈ uniformStartSelectedBallData ε ((ρ + R) / 2) R (κ / 2) →
      ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
        srwLaw (S.mult ε ω) x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
          planarBrownianMotion (vertexPoint ε (S.η ω) x)
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
            ENNReal.ofReal κ := by
  have hρρ' : ρ < (ρ + R) / 2 := by linarith
  have hρ'R : (ρ + R) / 2 < R := by linarith
  have hκ2 : 0 < κ / 2 := half_pos hκ
  filter_upwards [hη', hS.isAreaParametrized] with ω hω hap hsel
  intro x hx A
  have hsel' : ∀ z ∈ closedBall (0 : ℂ) ((ρ + R) / 2), ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)
          {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal (κ / 2)} +
          ENNReal.ofReal (κ / 2) := by
    intro z hz A
    have h := hsel z hz A
    simp only [hω] at h
    exact h
  have hbound := vertex_start_bound_of_selected hap hε hρρ' hρ'R (ENNReal.ofReal_pos.2 hκ2)
    (ENNReal.ofReal_pos.2 hκ2)
    (fun k A => srwLaw (S.mult ε ω) k
      {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A})
    (ENNReal.ofReal (κ / 2)) (ENNReal.ofReal (κ / 2)) hsel' x hx A
  have hhalf : ENNReal.ofReal (κ / 2) + ENNReal.ofReal (κ / 2) = ENNReal.ofReal κ := by
    rw [← ENNReal.ofReal_add hκ2.le hκ2.le, add_halves]
  rw [hhalf] at hbound
  exact hbound

/-- **The uniform reciprocal-mesh bound from the fixed-radius selected-cell bound on one reference environment.** The
same as `uniformReciprocal_of_selected_reference`, with `uniformStartSelectedBallData` (the walk and the Brownian
motion stopped at their exits from the ball) in place of `uniformStartSelectedData`. -/
theorem uniformReciprocal_of_selectedBall_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedBallData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        S.P {ω | ∀ x : ℤ, vertexPoint (1 / (n : ℝ)) (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (S.mult (1 / (n : ℝ)) ω) x
              {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (1 / (n : ℝ)) (S.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint (1 / (n : ℝ)) (S.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ}ᶜ ≤ ENNReal.ofReal θ := by
  intro γ hγ0 hγ2 R ρ hρ hρR κ hκ θ hθ
  obtain ⟨𝒮₀, hν₀, Ω₀, _, S₀, hS₀, η₀, hη₀m, hη₀, hbd⟩ := hRef γ hγ0 hγ2
  obtain ⟨N, hN⟩ := hbd R ((ρ + R) / 2) (by linarith) (by linarith) (κ / 2) (half_pos hκ) θ hθ
  refine ⟨max N 1, fun n hn Ω _ S hS => ?_⟩
  have hn0 : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    positivity
  obtain ⟨η', hη'm, hη'⟩ := hS.exists_curveVersion
  have hD : Measurable fun ω => (η' ω, S.mult (1 / (n : ℝ)) ω) :=
    hη'm.prodMk (hS.measurable_mult_array _)
  refine le_trans (measure_mono_ae (t := (fun ω => (η' ω, S.mult (1 / (n : ℝ)) ω)) ⁻¹'
      (uniformStartSelectedBallData (1 / (n : ℝ)) ((ρ + R) / 2) R (κ / 2))ᶜ) ?_)
    ((Measure.le_map_apply hD.aemeasurable _).trans ?_)
  · filter_upwards [hS.ae_mem_uniformStartGood_of_selectedBall hη' hn0 hρR hκ] with ω hω
    intro hbad hsel
    exact hbad (hω hsel)
  · rw [map_curveVersion_mult_eq_of_valid h1 hν₀ hγ0 hγ2 hS hS₀ hη'm hη' hη₀m hη₀ (1 / (n : ℝ))]
    exact hN n (le_of_max_le_left hn)

/-- **The uniform-start invariance principle from the fixed-radius selected-cell comparison on one reference
environment.** The same as `gms21UniformStartInput_of_selected_reference`, with `uniformStartSelectedBallData` (the
comparison of the stopped curves established in the proof of Gwynne–Miller–Sheffield, arXiv:1705.11161,
Theorem 3.4, case 1) in place of `uniformStartSelectedData`. -/
theorem gms21UniformStartInput_of_selectedBall_reference {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedBallData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    GMS21UniformStartInput 𝒮 :=
  gms21UniformStartInput_of_uniform_reciprocal h2 (uniformReciprocal_of_selectedBall_reference h1 hRef)

end MatedCRT
