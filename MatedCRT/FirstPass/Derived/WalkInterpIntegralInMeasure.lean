import MatedCRT.FirstPass.Derived.WalkFunctionalIntegral
import MatedCRT.FirstPass.Derived.InterpWalkLawVertexBound
import MatedCRT.FirstPass.S5c.ValidCellFacts
import MatedCRT.FirstPass.S3t.CellGeometry

/-!
# The quenched walk integral and the interpolated-law integral agree in probability

Berestycki–Gwynne (2020), Thm. 1.2, Step 1: for a bounded Lipschitz path functional `F` and a point `z`,
`R^ε = ∫ F(interpolatedWalk ε η (m^ε)) d srwLaw(a^ε_z)` (the quenched walk from the vertex `a^ε_z` of `z`) differs from
`R'^ε = ∫ F d P̃^ε_z` (the integral against the interpolated law at `z`) by a quantity that tends to `0` in probability
along every sequence `ε_n → 0⁺`.

* `abs_walkIntegral_sub_interpIntegral_le`: the deterministic bound on the good event (cells of diameter `≤ d`,
  vertex-indexed walk-law modulus `≤ a / 2`, interpolation weights locally finite and positive, `z` in the cell of its
  vertex).  It combines `integral_interpolatedWalk_eq_integral_walkPathLaw`,
  `pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell` and the comparison hypothesis `hcomp`
  (integrals of the bounded continuous functional against laws at small Lévy–Prokhorov distance).
* `tendsto_prob_abs_walkIntegral_sub_interpIntegral`: the probabilistic statement, from the equicontinuity in law of the
  vertex laws (`hEq`) and the convergence in probability of the maximal cell diameter.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- Two positive real numbers whose `ENNReal` sum is at most a given positive extended number. -/
theorem exists_ofReal_add_le {θ' : ℝ≥0∞} (h : 0 < θ') :
    ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ + ENNReal.ofReal θ ≤ θ' := by
  by_cases htop : θ' = ⊤
  · exact ⟨1, one_pos, by simp [htop]⟩
  · refine ⟨θ'.toReal / 2, half_pos (ENNReal.toReal_pos h.ne' htop), ?_⟩
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, ENNReal.ofReal_toReal htop]

/-- Almost surely every point lies in the cell of its smallest vertex, for every mesh. -/
theorem ae_mem_cell_vertexOf {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ x : ℂ, x ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) x) := by
  have hfirst : ∀ᵐ ω ∂S.P, ∀ x : ℂ, BddBelow {s : ℝ | S.η ω s = x} :=
    hS.ae_tendsto_cocompact.mono fun ω hp x => MatedCRT.TruncatedLaws.cellGeom_bddBelow_preimage hp x
  exact (MatedCRT.S5c.ae_cell_facts hS hfirst).mono fun ω h => h.1

/-- **The deterministic bound for `R^ε - R'^ε`.** On the event where the interpolation weights are locally finite and
positive, `η' ω = η ω`, every cell meeting `B_{R+1}` has diameter at most `d`, the vertex-indexed modulus of the quenched
walk laws at scale `δ ≥ 2 d + ε` is at most `a / 2`, and `z ∈ B̄_R` lies in the cell of its smallest vertex, the walk
integral from that vertex and the integral against the interpolated law at `z` differ by at most `η`, provided
integrals of the functional against laws at Lévy–Prokhorov distance below `a` differ by at most `η` (`hcomp`). -/
theorem abs_walkIntegral_sub_interpIntegral_le {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) {ω : Ω} (hηω : ⇑(η' ω) = S.η ω)
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    {R δ d a η : ℝ} (hd0 : 0 ≤ d) (hδ : 2 * d + ε ≤ δ) (h1 : ε + d < 1) (ha : 0 < a)
    (hD : maxCellDiam ε (⇑(η' ω)) R ≤ ENNReal.ofReal d)
    (hmod : walkLawModulus S η' ε R δ ω ≤ ENNReal.ofReal (a / 2))
    (hcomp : ∀ μ ν : ProbabilityMeasure (ContinuousPath ℂ), pathLevyProkhorovEDist μ ν < ENNReal.ofReal a →
      |∫ q, blPathFunctionalBCF hF q ∂(μ : Measure (ContinuousPath ℂ)) -
        ∫ q, blPathFunctionalBCF hF q ∂(ν : Measure (ContinuousPath ℂ))| ≤ η)
    {z : ℂ} (hz : ‖z‖ ≤ R) (hzc : z ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) z)) :
    |(∫ x, F (interpolatedWalk ε (S.η ω) (S.mε ε) x) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)) -
      ∫ q, blPathFunctionalBCF hF q ∂(interpWalkLaw S η' ε ω z : Measure (ContinuousPath ℂ))| ≤ η := by
  have hv : (fun ω => vertexPoint ε (⇑(η' ω))) ω = vertexPoint ε (S.η ω) := by
    show vertexPoint ε (⇑(η' ω)) = _
    rw [hηω]
  rw [integral_interpolatedWalk_eq_integral_walkPathLaw hF S ε ω (S.η ω) (fun ω => vertexPoint ε (⇑(η' ω))) hv]
  have hzj : z ∈ cell ε (⇑(η' ω)) (vertexOf ε (S.η ω) z) := by
    rw [hηω]
    exact hzc
  have hLP := pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell S η' hε hloc hpos hd0 hδ h1
    (by positivity) hD hmod hz hzj
  exact hcomp _ _ (lt_of_le_of_lt hLP ((ENNReal.ofReal_lt_ofReal_iff ha).2 (by linarith)))

/-- **`R^{ε_n} - R'^{ε_n} → 0` in probability.** Along `ε_n → 0⁺`, given the equicontinuity in law of the vertex laws
(`hEq`, the output of the cone scaling step) and the comparison hypothesis `hcomp` for the bounded Lipschitz
functional, `P[|R^{ε_n} - R'^{ε_n}| > δ] → 0` for every `δ > 0`. -/
theorem tendsto_prob_abs_walkIntegral_sub_interpIntegral {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0))
    (hEq : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a)
    {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    (hcomp : ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧
      ∀ μ ν : ProbabilityMeasure (ContinuousPath ℂ), pathLevyProkhorovEDist μ ν < ENNReal.ofReal a →
        |∫ q, blPathFunctionalBCF hF q ∂(μ : Measure (ContinuousPath ℂ)) -
          ∫ q, blPathFunctionalBCF hF q ∂(ν : Measure (ContinuousPath ℂ))| ≤ η)
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => S.P {ω | δ <
      |(∫ x, F (interpolatedWalk (eps n) (S.η ω) (S.mε (eps n)) x) ∂srwLaw (S.mult (eps n) ω)
          (vertexOf (eps n) (S.η ω) z)) -
        ∫ q, blPathFunctionalBCF hF q ∂(interpWalkLaw S η' (eps n) ω z : Measure (ContinuousPath ℂ))|})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro θ' hθ'
  obtain ⟨θ, hθ, hθsum⟩ := exists_ofReal_add_le hθ'
  obtain ⟨a, ha, hcδ⟩ := hcomp δ hδ
  have ha2 : 0 < min (a / 2) θ := lt_min (half_pos ha) hθ
  obtain ⟨δ0, hδ0, hev0⟩ := hEq ‖z‖ (min (a / 2) θ) ha2
  obtain ⟨δ1, hδ1def⟩ : ∃ δ1 : ℝ, δ1 = min δ0 1 := ⟨_, rfl⟩
  have hδ1 : 0 < δ1 := by rw [hδ1def]; exact lt_min hδ0 one_pos
  have hδ10 : δ1 ≤ δ0 := by rw [hδ1def]; exact min_le_left _ _
  have hδ11 : δ1 ≤ 1 := by rw [hδ1def]; exact min_le_right _ _
  have hεn : Tendsto eps atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have hdiam := (MatedCRT.CellDiameterEvent.tendsto_prob_maxCellDiam_nhdsWithin hS hae ‖z‖ (δ1 / 8)
    (by positivity)).comp hεn
  have hev1 : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal (δ1 / 8) < maxCellDiam (eps n) (⇑(η' ω)) ‖z‖} <
      ENNReal.ofReal θ := hdiam.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))
  have hev2 : ∀ᶠ n in atTop, eps n < δ1 / 8 := hε.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev0, hev1, hev2] with n h0 h1 h2
  have hgood := hS.ae_interpWeight_good hae (hε0 n)
  have hcell := ae_mem_cell_vertexOf hS
  refine (measure_mono_ae ?_).trans ((measure_union_le _ _).trans
    ((add_le_add h0 h1.le).trans ?_))
  · filter_upwards [hae, hgood, hcell] with ω hω hg hcl hbad
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨hmod, hD⟩ := hcon
    have hmod' : walkLawModulus S η' (eps n) ‖z‖ δ1 ω ≤ ENNReal.ofReal (a / 2) :=
      ((walkLawModulus_mono S η' (eps n) ‖z‖ hδ10 ω).trans hmod).trans
        (ENNReal.ofReal_le_ofReal ((min_le_left _ _)))
    have hdet := abs_walkIntegral_sub_interpIntegral_le hF S η' (hε0 n) hω hg.1 hg.2
      (R := ‖z‖) (δ := δ1) (d := δ1 / 8) (a := a) (η := δ) (by positivity) (by linarith) (by linarith) ha
      hD hmod' hcδ le_rfl (hcl (eps n) (hε0 n) z)
    exact absurd hbad (not_lt.2 hdet)
  · calc ENNReal.ofReal (min (a / 2) θ) + ENNReal.ofReal θ
        ≤ ENNReal.ofReal θ + ENNReal.ofReal θ :=
          add_le_add (ENNReal.ofReal_le_ofReal (min_le_right _ _)) le_rfl
      _ ≤ θ' := hθsum

end MatedCRT.FirstPass.Derived
