import MatedCRT.FirstPass.Derived.GMS21LocalCellConfiguration
import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusForm
import MatedCRT.FirstPass.Derived.BlockExitWalkUnbounded
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MatedLeastMeasurable
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec4.ObstacleSpecialization
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen

/-!
# From the zero cone to the `γ`-quantum cone on annuli (proof of Theorem 3.4, case 1)

Gwynne–Miller–Sheffield (arXiv:1705.11161), proof of Theorem 3.4, case 1: by Lemma 3.5 and local absolute continuity
(Lemma 3.3), with probability tending to `1` the embedded walk on the mated-CRT map of the `γ`-quantum cone is close to
Brownian motion when both are stopped at their exits from an annulus `B_R(0) \ closedBall 0 α` avoiding the origin,
for all starts in `closedBall 0 ρ \ B_b(0)`. The passage to balls (`GMS21BallOfAnnulus`,
`GMS21UniformStartOfVertexAnnulus`) then gives the uniform-start invariance principle `hTutteLP`.

For a valid environment, almost surely the vertices whose points lie in a bounded set and their neighbours are finitely
many at every positive mesh (`ae_localVertices_finite`: the curve is proper and the multigraph is locally finite), so
`tendsto_map_vertexAnnulusLPData_compl_of_localConfig` applies.

## Main results

* `vertexAnnulus_of_localConfig`: the comparison at the vertices on annuli for the `γ`-quantum cone from the same
  comparison for a second configuration (the shifted zero cone) and Lemma 3.3 for the two local configurations.
* `tendsto_uniformStartSelectedLPData_of_localConfig`: the premise `hTutteLP` from the same inputs.
* `tendsto_uniformStartSelectedLPData_of_zeroConeAnnulusLPForm`: the premise `hTutteLP` from the form on annuli of
  Lemma 3.5 for the shifted zero-cone configuration (`ZeroConeAnnulusLPForm`) and Lemma 3.3.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-- For a valid environment and a measurable version of its curve, almost surely the vertices at mesh `ε > 0` whose
points lie in a bounded set `V` and their neighbours are finitely many: the curve is proper and the multigraph is
locally finite. -/
theorem ae_localVertices_finite {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η₀ : Ω → C(ℝ, ℂ)} (hη₀ : ∀ᵐ ω ∂S.P, ⇑(η₀ ω) = S.η ω) {ε : ℝ} (hε : 0 < ε) {V : Set ℂ} {R : ℝ}
    (hV : V ⊆ closedBall (0 : ℂ) R) :
    ∀ᵐ ω ∂S.P, (localVertices V (vertexData ε (η₀ ω, S.mult ε ω))).Finite := by
  filter_upwards [hη₀, etaProperStep_holds 𝒮 γ hγ hγ2 Ω S hS,
    ae_locallyFinite_mult_of_adjacentCells hS hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hω hp hloc
  have hp' : Tendsto (⇑(η₀ ω)) (cocompact ℝ) (cocompact ℂ) := by rw [hω]; exact hp
  have hA : {x : ℤ | vertexPoint ε (η₀ ω) x ∈ V}.Finite :=
    (BlockExit.vertexPoint_preimage_closedBall_finite hε (η₀ ω).continuous hp' R).subset fun x hx => hV hx
  have hB : (⋃ x ∈ {x : ℤ | vertexPoint ε (η₀ ω) x ∈ V}, {y : ℤ | S.mult ε ω x y ≠ 0}).Finite :=
    hA.biUnion fun x _ => hloc ε hε x
  refine (hA.union hB).subset ?_
  rintro y (hy | ⟨x, hx, hxy⟩)
  · exact Or.inl hy
  · exact Or.inr (Set.mem_biUnion hx hxy)

/-- **The comparison on annuli for the `γ`-quantum cone by Lemma 3.3** (Gwynne–Miller–Sheffield, arXiv:1705.11161,
proof of Theorem 3.4, case 1). Let `S` be a valid environment for `0 < γ < 2` with a measurable version `η₀` of its
curve, and let `X' n` be embedded data at mesh `1/n` on a probability space `(Ω', P')` (the shifted zero cone). If the
laws of the local configurations near annuli of the data of `S` and of `X'` are uniformly mutually absolutely
continuous (Lemma 3.3) and the comparison at the vertices on annuli holds for `X'` with probability tending to `1`, then
it holds for `S`. -/
theorem vertexAnnulus_of_localConfig {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η₀ : Ω → C(ℝ, ℂ)} (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ω ∂S.P, ⇑(η₀ ω) = S.η ω)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : ℕ → Ω' → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (hX' : ∀ n, AEMeasurable (X' n) P')
    (h33 : LocalConfigUniformlyMutuallyAbsolutelyContinuous S.P
      (fun n ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) P' X')
    (h0 : ∀ α b ρ R c : ℝ, 0 < α → α < b → b < ρ → ρ < R → 0 < c → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        P'.map (X' n) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ α b ρ R c : ℝ, 0 < α → α < b → b < ρ → ρ < R → 0 < c → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ := by
  intro α b ρ R c hα hαb hbρ hρR hc θ hθ
  have hP := hS.isProbabilityMeasure
  have hX : ∀ n : ℕ, AEMeasurable (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) S.P := fun n =>
    (hη₀m.prodMk (hS.measurable_mult_array _)).aemeasurable
  have hfin : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂S.P, (localVertices (ball (0 : ℂ) R \ closedBall (0 : ℂ) α)
      (vertexData (1 / (n : ℝ)) (η₀ ω, S.mult (1 / (n : ℝ)) ω))).Finite := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hε : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.2 (by exact_mod_cast hn)
    exact ae_localVertices_finite hγ hγ2 hS hη₀ hε (R := R) fun z hz => ball_subset_closedBall hz.1
  have h2 : Tendsto (fun n : ℕ => P'.map (X' n) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ)
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεt
    · exact Eventually.of_forall fun _ => le_top
    · obtain ⟨N, hN⟩ := h0 α b ρ R c hα hαb hbρ hρR hc ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hN n hn).trans (ENNReal.ofReal_toReal hεt).le
  have h1 := tendsto_map_vertexAnnulusLPData_compl_of_localConfig
    (X₁ := fun n ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) hX hX' hαb hρR hfin
    (h33 α R hα (by linarith)).2 h2
  exact eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 h1) (ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ))

/-- **The uniform-start invariance principle for the `γ`-quantum cone by Lemma 3.3** (Gwynne–Miller–Sheffield,
arXiv:1705.11161, proof of Theorem 3.4, case 1): the premise `hTutteLP` at `S` and `η₀` from the comparison on annuli
for a second configuration and Lemma 3.3 for the two local configurations. -/
theorem tendsto_uniformStartSelectedLPData_of_localConfig {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η₀ : Ω → C(ℝ, ℂ)} (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ω ∂S.P, ⇑(η₀ ω) = S.η ω)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : ℕ → Ω' → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} (hX' : ∀ n, AEMeasurable (X' n) P')
    (h33 : LocalConfigUniformlyMutuallyAbsolutelyContinuous S.P
      (fun n ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) P' X')
    (h0 : ∀ α b ρ R c : ℝ, 0 < α → α < b → b < ρ → ρ < R → 0 < c → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        P'.map (X' n) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ :=
  tendsto_uniformStartSelectedLPData_of_vertexAnnulus hγ hγ2 hS hη₀m hη₀
    (vertexAnnulus_of_localConfig hγ hγ2 hS hη₀m hη₀ hX' h33 h0)

section ZeroCone

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

/-- The shifted zero-cone data at mesh `1/n` at `(ω, θ)`: the curve `t ↦ η₀(t + θ/n)` and the contour edge counts at
mesh `1/n` of `t ↦ G(t + θ/n)`. -/
noncomputable def zeroConeShiftedData {Ω : Type} (η₀ : Ω → C(ℝ, ℂ)) (G : Ω → Path2) (n : ℕ) (p : Ω × ℝ) :
    C(ℝ, ℂ) × (ℤ → ℤ → ℕ) :=
  (phaseShiftedCurve (1 / (n : ℝ)) p.2 (η₀ p.1), phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1))

theorem measurable_zeroConeShiftedData {Ω : Type} [MeasurableSpace Ω] {η₀ : Ω → C(ℝ, ℂ)} {G : Ω → Path2}
    (hη : Measurable η₀) (hG : Measurable G) (n : ℕ) : Measurable (zeroConeShiftedData η₀ G n) := by
  have hev : Measurable fun q : C(ℝ, ℂ) × ℝ => q.1 q.2 := continuous_eval.measurable
  have hevG : Measurable fun q : Path2 × ℝ => q.1 q.2 := continuous_eval.measurable
  have hsh : ∀ t : ℝ, Measurable fun p : Ω × ℝ => t + 1 / (n : ℝ) * p.2 := fun t =>
    measurable_const.add (measurable_const.mul measurable_snd)
  have hc : Measurable fun p : Ω × ℝ => phaseShiftedCurve (1 / (n : ℝ)) p.2 (η₀ p.1) := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    show Measurable ((fun q : C(ℝ, ℂ) × ℝ => q.1 q.2) ∘
      fun p : Ω × ℝ => (η₀ p.1, t + 1 / (n : ℝ) * p.2))
    exact hev.comp ((hη.comp measurable_fst).prodMk (hsh t))
  let sG : Ω × ℝ → Path2 := fun p =>
    (G p.1).comp ⟨fun t => t + 1 / (n : ℝ) * p.2, continuous_id.add continuous_const⟩
  have hs : Measurable sG := by
    refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    show Measurable ((fun q : Path2 × ℝ => q.1 q.2) ∘
      fun p : Ω × ℝ => (G p.1, t + 1 / (n : ℝ) * p.2))
    exact hevG.comp ((hG.comp measurable_fst).prodMk (hsh t))
  have he : Measurable fun p : Ω × ℝ => phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1) := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    show Measurable ((fun w : Path2 =>
      bmEdgeCount (1 / (n : ℝ)) (fun t => (w t).1) (fun t => (w t).2) j k) ∘ sG)
    exact (measurable_bmEdgeCount_path (1 / (n : ℝ)) j k).comp hs
  unfold zeroConeShiftedData
  exact hc.prodMk he

/-- **The uniform-start invariance principle for the `γ`-quantum cone from the zero cone** (Gwynne–Miller–Sheffield,
arXiv:1705.11161, proof of Theorem 3.4, case 1). Let `S` be a valid environment for `0 < γ < 2` with a measurable
version `ηS` of its curve, and let `D` be a mating-of-trees coupling with zero-cone curve `η₀` and a measurable version
`G` of the boundary-length pair of `η₀`. Given the form on annuli of Lemma 3.5 for the shifted zero-cone configuration
(`ZeroConeAnnulusLPForm`) and Lemma 3.3 for the local configurations of `S` and of the shifted zero cone under
`P ⊗ Unif[0, 1]`, the premise `hTutteLP` holds at `S` and `ηS`. -/
theorem tendsto_uniformStartSelectedLPData_of_zeroConeAnnulusLPForm {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ωγ : Type} [MeasurableSpace Ωγ] {S : MatedCRTEnv Ωγ}
    (hS : S.IsValid 𝒮 γ) {ηS : Ωγ → C(ℝ, ℂ)} (hηSm : Measurable ηS) (hηS : ∀ᵐ ω ∂S.P, ⇑(ηS ω) = S.η ω)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγI : γ ∈ Ioo (0 : ℝ) 2)
    {G : Ω → Path2} (hG : IsZeroConeBoundaryPair D hγI G) (hZ : ZeroConeAnnulusLPForm D hγI)
    (h33 : LocalConfigUniformlyMutuallyAbsolutelyContinuous S.P
      (fun n ω => (ηS ω, S.mult (1 / (n : ℝ)) ω)) (P.prod zeroConePhase) (zeroConeShiftedData η₀ G)) :
    ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (ηS ω, S.mult (1 / (n : ℝ)) ω))
          (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  refine tendsto_uniformStartSelectedLPData_of_localConfig hγ hγ2 hS hηSm hηS
    (fun n => (measurable_zeroConeShiftedData D.measurable_curves.2.2.1 hG.1 n).aemeasurable) h33 ?_
  intro α b ρ R c hα hαb hbρ hρR hc θ hθ
  obtain ⟨N, hN⟩ := hZ G hG α b ρ R c hα hαb hbρ hρR hc θ hθ
  refine ⟨max N 1, fun n hn => le_trans (measure_mono ?_) (hN n (le_of_max_le_left hn))⟩
  have hε : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.2 (by exact_mod_cast le_of_max_le_right hn)
  exact compl_subset_compl.2 (annulusSelectedLPData_subset_vertexAnnulusLPData hε α b ρ R c)

end ZeroCone

end MatedCRT
