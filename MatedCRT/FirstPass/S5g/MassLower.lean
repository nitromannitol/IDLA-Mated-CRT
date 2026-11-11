import MatedCRT.FirstPass.S5e.SecondGreenStep
import MatedCRT.FirstPass.S5g
import MatedCRT.FirstPass.S5c.EnvInputs
import MatedCRT.FirstPass.S4S6c.EnvInputs68
import MatedCRT.Proofs.Sec5.LLowerBound.Mass

/-!
# Uniform positive mass lower bound for the second Green inequality (Proposition 5.1, correction [C21])

Written source: `paper/idla_mated_crt-corrected.tex`, proof of Proposition 5.1, lines 2368-2372 (`% CORRECTION [C21]`):
"The full support of `μ_h` and a finite cover of the possible centers give a uniform positive random lower bound for the
masses of these smaller balls." Referee check: `notes/fp-gaps/CHATGPT-idla-C20-C21-referee.md`, lines 252-300.

`stoppedMassLower_proved` proves the probabilistic input `StoppedMassLowerStep` (FirstPass/S5e/SecondGreenStep.lean:43),
which `stoppedSecondGreenStep_of_inputs` consumes. It takes no hypothesis beyond the statement: every valid environment
`S : MatedCRTEnv Ω` supplies the area parametrization of `S.μ` and the field-measurable version of `S.μ`.

Route (the same finite-net argument as `stoppedTargetMass_tendsToOne`, FirstPass/S5g.lean, without the cell-size event):
* A finite net `Z` of mesh `s/2` covers the closed ball `closedBall 0 ρ` (`finite_cover_balls_of_compact`).
* For `z ∈ closedBall 0 ρ` some net point `z'` has `dist z z' < s/2`, so `ball z' (s/2) ⊆ ball z s`.
* `mr := min_{z' ∈ Z} massFloor (g (ball z' (s/2)))`, where `g` is a field-measurable version of `S.μ`
  (`EnvInputs68.exists_fieldMeasurable_mu`). Then `mr` is `fieldSigma`-measurable, hence measurable for the ambient
  σ-algebra (`S5c.env_fieldSigma_le`), and `0 < mr` everywhere (`netMassFloor_pos`).
* The masses `S.μ ω (ball z' (s/2))` are positive almost surely, because `η` is area-parametrized, so `S.μ ω` has full
  support (`open_pos_of_area_parametrized`). Hence `ofReal (mr ω) ≤ ofReal (massFloor (g ω (ball z' (s/2)))) ≤ S.μ ω (ball z' (s/2))
  ≤ S.μ ω (ball z s)`.

Terminology: LQG measure and mass (Duplantier-Sheffield), full support of a measure parametrized by a continuous surjection
(Armstrong-Kuusi-Mourrat, mass lower bounds); potential-theoretic balls and Green kernel as in Armitage-Gardiner.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT

open StoppedTargetMass

/-- **Uniform positive mass lower bound (correction [C21]).** For every valid environment and every `s > 0`, there is a
measurable random level `mr > 0` such that, almost surely, `μ_h(B_s(z)) ≥ mr` for every centre `z ∈ B̄_ρ`. This proves the
probabilistic input `MatedCRT.S5e.StoppedMassLowerStep 𝒮` with no hypothesis. -/
theorem stoppedMassLower_proved (𝒮 : SpaceFillingSLEModel) : S5e.StoppedMassLowerStep 𝒮 := by
  classical
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω mΩ S hS s hs
  -- a field-measurable version `g` of the LQG measure, equal to `S.μ` almost surely
  obtain ⟨g, hg, hgμ⟩ := EnvInputs68.exists_fieldMeasurable_mu hγ0 hγ2 S hS
  -- a finite net `Z` of mesh `s/2` covering the closed ball of radius `ρ`
  obtain ⟨T, -, hTfin, hTcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) ρ) (half_pos hs)
  obtain ⟨Z, rfl⟩ : ∃ Z : Finset ℂ, (Z : Set ℂ) = T := ⟨hTfin.toFinset, hTfin.coe_toFinset⟩
  have hcov : ∀ y ∈ closedBall (0 : ℂ) ρ, ∃ z ∈ Z, dist y z < s / 2 := by
    intro y hy
    obtain ⟨z, hzZ, hyz⟩ := mem_iUnion₂.1 (hTcov hy)
    exact ⟨z, Finset.mem_coe.1 hzZ, mem_ball.1 hyz⟩
  have hZne : Z.Nonempty := by
    obtain ⟨z, hz, -⟩ := hcov 0 (mem_closedBall_self hρ0.le)
    exact ⟨z, hz⟩
  -- the random level is field-measurable, hence measurable for the ambient σ-algebra
  have hball : ∀ z : ℂ, Measurable[S.fieldSigma] fun ω => g ω (ball z (s / 2)) :=
    fun z => (Measure.measurable_coe measurableSet_ball).comp hg
  have hmr_fs : Measurable[S.fieldSigma] (netMassFloor g hZne (s / 2)) :=
    measurable_finset_inf'_real (fun z ω => massFloor (g ω (ball z (s / 2))))
      (fun z => measurable_massFloor.comp (hball z)) Z hZne
  have hmr : Measurable (netMassFloor g hZne (s / 2)) :=
    hmr_fs.mono (S5c.env_fieldSigma_le S hS) le_rfl
  refine ⟨netMassFloor g hZne (s / 2), hmr, Eventually.of_forall fun ω => netMassFloor_pos g hZne (s / 2) ω, ?_⟩
  -- almost surely: area parametrization and the identification `S.μ = g`
  have hgood : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧ S.μ ω = g ω := by
    filter_upwards [hS.isAreaParametrized, hgμ] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hgood] with ω hω
  obtain ⟨hAP, hμg⟩ := hω
  have := open_pos_of_area_parametrized hAP
  intro z hz
  obtain ⟨z', hz'Z, hzd⟩ := hcov z hz
  have hsmall : ball z' (s / 2) ⊆ ball z s := by
    intro y hy
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y z' z, dist_comm z' z]
  have hpos : g ω (ball z' (s / 2)) ≠ 0 := by
    rw [← hμg]
    exact (measure_ball_pos (S.μ ω) z' (half_pos hs)).ne'
  calc ENNReal.ofReal (netMassFloor g hZne (s / 2) ω)
      ≤ ENNReal.ofReal (massFloor (g ω (ball z' (s / 2)))) :=
        ENNReal.ofReal_le_ofReal (netMassFloor_le g hZne (s / 2) ω hz'Z)
    _ ≤ g ω (ball z' (s / 2)) := ofReal_massFloor_le hpos
    _ = S.μ ω (ball z' (s / 2)) := by rw [hμg]
    _ ≤ S.μ ω (ball z s) := measure_mono hsmall

end MatedCRT
