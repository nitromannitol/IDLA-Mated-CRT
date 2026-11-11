import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S5k.Assembly
import MatedCRT.FirstPass.Frozen.S4S6c

/-!
# First pass: measurable version of the continuum floor obstacle

`StoppedFloorObstacleVersion 𝒮` is the conclusion of the floor argument: a measurable version `Ŵ` of the continuum least supersolution `W_t = leastSupersolution (S.μ ω) ρ 0 t` of
the obstacle problem, on the event `{t < clusterExitTime (Λ ω) ρ}`, with every evaluation `ω ↦ Ŵ ω x` measurable for the
field σ-algebra `S.fieldSigma`, continuous on the closed disk `B̄_ρ`, and vanishing on its boundary for every `ω`.

The binders are those of `StoppedFloorCellStep` (S5d/FloorCellStep.lean:25) up to `t`; the parameter `δ` is not used by §4
and is omitted. The first commit contains only the definition; the theorem `stoppedFloorObstacleVersion_proved` is not
yet proved and is not in this file.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- **Measurable version of the continuum floor obstacle**.
For `γ ∈ (0,2)`, `ρ ∈ (0,1)`, a valid mated-CRT environment `S` on `Ω`, a family `Λ` of cone harmonic balls a.s. and
`t > 0`, there is `Ŵ : Ω → ℂ → ℝ` such that: each evaluation `ω ↦ Ŵ ω x` is `S.fieldSigma`-measurable; for every `ω`, the map
`Ŵ ω` is continuous on `B̄_ρ` and vanishes on `∂B_ρ`; and for `P`-a.e. `ω` on the event `{t < clusterExitTime (Λ ω) ρ}`,
`Ŵ ω` agrees on `B̄_ρ` with the continuum least supersolution `W_t = leastSupersolution (S.μ ω) ρ 0 t`
(`HarmonicBalls.leastSupersolution`, the obstacle `-t G_{B_ρ}(0,·)`, Harmonic-Balls-LQG `HarmonicBalls/Defs/Obstacle.lean:63`).

The measurability is with respect to `S.fieldSigma`, not the ambient σ-algebra; no measurability of the raw expression
`leastSupersolution (S.μ ω) …` is asserted. Source: Part I, Step 4.2 and (7). -/
def StoppedFloorObstacleVersion (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
    ∃ What : Ω → ℂ → ℝ,
      (∀ x : ℂ, Measurable[S.fieldSigma] fun ω => What ω x) ∧
      (∀ ω, ContinuousOn (What ω) (closedBall (0 : ℂ) ρ)) ∧
      (∀ ω, ∀ x ∈ sphere (0 : ℂ) ρ, What ω x = 0) ∧
      (∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        ∀ x ∈ closedBall (0 : ℂ) ρ,
          What ω x = _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x)

open MeasureTheory Metric Set Filter Topology HarmonicBalls in
/-- **Measurable version of the continuum floor obstacle.** The measurable version `Ŵ` is the Lusin-Souslin decoder of the
Borel graph of (6) (`Graph/Main.lean`) applied to the zero-replaced restriction of `μ` to `B̄_ρ`
(`Assembly.lean`); it equals the continuum least supersolution `W_t` on `B̄_ρ` for almost every `ω` on
`{t < clusterExitTime (Λ ω) ρ}`. The hypotheses are the frozen external inputs: the measurability of the LQG measure
(`hμae`), the standard Borel structure of the finite measures on a closed disk (`hSB`), the supersolution membership of
the least supersolution (`hsup`, HB Lemma 3.1), and the disc Green function (`hG`). -/
theorem stoppedFloorObstacleVersion_proved (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮) (hG : FrozenGreenDiscPole) :
    StoppedFloorObstacleVersion 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS Λ hΛ t ht
  obtain ⟨g, hgm, hgae⟩ := hμae γ hγ0 hγ2 Ω S hS
  obtain ⟨F, hFm, hF1, hF0⟩ := exists_decoder_disk (ρ := ρ) (t := t) hSB hG hρ0 ht
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) :=
    hS.isLQGMeasure.mono fun ω h => h.isLocallyFiniteMeasure
  have hsupω := hsup γ hγ0 hγ2 Ω S hS
  refine ⟨fun ω x => extDisk ρ (F (diskMeasOf ρ (g ω))) x, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (measurable_extDisk_eval x).comp (hFm.comp ((measurable_diskMeasOf ρ).comp hgm))
  · intro ω
    exact continuousOn_extDisk _
  · intro ω x hx
    show extDisk ρ (F (diskMeasOf ρ (g ω))) x = 0
    by_cases hex : ∃ f : DiskFun ρ,
        IsObstacleSolutionOn ρ t ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ) (extDisk ρ f)
    · exact (hF1 _ hex).zero_on_sphere x hx
    · rw [hF0 _ hex, extDisk_apply_of_mem _ (sphere_subset_closedBall hx)]
      rfl
  · filter_upwards [hgae, hΛ, hloc, hsupω] with ω hωg hωΛ hωloc hωsup
    intro hexit x hx
    show extDisk ρ (F (diskMeasOf ρ (g ω))) x = leastSupersolution (S.μ ω) ρ 0 t x
    have hsupW := hωsup ρ hρ0 hρ1 t ht
    have hId := isObstacleSolutionOn_leastSupersolution hG hωΛ hρ0 ht hsupW hexit
    have hmeas : ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ) =
        (S.μ ω).restrict (closedBall (0 : ℂ) ρ) := by
      rw [← hωg]
      exact restrictOrZero_eq_restrict hωloc
    have hId' : IsObstacleSolutionOn ρ t ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ)
        (leastSupersolution (S.μ ω) ρ 0 t) := by
      rw [hmeas]
      exact hId
    let fW : DiskFun ρ := ⟨(closedBall (0 : ℂ) ρ).domRestrict (leastSupersolution (S.μ ω) ρ 0 t),
      continuousOn_iff_continuous_domRestrict.1 hId'.continuousOn⟩
    have hcong : IsObstacleSolutionOn ρ t ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ) (extDisk ρ fW) :=
      hId'.congr_closedBall hG hρ0 ht (fun y hy => by rw [extDisk_apply_of_mem _ hy]; rfl)
    have hex : ∃ f : DiskFun ρ,
        IsObstacleSolutionOn ρ t ((diskMeasOf ρ (g ω) : FinMeasDisk ρ) : Measure ℂ) (extDisk ρ f) := ⟨fW, hcong⟩
    exact (hF1 _ hex).eqOn_closedBall hId' hx

end MatedCRT
