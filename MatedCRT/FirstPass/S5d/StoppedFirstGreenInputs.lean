import MatedCRT.FirstPass.S5d.StoppedSteps
import MatedCRT.FirstPass.S5d.GreenEvent
import MatedCRT.FirstPass.S5d.SurplusIdentity
import MatedCRT.FirstPass.S5d.CoverEvent
import MatedCRT.FirstPass.S5d.ClusterFromOdometer

/-!
# The first Green inequality of the stopped clause from its surplus inputs (task fp-S5d-5-1-stopped-repair)

Reduces `StoppedFirstGreenStep` (StoppedSteps.lean:63) to one NEW probabilistic input, `StoppedFirstGreenInputsStep`:
random constants `c, C > 0` such that, with probability tending to one on `{t < T}`,
* (floor) `c/ε ≤ u^ε(a)` for every target `a ∈ Z^ε_t` (`stoppedTargetSet`);
* (ceiling) `u^ε(b) ≤ c/(2ε)` for every `b` outside the killing set `I^ε_t` (`stoppedKillSet`);
* (exit) `∑_{b∈I} G_I(b,a) ≤ C/ε` (the Green expectation of the exit time) for every target `a`.

The floor is the strict-gap argument of [C21] (CORRECTIONS.md; corrected tex 2350-2395, "u^ε ≥ c ε⁻¹ for every cell meeting
B⁻_{δ/2}(Λ_t)"), the pole value at `0` being an extra claim (`0 ∈ O₁` is required by Lemma 5.2, Draft/Section5.lean:40).
The ceiling is NOT written in [C21]: the comparison there uses `M_ε = sup_{a∉I} u^ε(a)` without a bound `M_ε ≤ c/(2ε)`.

The deterministic part is complete: `firstGreen_of_floor_ceiling_exit` (below) is `firstGreen_pathwise` (GreenEvent.lean:78)
with the Finset sums turned into `tsum`s by `firstGreen_relaxed` (GreenEvent.lean:49); the surplus identity is
`mLaplacian_stoppedOdometer_on_cluster` (SurplusIdentity.lean:23).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Pathwise first Green inequality of the stopped clause (referee 5.2, (5.4)-(5.5)).** Given the surplus floor `c/ε` on the
targets, the ceiling `c/(2ε)` off the killing set `I`, and the exit bound `C/ε`, the first Green inequality of Lemma 5.2 holds
on the targets with the factor `1 + c/(2C)`. -/
theorem firstGreen_of_floor_ceiling_exit {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {I Z : Set ℤ} (hI : I.Finite)
    {ε t c C : ℝ} {v : ℤ → ℝ} (hε : 0 < ε) (hC : 0 < C) (hc : 0 ≤ c)
    (hv : ∀ a ∈ I, mLaplacian m v a = (mdeg m a : ℝ)⁻¹ - t / ε * (if a = 0 then (mdeg m 0 : ℝ)⁻¹ else 0))
    (hZI : Z ⊆ I) (hvM : ∀ b ∉ I, v b ≤ c / (2 * ε)) (hlow : ∀ a ∈ Z, c / ε ≤ v a)
    (hq : ∀ a ∈ Z, ∑' b : I, greenKernel m I a b ≤ C / ε) :
    ∀ a ∈ Z, (1 + c / (2 * C)) * ∑' b : I, greenFn m I b a ≤ t / ε * greenFn m I 0 a := by
  intro a ha
  have hq' : ∀ a ∈ Z, ∑ b ∈ hI.toFinset, greenKernel m I a b ≤ C / ε := by
    intro a ha
    have e := tsum_subtype_eq_sum_finite hI (greenKernel m I a)
    have h := hq a ha
    rw [e] at h
    exact h
  have h1 := firstGreen_pathwise hlf hcons hI hε hC hc hv hvM le_rfl hZI hlow hq'
  exact firstGreen_relaxed hsymm hlf hcons hI (h1 a ha)

/-- The deterministic inputs of the stopped clause at one scale `ε` and one outcome `ω`: symmetry, local finiteness and
connectedness of the edge multiplicities, finiteness of `B_ρ` (both the cells and the interior), harmonicity of the
least supersolution on the discrete cluster (the obstacle identity, used through `mLaplacian_stoppedOdometer_on_cluster`),
finiteness of the killing set, and `0 ∈ V^ε(Λ_t)` (the origin is killed). -/
def StoppedPathwiseInputs {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t ε : ℝ)
    (ω : Ω) : Prop :=
  (∀ a b, S.mult ε ω a b = S.mult ε ω b a) ∧ IsLocallyFiniteMult (S.mult ε ω) ∧
  (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧ (ballInterior ε (S.η ω) ρ).Finite ∧
  (cellVertices ε (S.η ω) (ball 0 ρ)).Finite ∧
  (∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      mLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a = (mdeg (S.mult ε ω) a : ℝ)⁻¹) ∧
  (0 : ℤ) ∈ cellVertices ε (S.η ω) (Λ ω t)

/-- **NEW, OPEN (probabilistic input; [C21] of CORRECTIONS.md, referee 5.1-5.2 (5.1), (5.2), (5.4), (5.5)).** For `δ ∈ (0, ρ)`
and `t > 0`, there are measurable random constants `c, C > 0` such that on `{t < T}`, with probability tending to `1` as
`ε → 0⁺`: the surplus floor on the targets `Z^ε_t = stoppedTargetSet`, the ceiling off the killing set `I^ε_t =
stoppedKillSet`, and the exit bound `∑_{b∈I} G_I(b,a) ≤ C/ε` on the targets. -/
def StoppedFirstGreenInputsStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ c C : Ω → ℝ, Measurable[S.envSigma] c ∧ Measurable[S.envSigma] C ∧
    (∀ ω, 0 < c ω) ∧ (∀ ω, 0 < C ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      (∀ a ∈ stoppedTargetSet S Λ δ t ε ω, c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ∧
      (∀ b ∉ stoppedKillSet S Λ ρ t ε ω, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤ c ω / (2 * ε)) ∧
      (∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
        ∑' b : stoppedKillSet S Λ ρ t ε ω, greenKernel (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a b ≤ C ω / ε)}

/-- The cell vertices of a smaller set form a subset of the cell vertices of a larger one. -/
theorem cellVertices_mono_set {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' := fun _ ⟨x, hx, hy⟩ => ⟨x, hx, h hy⟩

/-- A vertex of the discrete cluster has its cell in `B_ρ`. -/
theorem mem_cellVertices_ball_of_mem_matedDiscreteCluster {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ} {a : ℤ}
    (h : a ∈ matedDiscreteCluster m ε η ρ t) : a ∈ cellVertices ε η (ball 0 ρ) := by
  unfold matedDiscreteCluster discreteCluster at h
  exact h.1

/-- **Reduction.** The NEW input `StoppedFirstGreenInputsStep` (with the deterministic `StoppedPathwiseInputs`, assumed almost
surely for every `ε > 0`) gives the first Green step of the stopped clause with the factor `s = c/(2C)`. -/
theorem stoppedFirstGreenStep_of_inputs (𝒮 : SpaceFillingSLEModel) (hin : StoppedFirstGreenInputsStep 𝒮)
    (hdet : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → StoppedPathwiseInputs S Λ ρ t ε ω) :
    StoppedFirstGreenStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, C, hcm, hCm, hcpos, hCpos, hE⟩ := hin γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  have hae : ∀ᵐ ω ∂S.P, MonotoneOn (Λ ω) (Ioi 0) ∧
      ∀ ε : ℝ, 0 < ε → StoppedPathwiseInputs S Λ ρ t ε ω :=
    (hΛ.mono fun ω h => h.2.1.monotoneOn).and (hdet γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht)
  have hN : S.P {ω | ¬ (MonotoneOn (Λ ω) (Ioi 0) ∧
      ∀ ε : ℝ, 0 < ε → StoppedPathwiseInputs S Λ ρ t ε ω)} = 0 := ae_iff.1 hae
  have hsm : Measurable[S.envSigma] (fun ω => c ω / (2 * C ω)) :=
    hcm.div (measurable_const.mul hCm)
  refine ⟨fun ω => c ω / (2 * C ω), hsm, fun ω => ?_, ?_⟩
  · have := hCpos ω
    exact div_pos (hcpos ω) (by linarith)
  refine tendsToOneOn_of_good_cover hE (Z := fun _ => univ) ?_ hN ?_
  · simp only [compl_univ, measure_empty]
    exact tendsto_const_nhds
  filter_upwards [eventually_mem_nhdsWithin] with ε hε0
  intro ω hωF hωN _ hωE
  obtain ⟨hmono, hPI⟩ := not_not.mp hωN
  obtain ⟨hsymm, hlf, hcons, hB, hBfin, hcl, -⟩ := hPI ε hε0
  obtain ⟨h1, h2, h3⟩ := hωE
  have hε : (0 : ℝ) < ε := hε0
  have hT : t < clusterExitTime (Λ ω) ρ := hωF
  have hΛball : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime hρ hmono ht hT
  -- the targets lie in the killing set: their cells meet `Λ_t`, and the floor makes them cluster vertices
  have hclMem : ∀ a ∈ stoppedTargetSet S Λ δ t ε ω, a ∈ stoppedKillSet S Λ ρ t ε ω := by
    intro a ha
    have hΛa : a ∈ cellVertices ε (S.η ω) (Λ ω t) :=
      cellVertices_mono_set (fun _ hy => hy.1) (show a ∈ cellVertices ε (S.η ω) (innerNbhd δ (Λ ω t)) from ha)
    have hWa : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) := cellVertices_mono_set hΛball hΛa
    have hpos : 0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a :=
      lt_of_lt_of_le (div_pos (hcpos ω) hε) (h1 a ha)
    have hcb : a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ) :=
      cellVertices_mono_set ball_subset_closedBall hWa
    unfold stoppedOdometer at hpos
    simp only [hcb, ↓reduceIte] at hpos
    refine ⟨hT, ?_, hΛa⟩
    unfold matedDiscreteCluster discreteCluster
    exact ⟨hWa, by linarith⟩
  have hZI : stoppedTargetSet S Λ δ t ε ω ⊆ stoppedKillSet S Λ ρ t ε ω := hclMem
  have hI : (stoppedKillSet S Λ ρ t ε ω).Finite :=
    hBfin.subset fun a ha => mem_cellVertices_ball_of_mem_matedDiscreteCluster ha.2.1
  have hvk : ∀ a ∈ stoppedKillSet S Λ ρ t ε ω,
      mLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a =
        (mdeg (S.mult ε ω) a : ℝ)⁻¹ - t / ε * (if a = 0 then (mdeg (S.mult ε ω) 0 : ℝ)⁻¹ else 0) :=
    fun a ha => mLaplacian_stoppedOdometer_on_cluster hsymm hlf hcons hε ht hB hcl ha.2.1
  simp only [stoppedFirstGreenEvent, Set.mem_ofPred_eq]
  refine ⟨hZI, fun a ha => ?_⟩
  exact firstGreen_of_floor_ceiling_exit hsymm hlf hcons hI hε (hCpos ω) (hcpos ω).le hvk hZI h2 h1 h3 a ha

end MatedCRT
