import MatedCRT.Proofs.Sec5.StoppedExterior
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.Sec5.StoppedInteriorMarginProof

/-!
# The interior lower bound of the stopped surplus: deterministic core (`StoppedSurplusInteriorStep`)

For one sample point and one mesh `ε`, write `w̃ = matedLeastSupersolution`, `G = greenFunction (ball 0 ρ) 0` and
`w̄ = leastSupersolution`, so that the stopped surplus is `v(a) = w̃(a) + (t/ε) g^ε_{B_ρ}(0, a)`.

* `interior_real_bound`: if `m_ε⁻¹ w̃(a)` is within `δ` of `c w̄(x)` and `m_ε⁻¹ (ε⁻¹ g(0,a))` is within `δ'` of `c G(x)`,
  and `c₁ ≤ w̄(x) + t G(x)`, then `m_ε (c c₁ - δ - t δ') ≤ w̃(a) + t (ε⁻¹ g(0,a))`.
* `interior_vertex_bound`: the same at the vertex `a = vertexOf x` of a point `x` of the annulus `s ≤ |x|`, given the
  two convergence bounds (Theorem 4.1 on `B_ρ`, Lemma 3.3 on the annulus) at this sample point.
* `exists_pos_lower_surplus`: if `Λ` is open and `Λ ⊆ 𝒞` (the cluster, which is the content of the strict obstacle gap
  `HarmonicBallStrictObstacleGapStep`), then on the compact set of points of `Λ` at distance at least `δ'` from
  `Λᶜ` and at least `s` from the pole, `w̄ + t G(0,·)` has a positive lower bound `c₁` (compactness and continuity off the
  pole, `HarmonicBalls.continuousOn_greenFunction_ball`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace StoppedInterior

/-- Real-number form of the interior bound (the interior analogue of `StoppedExterior.exterior_real_bound`). -/
theorem interior_real_bound {mε c t δ δ' Wa Ga rW rG wbar gbar c1 : ℝ} (hmε : 0 < mε) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hrW : rW = mε⁻¹ * Wa) (hrG : rG = mε⁻¹ * Ga)
    (hW : |rW - c * wbar| ≤ δ) (hG : |rG - c * gbar| ≤ δ') (hf : c1 ≤ wbar + t * gbar) :
    mε * (c * c1 - δ - t * δ') ≤ Wa + t * Ga := by
  have h1 : c * wbar - δ ≤ rW := by linarith [(abs_le.1 hW).1]
  have h2 : c * gbar - δ' ≤ rG := by linarith [(abs_le.1 hG).1]
  have h3 : t * (c * gbar - δ') ≤ t * rG := mul_le_mul_of_nonneg_left h2 ht
  have h4 : c * c1 ≤ c * (wbar + t * gbar) := mul_le_mul_of_nonneg_left hf hc
  have e2 : c * wbar + t * (c * gbar - δ') = c * (wbar + t * gbar) - t * δ' := by ring
  have h5 : c * c1 - δ - t * δ' ≤ rW + t * rG := by linarith
  have e : mε⁻¹ * (Wa + t * Ga) = rW + t * rG := by rw [hrW, hrG]; ring
  have h6 : mε * (c * c1 - δ - t * δ') ≤ mε * (mε⁻¹ * (Wa + t * Ga)) :=
    mul_le_mul_of_nonneg_left (by rw [e]; exact h5) hmε.le
  rwa [← mul_assoc, mul_inv_cancel₀ hmε.ne', one_mul] at h6

/-- **Interior bound at a representative point, deterministic core.** Fix a sample point and a mesh `ε`. Suppose
the rescaled least supersolution is within `δ` of `c w̄` on `B_ρ` (Theorem 4.1 at this sample point) and the rescaled
Green kernel `ε⁻¹ g^ε_{B_ρ}(0, ·)` is within `δ'` of `c G_{B_ρ}(0, ·)` on the annulus `s ≤ |y|` (Lemma 3.3). If
`x ∈ B_ρ`, `s ≤ |x|` and `c₁ ≤ w̄(x) + t G(0, x)`, then the stopped surplus at the vertex `a = vertexOf x` satisfies
`m_ε (c c₁ - δ - t δ') ≤ w̃(a) + (t/ε) g^ε_{B_ρ}(0, a)`. -/
theorem interior_vertex_bound {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t s c c1 δ δ' mε : ℝ}
    (ht : 0 < t) (hc : 0 ≤ c) (hmε : 0 < mε)
    (hv0 : vertexOf ε η 0 = 0)
    (hW : ∀ y ∈ ball (0 : ℂ) ρ, |rescale mε ε η (matedLeastSupersolution m ε η ρ t) y -
      c * HarmonicBalls.leastSupersolution μ ρ 0 t y| ≤ δ)
    (hG : ∀ y ∈ ball (0 : ℂ) ρ, s ≤ ‖y‖ →
      |rescale mε ε η (fun b => ε⁻¹ * greenKernel m (interiorCellVertices ε η (ball 0 ρ)) (vertexOf ε η 0) b) y -
        c * HarmonicBalls.greenFunction (ball 0 ρ) 0 y| ≤ δ')
    {x : ℂ} (hxball : x ∈ ball (0 : ℂ) ρ) (hsx : s ≤ ‖x‖)
    (hf : c1 ≤ HarmonicBalls.leastSupersolution μ ρ 0 t x + t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x) :
    mε * (c * c1 - δ - t * δ') ≤
      matedLeastSupersolution m ε η ρ t (vertexOf ε η x) +
        t / ε * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x) := by
  rw [hv0] at hG
  have hrW : rescale mε ε η (matedLeastSupersolution m ε η ρ t) x =
      mε⁻¹ * matedLeastSupersolution m ε η ρ t (vertexOf ε η x) := by
    simp [rescale]
  have hrG : rescale mε ε η (fun b => ε⁻¹ * greenKernel m (interiorCellVertices ε η (ball 0 ρ)) 0 b) x =
      mε⁻¹ * (ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x)) := by
    simp [rescale, ballInterior]
  have key := interior_real_bound hmε hc ht.le hrW hrG (hW x hxball) (hG x hxball hsx) hf
  have e : t / ε * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x) =
      t * (ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x)) := by ring
  rw [e]
  exact key

/-- **Positive continuum margin from the strict obstacle gap (deterministic).** Let `Λ` be open with `Λ ⊆ 𝒞_t`, the
unregularized cluster of `HarmonicBalls` in `B_ρ` with source `0` (this is the conclusion of
`HarmonicBallStrictObstacleGapStep`). Let `w̄` be continuous on `cl B_ρ`. Then for `s, δ' > 0` there is
`c₁ > 0` with `c₁ ≤ w̄(x) + t G_{B_ρ}(0, x)` for all `x ∈ Λ` with `s ≤ |x|` and `δ' ≤ dist(x, Λᶜ)`. The points of
`Λ` at distance at least `s` from the pole form a compact set on which the surplus is continuous and positive. -/
theorem exists_pos_lower_surplus {μ : Measure ℂ} {ρ t s δ' : ℝ} {Λ : Set ℂ} (hρ : 0 < ρ) (hs : 0 < s)
    (hδ' : 0 < δ') (hΛcl : Λ ⊆ HarmonicBalls.cluster μ ρ 0 t)
    (hcont : ContinuousOn (HarmonicBalls.leastSupersolution μ ρ 0 t) (closedBall 0 ρ)) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ x ∈ Λ, s ≤ ‖x‖ → δ' ≤ infDist x Λᶜ →
      c1 ≤ HarmonicBalls.leastSupersolution μ ρ 0 t x + t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x := by
  set F : ℂ → ℝ := fun x => HarmonicBalls.leastSupersolution μ ρ 0 t x +
    t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x with hFdef
  set K : Set ℂ := closedBall 0 ρ ∩ {x | δ' ≤ infDist x Λᶜ} ∩ {x | s ≤ ‖x‖} with hKdef
  have hKc : IsCompact K :=
    ((isCompact_closedBall 0 ρ).inter_right
      (isClosed_le continuous_const (Metric.continuous_infDist_pt _))).inter_right
      (isClosed_le continuous_const continuous_norm)
  have hmemK : ∀ x ∈ Λ, s ≤ ‖x‖ → δ' ≤ infDist x Λᶜ → x ∈ K := fun x hxΛ hsx hδx =>
    ⟨⟨ball_subset_closedBall (hΛcl hxΛ).1, hδx⟩, hsx⟩
  have hKΛ : ∀ x ∈ K, x ∈ Λ := by
    intro x hx
    by_contra hxΛ
    have h0 : infDist x Λᶜ = 0 := Metric.infDist_zero_of_mem (mem_compl hxΛ)
    have h1 : δ' ≤ infDist x Λᶜ := hx.1.2
    linarith
  have hKpos : ∀ x ∈ K, 0 < F x := by
    intro x hx
    have hxΛ := hKΛ x hx
    have hsx : s ≤ ‖x‖ := hx.2
    obtain ⟨-, hcl⟩ := hΛcl hxΛ
    rcases hcl with hz | hlt
    · exfalso
      rw [hz, norm_zero] at hsx
      linarith
    · show 0 < HarmonicBalls.leastSupersolution μ ρ 0 t x + t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x
      have e : -t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x = -(t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x) := by
        ring
      linarith
  have hFc : ContinuousOn F K := by
    have hK1 : K ⊆ closedBall 0 ρ := fun x hx => hx.1.1
    have hK2 : K ⊆ {(0 : ℂ)}ᶜ := fun x hx hx0 => by
      have hz : ‖x‖ = 0 := by rw [mem_singleton_iff.1 hx0, norm_zero]
      have hsx : s ≤ ‖x‖ := hx.2
      linarith
    have hGc : ContinuousOn (HarmonicBalls.greenFunction (ball 0 ρ) 0) K :=
      (HarmonicBalls.continuousOn_greenFunction_ball (mem_ball_self hρ)).mono hK2
    show ContinuousOn (fun x => HarmonicBalls.leastSupersolution μ ρ 0 t x +
      t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x) K
    exact (hcont.mono hK1).add (continuousOn_const.mul hGc)
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0K, hmin⟩ := hKc.exists_isMinOn hne hFc
    exact ⟨F x0, hKpos x0 hx0K, fun x hxΛ hsx hδx => isMinOn_iff.1 hmin x (hmemK x hxΛ hsx hδx)⟩
  · exact ⟨1, one_pos, fun x hxΛ hsx hδx => absurd ⟨x, hmemK x hxΛ hsx hδx⟩ hne⟩

/-! ### Named inputs of the interior step -/

/-- **Pole lower bound (named input).** For `δ < ρ` and `t > 0` there are a radius `s > 0` and a
`σ(h,η)`-measurable `c > 0` such that, on `{t < T}`, with probability tending to one, `c/ε ≤ v^ε_t(a)` for every
`a ∈ V^ε(Λ_t)` in the `δ`-interior with `|η(a)| < s`, where `v^ε_t = w̃^ε_t + (t/ε) g^ε_{B_ρ}(0, ·)`. Theorem 4.1 and
Lemma 3.3 are used in the paper only on the annulus `{s ≤ |y|}`; the paper does not treat the discrete surplus at the
pole. Proved from Lemmas 2.16 and 2.18 and the annulus bound: `stoppedSurplusPole_of_steps`
(`MatedCRT/Proofs/Sec5/StoppedPoleReduction.lean`). -/
def StoppedSurplusPoleStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ s : ℝ, 0 < s ∧ ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
          ‖vertexPoint ε (S.η ω) a‖ < s →
          c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}

/-- **Discrete-to-continuum geometry (named input).** For `r > 0`, with probability tending to one, every
`δ`-interior vertex `a` of `V^ε(Λ_t)` has all points of its cell within `r` of the vertex point and at distance at least
`δ/2` from the complement of `Λ_t`. For fixed `ω` this follows from the cell diameters tending to zero (uniform
continuity of `η` on compacta, as in `cell_diam_small_of_proper`) and from `Λ_t = int cl 𝒞_t` (regularity), by a
compactness argument; it is not stated in the paper. Proved for every model:
`StoppedGeometry.stoppedInteriorGeometryStep_holds` (`MatedCRT/Proofs/Sec5/StoppedInteriorGeometryProof.lean`). -/
def StoppedInteriorGeometryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t r : ℝ, 0 < δ → 0 < t → 0 < r →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < r}

/-- **Measurability of the continuum margin (named input).**
For `δ, s, t > 0` let `M(ω)` be the infimum over the random compact set
`K(ω) = {x ∈ Λ_t(ω) : s ≤ |x|, δ ≤ dist(x, Λ_t(ω)ᶜ)}` of the continuum surplus `w̄_t + t G_{B_ρ}(0, ·)`; the infimum
over the empty set is `0`, as is an unbounded-below real infimum. The step asserts an almost sure measurable version:
there is an `S.envSigma`-measurable `Mhat` with `Mhat = M` almost surely on `{t < T}`, `T = clusterExitTime Λ ρ`.
Nothing is prescribed on the exceptional outcomes. -/
def StoppedInteriorMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ s t : ℝ, 0 < δ → 0 < s → 0 < t →
    ∃ Mhat : Ω → ℝ, Measurable[S.envSigma] Mhat ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        Mhat ω = ⨅ x : {x : ℂ | x ∈ Λ ω t ∧ s ≤ ‖x‖ ∧ δ ≤ infDist x (Λ ω t)ᶜ},
          (HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (x : ℂ) +
            t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (x : ℂ))

open StoppedInteriorMargin

/-- **Residual random-code construction (named input).** For `δ, s, t > 0` there are a
random nonempty compact `K` and a random continuous function `f` on the margin domain `A = closedBall 0 (ρ/2) ∩ {s ≤ |x|}`,
jointly `S.envSigma`-measurable, such that almost surely on `{t < T}`, `K = closure Λ_t` and
`f = w̄_t + t G_{B_ρ}(0, ·)` on `A`. The compact set is the field-measurable random compact set of the Borel-version
construction, and `f` is the Borel decoder of the surplus on `A`. Proved for every model:
`StoppedCode.stoppedMarginCodeStep_holds` (`MatedCRT/Proofs/Sec5/StoppedClusterCode.lean`). -/
def StoppedMarginCodeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ s t : ℝ, 0 < δ → 0 < s → 0 < t →
    ∃ (K : Ω → TopologicalSpace.NonemptyCompacts ℂ) (f : Ω → C(↥(marginDomain s (ρ / 2)), ℝ)),
      @Measurable Ω (TopologicalSpace.NonemptyCompacts ℂ × C(↥(marginDomain s (ρ / 2)), ℝ)) S.envSigma (borel _)
        (fun ω => (K ω, f ω)) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        (K ω : Set ℂ) = closure (Λ ω t) ∧
        ∀ x : ↥(marginDomain s (ρ / 2)), f ω x =
          HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x.1 +
            t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x.1

/-- **The repaired measurability step from the residual random-code construction.** The erosion minimum `m(K, f)` of the
residual code is `S.envSigma`-measurable (`measurable_erodedMin_comp`), and on `{t < T}` it equals the raw continuum
margin almost surely (`erodedMin_eq_raw`, with the regular-open identity and `Λ_t ⊆ B_{ρ/3}`). -/
theorem stoppedInteriorMeasurable_of_code (𝒮 : SpaceFillingSLEModel) (hcode : StoppedMarginCodeStep 𝒮) :
    StoppedInteriorMeasurableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ s t hδ hs ht
  obtain ⟨K, f, hKf, hae⟩ := hcode γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ s t hδ hs ht
  refine ⟨fun ω => erodedMin (marginDomain s (ρ / 2)) δ (K ω) (f ω), ?_, ?_⟩
  · exact @measurable_erodedMin_comp (marginDomain s (ρ / 2)) Ω S.envSigma
      (isCompact_marginDomain s (ρ / 2)) δ K f hKf
  · filter_upwards [hΛ, hae] with ω hΛω hωae hT
    obtain ⟨hK, hf⟩ := hωae hT
    have hsub : Λ ω t ⊆ ball 0 (ρ / 3) :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hΛω.2.1.monotoneOn ht hT
    have hEq := (hΛω.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
    have hreg : interior (closure (Λ ω t)) = Λ ω t := interior_closure_eq_self_of_eq hEq
    have hne : (Λ ω t)ᶜ.Nonempty := by
      refine ⟨(ρ : ℂ), fun h => ?_⟩
      have h1 := hsub h
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hρ.le] at h1
      linarith
    have hsubR : Λ ω t ⊆ closedBall 0 (ρ / 2) :=
      hsub.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    exact erodedMin_eq_raw
      (fun z => HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t z + t * HarmonicBalls.greenFunction (ball 0 ρ) 0 z)
      (K ω) (f ω) hδ hreg hne hsubR hK hf

/-- Union bound for six sets (left-nested unions). -/
theorem measure_union_six {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (s₁ s₂ s₃ s₄ s₅ s₆ : Set Ω) :
    P (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆) ≤ P s₁ + P s₂ + P s₃ + P s₄ + P s₅ + P s₆ := by
  refine (measure_union_le _ _).trans ?_
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  exact measure_union_le _ _

/-- Union bound for five sets (left-nested unions). -/
theorem measure_union_five {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (s₁ s₂ s₃ s₄ s₅ : Set Ω) :
    P (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅) ≤ P s₁ + P s₂ + P s₃ + P s₄ + P s₅ := by
  refine (measure_union_le _ _).trans ?_
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  exact measure_union_le _ _

/-- **Combination of the bad events.** Pole and geometry events have probability tending to one; for each level `κ` of a
positive random margin `c` there are fixed-error events `B₁, B₂` (the convergence events of Theorem 4.1 and Lemma 3.3) of
probability tending to zero such that, off them and off the good event, `c > κ` yields the bound. Then the target event
has probability tending to one. -/
theorem tendsToOneOn_of_levels {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F Good : Set Ω) (hGood : P Goodᶜ = 0) (c : Ω → ℝ) (hc : AEMeasurable c P) (hcpos : ∀ ω, 0 < c ω)
    (E Pole Geo : ℝ → Set Ω) (hPole : TendsToOneOn P F Pole) (hGeo : TendsToOneOn P F Geo)
    (hlev : ∀ κ : ℝ, 0 < κ → ∃ B₁ B₂ : ℝ → Set Ω,
      Tendsto (fun ε => P (F ∩ B₁ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun ε => P (F ∩ B₂ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F ∩ Pole ε ∩ Geo ε ∩ Good, ω ∉ B₁ ε → ω ∉ B₂ ε → κ < c ω → ω ∈ E ε) :
    TendsToOneOn P F E := by
  unfold TendsToOneOn at hPole hGeo ⊢
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη5 : (0 : ℝ≥0∞) < η / 5 := ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩
  obtain ⟨κ, hκ, hPκ⟩ := StoppedMeanValue.exists_measure_le_le_of_pos hc hcpos hη5
  obtain ⟨B₁, B₂, h1, h2, hsub⟩ := hlev κ hκ
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hPole (η / 5) hη5,
    ENNReal.tendsto_nhds_zero.1 hGeo (η / 5) hη5,
    ENNReal.tendsto_nhds_zero.1 h1 (η / 5) hη5, ENNReal.tendsto_nhds_zero.1 h2 (η / 5) hη5, hsub]
    with ε hP hG hb1 hb2 hsubε
  have hsub' : F ∩ (E ε)ᶜ ⊆ (F ∩ (Pole ε)ᶜ) ∪ (F ∩ (Geo ε)ᶜ) ∪ (F ∩ B₁ ε) ∪ (F ∩ B₂ ε) ∪
      {ω | c ω ≤ κ} ∪ Goodᶜ := by
    intro ω hω
    obtain ⟨hF, hEω⟩ := hω
    by_contra hbad
    have hG' : ω ∈ Good := by
      by_contra h
      exact hbad (Or.inr h)
    have hP' : ω ∈ Pole ε := by
      by_contra h
      exact hbad (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hF, h⟩)))))
    have hGe' : ω ∈ Geo ε := by
      by_contra h
      exact hbad (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hF, h⟩)))))
    have hB1' : ω ∉ B₁ ε := fun h => hbad (Or.inl (Or.inl (Or.inl (Or.inr ⟨hF, h⟩))))
    have hB2' : ω ∉ B₂ ε := fun h => hbad (Or.inl (Or.inl (Or.inr ⟨hF, h⟩)))
    have hκ' : κ < c ω := by
      by_contra h
      exact hbad (Or.inl (Or.inr (not_lt.1 h)))
    exact hEω (hsubε ω ⟨⟨⟨hF, hP'⟩, hGe'⟩, hG'⟩ hB1' hB2' hκ')
  calc P (F ∩ (E ε)ᶜ)
      ≤ P ((F ∩ (Pole ε)ᶜ) ∪ (F ∩ (Geo ε)ᶜ) ∪ (F ∩ B₁ ε) ∪ (F ∩ B₂ ε) ∪ {ω | c ω ≤ κ} ∪ Goodᶜ) :=
        measure_mono hsub'
    _ ≤ P ((F ∩ (Pole ε)ᶜ) ∪ (F ∩ (Geo ε)ᶜ) ∪ (F ∩ B₁ ε) ∪ (F ∩ B₂ ε) ∪ {ω | c ω ≤ κ}) + P Goodᶜ :=
        measure_union_le _ _
    _ ≤ (P (F ∩ (Pole ε)ᶜ) + P (F ∩ (Geo ε)ᶜ) + P (F ∩ B₁ ε) + P (F ∩ B₂ ε) + P {ω | c ω ≤ κ}) + P Goodᶜ := by
        gcongr
        exact measure_union_five P _ _ _ _ _
    _ ≤ (η / 5 + η / 5 + η / 5 + η / 5 + η / 5) + 0 := by
        rw [hGood]
        gcongr
    _ ≤ η := by
        rw [add_zero, ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div, ← ENNReal.add_div]
        exact ENNReal.div_le_of_le_mul (le_of_eq (by ring))

/-- **`StoppedSurplusInteriorStep` from the strict obstacle gap and three named inputs**. -/
theorem stoppedSurplusInterior_of_gap (𝒮 : SpaceFillingSLEModel) (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hpoleS : StoppedSurplusPoleStep 𝒮) (hgeo : StoppedInteriorGeometryStep 𝒮)
    (hmeas : StoppedInteriorMeasurableStep 𝒮) (hmeps : MepsScalingInput 𝒮) :
    StoppedSurplusInteriorStep 𝒮 := by
  intro _ _ h41 h33 _ _ γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  have hm0 : 0 < S.m₀ := MatedCRTEnv.IsValid.m₀_pos hγ hγ2 hS
  have hc0 : 0 < S.c₀ / 6 := by
    unfold MatedCRTEnv.c₀
    exact div_pos (div_pos (by norm_num) hm0) (by norm_num)
  obtain ⟨C, hC1, hCS⟩ := hmeps γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmεb⟩ := hCS Ω S hS
  obtain ⟨s, hs, cp, hcp, hcppos, hPoleE⟩ := hpoleS γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  have hGeoE := hgeo γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t (s / 2) hδ ht (half_pos hs)
  have hsA0 : 0 < min (s / 2) (ρ / 2) := lt_min (half_pos hs) (half_pos hρ)
  have hsAle : min (s / 2) (ρ / 2) ≤ s / 2 := min_le_left _ _
  obtain ⟨Mhat, hMhatMeas, hMhatAe⟩ := hmeas γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 2) (min (s / 2) (ρ / 2)) t
    (half_pos hδ) hsA0 ht
  have hgapE := hgap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  set sA : ℝ := min (s / 2) (ρ / 2) with hsA
  -- the raw margin `cinf` is used only through its a.s. agreement with the measurable version `Mhat` on `{t < T}`
  set cinf : Ω → ℝ := fun ω => ⨅ x : {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ},
    (HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (x : ℂ) +
      t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (x : ℂ)) with hcinf
  set cpos : Ω → ℝ := fun ω => if 0 < Mhat ω then Mhat ω else 1 with hcposdef
  have hcpos_meas : Measurable[S.envSigma] cpos :=
    Measurable.ite (measurableSet_lt measurable_const hMhatMeas) hMhatMeas measurable_const
  have hcpos_pos : ∀ ω, 0 < cpos ω := fun ω => by
    simp only [hcposdef]
    split_ifs with h
    · exact h
    · exact one_pos
  have hcpos_ae : AEMeasurable cpos S.P := hS.aemeasurable_of_envSigma hcpos_meas
  set c : ℝ := S.c₀ / 6 with hcdef
  set cfin : Ω → ℝ := fun ω => min (cp ω) (c * cpos ω / (2 * C)) with hcfin
  have hcfin_meas : Measurable[S.envSigma] cfin :=
    Measurable.min hcp ((measurable_const.mul hcpos_meas).div_const _)
  have hcfin_pos : ∀ ω, 0 < cfin ω := fun ω =>
    lt_min (hcppos ω) (div_pos (mul_pos hc0 (hcpos_pos ω)) (by linarith))
  have hgood : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
      (∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (t < clusterExitTime (Λ ω) ρ → Λ ω t ⊆ HarmonicBalls.cluster (S.μ ω) ρ 0 t) ∧
      (t < clusterExitTime (Λ ω) ρ → Mhat ω = cinf ω) :=
    hΛ.and (hS.isAreaParametrized.and ((MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero hS).and
      ((MatedCRTEnv.IsValid.ae_tendsto_cocompact hS).and (hgapE.and hMhatAe))))
  set Good : Set Ω := {ω | IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
    (∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    (t < clusterExitTime (Λ ω) ρ → Λ ω t ⊆ HarmonicBalls.cluster (S.μ ω) ρ 0 t) ∧
    (t < clusterExitTime (Λ ω) ρ → Mhat ω = cinf ω)} with hGooddef
  have hGoodnull : S.P Goodᶜ = 0 := ae_iff.1 hgood
  set Pole : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
      ‖vertexPoint ε (S.η ω) a‖ < s →
      cp ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} with hPoledef
  set Geo : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
      ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < s / 2} with hGeodef
  set E : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
      cfin ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} with hEdef
  -- the annulus of Lemma 3.3 and the sets of the convergence events
  have hO_pos : 0 < min sA (ρ / 2) := lt_min hsA0 (half_pos hρ)
  have hOsub : {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} ⊆ closedBall (0 : ℂ) ρ \ {0} := by
    intro y hy
    refine ⟨ball_subset_closedBall hy.1, fun h => ?_⟩
    rw [mem_singleton_iff] at h
    have hy2 := hy.2
    rw [h, norm_zero] at hy2
    exact absurd hy2 (not_le.2 hO_pos)
  have hOinf : 0 < infDist (0 : ℂ) {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} := by
    have hy0 : (((min sA (ρ / 2)) : ℝ) : ℂ) ∈ {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} :=
      ⟨mem_ball_zero_iff.2 (by
          rw [Complex.norm_real, Real.norm_of_nonneg hO_pos.le]
          linarith [min_le_right sA (ρ / 2)]),
        le_of_eq (by rw [Complex.norm_real, Real.norm_of_nonneg hO_pos.le])⟩
    have hle : min sA (ρ / 2) ≤ infDist (0 : ℂ) {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} :=
      (Metric.le_infDist ⟨_, hy0⟩).2 fun y hy => by
        rw [dist_zero_left]
        exact hy.2
    linarith
  -- the probability of the convergence events at the errors `δ0`, `δ1` (chosen from the level `κ`)
  have hlev : ∀ κ : ℝ, 0 < κ → ∃ B₁ B₂ : ℝ → Set Ω,
      Tendsto (fun ε => S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ B₁ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun ε => S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ B₂ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ} ∩ Pole ε ∩ Geo ε ∩ Good,
        ω ∉ B₁ ε → ω ∉ B₂ ε → κ < cpos ω → ω ∈ E ε := by
    intro κ hκ
    set δ0 : ℝ := c * κ / 4 with hδ0def
    set δ1 : ℝ := c * κ / 4 / (1 + t) with hδ1def
    have hδ0pos : 0 < δ0 := div_pos (mul_pos hc0 hκ) (by norm_num)
    have hδ1pos : 0 < δ1 := div_pos (div_pos (mul_pos hc0 hκ) (by norm_num)) (by linarith)
    have htδ1 : t * δ1 ≤ c * κ / 4 := by
      have e : t * δ1 = c * κ / 4 * (t / (1 + t)) := by
        rw [hδ1def]
        ring
      rw [e]
      exact mul_le_of_le_one_right (div_nonneg (mul_nonneg hc0.le hκ.le) (by norm_num))
        ((div_le_one (by linarith)).2 (by linarith))
    refine ⟨fun ε => {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
        δ0 < |rescaledMatedLeastSupersolution S ρ t ε ω x -
          S.c₀ / 6 * HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x|},
      fun ε => {ω | ¬ ∀ x ∈ {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖},
        |rescale (S.mε ε) ε (S.η ω) (fun a => ε⁻¹ *
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) a) x -
          c * HarmonicBalls.greenFunction (ball 0 ρ) 0 x| ≤ δ1}, ?_, ?_, ?_⟩
    · have hB1 := h41 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht δ0 hδ0pos
      exact Tendsto.congr (fun ε => congrArg S.P (Set.inter_eq_right.2 (fun ω hω => hω.1)).symm) hB1
    · have hP33 := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS ρ 0 0 hρ subset_rfl (mem_ball_self hρ) δ1 hδ1pos _ hOsub hOinf
      refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hP33 η hη] with ε hε
      exact le_trans (measure_mono Set.inter_subset_right) hε
    · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
      intro ω hω h1 h2 hκω
      obtain ⟨⟨⟨hF, hPole⟩, hGe⟩, hGω⟩ := hω
      obtain ⟨hΛω, hηω, hv0ω, hcocω, hclω, hMω⟩ := hGω
      have hT : t < clusterExitTime (Λ ω) ρ := hF
      have hε0 : 0 < ε := hε.1
      have hmεb' := hmεb ε hε.1 hε.2
      have hmpos : 0 < S.mε ε := lt_of_lt_of_le (mul_pos (inv_pos.2 (by linarith)) (inv_pos.2 hε0)) hmεb'.1
      have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
        IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hΛω.2.1.monotoneOn ht hT
      obtain ⟨-, hcont, -⟩ := hΛω.2.2 t (ρ / 3) ht (by linarith) hΛt ρ (by linarith)
      have hPole' : ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
          ‖vertexPoint ε (S.η ω) a‖ < s →
          cp ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a := by
        have hp := hPole
        simp only [hPoledef, Set.mem_ofPred_eq] at hp
        exact hp
      have hGe' : ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
          ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < s / 2 := by
        have hg := hGe
        simp only [hGeodef, Set.mem_ofPred_eq] at hg
        exact hg
      simp only [hEdef, Set.mem_ofPred_eq]
      intro a ha hδa
      by_cases hsa : ‖vertexPoint ε (S.η ω) a‖ < s
      · exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hε0.le) (hPole' a ha hδa hsa)
      · have hsa' : s ≤ ‖vertexPoint ε (S.η ω) a‖ := not_lt.1 hsa
        obtain ⟨x, hxcell, hxa⟩ := exists_vertexOf_eq_of_area_parametrized hηω hcocω hε0 a
        obtain ⟨hdx, hdist⟩ := hGe' a ha hδa x hxcell
        have hxΛ : x ∈ Λ ω t := by
          by_contra hn
          have h0 : infDist x (Λ ω t)ᶜ = 0 := Metric.infDist_zero_of_mem (mem_compl hn)
          linarith
        have hxcl : x ∈ HarmonicBalls.cluster (S.μ ω) ρ 0 t := hclω hT hxΛ
        have hxball : x ∈ ball (0 : ℂ) ρ := hxcl.1
        have hxsA : sA ≤ ‖x‖ := by
          have h1' : ‖vertexPoint ε (S.η ω) a‖ - ‖x‖ ≤ dist x (vertexPoint ε (S.η ω) a) := by
            rw [dist_comm, dist_eq_norm]
            exact norm_sub_norm_le _ _
          linarith
        obtain ⟨c1, hc1pos, hc1⟩ := exists_pos_lower_surplus hρ hsA0 (half_pos hδ) (hclω hT) hcont
        have hKne : ({x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ}).Nonempty :=
          ⟨x, hxΛ, hxsA, hdx⟩
        have : Nonempty {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ} := hKne.to_subtype
        have hbdd : ∀ y : {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ},
            c1 ≤ HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (y : ℂ) +
              t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (y : ℂ) := by
          intro y
          obtain ⟨hyΛ, hysA, hyd⟩ := y.2
          exact hc1 _ hyΛ hysA hyd
        have hcinf_ge : c1 ≤ cinf ω := le_ciInf hbdd
        have hcinf_le : cinf ω ≤ HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x +
            t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x :=
          ciInf_le ⟨c1, by rintro _ ⟨y, rfl⟩; exact hbdd y⟩ (⟨x, hxΛ, hxsA, hdx⟩ :
            {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ})
        have hMhatEq : Mhat ω = cinf ω := hMω hT
        have hpos' : 0 < cinf ω := lt_of_lt_of_le hc1pos hcinf_ge
        have hcpos_eq : cpos ω = cinf ω := by simp [hcposdef, hMhatEq, hpos']
        have hκc : κ < cinf ω := by
          rw [← hcpos_eq]
          exact hκω
        have hW : ∀ y ∈ ball (0 : ℂ) ρ, |rescale (S.mε ε) ε (S.η ω)
            (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) y -
            c * HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t y| ≤ δ0 := by
          intro y hy
          by_contra hlt
          exact h1 ⟨hF, y, hy, not_le.1 hlt⟩
        have hG : ∀ y ∈ ball (0 : ℂ) ρ, sA ≤ ‖y‖ → |rescale (S.mε ε) ε (S.η ω) (fun b => ε⁻¹ *
            greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) b) y -
            c * HarmonicBalls.greenFunction (ball 0 ρ) 0 y| ≤ δ1 := by
          intro y hy hyO
          exact not_not.1 h2 y ⟨hy, (min_le_left _ _).trans hyO⟩
        have hbound := interior_vertex_bound (μ := S.μ ω) (η := S.η ω) (m := S.mult ε ω) (ε := ε)
          (ρ := ρ) (t := t) (s := sA) (c := c) (c1 := cinf ω) (δ := δ0) (δ' := δ1) (mε := S.mε ε)
          ht hc0.le hmpos (hv0ω ε hε0) hW hG hxball hxsA hcinf_le
        rw [hxa] at hbound
        have hkey : c * cinf ω / 2 ≤ c * cinf ω - δ0 - t * δ1 := by
          have hcκ : c * κ ≤ c * cinf ω := mul_le_mul_of_nonneg_left hκc.le hc0.le
          linarith
        have hc2 : 0 ≤ c * cinf ω / 2 :=
          div_nonneg (mul_nonneg hc0.le (le_trans hc1pos.le hcinf_ge)) (by norm_num)
        have h3 : C⁻¹ * ε⁻¹ * (c * cinf ω / 2) ≤ S.mε ε * (c * cinf ω - δ0 - t * δ1) :=
          mul_le_mul hmεb'.1 hkey hc2 hmpos.le
        have hcf : cfin ω ≤ c * cinf ω / (2 * C) := (min_le_right _ _).trans (by rw [hcpos_eq])
        have h4 : cfin ω / ε ≤ C⁻¹ * ε⁻¹ * (c * cinf ω / 2) := by
          calc cfin ω / ε ≤ (c * cinf ω / (2 * C)) / ε := div_le_div_of_nonneg_right hcf hε0.le
            _ = C⁻¹ * ε⁻¹ * (c * cinf ω / 2) := by ring
        exact le_trans h4 (le_trans h3 hbound)
  refine ⟨cfin, hcfin_meas, hcfin_pos, ?_⟩
  exact tendsToOneOn_of_levels S.P {ω | t < clusterExitTime (Λ ω) ρ} Good hGoodnull cpos hcpos_ae hcpos_pos
    E Pole Geo hPoleE hGeoE hlev


end StoppedInterior

end MatedCRT
