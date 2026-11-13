import MatedCRT.FirstPass.S3e.HolderGoodEventCorrected
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedGeometry
import MatedCRT.FirstPass.Derived.ExitTimeLowerBound
import MatedCRT.FirstPass.S3i.GoodEvent

/-!
# Total variation distance between first exit vertices (Berestycki–Gwynne (2020), Lemma 6.13, first part)

For `z ∈ B_ρ` and `δ ∈ (0,1)` let `V = V^ε(B_{√δ}(z)) \ V^ε(∂B_{√δ}(z))` be the interior vertex set of the ball of radius `√δ`
and let `X` be the walk on the mated-CRT map started at `x`.  The first vertex outside `V` (the first vertex of
`V^ε(∂B_{√δ}(z))` met by the walk, since consecutive vertices have intersecting cells) has law `srwLaw m x ∘ vExitPosition V⁻¹`.
Lemma 6.13: with polynomially high probability as `ε → 0`, for `x, y ∈ V^ε(B_δ(z))` the total variation distance between
the laws of the first exit vertices from `x` and from `y` is at most `A δ^ξ`.

Proof (the deterministic estimate): for a vertex set `T` the function `c ↦ P_c[exit vertex ∈ T]` is discrete harmonic on `V`
with values in `[0,1]` (exit-value harmonicity), so the discrete Hölder estimate (cited, corrected form) on the domain
`B_{√δ}(z)` bounds its oscillation between `x` and `y`, both at distance `≲ δ` from `z` (cell sizes) and at distance `≳ √δ`
from `∂B_{√δ}(z)`.  The domain is kept inside `B_{ρ₀}` with `ρ₀ = (1+ρ)/2`; for `δ` bounded below the estimate is trivial.
-/

set_option autoImplicit false

namespace MatedCRT
namespace HittingVertexTV

open MeasureTheory Metric Set Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Deterministic core: for a locally finite graph with consecutive edges and a proper curve, if the discrete Hölder
estimate holds on `B_s(z)` for every function harmonic on its interior vertex set and the cells meeting `B_{s²}(z)` are
small, then the exit laws from two vertices of `V^ε(B_{s²}(z))` differ by at most `A 6^ξ s^ξ` on every vertex set `T`. -/
theorem tv_le_of_holder {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {z : ℂ} {s ξ A β : ℝ}
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (hξ : 0 < ξ) (hA : 0 < A)
    (hcell : ∀ v ∈ cellVertices ε η (ball z (s ^ 2)), ∀ p ∈ cell ε η v,
      dist (vertexPoint ε η v) p < s ^ 2 / 4)
    (hβ : ε ^ β ≤ s ^ 2)
    (hH : ∀ f : ℤ → ℝ, (∀ v ∈ interiorCellVertices ε η (ball z s), matedLaplacian m f v = 0) →
      ∀ a ∈ interiorCellVertices ε η (ball z s), ∀ b ∈ cellVertices ε η (ball z s),
        |f a - f b| * infDist (vertexPoint ε η a) (frontier (ball z s)) ^ ξ ≤
          A * (⨆ a' : cellVertices ε η (ball z s), |f a'|) *
            max (ε ^ β) ‖vertexPoint ε η a - vertexPoint ε η b‖ ^ ξ)
    {x y : ℤ} (hx : x ∈ cellVertices ε η (ball z (s ^ 2)))
    (hy : y ∈ cellVertices ε η (ball z (s ^ 2))) (T : Set ℤ) :
    |(srwLaw m x).real {X | vExitPosition (interiorCellVertices ε η (ball z s)) X ∈ T} -
        (srwLaw m y).real {X | vExitPosition (interiorCellVertices ε η (ball z s)) X ∈ T}| ≤
      A * 6 ^ ξ * s ^ ξ := by
  have hs1 : s ^ 2 ≤ s := by nlinarith
  have hgeo : ∀ v ∈ cellVertices ε η (ball z (s ^ 2)),
      v ∈ cellVertices ε η (ball z s) ∧ dist (vertexPoint ε η v) z < 5 / 4 * s ^ 2 ∧
        v ∈ interiorCellVertices ε η (ball z s) := by
    intro v hv
    obtain ⟨q, hqc, hqb⟩ := hv
    have hd := hcell v ⟨q, hqc, hqb⟩ q hqc
    have hq := mem_ball.1 hqb
    have hz : dist (vertexPoint ε η v) z < 5 / 4 * s ^ 2 := by
      have := dist_triangle (vertexPoint ε η v) q z
      linarith
    have hvD : v ∈ cellVertices ε η (ball z s) := ⟨q, hqc, mem_ball.2 (lt_of_lt_of_le hq hs1)⟩
    refine ⟨hvD, hz, hvD, ?_⟩
    rintro ⟨p, hpc, hpf⟩
    rw [frontier_ball z hs0.ne'] at hpf
    have hpd := hcell v ⟨q, hqc, hqb⟩ p hpc
    have hps : dist p z = s := mem_sphere.1 hpf
    have h3 : dist p z ≤ dist (vertexPoint ε η v) p + dist (vertexPoint ε η v) z := by
      have := dist_triangle p (vertexPoint ε η v) z
      rwa [dist_comm p (vertexPoint ε η v)] at this
    nlinarith
  obtain ⟨hxD, hxz, hxV⟩ := hgeo x hx
  obtain ⟨hyD, hyz, hyV⟩ := hgeo y hy
  have hfin : (interiorCellVertices ε η (ball z s)).Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset fun _ h => h.1
  have hAex := projectedWalk_ae_finite_exit_of_finite m hlf hcons ε η s z hfin
  let g : ℤ → ℝ := T.indicator fun _ => (1 : ℝ)
  have hg : ∀ b, |g b| ≤ 1 := by
    intro b
    by_cases hb : b ∈ T <;> simp [g, hb]
  let f : ℤ → ℝ := fun c =>
    ∫ X, g (vExitPosition (interiorCellVertices ε η (ball z s)) X) ∂srwLaw m c
  have hharm : ∀ v ∈ interiorCellVertices ε η (ball z s), matedLaplacian m f v = 0 :=
    fun v hv => mLaplacian_integral_exitValue hlf hAex hv
      (mdeg_ne_zero_of_ne_zero hlf (hcons v)) hg
  have hms : MeasurableSet
      {X : ℕ → ℤ | vExitPosition (interiorCellVertices ε η (ball z s)) X ∈ T} :=
    (measurable_vExitPosition _) (MeasurableSet.of_discrete)
  have hfeq : ∀ c, f c =
      (srwLaw m c).real {X | vExitPosition (interiorCellVertices ε η (ball z s)) X ∈ T} := by
    intro c
    have hfun : (fun X => g (vExitPosition (interiorCellVertices ε η (ball z s)) X)) =
        {X | vExitPosition (interiorCellVertices ε η (ball z s)) X ∈ T}.indicator
          (fun _ => (1 : ℝ)) := by
      funext X
      simp [g, Set.indicator]
    show ∫ X, g (vExitPosition (interiorCellVertices ε η (ball z s)) X) ∂srwLaw m c = _
    rw [hfun, integral_indicator_const _ hms]
    simp
  have hf01 : ∀ c, |f c| ≤ 1 := by
    intro c
    rw [hfeq c, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hsup : (⨆ a' : cellVertices ε η (ball z s), |f a'|) ≤ 1 := by
    have : Nonempty (cellVertices ε η (ball z s)) := ⟨⟨x, hxD⟩⟩
    exact ciSup_le fun a' => hf01 a'
  have hk := hH f hharm x hxV y hyD
  have hinf : s / 2 ≤ infDist (vertexPoint ε η x) (frontier (ball z s)) := by
    rw [frontier_ball z hs0.ne']
    refine (Metric.le_infDist (NormedSpace.sphere_nonempty.2 hs0.le)).2 fun p hp => ?_
    have hps : dist p z = s := mem_sphere.1 hp
    have h3 : dist p z ≤ dist (vertexPoint ε η x) p + dist (vertexPoint ε η x) z := by
      have := dist_triangle p (vertexPoint ε η x) z
      rwa [dist_comm p (vertexPoint ε η x)] at this
    nlinarith
  have hmax : max (ε ^ β) ‖vertexPoint ε η x - vertexPoint ε η y‖ ≤ 3 * s ^ 2 := by
    refine max_le (by nlinarith [sq_nonneg s]) ?_
    rw [← dist_eq_norm]
    have := dist_triangle (vertexPoint ε η x) z (vertexPoint ε η y)
    rw [dist_comm z (vertexPoint ε η y)] at this
    nlinarith [sq_nonneg s]
  have hmax0 : 0 ≤ max (ε ^ β) ‖vertexPoint ε η x - vertexPoint ε η y‖ :=
    le_max_of_le_right (norm_nonneg _)
  have h1 : (s / 2) ^ ξ ≤ infDist (vertexPoint ε η x) (frontier (ball z s)) ^ ξ :=
    Real.rpow_le_rpow (by positivity) hinf hξ.le
  have h2 : A * (⨆ a' : cellVertices ε η (ball z s), |f a'|) *
        max (ε ^ β) ‖vertexPoint ε η x - vertexPoint ε η y‖ ^ ξ ≤ A * (3 * s ^ 2) ^ ξ := by
    have h2a : max (ε ^ β) ‖vertexPoint ε η x - vertexPoint ε η y‖ ^ ξ ≤ (3 * s ^ 2) ^ ξ :=
      Real.rpow_le_rpow hmax0 hmax hξ.le
    have h2b : A * (⨆ a' : cellVertices ε η (ball z s), |f a'|) ≤ A * 1 :=
      mul_le_mul_of_nonneg_left hsup hA.le
    calc A * (⨆ a' : cellVertices ε η (ball z s), |f a'|) *
          max (ε ^ β) ‖vertexPoint ε η x - vertexPoint ε η y‖ ^ ξ
        ≤ (A * 1) * (3 * s ^ 2) ^ ξ :=
          mul_le_mul h2b h2a (Real.rpow_nonneg hmax0 _) (by positivity)
      _ = A * (3 * s ^ 2) ^ ξ := by ring
  have h3 : (3 * s ^ 2) ^ ξ = (6 * s) ^ ξ * (s / 2) ^ ξ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have h4 : |f x - f y| * (s / 2) ^ ξ ≤ A * (6 * s) ^ ξ * (s / 2) ^ ξ := by
    calc |f x - f y| * (s / 2) ^ ξ ≤ |f x - f y| * infDist (vertexPoint ε η x) (frontier (ball z s)) ^ ξ :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ A * (3 * s ^ 2) ^ ξ := hk.trans h2
      _ = A * (6 * s) ^ ξ * (s / 2) ^ ξ := by rw [h3]; ring
  have h5 : |f x - f y| ≤ A * (6 * s) ^ ξ :=
    le_of_mul_le_mul_right h4 (Real.rpow_pos_of_pos (by positivity) _)
  rw [← hfeq x, ← hfeq y]
  calc |f x - f y| ≤ A * (6 * s) ^ ξ := h5
    _ = A * 6 ^ ξ * s ^ ξ := by rw [Real.mul_rpow (by norm_num) hs0.le]; ring

/-- Two values of a probability measure lie at distance at most `1`. -/
theorem abs_real_sub_le_one (μ ν : Measure (ℕ → ℤ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (ℕ → ℤ)) : |μ.real E - ν.real E| ≤ 1 := by
  have h1 : μ.real E ≤ 1 := measureReal_le_one
  have h2 : ν.real E ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ μ.real E := measureReal_nonneg
  have h4 : 0 ≤ ν.real E := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- **Berestycki–Gwynne (2020), Lemma 6.13, first part.**  Given the corrected discrete Hölder estimate and the cell size
estimate: for `γ ∈ (0,2)` and `ρ ∈ (0,1)` there are `ξ, A > 0` such that for every `δ ∈ (0,1)`, with polynomially high
probability as `ε → 0` (in every valid environment), for each `z ∈ B_ρ` and each `x, y ∈ V^ε(B_δ(z))` and each vertex set `T`,
the probabilities that the first vertex outside the interior vertex set of `B_{√δ}(z)` lies in `T` differ by at most `A δ^ξ`
for the walks started at `x` and at `y`; i.e. the total variation distance between the laws of the first exit vertices is
at most `A δ^ξ`. -/
theorem hittingVertex_tv_le (𝒮 : SpaceFillingSLEModel) (h28 : CellSizeEstimateStmt 𝒮)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ z ∈ ball (0 : ℂ) ρ,
        ∀ x ∈ cellVertices ε (S.η ω) (ball z δ), ∀ y ∈ cellVertices ε (S.η ω) (ball z δ),
          ∀ T : Set ℤ,
          |(srwLaw (S.mult ε ω) x).real
              {X | vExitPosition (interiorCellVertices ε (S.η ω) (ball z (Real.sqrt δ))) X ∈ T} -
            (srwLaw (S.mult ε ω) y).real
              {X | vExitPosition (interiorCellVertices ε (S.η ω) (ball z (Real.sqrt δ))) X ∈ T}| ≤
            A * δ ^ ξ} := by
  intro γ hγ hγ2 ρ hρ hρ1
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : ℝ, ρ₀ = (1 + ρ) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = (1 + ρ₀) / 2 := ⟨_, rfl⟩
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀1 : ρ₀ < 1 := by rw [hρ₀def]; linarith
  have hρρ₀ : ρ < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁def]; linarith
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁def]; linarith
  have hρ₀ρ₁ : ρ₀ < ρ₁ := by rw [hρ₁def]; linarith
  obtain ⟨ξ, A, β, hξ, hξ1, hA, hβ, hβ1, hholder⟩ := h32 γ hγ hγ2 ρ₀ hρ₀0 hρ₀1
  obtain ⟨ξ', C, hξ', hξ'1, hC, hreg⟩ := hholder 1 1 one_pos le_rfl one_pos
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀ : ℝ, s₀ = ρ₀ - ρ := ⟨_, rfl⟩
  have hs₀ : 0 < s₀ := by rw [hs₀def]; linarith
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = min (1 / 16) (s₀ ^ 2) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact lt_min (by norm_num) (by positivity)
  refine ⟨ξ / 2, A * 6 ^ ξ + (δ₀ ^ (ξ / 2))⁻¹, by positivity, by positivity, ?_⟩
  intro δ hδ0 hδ1 Ω _ S hS
  by_cases hδ : δ₀ ≤ δ
  · -- large `δ`: the bound is trivial
    refine ExitTimeLowerBound.polyHighProb_of_ae_of_small (E := fun _ => (Set.univ : Set Ω)) (G := Set.univ)
      ⟨1, one_pos, 0, 1, one_pos, fun r _ _ => by simp⟩ (ae_of_all _ fun _ => trivial)
      (r₁ := 1) one_pos ?_
    intro r hr hr1 ω _ z hz x hx y hy T
    refine (abs_real_sub_le_one _ _ _).trans ?_
    have hpow : δ₀ ^ (ξ / 2) ≤ δ ^ (ξ / 2) :=
      Real.rpow_le_rpow hδ₀.le hδ (by positivity)
    have hpos : 0 < δ₀ ^ (ξ / 2) := Real.rpow_pos_of_pos hδ₀ _
    have hge : 1 ≤ (δ₀ ^ (ξ / 2))⁻¹ * δ ^ (ξ / 2) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpos]
      linarith
    have hAnn : 0 ≤ (A * 6 ^ ξ) * δ ^ (ξ / 2) := by positivity
    nlinarith
  · -- small `δ`
    replace hδ := not_le.1 hδ
    have hδ16 : δ < 1 / 16 := lt_of_lt_of_le hδ (by rw [hδ₀def]; exact min_le_left _ _)
    have hδs : δ < s₀ ^ 2 := lt_of_lt_of_le hδ (by rw [hδ₀def]; exact min_le_right _ _)
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt δ := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hδ0
    have hss : s ^ 2 = δ := by rw [hsdef]; exact Real.sq_sqrt hδ0.le
    have hs4 : s ≤ 1 / 4 := by nlinarith
    have hss0 : s ≤ s₀ := by nlinarith
    have hss1 : s ≤ 1 := by linarith
    obtain ⟨a, ha, halim, hcellev⟩ := exists_vanishing_closedBall_cellRadius 𝒮 h28 (ρ := ρ₁)
      (r := ρ₀) (z := 0) hγ hγ2 hρ₁0 hρ₁1 hρ₀0
      (by
        intro p hp
        rw [mem_ball_zero_iff] at hp ⊢
        linarith) S hS
    have hEh := hreg Ω S hS
    have hG : ∀ᵐ ω ∂S.P, ω ∈ {ω : Ω | Continuous (S.η ω) ∧
        Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
        ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)} := by
      filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
        hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hη hp hlf
      exact ⟨hη.1, hp, hlf⟩
    have hβlim : Tendsto (fun ε : ℝ => ε ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuous_rpow_const hβ.le).tendsto 0
      rw [Real.zero_rpow hβ.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ a < δ / 4 ∧ ε ^ β < δ ∧ ε < 1 :=
      (halim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 4))).and
        ((hβlim.eventually (Iio_mem_nhds hδ0)).and
          (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)))
    obtain ⟨r₁, hr₁, hr₁sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ExitTimeLowerBound.polyHighProb_of_ae_of_small (FirstPass36.polyHighProb_inter hEh hcellev) hG hr₁ ?_
    rintro r hr hrr ω ⟨⟨hωH, hωC⟩, hωη, hωp, hωlf⟩ z hz x hx y hy T
    obtain ⟨hra, hrβ, hr1⟩ := hr₁sub ⟨hr, hrr⟩
    have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
    have hball : ball z s ⊆ ball (0 : ℂ) ρ₀ := by
      intro p hp
      have h1 : dist p z < s := mem_ball.1 hp
      have h3 := dist_triangle p z 0
      simp only [dist_zero_right] at h3
      rw [mem_ball_zero_iff]
      linarith
    have hcell : ∀ v ∈ cellVertices r (S.η ω) (ball z (s ^ 2)), ∀ p ∈ cell r (S.η ω) v,
        dist (vertexPoint r (S.η ω) v) p < s ^ 2 / 4 := by
      intro v hv p hp
      have hv' : v ∈ cellVertices r (S.η ω) (closedBall (0 : ℂ) ρ₀) := by
        obtain ⟨q, hqc, hqb⟩ := hv
        refine ⟨q, hqc, ?_⟩
        have hq : q ∈ ball z s := mem_ball.2 (lt_of_lt_of_le (mem_ball.1 hqb) (by nlinarith))
        exact ball_subset_closedBall (hball hq)
      have := hωC v hv' p hp
      rw [hss]
      linarith
    have hβ' : r ^ β ≤ s ^ 2 := by rw [hss]; exact hrβ.le
    have hH : ∀ f : ℤ → ℝ,
        (∀ v ∈ interiorCellVertices r (S.η ω) (ball z s), matedLaplacian (S.mult r ω) f v = 0) →
        ∀ a ∈ interiorCellVertices r (S.η ω) (ball z s), ∀ b ∈ cellVertices r (S.η ω) (ball z s),
          |f a - f b| * infDist (vertexPoint r (S.η ω) a) (frontier (ball z s)) ^ ξ ≤
            A * (⨆ a' : cellVertices r (S.η ω) (ball z s), |f a'|) *
              max (r ^ β) ‖vertexPoint r (S.η ω) a - vertexPoint r (S.η ω) b‖ ^ ξ :=
      fun f hharm => (hωH (ball z s) f hball isOpen_ball
        ((convex_ball z s).isConnected ⟨z, mem_ball_self hs0⟩) hharm).1
    have hcore := tv_le_of_holder (hωlf r hr) (S.mult_succ_ne_zero hr.le ω) hr hωη hωp hs0 hs4 hξ hA
      hcell hβ' hH (by rw [hss]; exact hx) (by rw [hss]; exact hy) T
    have hsq : Real.sqrt δ = s := hsdef.symm
    have hsξ : s ^ ξ = δ ^ (ξ / 2) := by
      rw [hsdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ0.le]
      congr 1
      ring
    rw [hsq]
    refine hcore.trans ?_
    rw [hsξ]
    have hpos : 0 ≤ δ ^ (ξ / 2) := Real.rpow_nonneg hδ0.le _
    have hinv : 0 ≤ (δ₀ ^ (ξ / 2))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hδ₀.le _)
    rw [add_mul]
    exact le_add_of_nonneg_right (mul_nonneg hinv hpos)

end HittingVertexTV
end MatedCRT
