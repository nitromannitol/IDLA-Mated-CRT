import MatedCRT.FirstPass.Derived.ExitCouplingEvent
import MatedCRT.FirstPass.Derived.ExitCouplingBoundaryEvent
import MatedCRT.FirstPass.Derived.ExitBeforeBallHitEnv

/-!
# Proposition 6.12 of Berestycki-Gwynne: the case near the sphere, and the full event

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Proposition 6.12, Step 3.  The event-level union of `ExitCouplingEvent` covers
the starting points `z ∈ B_{ρ₀ - √δ}`.  For two vertices whose embedded points are `δ`-close and one of which
lies in `B_{ρ₀} \ B_{ρ₀ - √δ}`, both lie in `B_{ρ₀} \ B_{ρ₀ - 2√δ}` and by the last assertion of Lemma 6.13
(`ExitBeforeBallHitEnv.exitBeforeBallHit_polyHighProb_cells`, with `2√δ` in place of `δ`) each walk stays, up to
its exit time from `V^ε(B_{ρ₀})`, in cells inside a disc of radius `√(2√δ)` about its starting point with
probability at least `1 - A (2√δ)^ξ`.  The near-boundary comparison of laws
(`ExitCouplingBoundary.levyProkhorovEDist_stoppedInterp_le_of_cells_event`) then bounds the Lévy-Prokhorov
distance.  The two cases together give the vertex form of Proposition 6.12:

* `exists_small_boundary_parameters`: the parameter choice (`T₀`, `δ₀`) for the near-boundary case;
* `exists_mid`: two nearby points of a ball have a common point of the ball nearby;
* `limLimSmall_levyProkhorovEDist_stoppedWalk_vertices`: for every `r > 0`, the event that two vertices of
  `V^ε(B_{ρ₀})` whose embedded points are at distance at most `δ` have stopped walks (stopped at the exit of the
  interior vertices of `B_{ρ₀}`) with laws at Lévy-Prokhorov distance `> r` is negligible as `ε → 0` and then
  `δ → 0`.

The localization event of Lemma 6.13 enters as an explicit hypothesis (the conclusion of
`exitBeforeBallHit_polyHighProb_cells`).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingBoundaryUnion

open MeasureTheory Set Metric Filter LatticeProb LatticeProb.Gauss
open scoped ENNReal NNReal Topology
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingQuenched MatedCRT.ExitCouplingCells
  MatedCRT.ExitCouplingGlue MatedCRT.ExitCouplingNoShortTravel MatedCRT.ExitCouplingMarkov
  MatedCRT.ExitCouplingHq
  MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived MatedCRT.InteriorCellGeometry

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- A property that holds for all `δ` close to `0⁺` holds on an interval `(0, δ₀)`. -/
theorem exists_delta_of_eventually {P : ℝ → Prop} (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), P δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → P δ := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ₀, hδ₀, h'⟩ := h
  exact ⟨δ₀, hδ₀, fun δ hδ hδlt =>
    h' (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact hδlt) hδ⟩

/-- **Choice of the parameters near the sphere.**  For `A`, `ξ, r > 0` there are `T₀` and `δ₀ > 0` such that for
`0 < δ < δ₀`: `δ < 1`, `T₀ (2 R + δ) + exp (-T₀) < r` with `R = √(2 √δ)`, and `2 A (2 √δ)^ξ ≤ r`. -/
theorem exists_small_boundary_parameters {A ξ r : ℝ} (hξ : 0 < ξ) (hr : 0 < r) :
    ∃ T₀ : ℝ≥0, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → δ < 1 ∧
      (T₀ : ℝ) * (2 * Real.sqrt (2 * Real.sqrt δ) + δ) + Real.exp (-(T₀ : ℝ)) < r ∧
      2 * (A * (2 * Real.sqrt δ) ^ ξ) ≤ r := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ≥0, Real.exp (-(T₀ : ℝ)) ≤ r / 4 := by
    refine ⟨(Real.log (4 / r)).toNNReal, ?_⟩
    have h4 : 0 < 4 / r := by positivity
    calc Real.exp (-(((Real.log (4 / r)).toNNReal : ℝ≥0) : ℝ))
        ≤ Real.exp (-Real.log (4 / r)) :=
          Real.exp_le_exp.2 (neg_le_neg (by rw [Real.coe_toNNReal']; exact le_max_left _ _))
      _ = r / 4 := by rw [Real.exp_neg, Real.exp_log h4]; field_simp
  have hc1 : Continuous (fun δ : ℝ => (T₀ : ℝ) * (2 * Real.sqrt (2 * Real.sqrt δ) + δ)) :=
    continuous_const.mul (((Real.continuous_sqrt.comp
      (continuous_const.mul Real.continuous_sqrt)).const_smul (2 : ℝ)).add continuous_id)
  have hc2 : Continuous (fun δ : ℝ => 2 * (A * (2 * Real.sqrt δ) ^ ξ)) :=
    continuous_const.mul (continuous_const.mul
      ((Real.continuous_rpow_const hξ.le).comp (continuous_const.mul Real.continuous_sqrt)))
  have h1 : Tendsto (fun δ : ℝ => (T₀ : ℝ) * (2 * Real.sqrt (2 * Real.sqrt δ) + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hc1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have h2 : Tendsto (fun δ : ℝ => 2 * (A * (2 * Real.sqrt δ) ^ ξ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hc2.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.zero_rpow hξ.ne'] using this
  have e1 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < 1 := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  have e2 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), (T₀ : ℝ) * (2 * Real.sqrt (2 * Real.sqrt δ) + δ) < r / 2 :=
    h1.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 2 * (A * (2 * Real.sqrt δ) ^ ξ) < r :=
    h2.eventually (gt_mem_nhds hr)
  obtain ⟨δ₀, hδ₀, h⟩ := exists_delta_of_eventually (e1.and (e2.and e3))
  refine ⟨T₀, δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h δ hδ hδlt
  exact ⟨a1, by linarith, a3.le⟩

/-- Two points of the ball `B_ρ(0)` at distance at most `δ` are both at distance `< δ` from a common point of
the ball. -/
theorem exists_mid {a b : ℂ} {ρ δ : ℝ} (ha : ‖a‖ < ρ) (hb : ‖b‖ < ρ) (hab : dist a b ≤ δ)
    (hδ : 0 < δ) : ∃ z ∈ ball (0 : ℂ) ρ, dist a z < δ ∧ dist b z < δ := by
  refine ⟨(a + b) / 2, ?_, ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have := norm_add_le a b
    linarith
  · have : a - (a + b) / 2 = (a - b) / 2 := by ring
    rw [dist_eq_norm, this, norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, ← dist_eq_norm]
    linarith
  · have : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [dist_eq_norm, this, norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, ← dist_eq_norm, dist_comm]
    linarith

/-- **Proposition 6.12 of Berestycki-Gwynne at the event level, vertex form.**  Fix `0 < ρ₀ < ρ₁ < 1` and
`r > 0`.  Under the hypotheses of `ExitCouplingEvent.limLimSmall_levyProkhorovEDist_stoppedWalk` and the
localization event of Lemma 6.13 (`hbd`), for every valid environment the event that two vertices of `V^ε(B_{ρ₀})`,
whose embedded points are at distance at most `δ`, have walks stopped at the exit of the interior vertices of
`B_{ρ₀}` whose laws are at Lévy-Prokhorov distance `> r` is negligible as `ε → 0` and then `δ → 0`. -/
theorem limLimSmall_levyProkhorovEDist_stoppedWalk_vertices {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ρ0 ρ1 : ℝ} (hρ0 : 0 < ρ0) (hρ0ρ1 : ρ0 < ρ1) (hρ1 : ρ1 < 1)
    (h632 : ∀ ℓ : ℝ, 1 < ℓ → ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ1 - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ)
    (h636 : ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun s ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X ≤
              succExit (fun w => interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) (2 * s)))
                ⌊(2 * s) ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ (2 * s))}))
    (hbd : ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω)
          (ball (0 : ℂ) ρ0 \ ball (0 : ℂ) (ρ0 - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X <
            vHitTime (cellVertices ε (S.η ω)
              (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}})
    {r : ℝ} (hr : 0 < r) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    LimLimSmall S.P (fun δ ε => {ω | ∃ x y : ℤ, vertexPoint ε (S.η ω) x ∈ ball (0 : ℂ) ρ0 ∧
      vertexPoint ε (S.η ω) y ∈ ball (0 : ℂ) ρ0 ∧
      dist (vertexPoint ε (S.η ω) x) (vertexPoint ε (S.η ω) y) ≤ δ ∧
      ENNReal.ofReal r < levyProkhorovEDist
        ((srwLaw (S.mult ε ω) x).map
          (stoppedInterp (vertexPoint ε (S.η ω)) (ε⁻¹).toNNReal
            (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0))))
        ((srwLaw (S.mult ε ω) y).map
          (stoppedInterp (vertexPoint ε (S.η ω)) (ε⁻¹).toNNReal
            (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0))))}) := by
  obtain ⟨ξ, A, hξ, hA, hbd'⟩ := hbd
  obtain ⟨T₀, δ₁, hδ₁, hnum⟩ := exists_small_boundary_parameters (A := A) hξ hr
  have hint := ExitCouplingEvent.limLimSmall_levyProkhorovEDist_stoppedWalk h28 h32 h213 h214 h219
    hγ hγ2 hρ0 hρ0ρ1 hρ1 h632 h636 hr Ω S hS
  have hsqrt : Tendsto (fun δ : ℝ => 2 * Real.sqrt δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).const_mul 2
    rw [Real.sqrt_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hbdry := (LimLimSmall.of_polyHighProb (P := S.P)
    (E := fun δ ε => {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0 \ ball (0 : ℂ) (ρ0 - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X <
            vHitTime (cellVertices ε (S.η ω)
              (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}})
    (fun δ hδ hδ1 => hbd' δ hδ hδ1 Ω S hS)).comp_delta (φ := fun δ : ℝ => 2 * Real.sqrt δ)
    (fun δ hδ => by positivity) hsqrt
  refine LimLimSmall.mono_of_small_ae (hint.union hbdry) ⟨δ₁, hδ₁, fun δ hδ hδlt =>
    ⟨1, one_pos, fun ε hε _ => ae_of_all _ fun ω hω => ?_⟩⟩
  obtain ⟨x, y, hx, hy, hxy, hlt⟩ := hω
  by_contra hG
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, not_or, not_not] at hG
  obtain ⟨hI, hB⟩ := hG
  obtain ⟨hδ1, hr1, ha1⟩ := hnum δ hδ hδlt
  have hmem : ∀ k : ℤ, vertexPoint ε (S.η ω) k ∈ cell ε (S.η ω) k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hsq0 := Real.sqrt_nonneg δ
  have hxn : ‖vertexPoint ε (S.η ω) x‖ < ρ0 := mem_ball_zero_iff.1 hx
  have hyn : ‖vertexPoint ε (S.η ω) y‖ < ρ0 := mem_ball_zero_iff.1 hy
  by_cases hin : ‖vertexPoint ε (S.η ω) x‖ < ρ0 - Real.sqrt δ ∧
      ‖vertexPoint ε (S.η ω) y‖ < ρ0 - Real.sqrt δ
  · -- both away from the sphere: the event of `ExitCouplingEvent`
    obtain ⟨z, hz, hxz, hyz⟩ := exists_mid hin.1 hin.2 hxy hδ
    exact hI ⟨z, hz, x, ⟨vertexPoint ε (S.η ω) x, hmem x, mem_ball.2 hxz⟩, y,
      ⟨vertexPoint ε (S.η ω) y, hmem y, mem_ball.2 hyz⟩, hlt⟩
  · -- near the sphere: both vertices are in `V^ε(B_{ρ₀} \ B_{ρ₀ - 2√δ})`
    have hδsq : δ ≤ Real.sqrt δ := by
      have h1 : Real.sqrt δ ≤ 1 := by rw [Real.sqrt_le_one]; exact hδ1.le
      calc δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ.le).symm
        _ ≤ Real.sqrt δ * 1 := mul_le_mul_of_nonneg_left h1 hsq0
        _ = Real.sqrt δ := mul_one _
    have hnorm : |‖vertexPoint ε (S.η ω) x‖ - ‖vertexPoint ε (S.η ω) y‖| ≤ δ :=
      (abs_norm_sub_norm_le _ _).trans (by rw [← dist_eq_norm]; exact hxy)
    rw [abs_le] at hnorm
    have hx2 : ρ0 - 2 * Real.sqrt δ ≤ ‖vertexPoint ε (S.η ω) x‖ := by
      by_cases hxx : ‖vertexPoint ε (S.η ω) x‖ < ρ0 - Real.sqrt δ
      · have hyy : ρ0 - Real.sqrt δ ≤ ‖vertexPoint ε (S.η ω) y‖ := by
          by_contra hh; exact hin ⟨hxx, not_le.1 hh⟩
        linarith [hnorm.1, hnorm.2]
      · linarith [not_lt.1 hxx]
    have hy2 : ρ0 - 2 * Real.sqrt δ ≤ ‖vertexPoint ε (S.η ω) y‖ := by
      by_cases hyy : ‖vertexPoint ε (S.η ω) y‖ < ρ0 - Real.sqrt δ
      · have hxx : ρ0 - Real.sqrt δ ≤ ‖vertexPoint ε (S.η ω) x‖ := by
          by_contra hh; exact hin ⟨not_le.1 hh, hyy⟩
        linarith [hnorm.1, hnorm.2]
      · linarith [not_lt.1 hyy]
    have hxA : x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0 \ ball (0 : ℂ) (ρ0 - 2 * Real.sqrt δ)) :=
      ⟨vertexPoint ε (S.η ω) x, hmem x, hx, fun h => by
        rw [mem_ball_zero_iff] at h; linarith⟩
    have hyA : y ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0 \ ball (0 : ℂ) (ρ0 - 2 * Real.sqrt δ)) :=
      ⟨vertexPoint ε (S.η ω) y, hmem y, hy, fun h => by
        rw [mem_ball_zero_iff] at h; linarith⟩
    have hbx := hB x hxA
    have hby := hB y hyA
    have hnn : 0 ≤ A * (2 * Real.sqrt δ) ^ ξ := by positivity
    have hm : 0 < (ε⁻¹).toNNReal := by simpa using inv_pos.2 hε
    let E : ℤ → Set (ℕ → ℤ) := fun c => {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X <
        vHitTime (cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) c)
          (Real.sqrt (2 * Real.sqrt δ))))) X ∧
      ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X →
        cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) c) (Real.sqrt (2 * Real.sqrt δ))}
    have hE : ∀ c : ℤ, E c ⊆ {X | ∀ n : ℕ, (n : ℕ∞) ≤
        vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0)) X →
        cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) c) (Real.sqrt (2 * Real.sqrt δ))} :=
      fun c X hX => hX.2
    have hle := ExitCouplingBoundary.levyProkhorovEDist_stoppedInterp_le_of_cells_event
      (mult := S.mult ε ω) (η := S.η ω) hε.le hm
      (A := interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ0))
      (B := cellVertices ε (S.η ω) (ball (0 : ℂ) ρ0))
      (interiorCellVertices_subset ε (S.η ω) _) (x := x) (y := y)
      (R := Real.sqrt (2 * Real.sqrt δ)) (d := δ) hxy T₀ (A * (2 * Real.sqrt δ) ^ ξ).toNNReal r.toNNReal
      (Ex := E x) (Ey := E y) (hE x) (hE y)
      (by rw [Real.coe_toNNReal _ hnn]; exact hbx) (by rw [Real.coe_toNNReal _ hnn]; exact hby)
      (by rw [Real.coe_toNNReal _ hr.le]; exact hr1)
      (by
        have : ((A * (2 * Real.sqrt δ) ^ ξ).toNNReal + (A * (2 * Real.sqrt δ) ^ ξ).toNNReal : ℝ≥0) ≤
            r.toNNReal := by
          rw [← NNReal.coe_le_coe]
          push_cast
          rw [Real.coe_toNNReal _ hnn, Real.coe_toNNReal _ hr.le]
          linarith
        exact this)
    exact absurd hlt (not_lt.2 hle)

end ExitCouplingBoundaryUnion
end MatedCRT

#print axioms MatedCRT.ExitCouplingBoundaryUnion.exists_small_boundary_parameters
#print axioms MatedCRT.ExitCouplingBoundaryUnion.exists_mid
#print axioms MatedCRT.ExitCouplingBoundaryUnion.limLimSmall_levyProkhorovEDist_stoppedWalk_vertices
