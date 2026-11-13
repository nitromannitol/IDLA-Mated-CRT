import MatedCRT.FirstPass.Derived.ExitTimeLowerLemma611
import MatedCRT.FirstPass.Derived.ExitTimeLowerLemma67Strong

/-!
# Lemma 6.11 of Berestycki-Gwynne with a superpolynomial function and thresholds independent of the environment

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Lemma 6.11, in the strong quantifier order: the superpolynomial function `ψ` and the
threshold `δ₀` depend only on the model, `γ`, `χ`, `ρ` (and the tolerance `θ` for `δ₀`), not on the environment;
only the threshold `ε₀` depends on the environment. This is the order in which BG20 uses Lemma 6.11 for the lower
bound of (1.8) on `m_ε`, where a single constant `c₁ = c₁(γ)` must serve every environment.

The proof is the one of `exitTimeLowerTail_611` (BG20, pp. 43-44), with two changes:
* Lemma 6.7 enters in its strong form `exitTimeLowerTail_strong` (threshold `δ₀` before the environment);
* the estimate (6.32), the conclusion of BG20 Lemma 6.9, enters in the form printed there: its superpolynomial
  function `ψ₀` depends only on `ζ`, `ℓ`, `γ` (and the radius `ρ`), not on the environment (hypothesis `h632`).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss
open scoped ENNReal

/-- **Berestycki-Gwynne, Lemma 6.11** (arXiv:2003.10320, p. 44), with `ψ` and `δ₀` independent of the
environment. Let `0 < γ < 2`, `χ > 2(2 + γ)/(2 - γ)` and `ρ ∈ (0, 1)`. There is a superpolynomial function `ψ`
(BG20 Definition 6.4) such that for every `θ > 0` there is `δ₀ > 0` such that for each `δ ∈ (0, δ₀)` and each valid
environment there is `ε₀ > 0` with: for `ε ∈ (0, ε₀)`, outside an event of probability at most `θ`, every vertex
`x ∈ V^ε(B_{ρ - δ})` satisfies `P_x[τ_{B_δ(η(x))} < ε⁻¹ δ^χ] ≤ ψ(δ)`, where `τ_{B_δ(η(x))}` is the exit time from
`V^ε(B_δ(η(x)))`.

Inputs: the Green kernel lower bound `h213` (Lemma 2.13), the exit time moment bound `h214` (Lemma 2.14, first
conjunct) and `h632`, the estimate (6.32) (the conclusion of BG20 Lemma 6.9) as printed: for `ℓ > 1` and
`ζ ∈ (0, 1)` there is a superpolynomial `ψ₀`, depending only on `ζ`, `ℓ`, `γ` (and `ρ`), such that for every valid
environment and each `δ ∈ (0, 1)`, with probability tending to `1` as `ε → 0`, every `x ∈ V^ε(B_{ρ - δ})` satisfies
`P_x[τ_{B_δ(η(x))} < σ_K] ≤ ψ₀(δ)`, where `K = ⌊δ^{-(2-ζ)(ℓ-1)}⌋` and `σ_k` are the successive exit times from the
sets `V^ε(B_{δ^ℓ}(η(X_{σ_{k-1}})))`. -/
theorem exitTimeLowerTail_611_strong {𝒮 : SpaceFillingSLEModel} (h213 : GreenKernelLowerBoundStmt 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ}
    (hχ : 2 * (2 + γ) / (2 - γ) < χ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h632 : ∀ ℓ : ℝ, 1 < ℓ → ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ) :
    ∃ ψ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧ ψ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ θ : ℝ, 0 < θ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
            srwLaw (S.mult ε ω) x {y |
              (vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y : ℝ≥0∞) <
                ENNReal.ofReal (ε⁻¹ * δ ^ χ)} ≤ ENNReal.ofReal (ψ δ)}ᶜ ≤ ENNReal.ofReal θ := by
  classical
  -- the exponents `ℓ`, `b`, `a`, `ζ` of the proof
  have h4 : 0 < 4 - γ ^ 2 := by nlinarith
  have h2γ : 0 < 2 - γ := by linarith
  have hχ' : 2 * (2 + γ) < χ * (2 - γ) := by rwa [div_lt_iff₀ h2γ] at hχ
  have hLχ : 4 / (4 - γ ^ 2) < 2 * χ / (2 + γ) ^ 2 := by
    rw [div_lt_div_iff₀ h4 (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hχ' (by linarith : (0 : ℝ) < 2 * (2 + γ))]
  obtain ⟨ℓ, hℓL, hℓχ⟩ := exists_between hLχ
  have hℓ4 : 4 < ℓ * (4 - γ ^ 2) := by rwa [div_lt_iff₀ h4] at hℓL
  have hℓχ' : (2 + γ) ^ 2 * ℓ < 2 * χ := by
    rw [lt_div_iff₀ (by positivity)] at hℓχ; linarith
  have hℓ1 : 1 < ℓ := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_nonneg (sub_nonneg.2 hcon) h4.le, sq_nonneg γ]
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨b, hb1, hb2⟩ := exists_between (show (2 + γ) ^ 2 * ℓ / 2 < χ by linarith)
  obtain ⟨a, ha1, ha2⟩ := exists_between (show ℓ * γ ^ 2 / 2 < 2 * (ℓ - 1) by nlinarith)
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha1
  have hd : 0 < (2 * (ℓ - 1) - a) / (ℓ - 1) := div_pos (by linarith) (by linarith)
  obtain ⟨ζ, hζ0, hζ⟩ := exists_between (lt_min one_pos hd)
  have hζ1 : ζ < 1 := hζ.trans_le (min_le_left _ _)
  have hζa : ζ * (ℓ - 1) < 2 * (ℓ - 1) - a := by
    have h := hζ.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by linarith)] at h
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 - ζ) * (ℓ - 1) - a := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; nlinarith
  -- the superpolynomial function `ψ = ψ₀ + exp(2 - δ^{-c})`
  obtain ⟨ψ₀, ⟨hψ₀0, hψ₀z, hψ₀t⟩, h632'⟩ := h632 ℓ hℓ1 ζ hζ0 hζ1
  refine ⟨fun δ => ψ₀ δ + if 0 < δ then Real.exp (2 - δ ^ (-c)) else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro δ hδ
    refine add_nonneg (hψ₀0 δ hδ) ?_
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  · simp [hψ₀z]
  · intro p hp
    have h1 := (hψ₀t p hp).add (tendsto_rpow_neg_mul_exp_two_sub (p := p) hc0)
    rw [add_zero] at h1
    exact h1.congr fun δ => (mul_add _ _ _).symm
  intro θ hθ
  have hθ3 : 0 < θ / 3 := by positivity
  -- the thresholds in `δ`
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = (1 + ρ) / 2 := ⟨_, rfl⟩
  obtain ⟨δ₇, hδ₇, h67⟩ := exitTimeLowerTail_strong h213 h214 hγ hγ2 hℓ0 ha1 hb1
    (show 0 < ρ₁ by rw [hρ₁]; linarith) (show ρ₁ < 1 by rw [hρ₁]; linarith) hθ3
  obtain ⟨δ₁, hδ₁, hδ₁all⟩ := LatticeProb.LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT
    (eventually_rpow_le_const hℓ0 (show (0 : ℝ) < (1 - ρ) / 4 by linarith))
  refine ⟨min (min δ₇ δ₁) 1, lt_min (lt_min hδ₇ hδ₁) one_pos, fun δ hδ hδδ₀ Ω _ S hS => ?_⟩
  have hδ7 : δ < δ₇ := hδδ₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδℓ : δ ^ ℓ ≤ (1 - ρ) / 4 :=
    hδ₁all δ hδ (hδδ₀.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hδ1 : δ < 1 := hδδ₀.trans_le (min_le_right _ _)
  -- the thresholds in `ε`
  obtain ⟨ε₇, hε₇, h67δ⟩ := h67 δ hδ hδ7 Ω S hS
  obtain ⟨ε₂, hε₂, h632δ⟩ := h632' Ω S hS δ hδ hδ1 (θ / 3) hθ3
  obtain ⟨ζc, hζc⟩ : ∃ ζc : ℝ, ζc = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  have hζc0 : 0 < ζc := by rw [hζc]; positivity
  have hζc1 : ζc < 1 := by rw [hζc, div_lt_one (by positivity)]; nlinarith
  have hβc : 2 / (2 + γ) ^ 2 - ζc = ζc := by rw [hζc]; ring
  have ECs := cellSizeEstimateStmt_holds 𝒮 γ hγ hγ2 ζc ρ hζc0 hζc1 hρ hρ1 Ω S hS
  have hχb : δ ^ χ < δ ^ b := Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 hb2
  obtain ⟨ε₃, hε₃, hε₃all⟩ := LatticeProb.LQG.LQGMeasureNonatomicMass.exists_pos_of_eventually_nhdsGT
    ((eventually_rpow_le_const hζc0 (show (0 : ℝ) < (1 - ρ) / 4 by linarith)).and
      (polyHighProb_eventually_compl_le ECs hθ3))
  refine ⟨min (min ε₇ ε₂) (min ε₃ (δ ^ b - δ ^ χ)),
    lt_min (lt_min hε₇ hε₂) (lt_min hε₃ (by linarith)), fun ε hε hεε₀ => ?_⟩
  have hε7 : ε < ε₇ := hεε₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ε < ε₂ := hεε₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε3 : ε < ε₃ := hεε₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < δ ^ b - δ ^ χ := hεε₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hεc, hPC⟩ := hε₃all ε hε hε3
  -- the integer time threshold `g = ⌈ε⁻¹ δ^χ⌉ ≤ ε⁻¹ δ^b`
  obtain ⟨g, hg⟩ : ∃ g : ℕ, g = ⌈ε⁻¹ * δ ^ χ⌉₊ := ⟨_, rfl⟩
  have hrg : ε⁻¹ * δ ^ χ ≤ (g : ℝ) := by rw [hg]; exact Nat.le_ceil _
  have hgb : (g : ℝ) ≤ ε⁻¹ * δ ^ b := by
    have h1 : (g : ℝ) < ε⁻¹ * δ ^ χ + 1 := by
      rw [hg]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ ε⁻¹ * (δ ^ b - δ ^ χ) := by
      rw [le_inv_mul_iff₀ hε, mul_one]; linarith
    have h3 : ε⁻¹ * (δ ^ b - δ ^ χ) = ε⁻¹ * δ ^ b - ε⁻¹ * δ ^ χ := mul_sub _ _ _
    linarith
  -- the number of successive exits `K = ⌊δ^{-(2-ζ)(ℓ-1)}⌋` and the bound (6.35) on `(1 - δ^a)^{K-1}`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    rw [hK, Nat.one_le_floor_iff]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le
      (neg_nonpos.2 (mul_pos (by linarith) (by linarith)).le)
  have hda1 : δ ^ a ≤ 1 := Real.rpow_le_one hδ.le hδ1.le ha0.le
  have hpow : (1 - δ ^ a) ^ (K - 1) ≤ Real.exp (2 - δ ^ (-c)) := by
    have h1 : 1 - δ ^ a ≤ Real.exp (-δ ^ a) := by
      have := Real.add_one_le_exp (-δ ^ a); linarith
    have h2 : (1 - δ ^ a) ^ (K - 1) ≤ Real.exp (-δ ^ a) ^ (K - 1) :=
      pow_le_pow_left₀ (by linarith) h1 _
    rw [← Real.exp_nat_mul] at h2
    refine h2.trans (Real.exp_le_exp.2 ?_)
    have hfloor : δ ^ (-((2 - ζ) * (ℓ - 1))) - 2 ≤ ((K - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hK1, Nat.cast_one, hK]
      have := Nat.sub_one_lt_floor (δ ^ (-((2 - ζ) * (ℓ - 1))))
      linarith
    have hmul : δ ^ a * δ ^ (-((2 - ζ) * (ℓ - 1))) = δ ^ (-c) := by
      rw [← Real.rpow_add hδ, hc]; congr 1; ring
    have h3 := mul_le_mul_of_nonneg_left hfloor (Real.rpow_pos_of_pos hδ a).le
    linarith
  -- the three events
  have hθeq : θ = θ / 3 + θ / 3 + θ / 3 := by ring
  rw [hθeq]
  refine measure_compl_le_of_inter_subset ?_ (by linarith) hθ3.le
    (measure_compl_le_of_inter_subset subset_rfl hθ3.le hθ3.le (h67δ ε hε hε7) (h632δ ε hε hε2)) hPC
  rintro ω ⟨⟨hω67, hω632⟩, hωC⟩ x hx
  -- the cell of `x` is small, so `η(x)` is close to `B_{ρ - δ}`
  obtain ⟨t, htc, htb⟩ := id hx
  have ht : ‖t‖ < ρ - δ := mem_ball_zero_iff.1 htb
  obtain ⟨hdiam1, hdiam2⟩ := hωC x ⟨t, htc, ball_subset_ball (by linarith) htb⟩
  have hbdd : Bornology.IsBounded (cell ε (S.η ω) x) := by
    by_contra hb
    rw [Metric.diam_eq_zero_of_unbounded hb] at hdiam1
    exact absurd hdiam1 (not_le.2 (Real.rpow_pos_of_pos hε _))
  have hdist : dist (vertexPoint ε (S.η ω) x) t ≤ (1 - ρ) / 4 := by
    refine (Metric.dist_le_diam_of_mem hbdd (Lemma68C12Geom.vertexPoint_mem_cell hε.le x) htc).trans
      (hdiam2.trans ?_)
    rw [hβc]; exact hεc
  -- every vertex of `V^ε(B_δ(η(x)))` is a vertex of `V^ε(B_{ρ₁ - δ^ℓ})`, where Lemma 6.7 applies
  have hU : ∀ y ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ),
      y ∈ cellVertices ε (S.η ω) (ball 0 (ρ₁ - δ ^ ℓ)) := by
    rintro y ⟨w, hwc, hwb⟩
    show (cell ε (S.η ω) y ∩ ball 0 (ρ₁ - δ ^ ℓ)).Nonempty
    refine ⟨w, hwc, mem_ball_zero_iff.2 ?_⟩
    have h1 : dist w (vertexPoint ε (S.η ω) x) < δ := hwb
    have h2 := dist_triangle w (vertexPoint ε (S.η ω) x) t
    have h3 := dist_triangle w t 0
    rw [dist_zero_right, dist_zero_right] at h3
    rw [hρ₁]; linarith
  -- (6.33): one short gap has probability at most `1 - δ^a`
  have hq : ∀ y ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ),
      srwLaw (S.mult ε ω) y {z | vExitTime
        (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z < (g : ℕ∞)} ≤
        ENNReal.ofReal (1 - δ ^ a) := by
    intro y hy
    have hy67 := hω67 y (hU y hy)
    have hIA : interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ)) ⊆
        cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ)) := Set.sdiff_subset
    have hmeas : MeasurableSet {z : ℕ → ℤ | ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤
        (vExitTime (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z :
          ℝ≥0∞)} :=
      (measurable_vExitTime
          (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))))
        (Set.to_countable {s : ℕ∞ | ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤ (s : ℝ≥0∞)}).measurableSet
    have hsub : {z | vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z <
        (g : ℕ∞)} ⊆ {z : ℕ → ℤ | ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤
          (vExitTime (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z :
            ℝ≥0∞)}ᶜ := by
      intro z hz hz'
      have hz1 : vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z <
          (g : ℕ∞) := hz
      have hz2 : ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤
          (vExitTime (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z :
            ℝ≥0∞) := hz'
      have h1 := lt_of_le_of_lt (FiniteExitMomentHone68.vExitTime_mono_set hIA z) hz1
      have h2 := ENat.toENNReal_lt.2 h1
      have h3 : ((g : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (ε⁻¹ * δ ^ b) := by
        rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hgb
      exact absurd hz2 (not_le.2 (h2.trans_le h3))
    calc _ ≤ _ := measure_mono hsub
      _ = 1 - srwLaw (S.mult ε ω) y {z : ℕ → ℤ | ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤
          (vExitTime (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ))) z :
            ℝ≥0∞)} := prob_compl_eq_one_sub hmeas
      _ ≤ 1 - ENNReal.ofReal (δ ^ a) := tsub_le_tsub_left hy67 1
      _ = ENNReal.ofReal (1 - δ ^ a) := by
          rw [ENNReal.ofReal_sub _ (Real.rpow_nonneg hδ.le a), ENNReal.ofReal_one]
  -- every vertex lies in its own region
  have hAself : ∀ y : ℤ, y ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ)) := by
    intro y
    show (cell ε (S.η ω) y ∩ ball (vertexPoint ε (S.η ω) y) (δ ^ ℓ)).Nonempty
    exact ⟨_, Lemma68C12Geom.vertexPoint_mem_cell hε.le y,
      mem_ball_self (Real.rpow_pos_of_pos hδ ℓ)⟩
  -- (6.32) at `x`, then the quenched bound
  have h632x := hω632 x hx
  rw [← hK] at h632x
  refine (srwLaw_exitTime_lt_ofReal_le (S.mult ε ω) x
    (A := fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ))) hAself _ hK1 hrg
    (by linarith) hq h632x).trans ?_
  simp only [hδ, ↓reduceIte]
  rw [ENNReal.ofReal_add (hψ₀0 δ hδ.le) (Real.exp_pos _).le]
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hpow)

end MatedCRT.FirstPass.Derived
