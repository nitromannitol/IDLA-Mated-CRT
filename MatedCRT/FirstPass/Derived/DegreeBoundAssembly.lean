import MatedCRT.FirstPass.Derived.DegreeBoundWindow
import MatedCRT.FirstPass.Derived.DegreeBoundDarts

/-!
# The degree bound from the covering estimate and the exponential degree tail

This is the proof of GMS19 Lemma 2.6 (the degree bound eq:degree-bound, line 3071): with polynomially high
probability as `ε → 0`, `max_{a ∈ V^ε(B_ρ)} deg^ε(a) ≤ (log ε⁻¹)²`. Take `M = ε⁻¹`. Outside an event of
probability `O(M^{-c}) = O(ε^c)` the unit disk is covered by `η([-M, M])` (HS18 Proposition 6.2; GMS19 Lemma A.4),
and then every vertex of `V^ε(B_ρ)` lies in the deterministic window `[-N, N]`, `N = ⌈M/ε⌉ + 1`
(`IsAreaParametrized.cellVertices_ball_subset_Icc`). A union bound over the `2N + 1 = O(ε⁻²)` vertices of the window
with the exponential degree tail `P[deg^ε(x) > n] ≤ C₀ e^{-C₁ n}` (GMS19 Lemma 2.5) at `n = ⌊(log ε⁻¹)²⌋` gives a
contribution `O(ε⁻² e^{-C₁ (log ε⁻¹)²}) = O(ε)`.

The deterministic assembly is `polyHighProb_degreeBound_of_tail` (for any family of degrees satisfying the tail);
`MatedCRTEnv.IsValid.polyHighProb_degreeBound_of_edgeEndTail` specializes it to a valid environment, with the
covering estimate from the mating-of-trees coupling and the tail stated for the number of labelled edge ends of the
boundary-length pair (the extended degree of GMS19 Lemma 2.5), which bounds the degree
(`matedDeg_bmEdgeCount_le_encard`).

## Main statements

* `MatedCRT.polyHighProb_degreeBound_of_tail`
* `MatedCRT.MatedCRTEnv.IsValid.polyHighProb_degreeBound_of_edgeEndTail`
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The real inequality behind the union bound of GMS19 Lemma 2.6: for `ε < min 1 (e^{-3/C₁})`, the number
`2N + 1` of vertices of the window `[-N, N]`, `N = ⌈ε⁻¹/ε⌉ + 1`, times `e^{-C₁ ⌊(log ε⁻¹)²⌋}` is at most
`7 e^{C₁} ε`. -/
theorem window_card_mul_exp_le {C₁ ε : ℝ} (hC₁ : 0 < C₁) (hε : 0 < ε) (hε1 : ε < 1)
    (hεe : ε < Real.exp (-(3 / C₁))) :
    (2 * ((⌈ε⁻¹ / ε⌉₊ : ℝ) + 1) + 1) * Real.exp (-(C₁ * (⌊Real.log ε⁻¹ ^ 2⌋₊ : ℝ))) ≤
      7 * Real.exp C₁ * ε := by
  set L := Real.log ε⁻¹ with hL
  have hLε : L = -Real.log ε := by rw [hL, Real.log_inv]
  have hL3 : 3 / C₁ < L := by
    have := Real.log_lt_log hε hεe
    rw [Real.log_exp] at this
    linarith
  have hLpos : 0 < L := lt_trans (div_pos (by norm_num) hC₁) hL3
  have hC₁L : 3 ≤ C₁ * L := by
    have := (div_lt_iff₀ hC₁).1 hL3
    linarith
  -- the window size
  have hinv : ε⁻¹ / ε = (ε ^ 2)⁻¹ := by field_simp
  have hge1 : 1 ≤ (ε ^ 2)⁻¹ := one_le_inv₀ (by positivity) |>.2 (by nlinarith)
  have hceil : (⌈ε⁻¹ / ε⌉₊ : ℝ) ≤ (ε ^ 2)⁻¹ + 1 := by
    rw [hinv]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hcard : 2 * ((⌈ε⁻¹ / ε⌉₊ : ℝ) + 1) + 1 ≤ 7 * (ε ^ 2)⁻¹ := by linarith
  -- the exponential
  have hfloor : L ^ 2 - 1 ≤ (⌊L ^ 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ 2)
    linarith
  have hexp3 : Real.exp (-(3 * L)) = ε ^ 3 := by
    rw [hLε, show -(3 * -Real.log ε) = Real.log ε + Real.log ε + Real.log ε by ring, Real.exp_add, Real.exp_add,
      Real.exp_log hε]
    ring
  have hexp : Real.exp (-(C₁ * (⌊L ^ 2⌋₊ : ℝ))) ≤ Real.exp C₁ * ε ^ 3 := by
    rw [← hexp3, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : C₁ * (L ^ 2 - 1) ≤ C₁ * (⌊L ^ 2⌋₊ : ℝ) := mul_le_mul_of_nonneg_left hfloor hC₁.le
    have h2 : 3 * L ≤ C₁ * L * L := by nlinarith
    nlinarith
  calc (2 * ((⌈ε⁻¹ / ε⌉₊ : ℝ) + 1) + 1) * Real.exp (-(C₁ * (⌊L ^ 2⌋₊ : ℝ)))
      ≤ 7 * (ε ^ 2)⁻¹ * (Real.exp C₁ * ε ^ 3) :=
        mul_le_mul hcard hexp (Real.exp_pos _).le (by positivity)
    _ = 7 * Real.exp C₁ * ε := by field_simp

/-- **The degree bound from the covering estimate and the degree tail** (the proof of GMS19 Lemma 2.6). Let `η` be
a.s. parametrized by the area measure `μ`, with `P[𝔻 ⊄ η([-M, M])] ≤ C M^{-c}` for `M > 1`, and let the degrees
`deg ε ω x` have the uniform exponential tail `P[deg ε · x > n] ≤ C₀ e^{-C₁ n}`. Then for `ρ ≤ 1`, with polynomially
high probability as `ε → 0`, every vertex `a` whose cell `η([ε(a-1), εa])` meets `B_ρ` has
`deg ε ω a ≤ (log ε⁻¹)²`. -/
theorem polyHighProb_degreeBound_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ} {deg : ℝ → Ω → ℤ → ℕ} {ρ : ℝ} (hρ : ρ ≤ 1)
    (hAP : ∀ᵐ ω ∂P, IsAreaParametrized (μ ω) (η ω))
    (hcov : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ M : ℝ, 1 < M →
      P {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-M) M} ≤ ENNReal.ofReal (C * M ^ (-c)))
    (htail : ∃ C₀ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ∀ x : ℤ, ∀ n : ℕ,
      P {ω | n < deg ε ω x} ≤ ENNReal.ofReal (C₀ * Real.exp (-(C₁ * n)))) :
    PolyHighProb P fun ε => {ω | ∀ a ∈ cellVertices ε (η ω) (ball 0 ρ),
      ((deg ε ω a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2} := by
  obtain ⟨c, hc, C, hC⟩ := hcov
  obtain ⟨C₀, C₁, hC₁, hT⟩ := htail
  set p : ℝ := min c 1 with hp
  set K : ℝ := 7 * Real.exp C₁ * max C₀ 0 with hK
  refine ⟨p, lt_min hc one_pos, max C 0 + K, min 1 (Real.exp (-(3 / C₁))),
    lt_min one_pos (Real.exp_pos _), fun ε hε hεlt => ?_⟩
  have hε1 : ε < 1 := hεlt.trans_le (min_le_left _ _)
  have hεe : ε < Real.exp (-(3 / C₁)) := hεlt.trans_le (min_le_right _ _)
  set M : ℝ := ε⁻¹ with hMdef
  have hM : 1 < M := (one_lt_inv₀ hε).2 hε1
  set N : ℤ := (⌈M / ε⌉₊ : ℤ) + 1 with hN
  set n : ℕ := ⌊Real.log ε⁻¹ ^ 2⌋₊ with hn
  set B₀ : Set Ω := {ω | ¬ IsAreaParametrized (μ ω) (η ω)} with hB₀
  set B₁ : Set Ω := {ω | ¬ ball (0 : ℂ) 1 ⊆ η ω '' Icc (-M) M} with hB₁
  set B₂ : Set Ω := ⋃ x ∈ Finset.Icc (-N) N, {ω | n < deg ε ω x} with hB₂
  have hsub : {ω | ∀ a ∈ cellVertices ε (η ω) (ball 0 ρ), ((deg ε ω a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2}ᶜ ⊆
      B₀ ∪ B₁ ∪ B₂ := by
    intro ω hω
    simp only [mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hω
    obtain ⟨a, ha, hdeg⟩ := hω
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨h0, h1⟩, h2⟩ := hnot
    have hAPω : IsAreaParametrized (μ ω) (η ω) := by
      by_contra h; exact h0 h
    have hcovω : ball (0 : ℂ) 1 ⊆ η ω '' Icc (-M) M := by
      by_contra h; exact h1 h
    have haI := hAPω.cellVertices_ball_subset_Icc hcovω hε hρ ha
    apply h2
    refine mem_iUnion₂.2 ⟨a, haI, ?_⟩
    have : (n : ℝ) < deg ε ω a := (Nat.floor_le (sq_nonneg _)).trans_lt hdeg
    exact_mod_cast this
  -- the three bounds
  have hP₀ : P B₀ = 0 := ae_iff.1 hAP
  have hεp : ε ^ c ≤ ε ^ p := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_left _ _)
  have hεp1 : ε ≤ ε ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_right c 1)
  have hP₁ : P B₁ ≤ ENNReal.ofReal (max C 0 * ε ^ p) := by
    refine (hC M hM).trans (ENNReal.ofReal_le_ofReal ?_)
    have hMc : M ^ (-c) = ε ^ c := by
      rw [hMdef, Real.inv_rpow hε.le, Real.rpow_neg (by positivity), inv_inv]
    rw [hMc]
    exact mul_le_mul (le_max_left _ _) hεp (by positivity) (le_max_right _ _)
  have hP₂ : P B₂ ≤ ENNReal.ofReal (K * ε ^ p) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => (hT ε hε x n).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (Real.exp_pos _).le))).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcardZ : ((Finset.Icc (-N) N).card : ℤ) = 2 * ((⌈M / ε⌉₊ : ℤ) + 1) + 1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
      ring
    have hcardR : ((Finset.Icc (-N) N).card : ℝ) = 2 * ((⌈M / ε⌉₊ : ℝ) + 1) + 1 := by
      exact_mod_cast hcardZ
    rw [hcardR]
    have hw := window_card_mul_exp_le hC₁ hε hε1 hεe
    calc (2 * ((⌈M / ε⌉₊ : ℝ) + 1) + 1) * (max C₀ 0 * Real.exp (-(C₁ * (n : ℝ))))
        = max C₀ 0 * ((2 * ((⌈ε⁻¹ / ε⌉₊ : ℝ) + 1) + 1) *
            Real.exp (-(C₁ * (⌊Real.log ε⁻¹ ^ 2⌋₊ : ℝ)))) := by
          rw [hMdef, hn]; ring
      _ ≤ max C₀ 0 * (7 * Real.exp C₁ * ε) := mul_le_mul_of_nonneg_left hw (le_max_right _ _)
      _ = K * ε := by rw [hK]; ring
      _ ≤ K * ε ^ p := mul_le_mul_of_nonneg_left hεp1 (by positivity)
  calc P {ω | ∀ a ∈ cellVertices ε (η ω) (ball 0 ρ), ((deg ε ω a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2}ᶜ
      ≤ P (B₀ ∪ B₁ ∪ B₂) := measure_mono hsub
    _ ≤ P B₀ + P B₁ + P B₂ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (max C 0 * ε ^ p) + ENNReal.ofReal (K * ε ^ p) := by
      rw [hP₀]; exact add_le_add_three le_rfl hP₁ hP₂
    _ = ENNReal.ofReal ((max C 0 + K) * ε ^ p) := by
      rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf

/-- **The degree bound for a valid environment from the tail of the number of labelled edge ends** (GMS19 Lemma
2.6 from GMS19 Lemma 2.5). The covering estimate `P[𝔻 ⊄ η([-M, M])] ≤ C M^{-c}` is the `coverage` field of the
mating-of-trees coupling (HS18 Proposition 6.2; GMS19 Lemma A.4), transported to `η` by the a.s. equality of the
curves; the degree of the mated-CRT map is at most the number of labelled edge ends of the boundary-length pair
(`matedDeg_bmEdgeCount_le_encard`). -/
theorem MatedCRTEnv.IsValid.polyHighProb_degreeBound_of_edgeEndTail {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ρ : ℝ} (hρ : ρ ≤ 1)
    (htail : ∃ C₀ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ∀ x : ℤ, ∀ n : ℕ,
      S.P {ω | (n : ℕ∞) < {d : (ℤ × ℤ × Bool) × Bool | MatedCRTHarmonic.MatedCRT.IsEdge ε (S.bm ω) d.1 ∧
        (if d.2 then d.1.2.1 else d.1.1) = x}.encard} ≤ ENNReal.ofReal (C₀ * Real.exp (-(C₁ * n)))) :
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ((matedDeg (S.mult ε ω) a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2} := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hD, hae⟩ := hS.matingOfTrees
  obtain ⟨c, hc, C, hC⟩ := hD.coverage
  refine polyHighProb_degreeBound_of_tail (deg := fun ε ω x => matedDeg (S.mult ε ω) x) hρ
    hS.isAreaParametrized ⟨c, hc, C, fun M hM => (measure_mono_ae ?_).trans (hC M hM)⟩ ?_
  · filter_upwards [hae] with ω hω h
    rw [hω.1]
    exact h
  · obtain ⟨C₀, C₁, hC₁, hT⟩ := htail
    refine ⟨C₀, C₁, hC₁, fun ε hε x n =>
      (measure_mono fun ω (hω : n < matedDeg (S.mult ε ω) x) => ?_).trans (hT ε hε x n)⟩
    exact (Nat.cast_lt.2 hω).trans_le (matedDeg_bmEdgeCount_le_encard ε (S.bm ω) x)

end MatedCRT
