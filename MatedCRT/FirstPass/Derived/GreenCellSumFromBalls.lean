import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Derived.GreenUpperBoundOfInputs
import MatedCRT.FirstPass.Derived.HarnackRingGeometry
import MatedCRT.FirstPass.Derived.HarnackUnionBound
import MatedCRT.FirstPass.Derived.GreenBallGridUnion
import LatticeProb.Analysis.DyadicInverseSquareSum
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly

/-!
# The inverse-square cell sum from ball bounds on the cell sizes

Berestycki–Gwynne (2020), Lemma 5.3, Step 3: for a vertex `b` with embedded point `v = η(ε b)`
and `s ∈ [ε^β, (1 - ρ) / 8]`, the sum `∑_k deg(k) (diam H_k / dist(v, H_k))²` over a finite family of
cells outside `B_s(v)` is at most `C₂ log (1 / s)`.

The proof splits the cells into dyadic shells around `v` (`sum_div_sq_le_log_of_quadratic_count`)
and needs only the ball bound of Gwynne–Miller–Sheffield (2019), Proposition 2.9: with polynomially
high probability, for every ball `B_r(z) ⊆ B_ρ'` of radius `r ≥ ε^β`, the cells meeting `B_r(z)` satisfy
`∑ deg(k) (diam H_k)² ≤ A r²`.

* `MatedCRT.sum_mdeg_mul_div_infDist_sq_le`: the deterministic step.
* `MatedCRT.hsum_of_ball`: the `hsum` hypothesis of `greenKernelUpperBoundStmt_of_inputs` from the
  cell size estimate and the ball bound.
* `MatedCRT.greenKernelUpperBoundStmt_of_ring_ball`: the crude Green kernel upper bound (BG20 Lemma 5.4)
  from the cell size estimate, the ring events of BG20 Lemma 3.10 (`hRing`), the ball bound (`hball`) and
  the segment paths of BG20 Lemma 5.3, Step 1 (`hpath`).
* `MatedCRT.greenKernelUpperBoundStmt_of_ring_single`: the same with the ball bound replaced by its
  single-ball form (`hsingle`, GMS19 Proposition 2.9 for one ball), through the grid union bound.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace MatedCRT

/-- **Deterministic core of BG20 Lemma 5.3, Step 3.**  If the cells meeting `B_ρ` have diameter at most
`(1 - ρ) / 8` and the cells meeting any ball `B_r(z) ⊆ B_{(3+ρ)/4}` of radius `r ≥ ε^β` satisfy
`∑ deg(k) (diam H_k)² ≤ A r²`, then for a vertex `b` of `V(B_ρ)`, `ε^β ≤ s ≤ (1 - ρ) / 8` and a finite set `T`
of vertices of `V(B_{(1+ρ)/2})` whose cells miss `B_s(η(ε b))`, the inverse-square sum is at most
`18 (A / ((1 - ρ) / 8)²) log (1 / s)`. -/
theorem sum_mdeg_mul_div_infDist_sq_le {ε β ρ A s : ℝ} {η : ℝ → ℂ} (m : ℤ → ℤ → ℕ) {b : ℤ}
    {T : Finset ℤ} (hε : 0 < ε) (hη : Continuous η) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A)
    (hsz : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ (1 - ρ) / 8)
    (hball : ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z r ⊆ ball 0 ((3 + ρ) / 4) →
      ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε η (ball z r)) →
        ∑ k ∈ T, (mdeg m k : ℝ) * diam (cell ε η k) ^ 2 ≤ A * r ^ 2)
    (hb : b ∈ cellVertices ε η (ball 0 ρ)) (hs : ε ^ β ≤ s) (hs1 : s ≤ (1 - ρ) / 8)
    (hT : ∀ k ∈ T, k ∈ cellVertices ε η (ball 0 ((1 + ρ) / 2)) ∧
      k ∉ cellVertices ε η (ball (vertexPoint ε η b) s)) :
    ∑ k ∈ T, (mdeg m k : ℝ) *
        (diam (cell ε η k) / infDist (vertexPoint ε η b) (cell ε η k)) ^ 2 ≤
      18 * (A / ((1 - ρ) / 8) ^ 2) * Real.log (1 / s) := by
  have hr₁0 : 0 < (1 - ρ) / 8 := by linarith
  have hr₁1 : (1 - ρ) / 8 < 1 := by linarith
  have hεβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hs0 : 0 < s := lt_of_lt_of_le hεβ hs
  have hcellne : ∀ k : ℤ, (cell ε η k).Nonempty := fun k =>
    ⟨_, MatedCRT.vertexPoint_mem_cell hε.le η k⟩
  have hvnorm : ‖vertexPoint ε η b‖ < ρ + (1 - ρ) / 8 := by
    have hb' : (cell ε η b ∩ ball 0 ρ).Nonempty := hb
    obtain ⟨y, hy, hyb⟩ := hb'
    have hbdd : Bornology.IsBounded (cell ε η b) := (isCompact_Icc.image hη).isBounded
    have h1 : dist (vertexPoint ε η b) y ≤ diam (cell ε η b) :=
      Metric.dist_le_diam_of_mem hbdd (MatedCRT.vertexPoint_mem_cell hε.le η b) hy
    have h2 := hsz b ⟨y, hy, hyb⟩
    have h3 : ‖y‖ < ρ := by simpa using hyb
    have h4 := norm_sub_norm_le (vertexPoint ε η b) y
    rw [← dist_eq_norm] at h4
    linarith
  have hA' : A ≤ A / ((1 - ρ) / 8) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hr2 : ((1 - ρ) / 8) ^ 2 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_left hr2 hA
    linarith
  have key := sum_div_sq_le_log_of_quadratic_count T
    (fun k => (mdeg m k : ℝ) * diam (cell ε η k) ^ 2)
    (fun k => infDist (vertexPoint ε η b) (cell ε η k))
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (A := A / ((1 - ρ) / 8) ^ 2) (R := 2) hs0 (by linarith) le_rfl (by linarith) ?_ ?_
  · calc ∑ k ∈ T, (mdeg m k : ℝ) *
          (diam (cell ε η k) / infDist (vertexPoint ε η b) (cell ε η k)) ^ 2
        = ∑ k ∈ T, (mdeg m k : ℝ) * diam (cell ε η k) ^ 2 /
            infDist (vertexPoint ε η b) (cell ε η k) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [div_pow, mul_div_assoc]
      _ ≤ _ := key
  · intro k hk
    obtain ⟨hk1, hk2⟩ := hT k hk
    refine ⟨?_, ?_⟩
    · refine (Metric.le_infDist (hcellne k)).2 fun y hy => ?_
      by_contra hlt
      push Not at hlt
      exact hk2 ⟨y, hy, by rw [mem_ball, dist_comm]; exact hlt⟩
    · have hk1' : (cell ε η k ∩ ball 0 ((1 + ρ) / 2)).Nonempty := hk1
      obtain ⟨y, hy, hyb⟩ := hk1'
      have h3 : ‖y‖ < (1 + ρ) / 2 := by simpa using hyb
      have h4 := norm_sub_le (vertexPoint ε η b) y
      rw [← dist_eq_norm] at h4
      have h5 : infDist (vertexPoint ε η b) (cell ε η k) ≤ dist (vertexPoint ε η b) y :=
        Metric.infDist_le_dist_of_mem hy
      linarith
  · intro r hsr hr4
    by_cases hr : r ≤ (1 - ρ) / 8
    · have hsub : ball (vertexPoint ε η b) r ⊆ ball 0 ((3 + ρ) / 4) := by
        intro x hx
        rw [mem_ball, dist_eq_norm] at hx
        rw [mem_ball_zero_iff]
        have h4 := norm_sub_norm_le x (vertexPoint ε η b)
        linarith
      have h1 := hball (vertexPoint ε η b) r (hs.trans hsr) hsub
        (T.filter fun k => infDist (vertexPoint ε η b) (cell ε η k) < r) (fun k hk => by
          obtain ⟨y, hy, hyr⟩ := (Metric.infDist_lt_iff (hcellne k)).1 (Finset.mem_filter.1 hk).2
          exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hyr⟩)
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right hA' (sq_nonneg r)
    · push Not at hr
      have hρ'' : ball (0 : ℂ) ((3 + ρ) / 4) ⊆ ball 0 ((3 + ρ) / 4) := subset_rfl
      have h1 := hball 0 ((3 + ρ) / 4) (by linarith) hρ''
        (T.filter fun k => infDist (vertexPoint ε η b) (cell ε η k) < r) (fun k hk => by
          obtain ⟨y, hy, hyb⟩ := (hT k (Finset.mem_filter.1 hk).1).1
          exact ⟨y, hy, by rw [mem_ball_zero_iff] at hyb ⊢; linarith⟩)
      refine h1.trans ?_
      have h2 : A * ((3 + ρ) / 4) ^ 2 ≤ A * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith) hA
      have h3 : 1 ≤ r ^ 2 / ((1 - ρ) / 8) ^ 2 :=
        (one_le_div (by positivity)).2 (by nlinarith)
      calc A * ((3 + ρ) / 4) ^ 2 ≤ A * 1 := h2
        _ ≤ A * (r ^ 2 / ((1 - ρ) / 8) ^ 2) := mul_le_mul_of_nonneg_left h3 hA
        _ = A / ((1 - ρ) / 8) ^ 2 * r ^ 2 := by ring

/-- **The inverse-square cell sum (BG20 Lemma 5.3, Step 3) from the ball bound and the cell size
estimate.**  `hball` is the ball form of GMS19 Proposition 2.9: with polynomially high probability, for
every ball `B_r(z) ⊆ B_ρ` of radius `r ≥ ε^β`, the cells meeting `B_r(z)` satisfy
`∑ deg(k) (diam H_k)² ≤ A r²`. -/
theorem hsum_of_ball {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hball : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z r ⊆ ball 0 ρ →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ s : ℝ,
        ε ^ β ≤ s → s ≤ (1 - ρ) / 8 →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)) ∧
            k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) b) s)) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) *
            (diam (cell ε (S.η ω) k) /
              infDist (vertexPoint ε (S.η ω) b) (cell ε (S.η ω) k)) ^ 2 ≤
            C₂ * Real.log (1 / s)} := by
  intro γ hγ hγ2
  obtain ⟨β, hβ, hB⟩ := hball γ hγ hγ2
  refine ⟨β, hβ, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨A, hA, hAP⟩ := hB ((3 + ρ) / 4) (by linarith) (by linarith)
  refine ⟨18 * (A / ((1 - ρ) / 8) ^ 2), by
    have : 0 < (1 - ρ) / 8 := by linarith
    positivity, fun Ω _ S hS => ?_⟩
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have h2e : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he]
    ring
  have hsz : Gauss.PolyHighProb S.P _ := hsize γ hγ hγ2 e ρ he0 he1 hρ hρ1 Ω S hS
  have hbl : Gauss.PolyHighProb S.P _ := hAP Ω S hS
  have hc : ∀ᵐ ω ∂S.P, ω ∈ {ω | Continuous (S.η ω)} :=
    TraceInputs68.ae_continuous_eta hS
  have h2 := polyHighProb_inter_ae (polyHighProb_inter hbl hsz) hc
  obtain ⟨r₁, hr₁, hr₁h⟩ := exists_rpow_le_of_small he0 (show 0 < (1 - ρ) / 8 by linarith)
  refine polyHighProb_mono_of_small h2 (r₁ := min r₁ 1) (lt_min hr₁ one_pos) ?_
  intro ε hε hεr
  rintro ω ⟨⟨hBω, hSzω⟩, hηω⟩
  have hεr₁ : ε < r₁ := lt_of_lt_of_le hεr (min_le_left _ _)
  have hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      diam (cell ε (S.η ω) k) ≤ (1 - ρ) / 8 := fun k hk => by
    have hd := (hSzω k hk).2
    rw [h2e] at hd
    exact hd.trans (hr₁h ε hε hεr₁)
  intro b hb s hs hs1 T hT
  exact sum_mdeg_mul_div_infDist_sq_le (S.mult ε ω) hε hηω hρ hρ1 hA.le hdiam hBω hb hs hs1 hT

/-- **The crude Green kernel upper bound** (Berestycki–Gwynne 2020, Lemma 5.4) from the cell size
estimate, the ring events of Lemma 3.10 (`hRing`), the ball form of Gwynne–Miller–Sheffield (2019),
Proposition 2.9 (`hball`) and the segment paths of Lemma 5.3, Step 1 (`hpath`): the Harnack inequality on
circles and the inverse-square cell sum are derived from `hRing` and `hball`. -/
theorem greenKernelUpperBoundStmt_of_ring_ball {𝒮 : SpaceFillingSLEModel}
    (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hball : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z r ⊆ ball 0 ρ →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2})
    (hpath : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)),
        ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).IsChain
            fun a c => S.mult ε ω a c ≠ 0) ∧
        (∀ᵐ θ ∂uniformDirection, ∃ p,
          segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ = b :: p ∧
          (∀ v ∈ b :: p, v ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) ∧
          (b :: p).getLast (List.cons_ne_nil b p) ∉
            interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)))}) :
    GreenKernelUpperBoundStmt 𝒮 :=
  greenKernelUpperBoundStmt_of_ring hsize hRing (hsum_of_ball hsize hball) hpath

/-- **The crude Green kernel upper bound** (Berestycki–Gwynne 2020, Lemma 5.4) from the cell size
estimate, the ring events of Lemma 3.10 (`hRing`), the single-ball estimate of Gwynne–Miller–Sheffield (2019),
Proposition 2.9 (`hsingle`: a fixed ball `B_r(z) ⊆ B_{ρ'}` of radius `r ≥ ε^{β₀}` has
`∑ deg(k) (diam H_k)² ≤ A r²` except with probability `C ε^{α₀}`) and the segment paths of Lemma 5.3, Step 1
(`hpath`). -/
theorem greenKernelUpperBoundStmt_of_ring_single {𝒮 : SpaceFillingSLEModel}
    (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hsingle : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (z : ℂ) (r : ℝ), ε ^ β₀ ≤ r → ball z r ⊆ ball 0 ρ' →
          S.P {ω | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
            ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2} ≤
              ENNReal.ofReal (C * ε ^ α₀))
    (hpath : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)),
        ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).IsChain
            fun a c => S.mult ε ω a c ≠ 0) ∧
        (∀ᵐ θ ∂uniformDirection, ∃ p,
          segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ = b :: p ∧
          (∀ v ∈ b :: p, v ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) ∧
          (b :: p).getLast (List.cons_ne_nil b p) ∉
            interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)))}) :
    GreenKernelUpperBoundStmt 𝒮 :=
  greenKernelUpperBoundStmt_of_ring_ball hsize hRing (hball_of_pointwise hsingle) hpath

end MatedCRT
