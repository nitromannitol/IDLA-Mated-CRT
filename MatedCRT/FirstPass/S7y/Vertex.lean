import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Vertex
import MatedCRT.FirstPass.S7y.Core

/-!
# Measurable-binder copy of `stay_le_at_frontier_vertex` (fp-S7y-h29-measurable, operator plumbing)

Copy of `ConstantOrderDiv.stay_le_at_frontier_vertex` (MatedCRT/Proofs/Sec6/ConstantOrderLowerBoundDiv/Vertex.lean:30)
with the Lemma 2.9 hypothesis `CountingAt` replaced by `CountingAtMeas` (Borel `D`, S7y/Core.lean). The proof is the
original's; its single use of the hypothesis, at `D = ball y (c₀ * R)`, supplies `measurableSet_ball`. Original unchanged.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

namespace ConstantOrderDiv

set_option maxHeartbeats 400000 in
/-- **Steps 2-4 at a vertex of `V^ε(∂B_{(4/3)R}(z)) ∩ A`.** -/
theorem stay_le_at_frontier_vertex_meas {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : Continuous η)
    {ρ βm βp c₀ CE C₁ C₂ α₁ α₉ β₉ ω₂ κ s₁ s₂ r R lam : ℝ} {N : ℕ} {Θ A : Set ℤ} {z : ℂ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC₂ : 0 < C₂) (hc₀ : c₀ = Real.exp (-(3 / 2) * C₂) / 12) (hCE : 0 < CE)
    (hC₁ : 0 < C₁) (hβm : 1 ≤ βm) (hβ₉ : 0 < β₉) (hs₁ : s₁ = 1 / 4 * (c₀ / 256) ^ βm)
    (hs₂ : s₂ ≤ 1 / (2592 * C₁ ^ 2 * CE ^ 2))
    (hr : 0 < r) (hr1 : r ≤ 1) (hrN : r ≤ (1 / 2 : ℝ) ^ N) (hR : 0 < R) (hRr : 8 * R ≤ r)
    (hr2R : r ^ 2 / 128 ≤ R) (hlamR : lam ≤ R) (hlam : 0 < lam)
    (hS1 : ε ^ κ ≤ c₀ * lam / 100) (hS2 : ε ^ ω₂ ≤ lam / 4) (hS3 : ε ^ α₁ ≤ lam / 100)
    (hS4 : ε ^ α₁ ≤ (c₀ * lam / 2) ^ βm) (hS5 : 4 * ε ^ α₉ ≤ (c₀ * lam / 2) ^ βm)
    (hS6 : Real.exp (3 / 2 * C₂) ≤ ε⁻¹)
    (hzρ : ‖z‖ + 2 * r ≤ 7 * ρ / 8)
    (hnear : ∀ w : ℂ, ‖w - z‖ < 2 * R →
      w ∈ thickening r (fillCells ε η Θ) ∧ w ∉ closure (fillCells ε η Θ))
    (hdiam : ∀ k, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ ε ^ κ)
    (hfin : (cellVertices ε η (ball 0 ρ)).Finite)
    (h216 : GreenLowerAt m ε η ρ ω₂ C₂) (hLL : LogLossAt m ε η μ ρ α₁ C₁) (h29 : CountingAtMeas ε η μ ρ α₉ β₉)
    (hvol : ∀ n, N ≤ n → VolumeGrowthAt μ βp βm ((1 / 2 : ℝ) ^ n))
    (hgood : IsGoodAnnulusEvent μ c₀ CE R z)
    (hA : ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε)
    {b : ℤ} (hb : b ∈ cellVertices ε η (frontier (ball z (4 * R / 3)))) :
    srwLaw m b {x | ∀ n : ℕ,
        (n : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η Θ)) \ Θ) x → x n ∈ A} ≤
      ENNReal.ofReal (1 - s₂ / (1 + |Real.log r|) ^ 2) := by
  -- constants
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  have hkey : Real.exp (3 / 2 * C₂) * c₀ = 1 / 12 := by
    rw [hc₀, show -(3 / 2) * C₂ = -(3 / 2 * C₂) by ring, Real.exp_neg]
    field_simp
  have hexp1 : 1 ≤ Real.exp (3 / 2 * C₂) := Real.one_le_exp (by positivity)
  have hc₀12 : c₀ ≤ 1 / 12 := by
    calc c₀ = c₀ * 1 := (mul_one _).symm
      _ ≤ c₀ * Real.exp (3 / 2 * C₂) := mul_le_mul_of_nonneg_left hexp1 hc₀pos.le
      _ = 1 / 12 := by rw [mul_comm]; exact hkey
  have hc₀R : c₀ * R ≤ R / 12 := by
    have := mul_le_mul_of_nonneg_right hc₀12 hR.le
    linarith
  have hc₀lam : c₀ * lam ≤ c₀ * R := mul_le_mul_of_nonneg_left hlamR hc₀pos.le
  have hd : ε ^ κ ≤ c₀ * R / 100 := by linarith
  -- the vertex `b` and `y = η(b)`
  obtain ⟨w₀, hw₀b, hw₀F⟩ := hb
  rw [frontier_ball z (by positivity : 4 * R / 3 ≠ 0)] at hw₀F
  have hw₀z : ‖w₀ - z‖ = 4 * R / 3 := mem_sphere_iff_norm.1 hw₀F
  have hyb : vertexPoint ε η b ∈ cell ε η b := vertexPoint_mem_cell hε.le η b
  set y := vertexPoint ε η b with hydef
  have hw₀ρ : w₀ ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]
    have := norm_le_add_norm_sub w₀ z
    linarith
  have hyw₀ : ‖y - w₀‖ ≤ c₀ * R / 100 := (norm_sub_le_of_cell hη hdiam hw₀b hw₀ρ hyb).trans hd
  have hyz1 : 4 * R / 3 - R / 1200 ≤ ‖y - z‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub w₀ y z
    rw [norm_sub_rev w₀ y] at this
    linarith
  have hyz2 : ‖y - z‖ ≤ 4 * R / 3 + R / 1200 := by
    have := norm_sub_le_norm_sub_add_norm_sub y w₀ z
    linarith
  have hynorm : ‖y‖ + r + R ≤ 7 * ρ / 8 := by
    have := norm_le_add_norm_sub y z
    linarith
  -- the annulus `𝔸 = 𝔸_{R,2R}(z)` contains `B_{R/4 + R/100}(y)`
  have hball𝔸 : ∀ w : ℂ, ‖w - y‖ < R / 4 + R / 100 → w ∈ annulus z R (2 * R) ∧ ‖w - z‖ < 2 * R := by
    intro w hw
    have h1 := norm_sub_le_norm_sub_add_norm_sub w y z
    have h2 := norm_sub_le_norm_sub_add_norm_sub y w z
    rw [norm_sub_rev y w] at h2
    exact ⟨mem_annulus_iff_norm.2 ⟨by linarith, by linarith⟩, by linarith⟩
  have hy𝔸 : y ∈ annulus z R (2 * R) := (hball𝔸 y (by rw [sub_self, norm_zero]; positivity)).1
  have hyρ : ∀ t, t ≤ r + R → ball y t ⊆ ball 0 ρ := by
    intro t ht w hw
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hw
    have := norm_le_add_norm_sub w y
    linarith
  -- `W ⊆ U`
  have hWU : interiorCellVertices ε η (ball y (R / 4)) ⊆
      cellVertices ε η (thickening r (fillCells ε η Θ)) \ Θ := by
    rintro k ⟨⟨w, hwk, hwB⟩, -⟩
    rw [mem_ball, dist_eq_norm] at hwB
    obtain ⟨-, hwz⟩ := hball𝔸 w (by linarith)
    obtain ⟨hwT, hwcl⟩ := hnear w hwz
    exact ⟨⟨w, hwk, hwT⟩, fun hkΘ => hwcl (subset_closure (mem_biUnion hkΘ hwk))⟩
  -- `V^ε(B_{𝐜₀R}(y)) ⊆ W`
  have hcellc : ∀ k ∈ cellVertices ε η (ball y (c₀ * R)), ∀ w' ∈ cell ε η k,
      ‖w' - y‖ < c₀ * R + c₀ * R / 100 := by
    rintro k ⟨w, hwk, hwB⟩ w' hw'
    rw [mem_ball, dist_eq_norm] at hwB
    have hwρ : w ∈ ball (0 : ℂ) ρ :=
      hyρ (c₀ * R) (by linarith) (by rw [mem_ball, dist_eq_norm]; exact hwB)
    have h1 := (norm_sub_le_of_cell hη hdiam hwk hwρ hw').trans hd
    have h2 := norm_sub_le_norm_sub_add_norm_sub w' w y
    linarith
  have hVcW : cellVertices ε η (ball y (c₀ * R)) ⊆ interiorCellVertices ε η (ball y (R / 4)) := by
    intro k hk
    obtain ⟨w, hwk, hwB⟩ := hk
    refine ⟨⟨w, hwk, ball_subset_ball (by linarith) hwB⟩, ?_⟩
    rintro ⟨w', hw'k, hw'F⟩
    rw [frontier_ball y (by positivity : R / 4 ≠ 0)] at hw'F
    have := hcellc k ⟨w, hwk, hwB⟩ w' hw'k
    rw [mem_sphere_iff_norm.1 hw'F] at this
    linarith
  have hVcVr : cellVertices ε η (ball y (c₀ * R)) ⊆ cellVertices ε η (ball y r) :=
    cellVertices_mono' (ball_subset_ball (by linarith))
  have hVrfin : (cellVertices ε η (ball y r)).Finite := hfin.subset (cellVertices_mono' (hyρ r (by linarith)))
  have hVcfin : (cellVertices ε η (ball y (c₀ * R))).Finite := hVrfin.subset hVcVr
  -- Lemma 2.16: `G_W(b, b') ≥ 1/2` on `V^ε(B_{𝐜₀R}(y))`
  have hG : ∀ b' ∈ cellVertices ε η (ball y (c₀ * R)),
      (1 / 2 : ℝ) ≤ greenFn m (interiorCellVertices ε η (ball y (R / 4))) b b' := by
    intro b' hb'
    have hbρ : b ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₂)) := by
      refine ⟨y, hyb, ?_⟩
      rw [mem_ball_zero_iff]
      linarith
    have hinf : R / 4 ≤ infDist y (sphere 0 ρ) := le_infDist_sphere hρ.le (by linarith)
    have hb'3 : b' ∈ cellVertices ε η (ball y (R / 4 / 3)) :=
      cellVertices_mono' (ball_subset_ball (by linarith)) hb'
    obtain ⟨hgk, hlow⟩ := h216 b hbρ (R / 4) (by linarith) hinf b' hb'3
    refine half_le_greenFn hC₂ ?_ hlow hgk
    split_ifs with hyy
    · exact hS6
    · refine le_min ?_ hS6
      have hy'b' : vertexPoint ε η b' ∈ cell ε η b' := vertexPoint_mem_cell hε.le η b'
      have hdist := hcellc b' hb' _ hy'b'
      rw [norm_sub_rev] at hdist
      have hpos : 0 < ‖y - vertexPoint ε η b'‖ := norm_pos_iff.2 (sub_ne_zero.2 hyy)
      rw [le_div_iff₀ hpos]
      have hmul := mul_le_mul_of_nonneg_left hdist.le (Real.exp_pos (3 / 2 * C₂)).le
      have hval : Real.exp (3 / 2 * C₂) * (c₀ * R + c₀ * R / 100) = 101 * R / 1200 := by
        rw [show Real.exp (3 / 2 * C₂) * (c₀ * R + c₀ * R / 100) =
          (Real.exp (3 / 2 * C₂) * c₀) * (101 * R / 100) by ring, hkey]
        ring
      linarith
  -- Lemma 2.9 with `f ≡ 1`: `|V^ε(B_{𝐜₀R}(y))| ≥ ε⁻¹ M - ε^{-1+α}`
  have hcount : ε⁻¹ * (μ (ball y (c₀ * R))).toReal - ε ^ (-1 + α₉) ≤
      ((cellVertices ε η (ball y (c₀ * R))).ncard : ℝ) := by
    classical
    have h := (h29 (ball y (c₀ * R)) (fun _ => 1)
      (fun k => if h : (cell ε η k ∩ ball y (c₀ * R)).Nonempty then h.some else 0)
      measurableSet_ball (hyρ _ (by linarith))
      (fun x _ => ⟨zero_le_one, by
        show |(1 : ℝ)| ≤ ε ^ (-β₉)
        rw [abs_one]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)⟩)
      (fun x _ x' _ => by simp only [sub_self, abs_zero]; positivity)
      (fun k hk => by
        split_ifs with h
        · exact ⟨h.some_mem.1, subset_closure h.some_mem.2⟩
        · exact absurd hk h)).1
    beta_reduce at h
    rw [tsum_one_eq_ncard hVcfin, setIntegral_const, smul_eq_mul, mul_one] at h
    exact h
  -- Lemma 2.7: `M ≥ δ₂^{β⁻}` and `M < ∞`
  obtain ⟨n₂, hn₂1, hn₂2⟩ := exists_half_pow_mem (by positivity : 0 < c₀ * R) (by linarith)
  obtain ⟨n₃, hn₃1, hn₃2⟩ := exists_half_pow_mem (by positivity : 0 < 2 * (c₀ * R)) (by linarith)
  have hN₂ : N ≤ n₂ := ge_of_half_pow_lt (by linarith)
  have hN₃ : N ≤ n₃ := ge_of_half_pow_lt (by linarith)
  have hδ₂pos : (0 : ℝ) < (1 / 2) ^ n₂ := by positivity
  have hylow : ENNReal.ofReal (((1 / 2 : ℝ) ^ n₂) ^ βm) ≤ μ (ball y ((1 / 2) ^ n₂)) :=
    (hvol n₂ hN₂ y (by rw [mem_ball_zero_iff]; linarith)).1
  have hyup : μ (ball y ((1 / 2) ^ n₃)) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n₃) ^ βp) :=
    (hvol n₃ hN₃ y (by rw [mem_ball_zero_iff]; linarith)).2
  have hMtop : μ (ball y (c₀ * R)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono (ball_subset_ball (by linarith))).trans hyup)
  set M := (μ (ball y (c₀ * R))).toReal with hMdef
  have hMδ₂ : ((1 / 2 : ℝ) ^ n₂) ^ βm ≤ M :=
    (ENNReal.ofReal_le_iff_le_toReal hMtop).1 (hylow.trans (measure_mono (ball_subset_ball hn₂2)))
  have hlamδ₂ : (c₀ * lam / 2) ^ βm ≤ ((1 / 2 : ℝ) ^ n₂) ^ βm :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hMδ₂
  have hsmall : ε ^ α₉ + s₁ * r ^ (2 * βm) ≤ M / 2 := by
    have hr2 : r ^ (2 * βm) = (r ^ 2) ^ βm := by
      rw [Real.rpow_mul hr.le, Real.rpow_two]
    have hs₁r : s₁ * r ^ (2 * βm) = 1 / 4 * (c₀ / 256 * r ^ 2) ^ βm := by
      rw [hs₁, hr2, Real.mul_rpow (by positivity) (by positivity)]
      ring
    have hc₀r : c₀ * (r ^ 2 / 128) ≤ c₀ * R := mul_le_mul_of_nonneg_left hr2R hc₀pos.le
    have hle : (c₀ / 256 * r ^ 2) ^ βm ≤ ((1 / 2 : ℝ) ^ n₂) ^ βm :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    rw [hs₁r]
    linarith
  -- Step 4, route (b)
  have hL : 0 ≤ Real.log (4 / R) := Real.log_nonneg (by rw [le_div_iff₀ hR]; linarith)
  have hTy : thickening (ε ^ α₁) (ball y (R / 4)) ⊆ ball y (R / 4 + R / 100) := by
    intro w hw
    obtain ⟨q, hq, hwq⟩ := mem_thickening_iff.1 hw
    rw [mem_ball, dist_eq_norm] at hq ⊢
    rw [dist_eq_norm] at hwq
    have := norm_sub_le_norm_sub_add_norm_sub w q y
    linarith
  have hT𝔸 : thickening (ε ^ α₁) (ball y (R / 4)) ⊆ annulus z R (2 * R) := fun w hw =>
    (hball𝔸 w (by have := hTy hw; rwa [mem_ball, dist_eq_norm] at this)).1
  have hD𝔸 : ball y (R / 4) ⊆ annulus z R (2 * R) := fun w hw =>
    (hball𝔸 w (by rw [mem_ball, dist_eq_norm] at hw; linarith)).1
  have hTR : thickening (ε ^ α₁) (ball y (R / 4)) ⊆ ball y R := hTy.trans (ball_subset_ball (by linarith))
  have hμB' : ENNReal.ofReal (ε ^ α₁) ≤ μ (ball y (R / 4)) :=
    (ENNReal.ofReal_le_ofReal (hS4.trans hlamδ₂)).trans
      (hylow.trans (measure_mono (ball_subset_ball (by linarith))))
  have hLLb := hLL y (R / 4) (by positivity) (hyρ _ (by linarith)) hμB' b
    ⟨y, hyb, mem_ball_self (by positivity)⟩ 2
  have hQ := (exitTimeLogLoss_le μ hR isOpen_thickening.measurableSet hD𝔸 hT𝔸 hy𝔸 hTR).trans
    (mul_le_mul_of_nonneg_left (annulusLogPotential_le_of_good hgood hy𝔸) zero_le)
  rw [← ENNReal.ofReal_toReal hMtop] at hQ
  have hY := exitTimeMoment_le_of_logLoss hε hL hCE.le hMpos.le hLLb hQ
  -- conclusion
  have hK : 0 < 2 * C₁ ^ 2 * (1 + Real.log (4 / R)) ^ 2 * CE ^ 2 := by positivity
  refine (stay_le_at_vertex hε hWU hVcW hVcVr hVrfin hG hcount (hA y) hsmall hMpos hK hY).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h9 := one_add_log_le hr hr1 hr2R
  have hlogr : 0 < 1 + |Real.log r| := by positivity
  have hsq : (1 + Real.log (4 / R)) ^ 2 ≤ 81 * (1 + |Real.log r|) ^ 2 := by
    calc (1 + Real.log (4 / R)) ^ 2 ≤ (9 * (1 + |Real.log r|)) ^ 2 := pow_le_pow_left₀ (by linarith) h9 2
      _ = 81 * (1 + |Real.log r|) ^ 2 := by ring
  have hCC : 0 ≤ 32 * C₁ ^ 2 * CE ^ 2 := by positivity
  have hden : 16 * (2 * C₁ ^ 2 * (1 + Real.log (4 / R)) ^ 2 * CE ^ 2) ≤
      2592 * C₁ ^ 2 * CE ^ 2 * (1 + |Real.log r|) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hCC
    linarith
  have hfrac : s₂ / (1 + |Real.log r|) ^ 2 ≤ 1 / (16 * (2 * C₁ ^ 2 * (1 + Real.log (4 / R)) ^ 2 * CE ^ 2)) := by
    calc s₂ / (1 + |Real.log r|) ^ 2 ≤ 1 / (2592 * C₁ ^ 2 * CE ^ 2) / (1 + |Real.log r|) ^ 2 := by gcongr
      _ = 1 / (2592 * C₁ ^ 2 * CE ^ 2 * (1 + |Real.log r|) ^ 2) := by rw [div_div]
      _ ≤ 1 / (16 * (2 * C₁ ^ 2 * (1 + Real.log (4 / R)) ^ 2 * CE ^ 2)) :=
          one_div_le_one_div_of_le (by positivity) hden
  linarith


end ConstantOrderDiv

end MatedCRT
