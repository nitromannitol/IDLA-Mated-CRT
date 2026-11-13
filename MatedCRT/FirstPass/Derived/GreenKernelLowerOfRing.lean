import MatedCRT.FirstPass.Derived.HarnackUnionBound
import MatedCRT.FirstPass.Derived.HarnackRingBall
import MatedCRT.FirstPass.Derived.GreenKernelLowerOnCells

/-!
# The Harnack bound (4.13) of Lemma 4.4 from the ring events

Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, proof of Lemma 4.4.
With polynomially high probability, for every `a ∈ V^ε(B_ρ)`, every `r ≤ dist(η(a), ∂B_ρ)` and every
`s ∈ [ε^β, r/4]`, the Green kernel `g = g_{B_r(η(a))}(a, ·)` of the domain `V^ε(B_r(η(a))) \ V^ε(∂B_r(η(a)))`
satisfies the Harnack bound (4.13) `g(y) ≤ p⁻¹ g(y')` on `V^ε(∂B_s(η(a)))`. The inputs are the cell size estimate
(Lemma 2.7, cells meeting `B_ρ` have diameter at most `ε^{1/(2+γ)²}`) and the ring events of ibid. Lemma 3.10 (the
hypothesis `hRing`, the same as for Proposition 3.8), which hold simultaneously at all grid circles
`z' = h (m + n i)`, `s' = (√2)^a`, `h = ε^{2β}`, `s' ≥ ε^β`, `2 s' ≤ (1 + ρ)/2 - |z'|` by the union bound
`polyHighProb_ringEvents`.

* `norm_add_le_or_add_le_norm_of_le_infDist_sphere`: `r ≤ dist(x, ∂B_ρ)` gives `|x| + r ≤ ρ` or `ρ + r ≤ |x|`.
* `hHarn_ball_of_ring`: the hypothesis `hHarn` of `greenKernelLowerBoundStmt_of_inputs`.
* `greenKernelLowerBoundStmt_of_ring`: Lemma 2.16 (ibid. Lemma 4.4) from the cell size estimate, the ring events
  of Lemma 3.10 and the resistance bound (4.15).
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace MatedCRT

/-- If `r ≤ dist(x, ∂B_ρ)` then `|x| + r ≤ ρ` or `ρ + r ≤ |x|` (compare with the radial point `ρ x/|x|` of the
circle, or with `ρ` when `x = 0`). -/
theorem norm_add_le_or_add_le_norm_of_le_infDist_sphere {x : ℂ} {ρ r : ℝ} (hρ : 0 < ρ)
    (hr : r ≤ infDist x (sphere 0 ρ)) : ‖x‖ + r ≤ ρ ∨ ρ + r ≤ ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | h0
  · have hw : ((ρ : ℝ) : ℂ) ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have h1 : infDist (0 : ℂ) (sphere 0 ρ) ≤ ρ := by
      calc infDist 0 (sphere 0 ρ) ≤ dist (0 : ℂ) (ρ : ℂ) := infDist_le_dist_of_mem hw
        _ = ρ := by rw [dist_comm, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    left
    rw [norm_zero]
    linarith
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 h0
    have hw : ((ρ / ‖x‖ : ℝ) : ℂ) * x ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg hρ.le hxpos.le), div_mul_cancel₀ _ hxpos.ne']
    have e : (1 - ρ / ‖x‖) * ‖x‖ = ‖x‖ - ρ := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hxpos.ne']
    have h1 : infDist x (sphere 0 ρ) ≤ |‖x‖ - ρ| := by
      calc infDist x (sphere 0 ρ) ≤ dist x (((ρ / ‖x‖ : ℝ) : ℂ) * x) := infDist_le_dist_of_mem hw
        _ = |1 - ρ / ‖x‖| * ‖x‖ := by
          rw [dist_eq_norm, show x - ((ρ / ‖x‖ : ℝ) : ℂ) * x = ((1 - ρ / ‖x‖ : ℝ) : ℂ) * x by
            push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = |1 - ρ / ‖x‖| * |‖x‖| := by rw [abs_of_pos hxpos]
        _ = |‖x‖ - ρ| := by rw [← abs_mul, e]
    rcases le_total ‖x‖ ρ with h | h
    · left
      rw [abs_of_nonpos (sub_nonpos.2 h)] at h1
      linarith
    · right
      rw [abs_of_nonneg (sub_nonneg.2 h)] at h1
      linarith

/-- **The Harnack bound (4.13) for the Green kernel of `B_r(η(a))`** (Berestycki–Gwynne 2020, proof of Lemma 4.4)
from the cell size estimate and the ring events of Lemma 3.10 (`hRing`): the hypothesis `hHarn` of
`greenKernelLowerBoundStmt_of_inputs`, with `β = min(β₀, (2+γ)^{-2}/2, α₀/10)` and `C₁ = p⁻¹`. -/
theorem hHarn_ball_of_ring {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∀ y ∈ cellVertices ε (S.η ω) (sphere (vertexPoint ε (S.η ω) a) s),
        ∀ y' ∈ cellVertices ε (S.η ω) (sphere (vertexPoint ε (S.η ω) a) s),
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a y ≤
            C₁ * greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a y'} := by
  intro γ hγ hγ2
  obtain ⟨β₀, α₀, hβ₀, hα₀, hring⟩ := hRing γ hγ hγ2
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have h2e : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he]
    ring
  set β : ℝ := min β₀ (min (e / 2) (α₀ / 10)) with hβdef
  have hβ0 : 0 < β := lt_min hβ₀ (lt_min (by positivity) (by positivity))
  have hββ₀ : β ≤ β₀ := min_le_left _ _
  have hβe : β ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hβα : β ≤ α₀ / 10 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨β, hβ0, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨p, hp0, hp1, hringp⟩ := hring ((1 + ρ) / 2) (by linarith) (by linarith)
  refine ⟨p⁻¹, (one_le_inv₀ hp0).2 hp1, fun Ω _ S hS => ?_⟩
  obtain ⟨C, hC⟩ := hringp Ω S hS
  have hU : Gauss.PolyHighProb S.P _ := polyHighProb_ringEvents (P := S.P) S.mult S.η hβ0 hββ₀
    (ρ' := (1 + ρ) / 2) (p := p) (C := max C 0) (by linarith) (le_max_right _ _)
    (fun ε hε hε1 z' hz s' hs hs2 => (hC ε hε hε1 z' hz s' hs hs2).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _))))
  have hsz : Gauss.PolyHighProb S.P _ := hsize γ hγ hγ2 e ρ he0 he1 hρ hρ1 Ω S hS
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | HarnackQual S ω ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)} := by
    filter_upwards [hS.ae_harnack_inputs hγ hγ2, hS.ae_tendsto_cocompact] with ω h1 h2
    exact ⟨h1, h2⟩
  have h2 := polyHighProb_inter_ae (polyHighProb_inter hU hsz) hW
  obtain ⟨r₁, hr₁, hr₁t⟩ := exists_rpow_le_of_small hβ0 (show (0 : ℝ) < 1 / 10 by norm_num)
  refine polyHighProb_mono_of_eventually h2 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r₁ 1 from lt_min hr₁ one_pos)] with ε hε
  rintro ω ⟨⟨hUω, hSzω⟩, ⟨hηc, hall⟩, hprop⟩
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hεr : ε < r₁ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  obtain ⟨hlf, hcons, hedge, -⟩ := hall ε hε0
  have ht : ε ^ β ≤ 1 / 10 := hr₁t ε hε0 hεr
  have ht0 : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have ht2 : ε ^ (2 * β) = (ε ^ β) ^ 2 := by
    rw [show 2 * β = β * 2 by ring, Real.rpow_mul hε0.le, Real.rpow_two]
  have hsq : (ε ^ β) ^ 2 ≤ ε ^ β / 10 := by nlinarith
  have hh2 : ε ^ (2 * β) ≤ ε ^ β / 10 := by rw [ht2]; exact hsq
  have hh0 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
  have hδ : ε ^ e ≤ ε ^ β / 10 := by
    refine le_trans ?_ hsq
    rw [← ht2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have hbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε (S.η ω) k) := fun k =>
    (isCompact_Icc.image hηc).isBounded
  intro a ha r hr s hs hsr y hy y' hy'
  have hdiam : ∀ x ∈ cell ε (S.η ω) a, ∀ x' ∈ cell ε (S.η ω) a, dist x x' ≤ ε ^ e := by
    intro x hx x' hx'
    have hd := (hSzω a ha).2
    rw [h2e] at hd
    exact (Metric.dist_le_diam_of_mem (hbdd a) hx hx').trans hd
  have hBfin : (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)).Finite :=
    (cellVertices_finite_of_isCompact hηc hprop hε0
      (isCompact_closedBall (vertexPoint ε (S.η ω) a) r)).subset fun k hk => by
        obtain ⟨x, hx1, hx2⟩ := interiorCellVertices_subset _ _ _ hk
        exact ⟨x, hx1, ball_subset_closedBall hx2⟩
  obtain ⟨x₀, hx₀c, hx₀b⟩ := ha
  have hva : ‖vertexPoint ε (S.η ω) a‖ ≤ ρ + ε ^ e := by
    have h3 := norm_sub_norm_le (vertexPoint ε (S.η ω) a) x₀
    rw [← dist_eq_norm] at h3
    have h4 := hdiam _ (vertexPoint_mem_cell hε0.le _ a) _ hx₀c
    have h5 : ‖x₀‖ < ρ := mem_ball_zero_iff.1 hx₀b
    linarith
  have hnr : ‖vertexPoint ε (S.η ω) a‖ + r ≤ ρ := by
    rcases norm_add_le_or_add_le_norm_of_le_infDist_sphere hρ hr with h1 | h1
    · exact h1
    · exfalso
      linarith
  refine greenKernel_le_inv_mul_of_ringEvents_ball hε0.le hηc (S.mult_symm ε ω) hlf hcons hedge
    hh0 hp0 hBfin hdiam (by linarith) hsr (by linarith) ?_ y hy y' hy'
  intro m' n' a' hz hs1 hs2
  have h3 := norm_sub_norm_le (latticePt (ε ^ (2 * β)) m' n') (vertexPoint ε (S.η ω) a)
  rw [← dist_eq_norm, dist_comm] at h3
  have hn := norm_nonneg (latticePt (ε ^ (2 * β)) m' n')
  have hvn := norm_nonneg (vertexPoint ε (S.η ω) a)
  have hz1 : ‖latticePt (ε ^ (2 * β)) m' n'‖ < (1 + ρ) / 2 := by linarith
  have hz2 : ε ^ β ≤ sqrt2Pow a' := by linarith
  have hz3 : 2 * sqrt2Pow a' ≤ (1 + ρ) / 2 - ‖latticePt (ε ^ (2 * β)) m' n'‖ := by linarith
  exact hUω (m', n', a') (mem_gridIndexBox hh0 ht0 (by linarith) hz2 (by linarith)) ⟨hz1, hz2, hz3⟩

/-- **Lemma 2.16** (Berestycki–Gwynne 2020, Lemma 4.4) from the cell size estimate, the ring events of ibid.
Lemma 3.10 (`hRing`, giving the Harnack bound (4.13) by `hHarn_ball_of_ring`) and the resistance bound (4.15) for
the annuli `B_{3r/4}(η(a)) \ B̄_s(η(a))` (`hres`). -/
theorem greenKernelLowerBoundStmt_of_ring {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hres : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε (S.η ω) (closedBall (vertexPoint ε (S.η ω) a) s), h k = 1) ∧
          (∀ k, k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (3 * r / 4)) → h k = 0) ∧
          ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
            ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T, (S.mult ε ω k l : ℝ) * (h k - h l) ^ 2) ≤ C₂}) :
    GreenKernelLowerBoundStmt 𝒮 :=
  greenKernelLowerBoundStmt_of_inputs hsize (hHarn_ball_of_ring hsize hRing) hres

end MatedCRT
