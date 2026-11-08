import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Proofs.Field.WholePlaneConeLaw
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Measurability.FieldCircle
import MatedCRT.Proofs.Measurability.GoodScale

/-!
# `ConeWholePlaneWeylComparisonStep` (Lemma 6.5, Step 1), proved from the Harmonic-Balls definitions

Fix `r, z`, the annulus `U = annulus z (r/3) (3r)` (away from `0` by `r/100 ≤ infDist 0 U`), and the cut-off `c`
(`cutoffC`: `1` on `annulus z (4r/5) (11r/5)`, support in `U`). The good-annulus event depends only on the measure
restricted to `annulus z (4r/5) (11r/5)` (`isGoodAnnulusEvent_congr`), so it depends only on `c · μ`.

The cut-off LQG measure is the vague limit of the cut-off dyadic approximations. Their densities are built from the
grid versions (`FieldCircle.gridVersion`) of the region family, which are jointly measurable. So
`exists_theta` gives a measurable functional `Θ` of the region family whose value is `c · μ` whenever the approximations
converge vaguely. On the cone side the family is `(h_ε(w))_{region}`; on the whole-plane side it is
`(fieldCircleAverage γ h' ε w)_{region}`, where `fieldCircleAverage` contributes `|w|^{-γ²}` on `U`. `cone_circle_law`
says that the two families have the same law, so the two probabilities coincide.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT
namespace AnnulusHitField

open MatedCRT.Field

/-! ### Annuli and the cut-off -/

lemma mem_annulus_iff {z u : ℂ} {a b : ℝ} : u ∈ annulus z a b ↔ a < dist u z ∧ dist u z < b := by
  unfold annulus
  simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma isOpen_annulus (z : ℂ) (a b : ℝ) : IsOpen (annulus z a b) :=
  isOpen_ball.sdiff isClosed_closedBall

/-- The cut-off: `1` on `4r/5 ≤ |u - z| ≤ 11r/5`, `0` off `(r/3, 3r)`, piecewise linear in between. -/
def cutoffC (r : ℝ) (z u : ℂ) : ℝ :=
  min (min 1 (max 0 (15 / (7 * r) * (dist u z - r / 3))))
    (min 1 (max 0 (5 / (4 * r) * (3 * r - dist u z))))

lemma continuous_cutoffC (r : ℝ) (z : ℂ) : Continuous (cutoffC r z) := by
  have hd : Continuous fun u : ℂ => dist u z := continuous_id.dist continuous_const
  have h1 : Continuous fun u : ℂ => 15 / (7 * r) * (dist u z - r / 3) :=
    (hd.sub continuous_const).const_mul _
  have h2 : Continuous fun u : ℂ => 5 / (4 * r) * (3 * r - dist u z) :=
    (continuous_const.sub hd).const_mul _
  unfold cutoffC
  exact (continuous_const.min (continuous_const.max h1)).min
    (continuous_const.min (continuous_const.max h2))

lemma cutoffC_nonneg (r : ℝ) (z u : ℂ) : 0 ≤ cutoffC r z u := by
  unfold cutoffC
  exact le_min (le_min zero_le_one (le_max_left _ _)) (le_min zero_le_one (le_max_left _ _))

lemma cutoffC_eq_one {r : ℝ} (hr : 0 < r) {z u : ℂ} (h1 : 4 * r / 5 < dist u z)
    (h2 : dist u z < 11 * r / 5) : cutoffC r z u = 1 := by
  have hA : 1 ≤ 15 / (7 * r) * (dist u z - r / 3) := by
    rw [div_mul_eq_mul_div, one_le_div (mul_pos (by norm_num) hr)]
    linarith
  have hB : 1 ≤ 5 / (4 * r) * (3 * r - dist u z) := by
    rw [div_mul_eq_mul_div, one_le_div (mul_pos (by norm_num) hr)]
    linarith
  unfold cutoffC
  rw [max_eq_right (zero_le_one.trans hA), min_eq_left hA, max_eq_right (zero_le_one.trans hB),
    min_eq_left hB, min_self]

lemma cutoffC_eq_zero {r : ℝ} (hr : 0 < r) {z u : ℂ} (h : dist u z ≤ r / 3 ∨ 3 * r ≤ dist u z) :
    cutoffC r z u = 0 := by
  have hle : cutoffC r z u ≤ 0 := by
    unfold cutoffC
    rcases h with h | h
    · have h0 : 0 ≤ 15 / (7 * r) := div_nonneg (by norm_num) (by linarith)
      have hA : 15 / (7 * r) * (dist u z - r / 3) ≤ 0 := by
        nlinarith [mul_nonneg h0 (sub_nonneg.2 h)]
      exact (min_le_left _ _).trans (min_le_of_right_le (max_le le_rfl hA))
    · have h0 : 0 ≤ 5 / (4 * r) := div_nonneg (by norm_num) (by linarith)
      have hB : 5 / (4 * r) * (3 * r - dist u z) ≤ 0 := by
        nlinarith [mul_nonneg h0 (sub_nonneg.2 h)]
      exact (min_le_right _ _).trans (min_le_of_right_le (max_le le_rfl hB))
  exact le_antisymm hle (cutoffC_nonneg r z u)

lemma mem_annulus_of_cutoffC_ne {r : ℝ} (hr : 0 < r) {z u : ℂ} (h : cutoffC r z u ≠ 0) :
    u ∈ annulus z (r / 3) (3 * r) := by
  rw [mem_annulus_iff]
  by_contra hu
  refine h (cutoffC_eq_zero hr ?_)
  rw [not_and_or, not_lt, not_lt] at hu
  exact hu

lemma hasCompactSupport_cutoffC {r : ℝ} (hr : 0 < r) (z : ℂ) : HasCompactSupport (cutoffC r z) := by
  refine HasCompactSupport.intro (isCompact_closedBall z (3 * r)) fun u hu =>
    cutoffC_eq_zero hr (Or.inr ?_)
  rw [mem_closedBall, not_le] at hu
  exact hu.le

lemma norm_ge_of_mem_annulus {r : ℝ} {z w : ℂ}
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r))) (hw : w ∈ annulus z (r / 3) (3 * r)) :
    r / 100 ≤ ‖w‖ := by
  have h : infDist 0 (annulus z (r / 3) (3 * r)) ≤ dist 0 w := infDist_le_dist_of_mem hw
  rw [dist_zero_left] at h
  linarith

lemma cutoffC_eq_zero_of_norm_lt {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r))) {u : ℂ} (hu : ‖u‖ < r / 100) :
    cutoffC r z u = 0 := by
  by_contra hc
  have hmem := mem_annulus_of_cutoffC_ne hr hc
  have hn := norm_ge_of_mem_annulus hdist hmem
  linarith

/-- The weight `c(u) ‖u‖^{-γ²}` (the exponent is written as in the statement, `-γ ^ 2`). -/
def weightW (γ : ℝ) (c : ℂ → ℝ) (u : ℂ) : ℝ := c u * ‖u‖ ^ (-γ ^ 2)

lemma continuous_weightW {γ : ℝ} {c : ℂ → ℝ} (hc : Continuous c) {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ u, ‖u‖ < δ → c u = 0) : Continuous (weightW γ c) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    have hev : (fun v => weightW γ c v) =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℝ) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with v hv
      rw [mem_ball_zero_iff] at hv
      simp [weightW, hz v hv]
    exact continuousAt_const.congr hev.symm
  · exact (hc.continuousAt).mul ((continuous_norm.continuousAt).rpow_const
      (Or.inl (norm_ne_zero_iff.2 hu)))

lemma weightW_nonneg {γ : ℝ} {c : ℂ → ℝ} (hc0 : ∀ u, 0 ≤ c u) (u : ℂ) : 0 ≤ weightW γ c u :=
  mul_nonneg (hc0 u) (Real.rpow_nonneg (norm_nonneg u) _)

lemma continuous_slice_of_contOn {H : ℝ → ℂ → ℝ}
    (hH : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ} (hε : 0 < ε) :
    Continuous (H ε) := by
  have hc : ContinuousOn (fun z : ℂ => ((ε, z) : ℝ × ℂ)) univ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h : ContinuousOn (fun z : ℂ => H ε z) univ :=
    hH.comp hc (fun z _ => ⟨hε, mem_univ z⟩)
  exact continuousOn_univ.1 h

/-! ### Scales and the region -/

lemma dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  exact pow_pos (by norm_num) k

lemma dyadicScale_le {N k : ℕ} (h : N ≤ k) : dyadicScale k ≤ dyadicScale N := by
  unfold dyadicScale
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

lemma scale_lt {r ρ : ℝ} {N : ℕ} (hN : dyadicScale N < min (r / 100) (1 - ρ)) (n : ℕ) :
    dyadicScale (n + N) < min (r / 100) (1 - ρ) :=
  lt_of_le_of_lt (dyadicScale_le (Nat.le_add_left N n)) hN

lemma inLevelRegion_of_mem_annulus {r ρ : ℝ} {z w : ℂ} {ε : ℝ}
    (hsub : annulus z (r / 3) (3 * r) ⊆ ball 0 ρ)
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r)))
    (hε0 : 0 < ε) (hεδ : ε < min (r / 100) (1 - ρ)) (hw : w ∈ annulus z (r / 3) (3 * r)) :
    InLevelRegion ε w := by
  have h1 : r / 100 ≤ ‖w‖ := norm_ge_of_mem_annulus hdist hw
  have h2 : ‖w‖ < ρ := by
    have h := hsub hw
    rwa [mem_ball_zero_iff] at h
  have hd1 : ε < r / 100 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hd2 : ε < 1 - ρ := lt_of_lt_of_le hεδ (min_le_right _ _)
  exact ⟨hε0, by linarith, by linarith⟩

lemma exp_sub_log_norm {γ h : ℝ} {w : ℂ} (hw : 0 < ‖w‖) :
    Real.exp (γ * (h - γ * Real.log ‖w‖)) = Real.exp (γ * h) * ‖w‖ ^ (-γ ^ 2) := by
  rw [Real.rpow_def_of_pos hw, ← Real.exp_add]
  congr 1
  ring

/-! ### Extension of a region family and the grid densities -/

open Classical in
/-- Extension by zero of a region-indexed family to all scales and centres. -/
def extF (F : RegIdx → ℝ) (ε : ℝ) (w : ℂ) : ℝ :=
  if h : InLevelRegion ε w then F ⟨(ε, w), h⟩ else 0

lemma measurable_extF (ε : ℝ) (w : ℂ) : Measurable fun F : RegIdx → ℝ => extF F ε w := by
  by_cases h : InLevelRegion ε w
  · have e : (fun F : RegIdx → ℝ => extF F ε w) = fun F => F ⟨(ε, w), h⟩ := by
      funext F
      simp [extF, h]
    rw [e]
    exact measurable_pi_apply _
  · have e : (fun F : RegIdx → ℝ => extF F ε w) = fun _ => 0 := by
      funext F
      simp [extF, h]
    rw [e]
    exact measurable_const

/-- The cut-off grid density at dyadic index `n` (shifted by `N`) of the region family `F`. -/
def gdens (γ : ℝ) (c : ℂ → ℝ) (N n : ℕ) (F : RegIdx → ℝ) (z : ℂ) : ℝ :=
  c z * (dyadicScale (n + N) ^ (γ ^ 2 / 2) *
    Real.exp (γ * FieldCircle.gridVersion (fun w (G : RegIdx → ℝ) => extF G (dyadicScale (n + N)) w) F z))

/-- The measure with density `gdens`. -/
def gmeas (γ : ℝ) (c : ℂ → ℝ) (N n : ℕ) (F : RegIdx → ℝ) : Measure ℂ :=
  (volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (gdens γ c N n F z)

lemma gdens_nonneg {γ : ℝ} {c : ℂ → ℝ} (hc0 : ∀ z, 0 ≤ c z) (N n : ℕ) (F : RegIdx → ℝ) (z : ℂ) :
    0 ≤ gdens γ c N n F z :=
  mul_nonneg (hc0 z) (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _) (Real.exp_pos _).le)

lemma measurable_gdens (γ : ℝ) {c : ℂ → ℝ} (hc : Measurable c) (N n : ℕ) :
    Measurable (Function.uncurry (gdens γ c N n)) := by
  have hG := FieldCircle.measurable_gridVersion
    (fun w (G : RegIdx → ℝ) => extF G (dyadicScale (n + N)) w) (fun w => measurable_extF _ _)
  have e : Function.uncurry (gdens γ c N n) = fun p : (RegIdx → ℝ) × ℂ =>
      c p.2 * (dyadicScale (n + N) ^ (γ ^ 2 / 2) *
        Real.exp (γ * FieldCircle.gridVersion
          (fun w (G : RegIdx → ℝ) => extF G (dyadicScale (n + N)) w) p.1 p.2)) := rfl
  rw [e]
  exact (hc.comp measurable_snd).mul
    (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hG)))

lemma measurable_gmeas (γ : ℝ) {c : ℂ → ℝ} (hc : Measurable c) (N n : ℕ) :
    Measurable (gmeas γ c N n) :=
  LQGMeasureField.measurable_withDensity_ofReal (measurable_gdens γ hc N n)

lemma measurable_integral_gmeas (γ : ℝ) {c : ℂ → ℝ} (hc : Measurable c) (hc0 : ∀ z, 0 ≤ c z) (N n : ℕ)
    {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun F : RegIdx → ℝ => ∫ z, f z ∂(gmeas γ c N n F) :=
  LQGMeasureField.measurable_integral_withDensity_ofReal (measurable_gdens γ hc N n)
    (gdens_nonneg hc0 N n) hf

/-- A measurable functional `Θ` of the region family, equal to the vague limit of the cut-off approximations
whenever these converge vaguely (`exists_measurable_vagueLimit`). -/
lemma exists_theta (γ : ℝ) {c : ℂ → ℝ} (hc : Measurable c) (hc0 : ∀ z, 0 ≤ c z) (N : ℕ) :
    ∃ Θ : (RegIdx → ℝ) → Measure ℂ, Measurable Θ ∧
      ∀ (F : RegIdx → ℝ) (μ0 : Measure ℂ), (∀ K, IsCompact K → ∀ᶠ n in atTop, gmeas γ c N n F K < ⊤) →
        QuantumZipper.IsVagueLimitOn univ (fun n => gmeas γ c N n F) μ0 → Θ F = μ0 := by
  obtain ⟨Θ, hΘm, hΘ⟩ := VagueWholePlane.exists_measurable_vagueLimit (Ω := RegIdx → ℝ)
    (fun n => gmeas γ c N n) (fun n => measurable_gmeas γ hc N n)
    (fun n f hf _ => measurable_integral_gmeas γ hc hc0 N n hf.measurable)
  exact ⟨Θ, hΘm, fun F μ0 hfin hvag => hΘ F μ0 hfin hvag⟩

/-! ### Grid versions on an open set -/

lemma gridVersion_eq_of_open {Ω : Type*} {X : ℂ → Ω → ℝ} {ω : Ω} {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℝ}
    (hg : ContinuousOn g U) (hX : ∀ w ∈ U, X w ω = g w) {z : ℂ} (hz : z ∈ U) :
    FieldCircle.gridVersion X ω z = g z := by
  have h1 : Tendsto (fun m : ℕ => FieldCircle.gridApprox m z) atTop (𝓝 z) :=
    FieldCircle.tendsto_gridApprox z
  have h2 : Tendsto (fun m : ℕ => g (FieldCircle.gridApprox m z)) atTop (𝓝 (g z)) :=
    ((hg.continuousAt (hU.mem_nhds hz)).tendsto).comp h1
  have h3 : Tendsto (fun m : ℕ => X (FieldCircle.gridApprox m z) ω) atTop (𝓝 (g z)) := by
    refine h2.congr' ?_
    filter_upwards [h1.eventually (hU.mem_nhds hz)] with m hm
    exact (hX _ hm).symm
  exact h3.limsup_eq

/-- On the cone side the grid density of the restricted family is the cut-off circle-average density. -/
lemma gdens_cone {γ r ρ : ℝ} {z : ℂ} {N : ℕ} (hr : 0 < r)
    (hsub : annulus z (r / 3) (3 * r) ⊆ ball 0 ρ)
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r))) (hN : dyadicScale N < min (r / 100) (1 - ρ))
    {H : ℝ → ℂ → ℝ} (hH : ∀ k : ℕ, ContinuousOn (H (dyadicScale (k + N))) (annulus z (r / 3) (3 * r)))
    (n : ℕ) (w : ℂ) :
    gdens γ (cutoffC r z) N n (fun o : RegIdx => H o.1.1 o.1.2) w =
      cutoffC r z w * (dyadicScale (n + N) ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale (n + N)) w)) := by
  have hε0 : 0 < dyadicScale (n + N) := dyadicScale_pos _
  have hεδ : dyadicScale (n + N) < min (r / 100) (1 - ρ) := scale_lt hN n
  unfold gdens
  by_cases hw : w ∈ annulus z (r / 3) (3 * r)
  · have hgv : FieldCircle.gridVersion (fun u (G : RegIdx → ℝ) => extF G (dyadicScale (n + N)) u)
        (fun o : RegIdx => H o.1.1 o.1.2) w = H (dyadicScale (n + N)) w := by
      refine gridVersion_eq_of_open (isOpen_annulus z _ _) (hH n) (fun u hu => ?_) hw
      have hreg := inLevelRegion_of_mem_annulus hsub hdist hε0 hεδ hu
      show extF (fun o : RegIdx => H o.1.1 o.1.2) (dyadicScale (n + N)) u = H (dyadicScale (n + N)) u
      simp [extF, hreg]
    rw [hgv]
  · have hc : cutoffC r z w = 0 := by
      by_contra h
      exact hw (mem_annulus_of_cutoffC_ne hr h)
    rw [hc, zero_mul, zero_mul]

/-- On the whole-plane side the grid density of the restricted fieldCircleAverage family is the weighted density. -/
lemma gdens_wp {γ r ρ : ℝ} {z : ℂ} {N : ℕ} (hr : 0 < r)
    (hsub : annulus z (r / 3) (3 * r) ⊆ ball 0 ρ)
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r))) (hN : dyadicScale N < min (r / 100) (1 - ρ))
    {H : ℝ → ℂ → ℝ} (hH : ∀ k : ℕ, ContinuousOn (H (dyadicScale (k + N))) (annulus z (r / 3) (3 * r)))
    (n : ℕ) (w : ℂ) :
    gdens γ (cutoffC r z) N n (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ H o.1.1 o.1.2) w =
      weightW γ (cutoffC r z) w * (dyadicScale (n + N) ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale (n + N)) w)) := by
  have hε0 : 0 < dyadicScale (n + N) := dyadicScale_pos _
  have hεδ : dyadicScale (n + N) < min (r / 100) (1 - ρ) := scale_lt hN n
  unfold gdens weightW
  by_cases hw : w ∈ annulus z (r / 3) (3 * r)
  · have hnorm : r / 100 ≤ ‖w‖ := norm_ge_of_mem_annulus hdist hw
    have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by linarith) hnorm
    have hpos : ∀ u ∈ annulus z (r / 3) (3 * r), ‖u‖ ≠ 0 := fun u hu =>
      (lt_of_lt_of_le (by linarith) (norm_ge_of_mem_annulus hdist hu)).ne'
    have hcontU : ContinuousOn (fun u => H (dyadicScale (n + N)) u - γ * Real.log ‖u‖)
        (annulus z (r / 3) (3 * r)) :=
      (hH n).sub (continuousOn_const.mul (continuous_norm.continuousOn.log hpos))
    have hgv : FieldCircle.gridVersion (fun u (G : RegIdx → ℝ) => extF G (dyadicScale (n + N)) u)
        (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ H o.1.1 o.1.2) w =
          H (dyadicScale (n + N)) w - γ * Real.log ‖w‖ := by
      refine gridVersion_eq_of_open (isOpen_annulus z _ _) hcontU (fun u hu => ?_) hw
      have hreg := inLevelRegion_of_mem_annulus hsub hdist hε0 hεδ hu
      show extF (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ H o.1.1 o.1.2)
        (dyadicScale (n + N)) u = H (dyadicScale (n + N)) u - γ * Real.log ‖u‖
      rw [show extF (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ H o.1.1 o.1.2)
          (dyadicScale (n + N)) u = HarmonicBalls.fieldCircleAverage γ H (dyadicScale (n + N)) u by
        simp [extF, hreg]]
      unfold HarmonicBalls.fieldCircleAverage
      rw [circleAverage_log_norm_center hε0 hreg.2.1]
    rw [hgv, exp_sub_log_norm hw0]
    ring
  · have hc : cutoffC r z w = 0 := by
      by_contra h
      exact hw (mem_annulus_of_cutoffC_ne hr h)
    rw [hc, zero_mul, zero_mul]
    ring

/-! ### Measure-level identities -/

lemma integral_withDensity_ofReal' {α : Type*} [MeasurableSpace α] (ν : Measure α) {g : α → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (hgm : Measurable g) (f : α → ℝ) :
    ∫ x, f x ∂(ν.withDensity fun x => ENNReal.ofReal (g x)) = ∫ x, g x * f x ∂ν := by
  have hm : Measurable fun x => Real.toNNReal (g x) := hgm.real_toNNReal
  have e : (fun x => ENNReal.ofReal (g x)) = fun x => ((Real.toNNReal (g x) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [e, integral_withDensity_eq_integral_smul hm]
  congr 1
  funext x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hg0 x)]

/-- The vague-limit identification of the cut-off approximations (`IsLQGLimit` along dyadic scales). -/
lemma vague_of_lqg (γ : ℝ) {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ0 : ∀ z, 0 ≤ φ z) (N : ℕ) {H : ℝ → ℂ → ℝ} (hHc : ∀ k : ℕ, Continuous (H (dyadicScale (k + N))))
    {m : Measure ℂ} (hm : IsLQGLimit γ H m) (G : ℕ → Measure ℂ)
    (hG : ∀ n : ℕ, G n = (volume : Measure ℂ).withDensity fun z =>
      ENNReal.ofReal (φ z * (dyadicScale (n + N) ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale (n + N)) z)))) :
    (∀ K, IsCompact K → ∀ᶠ n in atTop, G n K < ⊤) ∧
      QuantumZipper.IsVagueLimitOn univ G (m.withDensity fun z => ENNReal.ofReal (φ z)) := by
  have hdc : ∀ n : ℕ, Continuous fun z => dyadicScale (n + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * H (dyadicScale (n + N)) z) := fun n =>
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hHc n)))
  have hdnn : ∀ n : ℕ, ∀ z, 0 ≤ dyadicScale (n + N) ^ (γ ^ 2 / 2) *
      Real.exp (γ * H (dyadicScale (n + N)) z) := fun n z =>
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _) (Real.exp_pos _).le
  have hfin : ∀ n : ℕ, ∀ K, IsCompact K → G n K < ⊤ := fun n K hK => by
    rw [hG n]
    exact LQGMeasureField.withDensity_ofReal_lt_top (hφc.mul (hdc n)) hK
  refine ⟨fun K hK => Eventually.of_forall fun n => hfin n K hK, ?_⟩
  unfold QuantumZipper.IsVagueLimitOn
  refine ⟨by simp, fun K hK _ => ?_, fun f hf hfs _ => ?_⟩
  · have := hm.isLocallyFiniteMeasure
    rw [withDensity_apply _ hK.measurableSet]
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφc.continuousOn
    calc ∫⁻ x in K, ENNReal.ofReal (φ x) ∂m ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂m :=
          setLIntegral_mono measurable_const fun x hx =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hM x hx))
      _ = ENNReal.ofReal M * m K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  · have hlim := (tendsto_add_atTop_iff_nat N).2
      (hm.tendsto_integral (fun z => φ z * f z) (hφc.mul hf) hφs.mul_right)
    rw [integral_withDensity_ofReal' m hφ0 hφc.measurable f]
    refine Tendsto.congr (fun n => ?_) hlim
    show ∫ z, φ z * f z ∂(lqgApprox γ H (dyadicScale (n + N))) = ∫ z, f z ∂(G n)
    have h1 : ∫ z, φ z * f z ∂(lqgApprox γ H (dyadicScale (n + N))) =
        ∫ z, (dyadicScale (n + N) ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicScale (n + N)) z)) * (φ z * f z)
          ∂(volume : Measure ℂ) :=
      integral_withDensity_ofReal' volume (fun z => hdnn n z) (hdc n).measurable _
    have h2 : ∫ z, f z ∂(G n) = ∫ z, (φ z * (dyadicScale (n + N) ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (dyadicScale (n + N)) z))) * f z ∂(volume : Measure ℂ) := by
      rw [hG n]
      exact integral_withDensity_ofReal' volume (fun z => mul_nonneg (hφ0 z) (hdnn n z))
        ((hφc.mul (hdc n)).measurable) f
    rw [h1, h2]
    congr 1
    funext z
    ring

/-! ### Locality of the good-annulus event -/

/-- The good-annulus event depends only on the densities on `annulus z (4r/5) (11r/5)`. -/
lemma isGoodAnnulusEvent_congr {c₀ C r : ℝ} {z : ℂ} (hr : 0 < r) (hc₀ : c₀ < 1 / 5) (μ : Measure ℂ)
    {g₁ g₂ : ℂ → ℝ≥0∞} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (heq : ∀ u ∈ annulus z (4 * r / 5) (11 * r / 5), g₁ u = g₂ u) :
    IsGoodAnnulusEvent (μ.withDensity g₁) c₀ C r z ↔ IsGoodAnnulusEvent (μ.withDensity g₂) c₀ C r z := by
  have hA₀V : annulus z r (2 * r) ⊆ annulus z (4 * r / 5) (11 * r / 5) := by
    intro u hu
    rw [mem_annulus_iff] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hballV : ∀ w ∈ annulus z r (2 * r), ball w (c₀ * r) ⊆ annulus z (4 * r / 5) (11 * r / 5) := by
    intro w hw u hu
    rw [mem_annulus_iff] at hw ⊢
    rw [mem_ball] at hu
    have ht1 := dist_triangle u w z
    have ht2 := dist_triangle w u z
    rw [dist_comm w u] at ht2
    have hcr : c₀ * r < 1 / 5 * r := mul_lt_mul_of_pos_right hc₀ hr
    constructor <;> linarith [hw.1, hw.2]
  have hmeasA : MeasurableSet (annulus z r (2 * r)) := (isOpen_annulus z r (2 * r)).measurableSet
  have hmeasF : ∀ v : ℂ, Measurable fun u : ℂ => ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) := fun v =>
    ENNReal.measurable_ofReal.comp ((measurable_const.div (measurable_id.sub_const v).norm).log.add_const 1)
  have hint : ∀ v : ℂ,
      ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂(μ.withDensity g₁) =
      ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂(μ.withDensity g₂) := by
    intro v
    rw [setLIntegral_withDensity_eq_setLIntegral_mul μ hg₁ (hmeasF v) hmeasA,
      setLIntegral_withDensity_eq_setLIntegral_mul μ hg₂ (hmeasF v) hmeasA]
    refine setLIntegral_congr_fun hmeasA fun u hu => ?_
    simp only [Pi.mul_apply]
    rw [heq u (hA₀V hu)]
  have hball : ∀ w ∈ annulus z r (2 * r),
      μ.withDensity g₁ (ball w (c₀ * r)) = μ.withDensity g₂ (ball w (c₀ * r)) := by
    intro w hw
    rw [withDensity_apply _ measurableSet_ball, withDensity_apply _ measurableSet_ball]
    refine setLIntegral_congr_fun measurableSet_ball fun u hu => ?_
    exact heq u (hballV w hw hu)
  unfold IsGoodAnnulusEvent
  have hL : (⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂(μ.withDensity g₁)) =
      (⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
        ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂(μ.withDensity g₂)) := by
    simp only [hint]
  have hR : (⨅ w ∈ annulus z r (2 * r), μ.withDensity g₁ (ball w (c₀ * r))) =
      ⨅ w ∈ annulus z r (2 * r), μ.withDensity g₂ (ball w (c₀ * r)) := by
    refine iInf_congr fun w => ?_
    by_cases hw : w ∈ annulus z r (2 * r)
    · rw [iInf_pos hw, iInf_pos hw, hball w hw]
    · rw [iInf_neg hw, iInf_neg hw]
  rw [hL, hR]

lemma measurable_fieldCircleAverage_of {Ω : Type*} [MeasurableSpace Ω] {H : Ω → ℝ → ℂ → ℝ} (γ : ℝ)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hm : ∀ r z, 0 < r → Measurable fun ω => H ω r z) :
    Measurable fun ω => HarmonicBalls.fieldCircleAverage γ (H ω) r z := by
  unfold HarmonicBalls.fieldCircleAverage
  exact (hm r z hr).sub measurable_const

/-! ### The Step -/

theorem coneWholePlaneWeylComparison : ConeWholePlaneWeylComparisonStep := by
  intro γ _ _ ρ _ hρ1 c₀ _ hc₀' C _ Ω _ P _ hcirc μ hcone Ω' _ P' _ hcirc' μ' _ hwp hlqg r z hr hsub hdist
  have hPprob : IsProbabilityMeasure P := hcone.1
  have hδ : 0 < min (r / 100) (1 - ρ) := lt_min (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨Θ, hΘm, hΘ⟩ := exists_theta γ (continuous_cutoffC r z).measurable (cutoffC_nonneg r z) N
  have hwcont : Continuous (weightW γ (cutoffC r z)) :=
    continuous_weightW (continuous_cutoffC r z) (δ := r / 100) (by linarith)
      (fun u hu => cutoffC_eq_zero_of_norm_lt hr hdist hu)
  have hwcs : HasCompactSupport (weightW γ (cutoffC r z)) :=
    (hasCompactSupport_cutoffC hr z).mul_right
  have hS : MeasurableSet (Θ ⁻¹' {m : Measure ℂ | IsGoodAnnulusEvent m c₀ C r z}ᶜ) :=
    hΘm (measurableSet_isGoodAnnulusEvent c₀ C hr z).compl
  have hLQG : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hcone.2.2
  have hLQG' : ∀ᵐ ω' ∂P', IsLQGLimit γ (hcirc' ω') (μ' ω') := hlqg
  -- the cone side: `Θ` evaluates to the cut-off LQG measure
  have hcone_ae : ∀ᵐ ω ∂P, Θ (fun o : RegIdx => hcirc ω o.1.1 o.1.2) =
      (μ ω).withDensity fun x => ENNReal.ofReal (cutoffC r z x) := by
    filter_upwards [hcone.2.1.ae_continuousOn_circle, hLQG] with ω hωc hωL
    obtain ⟨hfin, hvag⟩ := vague_of_lqg γ (continuous_cutoffC r z) (hasCompactSupport_cutoffC hr z)
      (cutoffC_nonneg r z) N (fun k => continuous_slice_of_contOn hωc (dyadicScale_pos (k + N))) hωL
      (fun n => gmeas γ (cutoffC r z) N n (fun o : RegIdx => hcirc ω o.1.1 o.1.2)) fun n => by
        show gmeas γ (cutoffC r z) N n (fun o : RegIdx => hcirc ω o.1.1 o.1.2) = _
        unfold gmeas
        congr 1
        funext w
        exact congrArg _ (gdens_cone hr hsub hdist hN
          (fun k => (continuous_slice_of_contOn hωc (dyadicScale_pos (k + N))).continuousOn) n w)
    exact hΘ _ _ hfin hvag
  -- the whole-plane side: `Θ` evaluates to the weighted LQG measure
  have hwp_ae : ∀ᵐ ω' ∂P', Θ (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2) =
      (μ' ω').withDensity fun x => ENNReal.ofReal (weightW γ (cutoffC r z) x) := by
    filter_upwards [hwp.ae_continuousOn_circle, hLQG'] with ω' hωc hωL
    obtain ⟨hfin, hvag⟩ := vague_of_lqg γ hwcont hwcs (weightW_nonneg (cutoffC_nonneg r z)) N
      (fun k => continuous_slice_of_contOn hωc (dyadicScale_pos (k + N))) hωL
      (fun n => gmeas γ (cutoffC r z) N n
        (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2)) fun n => by
        show gmeas γ (cutoffC r z) N n
          (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2) = _
        unfold gmeas
        congr 1
        funext w
        exact congrArg _ (gdens_wp hr hsub hdist hN
          (fun k => (continuous_slice_of_contOn hωc (dyadicScale_pos (k + N))).continuousOn) n w)
    exact hΘ _ _ hfin hvag
  -- locality of the event
  have hloc_cone : ∀ m : Measure ℂ, IsGoodAnnulusEvent m c₀ C r z ↔
      IsGoodAnnulusEvent (m.withDensity fun x => ENNReal.ofReal (cutoffC r z x)) c₀ C r z := by
    intro m
    have heq : ∀ u ∈ annulus z (4 * r / 5) (11 * r / 5),
        (1 : ℂ → ℝ≥0∞) u = ENNReal.ofReal (cutoffC r z u) := by
      intro u hu
      rw [mem_annulus_iff] at hu
      simp [cutoffC_eq_one hr hu.1 hu.2]
    have h := isGoodAnnulusEvent_congr (C := C) hr hc₀' m measurable_one
      (ENNReal.measurable_ofReal.comp (continuous_cutoffC r z).measurable) heq
    rwa [withDensity_one] at h
  have hloc_wp : ∀ m : Measure ℂ,
      IsGoodAnnulusEvent (m.withDensity fun x => ENNReal.ofReal (weightW γ (cutoffC r z) x)) c₀ C r z ↔
      IsGoodAnnulusEvent (m.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) c₀ C r z := by
    intro m
    have heq : ∀ u ∈ annulus z (4 * r / 5) (11 * r / 5),
        ENNReal.ofReal (weightW γ (cutoffC r z) u) = ENNReal.ofReal (‖u‖ ^ (-γ ^ 2)) := by
      intro u hu
      rw [mem_annulus_iff] at hu
      simp [weightW, cutoffC_eq_one hr hu.1 hu.2]
    exact isGoodAnnulusEvent_congr (C := C) hr hc₀' m hwcont.measurable.ennreal_ofReal
      ((measurable_norm.pow_const _).ennreal_ofReal) heq
  -- the two families have the same law (`cone_circle_law`)
  obtain ⟨Ω'', _, P'', hP'', hC'', hcirc'', hwp'', hlaw⟩ := hcone.2.1.lateral_law
  have hcl := cone_circle_law hcone.2.1 (fun r z hr => hcone.2.1.measurable_circle r z hr) hwp'' hlaw hwp
  have hXc : Measurable (fun (ω : Ω) (o : RegIdx) => hcirc ω o.1.1 o.1.2) :=
    measurable_pi_iff.mpr fun o => hcone.2.1.measurable_circle _ _ o.2.1
  have hXG : Measurable (fun (ω' : Ω') (o : RegIdx) =>
      HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2) :=
    measurable_pi_iff.mpr fun o => measurable_fieldCircleAverage_of γ o.1.2 o.2.1 hwp.measurable_circle
  refine le_of_eq ?_
  calc P {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z}
      = P {ω | ¬ IsGoodAnnulusEvent (Θ (fun o : RegIdx => hcirc ω o.1.1 o.1.2)) c₀ C r z} := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [hcone_ae] with ω hω
        show ¬ IsGoodAnnulusEvent (μ ω) c₀ C r z ↔
          ¬ IsGoodAnnulusEvent (Θ (fun o : RegIdx => hcirc ω o.1.1 o.1.2)) c₀ C r z
        rw [hω]
        exact not_congr (hloc_cone (μ ω))
    _ = P ((fun ω (o : RegIdx) => hcirc ω o.1.1 o.1.2) ⁻¹'
          (Θ ⁻¹' {m : Measure ℂ | IsGoodAnnulusEvent m c₀ C r z}ᶜ)) := rfl
    _ = P.map (fun ω (o : RegIdx) => hcirc ω o.1.1 o.1.2)
          (Θ ⁻¹' {m : Measure ℂ | IsGoodAnnulusEvent m c₀ C r z}ᶜ) :=
        (Measure.map_apply hXc hS).symm
    _ = P'.map (fun ω' (o : RegIdx) => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2)
          (Θ ⁻¹' {m : Measure ℂ | IsGoodAnnulusEvent m c₀ C r z}ᶜ) := by
        rw [hcl]
    _ = P' ((fun ω' (o : RegIdx) => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2) ⁻¹'
          (Θ ⁻¹' {m : Measure ℂ | IsGoodAnnulusEvent m c₀ C r z}ᶜ)) :=
        Measure.map_apply hXG hS
    _ = P' {ω' | ¬ IsGoodAnnulusEvent
          (Θ (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2)) c₀ C r z} := rfl
    _ = P' {ω' | ¬ IsGoodAnnulusEvent
          ((μ' ω').withDensity fun x => ENNReal.ofReal (weightW γ (cutoffC r z) x)) c₀ C r z} := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [hwp_ae] with ω' hω'
        show ¬ IsGoodAnnulusEvent
            (Θ (fun o : RegIdx => HarmonicBalls.fieldCircleAverage γ (hcirc' ω') o.1.1 o.1.2)) c₀ C r z ↔
          ¬ IsGoodAnnulusEvent ((μ' ω').withDensity fun x => ENNReal.ofReal (weightW γ (cutoffC r z) x)) c₀ C r z
        rw [hω']
    _ = P' {ω' | ¬ IsGoodAnnulusEvent
          ((μ' ω').withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) c₀ C r z} := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 (Filter.Eventually.of_forall fun ω' => ?_))
        show ¬ IsGoodAnnulusEvent ((μ' ω').withDensity fun x => ENNReal.ofReal (weightW γ (cutoffC r z) x))
            c₀ C r z ↔
          ¬ IsGoodAnnulusEvent ((μ' ω').withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) c₀ C r z
        exact not_congr (hloc_wp (μ' ω'))

end AnnulusHitField
end MatedCRT
