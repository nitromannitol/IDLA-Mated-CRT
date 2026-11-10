import HarmonicBalls.Defs.Notation

/-!
# Scale-covariant good-annulus event (chat 188, §3 `S1_correctedGoodAnnulus`): deterministic part

For a locally finite measure `μ` on `ℂ` (for the paper, `μ = μ_h`, the LQG measure) write
`𝔸 = 𝔸_{R,2R}(z) = annulus z R (2R)` (`HarmonicBalls.annulus`: the open annulus `{R < |u - z| < 2R}`), and

* `covKernel R v u`: the scale-covariant kernel `log (4R/|u-v|) + 1` on `𝔸` (`+∞` on the diagonal, as in the paper);
* `covN R z μ = sup_{v ∈ closure 𝔸} ∫_𝔸 (log (4R/|u-v|) + 1) dμ(u)`;
* `massBumpR c0 R z μ = inf_{w ∈ closure 𝔸} ∫ φ((u-w)/(c0 R)) dμ(u)` with `φ(x) = max {0, min {1, 3 - 4|x|}}`;
* `ScaleCovGoodAnnulusEvent c0 C R z μ = {0 < m_R^φ < ∞, N_R ≤ C m_R^φ}`.

This is the corrected good-annulus event of Lemmas 6.4/6.5. It replaces the printed unscaled, signed kernel
`log (1/|u-v|) + 1` ([C5], repair in `notes/fp-gaps/CHATGPT-lemma68-open-parts.md` §A4).

Proved here (deterministic):
* `scaleCovGoodAnnulusEvent_smul_iff`: the event is invariant under `μ ↦ a μ`, `a > 0` (§3 item 2);
* `scaleCovGoodAnnulusEvent_congr`: locality, the event depends only on `μ.restrict (ball z (3R))` (§3 item 1);
* `measure_annulus_le_covN`, `scaleCov_annulus_mass_le`: `μ(𝔸) ≤ N_R ≤ C m_R^φ` on the event (§3 item 4);
* `printedL_le_of_event_unit`: `L_R(z) ≤ C (1 + log 4)(1 + log(1/R)) m_R^φ` for `0 < R ≤ 1` (§3 item 4).

Not proved here:
* the measurability of the event (§3 item 1), OPEN: the countable reduction of `covN` and `massBumpR` as functions of
  `μ` is not yet written;
* the uniform one-annulus probability (§3 item 3), kept as the named hypothesis `ScaleCovUniformPrevalenceStmt`.

Terminology: LQG measure (Duplantier-Sheffield), good annuli (Berestycki-Powell, Armstrong-Kuusi-Mourrat),
log kernel potential theory (Armitage-Gardiner).
-/

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Window

/-- The radial bump `φ(x) = max {0, min {1, 3 - 4|x|}}`: `φ = 1` on `|x| ≤ 1/2`, `φ = 0` on `|x| ≥ 3/4`. -/
noncomputable def bumpPhi (x : ℂ) : ℝ := max 0 (min 1 (3 - 4 * ‖x‖))

lemma bumpPhi_nonneg (x : ℂ) : 0 ≤ bumpPhi x := le_max_left _ _

lemma bumpPhi_eq_zero {x : ℂ} (hx : 3 / 4 ≤ ‖x‖) : bumpPhi x = 0 := by
  unfold bumpPhi
  apply max_eq_left
  exact le_trans (min_le_right _ _) (by linarith)

/-- The scale-covariant kernel `log (4R/|u-v|) + 1` as an extended value; `⊤` on the diagonal. -/
noncomputable def covKernel (R : ℝ) (v u : ℂ) : ℝ≥0∞ :=
  if u = v then ⊤ else ENNReal.ofReal (Real.log (4 * R / ‖u - v‖) + 1)

/-- The printed-type kernel `log (1/|u-v|) + 1` of `L_R` (positive part; `⊤` on the diagonal). -/
noncomputable def printedKernel (v u : ℂ) : ℝ≥0∞ :=
  if u = v then ⊤ else ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1)

/-- `N_R(z; μ) = sup_{v ∈ closure 𝔸} ∫_𝔸 (log (4R/|u-v|) + 1) dμ(u)`, `𝔸 = annulus z R (2R)`. -/
noncomputable def covN (R : ℝ) (z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨆ v ∈ closure (annulus z R (2 * R)), ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ

/-- `L_R(z; μ) = sup_{v ∈ closure 𝔸} ∫_𝔸 (log (1/|u-v|) + 1) dμ(u)` (the `L_R` of §1 of the chat 188 answer). -/
noncomputable def printedL (R : ℝ) (z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨆ v ∈ closure (annulus z R (2 * R)), ∫⁻ u in annulus z R (2 * R), printedKernel v u ∂μ

/-- The bump mass `∫ φ((u-w)/(c0 R)) dμ(u)`. -/
noncomputable def bumpMass (c0 R : ℝ) (μ : Measure ℂ) (w : ℂ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))) ∂μ

/-- `m_R^φ(z; μ) = inf_{w ∈ closure 𝔸} ∫ φ((u-w)/(c0 R)) dμ(u)`. -/
noncomputable def massBumpR (c0 R : ℝ) (z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨅ w ∈ closure (annulus z R (2 * R)), bumpMass c0 R μ w

/-- The scale-covariant good-annulus event `G_{R,z}(C) = {0 < m_R^φ < ∞, N_R ≤ C m_R^φ}` (corrected Lemma 6.4/6.5). -/
def ScaleCovGoodAnnulusEvent (c0 C R : ℝ) (z : ℂ) (μ : Measure ℂ) : Prop :=
  0 < massBumpR c0 R z μ ∧ massBumpR c0 R z μ < ⊤ ∧ covN R z μ ≤ ENNReal.ofReal C * massBumpR c0 R z μ

/-- **Named hypothesis, not proved here** (§3 item 3 of chat 188, from the corrected Lemma 6.4/6.5): a uniform lower
bound `p ≤ P(G_{R,z}(C))` for all `R > 0` and `z ∈ ℂ`. Translation and dilation invariance of the whole-plane GFF gives
the independence of `(R, z)`; the positivity at one annulus is the prevalence input. -/
def ScaleCovUniformPrevalenceStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (c0 C : ℝ) : Prop :=
  ∃ p : ℝ≥0∞, 0 < p ∧ ∀ R : ℝ, 0 < R → ∀ z : ℂ, p ≤ P {ω | ScaleCovGoodAnnulusEvent c0 C R z (μ ω)}

/-! ### Geometry of the annulus -/

lemma mem_annulus_iff {z : ℂ} {r₁ r₂ : ℝ} {u : ℂ} :
    u ∈ annulus z r₁ r₂ ↔ r₁ < ‖u - z‖ ∧ ‖u - z‖ < r₂ := by
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma measurableSet_annulus' (z : ℂ) (R : ℝ) : MeasurableSet (annulus z R (2 * R)) :=
  (isOpen_ball.sdiff isClosed_closedBall).measurableSet

lemma annulus_subset_closedBall {R : ℝ} {z : ℂ} : annulus z R (2 * R) ⊆ closedBall z (2 * R) :=
  fun u hu => mem_closedBall.2 (by rw [dist_eq_norm]; exact (mem_annulus_iff.1 hu).2.le)

lemma closure_annulus_subset {R : ℝ} {z : ℂ} : closure (annulus z R (2 * R)) ⊆ closedBall z (2 * R) :=
  closure_minimal annulus_subset_closedBall isClosed_closedBall

lemma annulus_subset_ball {R : ℝ} {z : ℂ} (hR : 0 < R) : annulus z R (2 * R) ⊆ ball z (3 * R) :=
  fun u hu => mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (annulus_subset_closedBall hu)) (by linarith))

/-! ### Restriction to a ball -/

/-- Integrals of a function vanishing off `U` depend only on `μ.restrict U`. -/
lemma lintegral_eq_of_eq_restrict {U : Set ℂ} (hU : MeasurableSet U) {f : ℂ → ℝ≥0∞}
    (hf : ∀ u ∉ U, f u = 0) {μ μ' : Measure ℂ} (h : μ.restrict U = μ'.restrict U) :
    ∫⁻ u, f u ∂μ = ∫⁻ u, f u ∂μ' := by
  have key : ∀ ν : Measure ℂ, ∫⁻ u, f u ∂ν = ∫⁻ u in U, f u ∂ν := fun ν => by
    rw [← lintegral_indicator hU f]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ U
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hf u hu]
  rw [key μ, key μ', h]

/-- Locality of the good-annulus event: it depends only on `μ` restricted to `ball z (3R)`
(for `0 < c₀ ≤ 1`, the bump supports `B(w, 3c₀R/4)`, `w ∈ closure 𝔸`, and the annulus lie in `ball z (3R)`). -/
lemma scaleCovGoodAnnulusEvent_congr {c0 C R : ℝ} (hR : 0 < R) (hc0 : 0 < c0) (hc1 : c0 ≤ 1) {z : ℂ}
    {μ μ' : Measure ℂ} (h : μ.restrict (ball z (3 * R)) = μ'.restrict (ball z (3 * R))) :
    ScaleCovGoodAnnulusEvent c0 C R z μ ↔ ScaleCovGoodAnnulusEvent c0 C R z μ' := by
  have hAU : annulus z R (2 * R) ⊆ ball z (3 * R) := annulus_subset_ball hR
  have hAm : MeasurableSet (annulus z R (2 * R)) := measurableSet_annulus' z R
  have hUm : MeasurableSet (ball z (3 * R)) := isOpen_ball.measurableSet
  have hA : μ.restrict (annulus z R (2 * R)) = μ'.restrict (annulus z R (2 * R)) := by
    have e : ∀ ν : Measure ℂ, ν.restrict (annulus z R (2 * R)) =
        (ν.restrict (ball z (3 * R))).restrict (annulus z R (2 * R)) := fun ν => by
      rw [Measure.restrict_restrict hAm, inter_eq_left.2 hAU]
    rw [e μ, e μ', h]
  have hcov : covN R z μ = covN R z μ' := by
    unfold covN
    simp only [hA]
  have hbpt : ∀ w ∈ closure (annulus z R (2 * R)), bumpMass c0 R μ w = bumpMass c0 R μ' w := by
    intro w hw
    have hw' : ‖w - z‖ ≤ 2 * R := by
      have := closure_annulus_subset hw
      rwa [mem_closedBall, dist_eq_norm] at this
    unfold bumpMass
    refine lintegral_eq_of_eq_restrict (f := fun u => ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))))
      hUm ?_ h
    intro u hu
    show ENNReal.ofReal (bumpPhi ((u - w) / ((c0 * R : ℝ) : ℂ))) = 0
    have h1 : 3 * R ≤ ‖u - z‖ := by
      have : 3 * R ≤ dist u z := not_lt.1 (fun hlt => hu (mem_ball.2 hlt))
      rwa [dist_eq_norm] at this
    have h2 := norm_sub_norm_le (u - z) (w - z)
    rw [show u - z - (w - z) = u - w by ring] at h2
    have hd : R ≤ ‖u - w‖ := by linarith
    have hpos : 0 < c0 * R := mul_pos hc0 hR
    have hq : 3 / 4 ≤ ‖(u - w) / ((c0 * R : ℝ) : ℂ)‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, le_div_iff₀ hpos]
      nlinarith [mul_le_mul_of_nonneg_right hc1 hR.le]
    rw [bumpPhi_eq_zero hq, ENNReal.ofReal_zero]
  have hbump : massBumpR c0 R z μ = massBumpR c0 R z μ' := by
    unfold massBumpR
    refine iInf_congr fun w => ?_
    by_cases hw : w ∈ closure (annulus z R (2 * R))
    · rw [iInf_pos hw, iInf_pos hw, hbpt w hw]
    · rw [iInf_neg hw, iInf_neg hw]
  unfold ScaleCovGoodAnnulusEvent
  rw [hcov, hbump]

/-! ### Scaling by a constant -/

lemma covN_smul (a : ℝ≥0∞) (R : ℝ) (z : ℂ) (μ : Measure ℂ) :
    covN R z (a • μ) = a * covN R z μ := by
  unfold covN
  simp only [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ENNReal.mul_iSup]

lemma massBumpR_smul {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ⊤) (c0 R : ℝ) (z : ℂ) (μ : Measure ℂ) :
    massBumpR c0 R z (a • μ) = a * massBumpR c0 R z μ := by
  unfold massBumpR bumpMass
  simp only [lintegral_smul_measure, smul_eq_mul, ENNReal.mul_iInf_of_ne ha0 ha]

/-- §3 item 2: multiplying `μ` by a positive constant leaves the good-annulus event unchanged. -/
lemma scaleCovGoodAnnulusEvent_smul_iff {a : ℝ} (ha : 0 < a) (c0 C R : ℝ) (z : ℂ) (μ : Measure ℂ) :
    ScaleCovGoodAnnulusEvent c0 C R z (ENNReal.ofReal a • μ) ↔ ScaleCovGoodAnnulusEvent c0 C R z μ := by
  set c : ℝ≥0∞ := ENNReal.ofReal a with hcdef
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpos : ∀ m : ℝ≥0∞, 0 < c * m ↔ 0 < m := fun m => by
    simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, hc0, false_or]
  have hmul_lt : ∀ m : ℝ≥0∞, c * m < ⊤ ↔ m < ⊤ := by
    intro m
    rw [ENNReal.mul_lt_top_iff]
    constructor
    · rintro (⟨_, h⟩ | h | h)
      · exact h
      · exact absurd h hc0
      · rw [h]; exact ENNReal.zero_lt_top
    · intro h; exact Or.inl ⟨ENNReal.ofReal_lt_top, h⟩
  have hC' : ∀ m N : ℝ≥0∞, N ≤ ENNReal.ofReal C * m ↔ c * N ≤ ENNReal.ofReal C * (c * m) := by
    intro m N
    rw [show ENNReal.ofReal C * (c * m) = c * (ENNReal.ofReal C * m) by ring]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h zero_le
    · intro h
      have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0∞) ≤ c⁻¹ from zero_le)
      rwa [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hc0 hctop, one_mul] at h'
  unfold ScaleCovGoodAnnulusEvent
  rw [covN_smul, massBumpR_smul hc0 hctop, hpos, hmul_lt, ← hC']

/-! ### Consequences on the event (§3 item 4) -/

lemma measure_annulus_le_covN {R : ℝ} (hR : 0 < R) (z : ℂ) (μ : Measure ℂ) :
    μ (annulus z R (2 * R)) ≤ covN R z μ := by
  set v : ℂ := z + ((3 / 2 * R : ℝ) : ℂ) with hv
  have hvz : v - z = ((3 / 2 * R : ℝ) : ℂ) := by rw [hv, add_sub_cancel_left]
  have h32 : ‖((3 / 2 * R : ℝ) : ℂ)‖ = 3 / 2 * R := by
    rw [Complex.norm_real, Real.norm_of_nonneg (show (0 : ℝ) ≤ 3 / 2 * R by linarith)]
  have hvA : v ∈ annulus z R (2 * R) := by
    rw [mem_annulus_iff, hvz, h32]
    constructor <;> linarith
  have hkern : ∀ u ∈ annulus z R (2 * R), (1 : ℝ≥0∞) ≤ covKernel R v u := by
    intro u hu
    unfold covKernel
    split_ifs with huv
    · exact le_top
    · apply ENNReal.one_le_ofReal.2
      have hu2 := (mem_annulus_iff.1 hu).2
      have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
      have hle : ‖u - v‖ ≤ 4 * R := by
        have h3 := norm_sub_le (u - z) (v - z)
        rw [show u - z - (v - z) = u - v by ring, hvz, h32] at h3
        linarith
      have hlog : 0 ≤ Real.log (4 * R / ‖u - v‖) := Real.log_nonneg ((one_le_div hpos).2 hle)
      linarith
  calc μ (annulus z R (2 * R)) = ∫⁻ _ in annulus z R (2 * R), 1 ∂μ := by simp
    _ ≤ ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ :=
        setLIntegral_mono' (measurableSet_annulus' z R) fun u hu => hkern u hu
    _ ≤ covN R z μ := le_iSup₂ (f := fun v (_ : v ∈ closure (annulus z R (2 * R))) =>
        ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ) v (subset_closure hvA)

/-- §3 item 4, first part: on the event, `μ(𝔸_{R,2R}(z)) ≤ N_R ≤ C m_R^φ`. -/
lemma scaleCov_annulus_mass_le {c0 C R : ℝ} (hR : 0 < R) {z : ℂ} {μ : Measure ℂ}
    (h : ScaleCovGoodAnnulusEvent c0 C R z μ) :
    μ (annulus z R (2 * R)) ≤ ENNReal.ofReal C * massBumpR c0 R z μ :=
  (measure_annulus_le_covN hR z μ).trans h.2.2

lemma printedKernel_le_covKernel_add {R : ℝ} (hR : 0 < R) (v u : ℂ) :
    printedKernel v u ≤ covKernel R v u + ENNReal.ofReal |Real.log (4 * R)| := by
  unfold printedKernel covKernel
  split_ifs with huv
  · simp
  · have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
    have h4 : (4 * R) ≠ 0 := (by linarith : (0 : ℝ) < 4 * R).ne'
    have hlog : Real.log (1 / ‖u - v‖) + 1 ≤ (Real.log (4 * R / ‖u - v‖) + 1) + |Real.log (4 * R)| := by
      rw [one_div, Real.log_inv, Real.log_div h4 hpos.ne']
      linarith [neg_le_abs (Real.log (4 * R))]
    exact (ENNReal.ofReal_le_ofReal hlog).trans ENNReal.ofReal_add_le

lemma measurable_covKernel (R : ℝ) (v : ℂ) : Measurable (covKernel R v) := by
  unfold covKernel
  refine Measurable.ite (p := fun u : ℂ => u = v) (measurableSet_singleton v) measurable_const ?_
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_log.comp (measurable_const.div ((measurable_id.sub_const v).norm))).add_const 1)

/-- §3 item 4, second part: on the event, `L_R(z) ≤ C (1 + |log (4R)|) m_R^φ`. -/
lemma printedL_le_of_event {c0 C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C) {z : ℂ} {μ : Measure ℂ}
    (h : ScaleCovGoodAnnulusEvent c0 C R z μ) :
    printedL R z μ ≤ ENNReal.ofReal (C * (1 + |Real.log (4 * R)|)) * massBumpR c0 R z μ := by
  have hM := scaleCov_annulus_mass_le hR h
  have hN := h.2.2
  have hrhs : ENNReal.ofReal (C * (1 + |Real.log (4 * R)|)) * massBumpR c0 R z μ
      = ENNReal.ofReal C * massBumpR c0 R z μ
        + ENNReal.ofReal |Real.log (4 * R)| * (ENNReal.ofReal C * massBumpR c0 R z μ) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one]
    ring
  unfold printedL
  refine iSup₂_le fun v hv => ?_
  calc ∫⁻ u in annulus z R (2 * R), printedKernel v u ∂μ
      ≤ ∫⁻ u in annulus z R (2 * R), (covKernel R v u + ENNReal.ofReal |Real.log (4 * R)|) ∂μ :=
        lintegral_mono fun u => printedKernel_le_covKernel_add hR v u
    _ = (∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ)
          + ENNReal.ofReal |Real.log (4 * R)| * μ (annulus z R (2 * R)) := by
        rw [lintegral_add_left (measurable_covKernel R v), setLIntegral_const]
    _ ≤ covN R z μ + ENNReal.ofReal |Real.log (4 * R)| * (ENNReal.ofReal C * massBumpR c0 R z μ) :=
        add_le_add (le_iSup₂ (f := fun v (_ : v ∈ closure (annulus z R (2 * R))) =>
          ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ) v hv)
          (mul_le_mul_of_nonneg_left hM zero_le)
    _ ≤ ENNReal.ofReal C * massBumpR c0 R z μ
          + ENNReal.ofReal |Real.log (4 * R)| * (ENNReal.ofReal C * massBumpR c0 R z μ) :=
        add_le_add hN le_rfl
    _ = ENNReal.ofReal (C * (1 + |Real.log (4 * R)|)) * massBumpR c0 R z μ := hrhs.symm

/-- The real inequality behind the paper's form `1 + log(1/R)`: for `0 < R ≤ 1`,
`1 + |log (4R)| ≤ (1 + log 4)(1 + log(1/R))`. -/
lemma one_add_abs_log_four_mul_le {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    1 + |Real.log (4 * R)| ≤ (1 + Real.log 4) * (1 + Real.log (1 / R)) := by
  have hL4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (1 / R) := Real.log_nonneg (one_le_one_div hR hR1)
  have hsum : Real.log (4 * R) = Real.log 4 - Real.log (1 / R) := by
    rw [Real.log_mul (by norm_num) hR.ne', one_div, Real.log_inv]
    ring
  rcases le_total (4 * R) 1 with h | h
  · have hn : Real.log (4 * R) ≤ 0 := Real.log_nonpos (by linarith) h
    rw [abs_of_nonpos hn, hsum]
    nlinarith [mul_nonneg hL4 hl]
  · have hn : 0 ≤ Real.log (4 * R) := Real.log_nonneg h
    have hle : Real.log (4 * R) ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
    rw [abs_of_nonneg hn]
    nlinarith [mul_nonneg hL4 hl]

/-- §3 item 4 in the paper's form: for `0 < R ≤ 1`, `L_R(z) ≤ C (1 + log 4)(1 + log(1/R)) m_R^φ` on the event. -/
lemma printedL_le_of_event_unit {c0 C R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hC : 0 ≤ C) {z : ℂ}
    {μ : Measure ℂ} (h : ScaleCovGoodAnnulusEvent c0 C R z μ) :
    printedL R z μ ≤ ENNReal.ofReal (C * ((1 + Real.log 4) * (1 + Real.log (1 / R)))) * massBumpR c0 R z μ :=
  (printedL_le_of_event hR hC h).trans
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (one_add_abs_log_four_mul_le hR hR1) hC)) zero_le)

end Lemma68Window

end MatedCRT
