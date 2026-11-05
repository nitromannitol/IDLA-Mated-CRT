import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope

/-!
# Continuous mapping for functionals defined on a class of paths

Variant of `PathEnvelope` in which the functional `G` is only controlled on a class `𝒞`
of paths (e.g. continuous paths) carrying the walk and the limiting paths almost surely.
The envelopes `max(-1, sup_{v ∈ 𝒞} (G v - k d(v, w)))` are bounded Lipschitz on all paths.
This is needed for integral functionals such as `w ↦ ∫_0^{T ∧ τ(w)} f(w_t) dt`, which are
meaningful (and continuous) only on measurable, resp. continuous, paths.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- `G` is continuous at `w` for the local uniform distance, among paths of `𝒞`. -/
def PathFunctionalContinuousWithinAt (𝒞 : Set (ℝ≥0 → ℂ)) (G : (ℝ≥0 → ℂ) → ℝ)
    (w : ℝ≥0 → ℂ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ v ∈ 𝒞, localUniformDist v w < ρ → |G v - G w| ≤ η

/-- The envelope `max(-1, sup_{v ∈ 𝒞} (G v - k d(v, w)))`. -/
noncomputable def pathUpperEnvelopeOn (𝒞 : Set (ℝ≥0 → ℂ)) (G : (ℝ≥0 → ℂ) → ℝ) (k : ℝ)
    (w : ℝ≥0 → ℂ) : ℝ :=
  max (-1) (⨆ v : 𝒞, (G v - k * localUniformDist v w))

section EnvelopeOn

variable {𝒞 : Set (ℝ≥0 → ℂ)} {G : (ℝ≥0 → ℂ) → ℝ} (hG : ∀ w ∈ 𝒞, |G w| ≤ 1) {k : ℝ}
  (hk : 0 ≤ k)
include hG hk

theorem bddAbove_pathUpperEnvelopeOn (w : ℝ≥0 → ℂ) :
    BddAbove (range fun v : 𝒞 => G v - k * localUniformDist v w) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨v, rfl⟩
  have := (abs_le.mp (hG v v.2)).2
  have := mul_nonneg hk (localUniformDist_nonneg v w)
  linarith

theorem le_pathUpperEnvelopeOn {w : ℝ≥0 → ℂ} (hw : w ∈ 𝒞) :
    G w ≤ pathUpperEnvelopeOn 𝒞 G k w := by
  refine le_max_of_le_right (le_ciSup_of_le (bddAbove_pathUpperEnvelopeOn hG hk w) ⟨w, hw⟩ ?_)
  change G w ≤ G w - k * localUniformDist w w
  rw [localUniformDist_self, mul_zero, sub_zero]

theorem supEnvelope_le_one (h𝒞 : 𝒞.Nonempty) (w : ℝ≥0 → ℂ) :
    (⨆ v : 𝒞, (G v - k * localUniformDist v w)) ≤ 1 := by
  have : Nonempty 𝒞 := h𝒞.to_subtype
  refine ciSup_le fun v => ?_
  have := (abs_le.mp (hG v v.2)).2
  have := mul_nonneg hk (localUniformDist_nonneg v w)
  linarith

theorem abs_pathUpperEnvelopeOn_le_one (h𝒞 : 𝒞.Nonempty) (w : ℝ≥0 → ℂ) :
    |pathUpperEnvelopeOn 𝒞 G k w| ≤ 1 := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (supEnvelope_le_one hG hk h𝒞 w)⟩

theorem pathUpperEnvelopeOn_le_add (h𝒞 : 𝒞.Nonempty) (w w' : ℝ≥0 → ℂ) :
    pathUpperEnvelopeOn 𝒞 G k w ≤ pathUpperEnvelopeOn 𝒞 G k w' + k * localUniformDist w w' := by
  have : Nonempty 𝒞 := h𝒞.to_subtype
  have hd := mul_nonneg hk (localUniformDist_nonneg w w')
  unfold pathUpperEnvelopeOn
  refine max_le (by linarith [le_max_left (-1 : ℝ) (⨆ v : 𝒞, (G v - k * localUniformDist v w'))])
    (ciSup_le fun v => ?_)
  have htri := localUniformDist_triangle v w w'
  have hle : G v - k * localUniformDist v w' ≤ ⨆ v : 𝒞, (G v - k * localUniformDist v w') :=
    le_ciSup (bddAbove_pathUpperEnvelopeOn hG hk w') v
  have := mul_le_mul_of_nonneg_left htri hk
  have hmax := le_max_right (-1 : ℝ) (⨆ v : 𝒞, (G v - k * localUniformDist v w'))
  nlinarith

theorem isBoundedLipschitzPathFunctional_pathUpperEnvelopeOn (h𝒞 : 𝒞.Nonempty) :
    IsBoundedLipschitzPathFunctional (pathUpperEnvelopeOn 𝒞 G k) := by
  refine ⟨abs_pathUpperEnvelopeOn_le_one hG hk h𝒞, k, fun w w' => abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · have := pathUpperEnvelopeOn_le_add hG hk h𝒞 w w'
    linarith
  · have := pathUpperEnvelopeOn_le_add hG hk h𝒞 w' w
    rw [localUniformDist_comm] at this
    linarith

end EnvelopeOn

theorem tendsto_pathUpperEnvelopeOn {𝒞 : Set (ℝ≥0 → ℂ)} {G : (ℝ≥0 → ℂ) → ℝ}
    (hG : ∀ w ∈ 𝒞, |G w| ≤ 1) {w : ℝ≥0 → ℂ} (hw𝒞 : w ∈ 𝒞)
    (hw : PathFunctionalContinuousWithinAt 𝒞 G w) :
    Tendsto (fun n : ℕ => pathUpperEnvelopeOn 𝒞 G n w) atTop (𝓝 (G w)) := by
  have : Nonempty 𝒞 := ⟨⟨w, hw𝒞⟩⟩
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (le_pathUpperEnvelopeOn hG (Nat.cast_nonneg n) hw𝒞), fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hcont⟩ := hw ((a - G w) / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ρ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnρ : 2 ≤ (n : ℝ) * ρ := by
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 2 / ρ * ρ = 2 := div_mul_cancel₀ 2 hρ.ne'
    nlinarith
  have hGw := (abs_le.mp (hG w hw𝒞)).1
  refine lt_of_le_of_lt (max_le (by linarith) (ciSup_le fun v => ?_))
    (show G w + (a - G w) / 2 < a by linarith)
  have hd := localUniformDist_nonneg v w
  have hGv := (abs_le.mp (hG v v.2)).2
  rcases lt_or_ge (localUniformDist v w) ρ with hlt | hge
  · have := (abs_le.mp (hcont v v.2 hlt)).2
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hd]
  · have : (n : ℝ) * ρ ≤ n * localUniformDist v w :=
      mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg n)
    linarith

theorem pathFunctionalContinuousWithinAt_neg {𝒞 : Set (ℝ≥0 → ℂ)} {G : (ℝ≥0 → ℂ) → ℝ}
    {w : ℝ≥0 → ℂ} (hw : PathFunctionalContinuousWithinAt 𝒞 G w) :
    PathFunctionalContinuousWithinAt 𝒞 (fun v => -G v) w := by
  intro η hη
  obtain ⟨ρ, hρ, h⟩ := hw η hη
  refine ⟨ρ, hρ, fun v hv hd => ?_⟩
  rw [show -G v - -G w = -(G v - G w) by ring, abs_neg]
  exact h v hv hd

/-- **Continuous mapping in probability**, for functionals controlled on a path class `𝒞`. -/
theorem tendstoInProbability_of_ae_continuousWithin_pathFunctional
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : ℝ → Ω → Measure α) (hQ : ∀ ε ω, IsFiniteMeasure (Q ε ω))
    (W : ℝ → Ω → α → ℝ≥0 → ℂ)
    (R : Ω → Measure β) (hR : ∀ ω, IsFiniteMeasure (R ω)) (X : Ω → β → ℝ≥0 → ℂ)
    (hBL : ∀ F, IsBoundedLipschitzPathFunctional F →
      TendstoInProbability P (fun ε ω => ∫ x, F (W ε ω x) ∂(Q ε ω))
        (fun ω => ∫ b, F (X ω b) ∂(R ω)))
    (𝒞 : Set (ℝ≥0 → ℂ)) (h𝒞 : 𝒞.Nonempty)
    (G : (ℝ≥0 → ℂ) → ℝ) (hG : ∀ w ∈ 𝒞, |G w| ≤ 1)
    (hW𝒞 : ∀ ε ω, ∀ᵐ x ∂(Q ε ω), W ε ω x ∈ 𝒞)
    (hGW : ∀ ε ω, AEStronglyMeasurable (fun x => G (W ε ω x)) (Q ε ω))
    (hFW : ∀ F, IsBoundedLipschitzPathFunctional F → ∀ ε ω,
      AEStronglyMeasurable (fun x => F (W ε ω x)) (Q ε ω))
    (hFX : ∀ F, IsBoundedLipschitzPathFunctional F → ∀ᵐ ω ∂P,
      AEStronglyMeasurable (fun b => F (X ω b)) (R ω))
    (hFXω : ∀ F, IsBoundedLipschitzPathFunctional F →
      AEMeasurable (fun ω => ∫ b, F (X ω b) ∂(R ω)) P)
    (hcont : ∀ᵐ ω ∂P, ∀ᵐ b ∂(R ω), X ω b ∈ 𝒞 ∧
      PathFunctionalContinuousWithinAt 𝒞 G (X ω b)) :
    TendstoInProbability P (fun ε ω => ∫ x, G (W ε ω x) ∂(Q ε ω))
      (fun ω => ∫ b, G (X ω b) ∂(R ω)) := by
  have hG' : ∀ w ∈ 𝒞, |(fun v => -G v) w| ≤ 1 := fun w hw => by
    simpa only [abs_neg] using hG w hw
  have hBLU := fun n : ℕ =>
    isBoundedLipschitzPathFunctional_pathUpperEnvelopeOn hG (Nat.cast_nonneg (α := ℝ) n) h𝒞
  have hBLL := fun n : ℕ =>
    isBoundedLipschitzPathFunctional_pathUpperEnvelopeOn hG' (Nat.cast_nonneg (α := ℝ) n) h𝒞
  have hint : ∀ ε ω (F : (ℝ≥0 → ℂ) → ℝ), (∀ᵐ x ∂(Q ε ω), |F (W ε ω x)| ≤ 1) →
      AEStronglyMeasurable (fun x => F (W ε ω x)) (Q ε ω) →
      Integrable (fun x => F (W ε ω x)) (Q ε ω) := fun ε ω F hF hm => by
    have := hQ ε ω
    exact Integrable.of_bound hm 1 (hF.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)
  have hGb : ∀ ε ω, ∀ᵐ x ∂(Q ε ω), |G (W ε ω x)| ≤ 1 := fun ε ω =>
    (hW𝒞 ε ω).mono fun x hx => hG _ hx
  apply tendstoInProbability_of_sandwich P _ _
    (fun n ε ω => ∫ x, pathUpperEnvelopeOn 𝒞 G n (W ε ω x) ∂(Q ε ω))
    (fun n ε ω => -∫ x, pathUpperEnvelopeOn 𝒞 (fun v => -G v) n (W ε ω x) ∂(Q ε ω))
    (fun n ω => ∫ b, pathUpperEnvelopeOn 𝒞 G n (X ω b) ∂(R ω))
    (fun n ω => -∫ b, pathUpperEnvelopeOn 𝒞 (fun v => -G v) n (X ω b) ∂(R ω))
    (fun n => hBL _ (hBLU n)) (fun n => tendstoInProbability_neg (hBL _ (hBLL n)))
  · intro n ε ω
    refine integral_mono_ae (hint ε ω G (hGb ε ω) (hGW ε ω))
      (hint ε ω _ (Eventually.of_forall fun x => (hBLU n).1 _) (hFW _ (hBLU n) ε ω)) ?_
    filter_upwards [hW𝒞 ε ω] with x hx
    exact le_pathUpperEnvelopeOn hG (Nat.cast_nonneg n) hx
  · intro n ε ω
    rw [← integral_neg]
    refine integral_mono_ae
      (hint ε ω (fun w => -pathUpperEnvelopeOn 𝒞 (fun v => -G v) n w)
        (Eventually.of_forall fun x => by simpa only [abs_neg] using (hBLL n).1 _)
        (hFW _ (hBLL n) ε ω).neg) (hint ε ω G (hGb ε ω) (hGW ε ω)) ?_
    filter_upwards [hW𝒞 ε ω] with x hx
    have := le_pathUpperEnvelopeOn hG' (Nat.cast_nonneg (α := ℝ) n) hx
    change -pathUpperEnvelopeOn 𝒞 (fun v => -G v) n (W ε ω x) ≤ G (W ε ω x)
    linarith
  · intro δ hδ
    refine tendsto_measure_abs_sub_gt_of_ae_tendsto_nat P _ _ (fun n => hFXω _ (hBLU n)) ?_ hδ
    have hall := ae_all_iff.2 fun n : ℕ => hFX _ (hBLU n)
    filter_upwards [hall, hcont] with ω hm hc
    have := hR ω
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1)
      (fun n => Eventually.of_forall fun b => ?_) ?_
    · rw [Real.norm_eq_abs]; exact (hBLU n).1 _
    · filter_upwards [hc] with b hb
      exact tendsto_pathUpperEnvelopeOn hG hb.1 hb.2
  · intro δ hδ
    refine tendsto_measure_abs_sub_gt_of_ae_tendsto_nat P _ _
      (fun n => (hFXω _ (hBLL n)).neg) ?_ hδ
    have hall := ae_all_iff.2 fun n : ℕ => hFX _ (hBLL n)
    filter_upwards [hall, hcont] with ω hm hc
    have := hR ω
    have hlim := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm
      (integrable_const 1) (fun n => Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]; exact (hBLL n).1 _)
      (hc.mono fun b hb => tendsto_pathUpperEnvelopeOn hG' hb.1
        (pathFunctionalContinuousWithinAt_neg hb.2))
    have := hlim.neg
    rw [integral_neg, neg_neg] at this
    exact this

end MatedCRT
