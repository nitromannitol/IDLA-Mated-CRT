import MatedCRT.Proofs.Sec3.KilledOccupation.LimClockKernel

/-!
# The expected occupation measure of a clock up to the exit time of a disc

Let `κ (a, b)` be a family of measures on `ℝ≥0` (the Stieltjes measures of an additive functional of the path `b`,
depending on a parameter `a`), let `σ = exitNN z r` be the exit time of `ball z r` and let `μ` be a law on the path
space. The expected occupation measure of the clock `κ` up to `σ` is the measure on `ℂ`
`A ↦ ∫ μ(db) ∫_{[0, σ(b)]} 1_A(b_u) κ (a, b)(du)`.
For Liouville Brownian motion this is the left side of the occupation (Revuz) identity
`E_y ∫_0^σ f(b_u) dF_u = 2 ∫_D G_D(y, x) f(x) μ_h(dx)`.

* `clockOccupationPath κ z r a b`: the occupation measure of one path, the image of `κ (a, b)` restricted to
  `[0, σ(b)]` under `u ↦ b u`.
* `clockOccupationMeasure κ z r μ a`: its mean over `b` under `μ`, as a measure on `ℂ`;
  `lintegral_clockOccupationMeasure` and `clockOccupationMeasure_apply` compute its integrals and masses.
* `measurable_clockOccupationMeasure`: it is a measurable function of the parameter `a`, when the masses
  `κ p (Iic t)` are finite and measurable in `p`.
* `lintegral_clockOccupationMeasure_of_Iic_eq`: the clock `κ (a, ·)` can be replaced by any family `dA` of measures
  with the same masses on the intervals `[0, t]` for `μ`-almost every path. No measurability of `dA` is needed.
* `limClockOccupationMeasure γ ε z r μ ψ`: the instance for the Stieltjes kernel of the limit clock of the circle
  averages `ψ`; it is measurable in `ψ` (`measurable_limClockOccupationMeasure`).
-/

noncomputable section

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Two measures on `ℝ≥0` with the same finite masses on the intervals `[0, t]` have the same restriction to every
interval `[0, s]`. -/
lemma restrict_Icc_zero_eq_of_Iic_eq {κ₁ κ₂ : Measure ℝ≥0} (hfin : ∀ t, κ₁ (Iic t) ≠ ∞)
    (h : ∀ t, κ₁ (Iic t) = κ₂ (Iic t)) (s : ℝ≥0) :
    κ₁.restrict (Icc 0 s) = κ₂.restrict (Icc 0 s) := by
  have hI : Icc (0 : ℝ≥0) s = Iic s := by
    ext u
    simp
  rw [hI]
  have : IsFiniteMeasure (κ₁.restrict (Iic s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (hfin s).lt_top⟩
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic, h]

section Generic

variable {α : Type*} [MeasurableSpace α] (κ : α × ContinuousPath ℂ → Measure ℝ≥0) (z : ℂ) (r : ℝ)
  (μ : Measure (ContinuousPath ℂ))

/-- The occupation measure of the path `b` for the clock `κ (a, b)` up to the exit time `σ(b)` of `ball z r`: the
image of `κ (a, b)` restricted to `[0, σ(b)]` under `u ↦ b u`. -/
def clockOccupationPath (a : α) (b : ContinuousPath ℂ) : Measure ℂ :=
  ((κ (a, b)).restrict (Icc (0 : ℝ≥0) (exitNN z r b))).map fun u => b u

omit [MeasurableSpace α] in
lemma lintegral_clockOccupationPath (a : α) (b : ContinuousPath ℂ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(clockOccupationPath κ z r a b) =
      ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), g (b u) ∂(κ (a, b)) :=
  lintegral_map hg (map_continuous b).measurable

/-- The occupation measure of a path is a measurable function of the path. -/
lemma measurable_clockOccupationPath (hfin : ∀ p t, κ p (Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun p => κ p (Iic t)) (a : α) :
    Measurable (clockOccupationPath κ z r a) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have h : (fun b => clockOccupationPath κ z r a b A) = fun b =>
      ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), A.indicator 1 (b u) ∂(κ (a, b)) := by
    funext b
    rw [← lintegral_clockOccupationPath κ z r a b (measurable_one.indicator hA), lintegral_indicator_one hA]
  rw [h]
  exact measurable_setLIntegral_exitNN (fun b => κ (a, b)) (fun b t => hfin (a, b) t)
    (fun t => (hIic t).comp measurable_prodMk_left) z r _ (measurable_one.indicator hA)

/-- The expected occupation measure of the clock `κ (a, ·)` up to the exit time of `ball z r`, under the law `μ` of
the path. -/
def clockOccupationMeasure (a : α) : Measure ℂ :=
  μ.bind (clockOccupationPath κ z r a)

/-- Integrals against the expected occupation measure. -/
theorem lintegral_clockOccupationMeasure (hfin : ∀ p t, κ p (Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun p => κ p (Iic t)) (a : α) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(clockOccupationMeasure κ z r μ a) =
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), g (b u) ∂(κ (a, b)) ∂μ := by
  rw [clockOccupationMeasure,
    Measure.lintegral_bind (measurable_clockOccupationPath κ z r hfin hIic a).aemeasurable hg.aemeasurable]
  exact lintegral_congr fun b => lintegral_clockOccupationPath κ z r a b hg

/-- Masses of the expected occupation measure. -/
theorem clockOccupationMeasure_apply (hfin : ∀ p t, κ p (Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun p => κ p (Iic t)) (a : α) {A : Set ℂ} (hA : MeasurableSet A) :
    clockOccupationMeasure κ z r μ a A =
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), A.indicator 1 (b u) ∂(κ (a, b)) ∂μ := by
  rw [← lintegral_indicator_one hA,
    lintegral_clockOccupationMeasure κ z r μ hfin hIic a (measurable_one.indicator hA)]

/-- The expected occupation measure is a measurable function of the parameter. -/
theorem measurable_clockOccupationMeasure [SFinite μ] (hfin : ∀ p t, κ p (Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun p => κ p (Iic t)) :
    Measurable (clockOccupationMeasure κ z r μ) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp_rw [clockOccupationMeasure_apply κ z r μ hfin hIic _ hA]
  exact measurable_lintegral_setLIntegral_exitNN κ hfin hIic μ z r _ (measurable_one.indicator hA)

/-- In the integrals against the expected occupation measure, the clock `κ (a, ·)` can be replaced by any family
`dA` of measures on `ℝ≥0` with the same masses on the intervals `[0, t]`, for `μ`-almost every path. -/
theorem lintegral_clockOccupationMeasure_of_Iic_eq (hfin : ∀ p t, κ p (Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun p => κ p (Iic t)) (a : α) {dA : ContinuousPath ℂ → Measure ℝ≥0}
    (h : ∀ᵐ b ∂μ, ∀ t : ℝ≥0, κ (a, b) (Iic t) = dA b (Iic t)) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(clockOccupationMeasure κ z r μ a) =
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), g (b u) ∂(dA b) ∂μ := by
  rw [lintegral_clockOccupationMeasure κ z r μ hfin hIic a hg]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with b hb
  rw [restrict_Icc_zero_eq_of_Iic_eq (fun t => hfin (a, b) t) hb]

end Generic

section LimClock

variable (γ : ℝ) (ε : ℕ → ℝ) (z : ℂ) (r : ℝ) (μ : Measure (ContinuousPath ℂ))

/-- The expected occupation measure of the limit clock of the circle averages `ψ`, up to the exit time of
`ball z r`, under the law `μ` of the path. -/
def limClockOccupationMeasure (ψ : UnitDiskCircleIndex → ℝ) : Measure ℂ :=
  clockOccupationMeasure (fun p => limClockKernel γ ε (exitNN z r) p) z r μ ψ

/-- The expected occupation measure of the limit clock is a measurable function of the circle averages. -/
theorem measurable_limClockOccupationMeasure [SFinite μ] : Measurable (limClockOccupationMeasure γ ε z r μ) :=
  measurable_clockOccupationMeasure (fun p => limClockKernel γ ε (exitNN z r) p) z r μ
    (fun p t => limClockKernel_Iic_ne_top γ ε (exitNN z r) p t)
    (fun t => measurable_limClockKernel_Iic γ ε (exitNN z r) (measurable_exitNN z r) t)

/-- Integrals against the expected occupation measure of the limit clock. -/
theorem lintegral_limClockOccupationMeasure (ψ : UnitDiskCircleIndex → ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(limClockOccupationMeasure γ ε z r μ ψ) =
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), g (b u) ∂(limClockKernel γ ε (exitNN z r) (ψ, b)) ∂μ :=
  lintegral_clockOccupationMeasure (fun p => limClockKernel γ ε (exitNN z r) p) z r μ
    (fun p t => limClockKernel_Iic_ne_top γ ε (exitNN z r) p t)
    (fun t => measurable_limClockKernel_Iic γ ε (exitNN z r) (measurable_exitNN z r) t) ψ hg

/-- Masses of the expected occupation measure of the limit clock. -/
theorem limClockOccupationMeasure_apply (ψ : UnitDiskCircleIndex → ℝ) {A : Set ℂ} (hA : MeasurableSet A) :
    limClockOccupationMeasure γ ε z r μ ψ A =
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), A.indicator 1 (b u)
        ∂(limClockKernel γ ε (exitNN z r) (ψ, b)) ∂μ :=
  clockOccupationMeasure_apply (fun p => limClockKernel γ ε (exitNN z r) p) z r μ
    (fun p t => limClockKernel_Iic_ne_top γ ε (exitNN z r) p t)
    (fun t => measurable_limClockKernel_Iic γ ε (exitNN z r) (measurable_exitNN z r) t) ψ hA

/-- If, for `μ`-almost every path `b`, the Stieltjes kernel of the limit clock of `ψ` has the same masses on the
intervals `[0, t]` as a measure `dA b`, then the integrals against the expected occupation measure of the limit clock
are the expected clock integrals of `dA` up to the exit time. -/
theorem lintegral_limClockOccupationMeasure_of_Iic_eq (ψ : UnitDiskCircleIndex → ℝ)
    {dA : ContinuousPath ℂ → Measure ℝ≥0}
    (h : ∀ᵐ b ∂μ, ∀ t : ℝ≥0, limClockKernel γ ε (exitNN z r) (ψ, b) (Iic t) = dA b (Iic t))
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(limClockOccupationMeasure γ ε z r μ ψ) =
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), g (b u) ∂(dA b) ∂μ :=
  lintegral_clockOccupationMeasure_of_Iic_eq (fun p => limClockKernel γ ε (exitNN z r) p) z r μ
    (fun p t => limClockKernel_Iic_ne_top γ ε (exitNN z r) p t)
    (fun t => measurable_limClockKernel_Iic γ ε (exitNN z r) (measurable_exitNN z r) t) ψ h hg

end LimClock

end MatedCRT.KilledOccupation
