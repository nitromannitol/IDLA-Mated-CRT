import MatedCRT.Proofs.Field.ConeRadialSums
import MatedCRT.Proofs.Field.ConeGaussianClosure
import MatedCRT.LPStaging.Gauss.GaussianClosure

/-!
# Level integrals of a Gaussian process (eq:gff, `ConeMeanZeroRestrictionStep`)

Let `V : ℝ → Ω → ℝ` be a process with values in a centred Gaussian linear space `M` and almost surely continuous
paths, and let `Y = ∫ g(x) V_{s(x)} dν(x)` be one of its level integrals (`MatedCRT.Field.Level`), assumed to be
almost surely absolutely convergent. Then (`levelIntegral_versions`) a version of `Y` can be adjoined to `M` keeping
a centred Gaussian linear space, and covariances pass inside the integral:
`Cov(X, Y) = ∫ g(x) Cov(X, V_{s(x)}) dν(x)` for `X ∈ M`.

The proof follows the Riemann sums of `ConeRadialSums.lean`: they are elements of `M`; their almost sure limits are
adjoined by `isCentredGaussianSpace_sup_span_range` and `isCentredGaussianSpace_sup_span`; covariances are continuous
along almost sure limits in a centred Gaussian space (`tendsto_covariance_of_tendsto_ae`: variances converge, by the
characteristic functions, and covariances are polarized variances).
-/

namespace MatedCRT.Field.GaussClosure

open MeasureTheory ProbabilityTheory Filter Topology MatedCRT.Field.Level
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma memLp_two_of_map_eq {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ≥0} (h : P.map Z = gaussianReal 0 v) :
    MemLp Z 2 P :=
  LatticeProb.GaussianClosure.memLp_two_of_map_eq hZ h

lemma variance_of_map_eq {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ≥0} (h : P.map Z = gaussianReal 0 v) :
    Var[Z; P] = v :=
  LatticeProb.GaussianClosure.variance_of_map_eq hZ h

lemma IsCentredGaussianSpace.memLp {M : Set (Ω → ℝ)} (hM : IsCentredGaussianSpace P M) {Z : Ω → ℝ} (hZ : Z ∈ M) :
    MemLp Z 2 P :=
  LatticeProb.GaussianClosure.IsCentredGaussianSpace.memLp hM hZ

/-- Variances of centred Gaussians are continuous along almost sure limits. -/
lemma tendsto_variance_of_tendsto_ae [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y) (hX : ∀ n, ∃ v : ℝ≥0, P.map (X n) = gaussianReal 0 v)
    (hY : ∃ v : ℝ≥0, P.map Y = gaussianReal 0 v) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => Var[X n; P]) atTop (𝓝 Var[Y; P]) :=
  LatticeProb.GaussianClosure.tendsto_variance_of_tendsto_ae hXm hYm hX hY hae

lemma covariance_eq_polar [IsFiniteMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = (Var[X + Y; P] - Var[X - Y; P]) / 4 :=
  LatticeProb.GaussianClosure.covariance_eq_polar hX hY

/-- **Covariances are continuous along almost sure limits in a centred Gaussian linear space.** -/
theorem tendsto_covariance_of_tendsto_ae [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {X : Ω → ℝ} (hX : X ∈ M) {Z : ℕ → Ω → ℝ} (hZ : ∀ n, Z n ∈ M)
    {Y : Ω → ℝ} (hY : Y ∈ M) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => cov[X, Z n; P]) atTop (𝓝 cov[X, Y; P]) :=
  LatticeProb.GaussianClosure.tendsto_covariance_of_tendsto_ae hM hX hZ hY hae

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace Ω] in
/-- The Riemann sums of a process, as a finite linear combination of its values. -/
lemma levelRiemann_process_eq (ν : Measure α) (g s : α → ℝ) (n k : ℕ) (V : ℝ → Ω → ℝ) :
    (fun ω => levelRiemann ν g s n k fun u => V u ω) =
      ∑ j ∈ levelIndex n k, levelWeight ν g s n k j • V (gridVal n j) := by
  funext ω
  simp [levelRiemann, Finset.sum_apply, smul_eq_mul]

/-- **Level integrals of a Gaussian process.** The level integral `Y₀ = ∫ g · V_s dν` of `V` has a measurable
version `Y` which is the almost sure limit of measurable `T_k`, themselves almost sure limits of elements of `M` (so
`Y` can be adjoined to `M` by `isCentredGaussianSpace_sup_span_range` twice), and, in any centred Gaussian linear space
`M* ⊇ M` containing the `T_k` and `Y`, `Cov(X, Y) = ∫ g(x) Cov(X, V_{s(x)}) dν(x)` for `X ∈ M*`. -/
theorem levelIntegral_versions [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {V : ℝ → Ω → ℝ} (hV : ∀ u, V u ∈ M)
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => V u ω) {ν : Measure α} {g s : α → ℝ} (hg : Integrable g ν)
    (hs : Measurable s) (hint : ∀ᵐ ω ∂P, Integrable (fun x => g x * V (s x) ω) ν) :
    ∃ (T : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ k, Measurable (T k)) ∧ (∀ k, IsAeLimitOf P M (T k)) ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => T k ω) atTop (𝓝 (Y ω))) ∧
      (fun ω => levelIntegral ν g s fun u => V u ω) =ᵐ[P] Y ∧
      ∀ M' : Submodule ℝ (Ω → ℝ), IsCentredGaussianSpace P M' → M ≤ M' → (∀ k, T k ∈ M') → Y ∈ M' →
      ∀ X ∈ M', Continuous (fun u => cov[X, V u; P]) → Integrable (fun x => g x * cov[X, V (s x); P]) ν →
        cov[X, Y; P] = levelIntegral ν g s fun u => cov[X, V u; P] := by
  set R : ℕ → ℕ → Ω → ℝ := fun n k ω => levelRiemann ν g s n k fun u => V u ω with hRdef
  have hRmem : ∀ n k, R n k ∈ M := by
    intro n k
    show (fun ω => levelRiemann ν g s n k fun u => V u ω) ∈ M
    rw [levelRiemann_process_eq]
    exact Submodule.sum_mem _ fun j _ => M.smul_mem _ (hV _)
  set T : ℕ → Ω → ℝ := fun k ω => levelTrunc ν g s k fun u => V u ω with hTdef
  have hRT : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => R n k ω) atTop (𝓝 (T k ω)) := fun k => by
    filter_upwards [hcont] with ω hω using tendsto_levelRiemann hs hg k hω
  have hTae : ∀ k, AEMeasurable (T k) P := fun k =>
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hM _ (hRmem n k)).1.aemeasurable) (hRT k)
  set T' : ℕ → Ω → ℝ := fun k => (hTae k).mk (T k) with hT'def
  have hT'm : ∀ k, Measurable (T' k) := fun k => (hTae k).measurable_mk
  have hRT' : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n => R n k ω) atTop (𝓝 (T' k ω)) := fun k => by
    filter_upwards [hRT k, (hTae k).ae_eq_mk] with ω hω h
    rw [show T' k ω = T k ω from h.symm]
    exact hω
  set Y₀ : Ω → ℝ := fun ω => levelIntegral ν g s fun u => V u ω with hY₀def
  have hTY : ∀ᵐ ω ∂P, Tendsto (fun k => T' k ω) atTop (𝓝 (Y₀ ω)) := by
    have hall : ∀ᵐ ω ∂P, ∀ k, T k ω = T' k ω := ae_all_iff.2 fun k => (hTae k).ae_eq_mk
    filter_upwards [hint, hall] with ω hω hk
    exact (tendsto_levelTrunc hs hω).congr fun k => hk k
  have hYae : AEMeasurable Y₀ P := aemeasurable_of_tendsto_metrizable_ae' (fun k => (hT'm k).aemeasurable) hTY
  set Y : Ω → ℝ := hYae.mk Y₀ with hYdef
  have hTY' : ∀ᵐ ω ∂P, Tendsto (fun k => T' k ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [hTY, hYae.ae_eq_mk] with ω hω h
    rw [show Y ω = Y₀ ω from h.symm]
    exact hω
  refine ⟨T', Y, hT'm, fun k => ⟨fun n => R n k, fun n => hRmem n k, hRT' k⟩, hYae.measurable_mk, hTY',
    hYae.ae_eq_mk, fun M' hM' hMM' hT'mem hYmem X hX hc hci => ?_⟩
  -- the covariance of `X` with a Riemann sum is the Riemann sum of the covariances
  have hcovR : ∀ n k, cov[X, R n k; P] = levelRiemann ν g s n k fun u => cov[X, V u; P] := by
    intro n k
    show cov[X, (fun ω => levelRiemann ν g s n k fun u => V u ω); P] = _
    rw [levelRiemann_process_eq, covariance_sum_right'
      (fun j _ => (hM'.memLp (hMM' (M.smul_mem _ (hV _))))) (hM'.memLp hX)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_smul_right]
  have hcovT : ∀ k, cov[X, T' k; P] = levelTrunc ν g s k fun u => cov[X, V u; P] := by
    intro k
    refine tendsto_nhds_unique (tendsto_covariance_of_tendsto_ae hM' hX
      (fun n => hMM' (hRmem n k)) (hT'mem k) (hRT' k)) ?_
    exact (tendsto_levelRiemann hs hg k hc).congr fun n => (hcovR n k).symm
  refine tendsto_nhds_unique (tendsto_covariance_of_tendsto_ae hM' hX hT'mem hYmem hTY') ?_
  exact (tendsto_levelTrunc hs hci).congr fun k => (hcovT k).symm

end MatedCRT.Field.GaussClosure
