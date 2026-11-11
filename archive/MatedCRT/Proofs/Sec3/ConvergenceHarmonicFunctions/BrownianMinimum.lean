import MatedCRT.Proofs.MatingOfTrees.BrownianLocalMin

/-!
# Separated-interval minima of a correlated Brownian coordinate

Source: `notes/wpn-steps2/steps2-r3.tex`, Section 3, Lemma `lem:bm-minimum-unique`
(r3:534-599), separated-interval part; audited CORRECT in `AUDIT-steps2-r3.md`.

Let `X` be a centred continuous Gaussian process with covariance `twoSidedMin`, that is
`½(|s| + |t| - |s - t|)`, which is valid across zero. For `a < b < c < d` set
`A = min_{[a,b]} (X - X b)`, `C = min_{[c,d]} (X - X c)` and `G = X c - X b`. Then
`min_{[c,d]} X - min_{[a,b]} X = G + C - A`. The gap increment `G` is Gaussian with variance
`c - b > 0`, and it is uncorrelated with every increment that defines `A` or `C`. Joint
Gaussianity makes `G` independent of that pair, so `P(G = A - C) = 0` because the law of `G`
has no atoms. The minima are infima over countably many rational times, by continuity of the
paths, hence measurable functions of countably many increments.

This file proves the separated-interval part only. Unique minimizers, the cells-meet premise
(`adjacentCellsMeetAeStep`) and the rate statements are separate results.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MatedCRT.SeparatedMinimum

/-! ### The covariance kernel `twoSidedMin` -/

/-- The kernel `twoSidedMin` equals `½(|s| + |t| - |s - t|)` on the whole real line. -/
lemma twoSidedMin_eq_abs (s t : ℝ) : twoSidedMin s t = (|s| + |t| - |s - t|) / 2 := by
  unfold twoSidedMin
  rcases le_total 0 s with hs | hs <;> rcases le_total 0 t with ht | ht <;>
    rcases le_total s t with hst | hst <;>
    simp [abs_of_nonneg, abs_of_nonpos, hs, ht, hst] <;> linarith

lemma lrCov_self (γ : ℝ) (i : Fin 2) : lrCov γ i i = 1 := by
  simp [lrCov]

/-- Gap increment against a left increment with `q ≤ b < c`: the covariance vanishes. -/
lemma gap_cov_left_zero {b c q : ℝ} (hqb : q ≤ b) (hbc : b < c) :
    twoSidedMin c q - twoSidedMin c b - twoSidedMin b q + twoSidedMin b b = 0 := by
  have h1 : |c - q| = c - q := abs_of_nonneg (by linarith)
  have h2 : |c - b| = c - b := abs_of_nonneg (by linarith)
  have h3 : |b - q| = b - q := abs_of_nonneg (by linarith)
  simp only [twoSidedMin_eq_abs, h1, h2, h3, sub_self, abs_zero]
  ring

/-- Gap increment against a right increment with `b < c ≤ r`: the covariance vanishes. -/
lemma gap_cov_right_zero {b c r : ℝ} (hbc : b < c) (hcr : c ≤ r) :
    twoSidedMin c r - twoSidedMin c c - twoSidedMin b r + twoSidedMin b c = 0 := by
  have h1 : |c - r| = r - c := by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  have h2 : |b - r| = r - b := by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  have h3 : |b - c| = c - b := by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  simp only [twoSidedMin_eq_abs, h1, h2, h3, sub_self, abs_zero]
  ring

/-- The gap increment has variance `c - b`. -/
lemma gap_var {b c : ℝ} (hbc : b < c) :
    twoSidedMin c c - twoSidedMin c b - twoSidedMin b c + twoSidedMin b b = c - b := by
  have h2 : |c - b| = c - b := abs_of_nonneg (by linarith)
  have h3 : |b - c| = c - b := by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  simp only [twoSidedMin_eq_abs, h2, h3, sub_self, abs_zero]
  ring

/-! ### Minima as infima over countable rational times -/

/-- Rational times in a compact interval; a countable index set. -/
abbrev RatIcc (a b : ℝ) : Type := {q : ℚ // (q : ℝ) ∈ Icc a b}

lemma bddBelow_Icc_image {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    BddBelow (range fun s : Icc a b => g s) := by
  obtain ⟨m, hm⟩ := (isCompact_Icc.image hg).bddBelow
  exact ⟨m, by rintro _ ⟨s, rfl⟩; exact hm (mem_image_of_mem g s.2)⟩

/-- The infimum over rational times of `[a, b]` lies below the value at every point of `[a, b]`. -/
lemma iInf_ratIcc_le {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) {s : ℝ}
    (hs : s ∈ Icc a b) : (⨅ q : RatIcc a b, g q) ≤ g s := by
  have hbdd : BddBelow (range fun q : RatIcc a b => g q) := by
    obtain ⟨m, hm⟩ := (isCompact_Icc.image hg).bddBelow
    exact ⟨m, by rintro _ ⟨q, rfl⟩; exact hm (mem_image_of_mem g q.2)⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hg s ε hε
  have hlt : max a (s - δ) < min b (s + δ) := by
    obtain ⟨hs1, hs2⟩ := hs
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨hab, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hqI : (q : ℝ) ∈ Icc a b :=
    ⟨(le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _)⟩
  have hqd : dist (q : ℝ) s < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [(le_max_right a (s - δ)).trans_lt hq1]
    · linarith [hq2.trans_le (min_le_right b (s + δ))]
  have h1 := hball _ hqd
  rw [Real.dist_eq, abs_lt] at h1
  calc (⨅ q : RatIcc a b, g q) ≤ g (q : ℝ) := ciInf_le hbdd ⟨q, hqI⟩
    _ ≤ g s + ε := by linarith [h1.2]

/-- The infimum over `[a, b]` equals the infimum over rational times of `[a, b]`. -/
lemma iInf_Icc_eq_ratIcc {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    (⨅ s : Icc a b, g s) = ⨅ q : RatIcc a b, g q := by
  have : Nonempty (RatIcc a b) := by
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
    exact ⟨⟨q, hq1.le, hq2.le⟩⟩
  have : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.2 hab.le⟩⟩
  apply le_antisymm
  · exact le_ciInf fun q => ciInf_le (bddBelow_Icc_image hg a b) ⟨(q.1 : ℝ), q.2⟩
  · exact le_ciInf fun s => iInf_ratIcc_le hg hab s.2

/-- Translation invariance of a real infimum over a nonempty family bounded below. -/
lemma ciInf_add_const_real {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddBelow (range f))
    (k : ℝ) : (⨅ i, (f i + k)) = (⨅ i, f i) + k := by
  have hf' : BddBelow (range fun i => f i + k) := by
    obtain ⟨m, hm⟩ := hf
    exact ⟨m + k, by rintro _ ⟨i, rfl⟩; linarith [hm ⟨i, rfl⟩]⟩
  apply le_antisymm
  · have h1 : ∀ i, (⨅ j, (f j + k)) - k ≤ f i := fun i => by linarith [ciInf_le hf' i]
    linarith [le_ciInf h1]
  · exact le_ciInf fun i => by linarith [ciInf_le hf i]

/-- The minimum over `[a, b]` of a continuous function is `g b`-shifted infimum of increments. -/
lemma iInf_Icc_eq_shift {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) (k : ℝ) :
    (⨅ s : Icc a b, g s) = (⨅ q : RatIcc a b, (g q - k)) + k := by
  have : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.2 hab.le⟩⟩
  have hcont : Continuous fun s => g s - k := hg.sub continuous_const
  calc (⨅ s : Icc a b, g s) = ⨅ s : Icc a b, ((g s - k) + k) := by simp only [sub_add_cancel]
    _ = (⨅ s : Icc a b, (g s - k)) + k :=
        ciInf_add_const_real _ (bddBelow_Icc_image hcont a b) k
    _ = (⨅ q : RatIcc a b, (g q - k)) + k := by rw [iInf_Icc_eq_ratIcc hcont hab]

/-! ### Gaussian increments and independence -/

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The covariance of two increments of a Gaussian process with kernel `twoSidedMin`. -/
lemma cov_sub_sub_of_kernel {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hX : IsGaussianProcess X μ) (hcov : ∀ s t, cov[X s, X t; μ] = twoSidedMin s t)
    (s t u v : ℝ) :
    cov[fun ω => X s ω - X t ω, fun ω => X u ω - X v ω; μ]
      = twoSidedMin s u - twoSidedMin s v - twoSidedMin t u + twoSidedMin t v := by
  have h := covariance_sub_sub (hX.hasGaussianLaw_eval s).memLp_two
    (hX.hasGaussianLaw_eval t).memLp_two (hX.hasGaussianLaw_eval u).memLp_two
    (hX.hasGaussianLaw_eval v).memLp_two
  rw [hcov, hcov, hcov, hcov] at h
  exact h

/-- Differences `X (p u) - X (q u)` of a Gaussian process form a Gaussian process. -/
lemma isGaussianProcess_sub_pair {μ : Measure Ω} {X : ℝ → Ω → ℝ} (hX : IsGaussianProcess X μ)
    {U : Type*} (p q : U → ℝ) :
    IsGaussianProcess (fun u ω => X (p u) ω - X (q u) ω) μ := by
  classical
  refine hX.of_isGaussianProcess fun u => ⟨{p u, q u},
    ContinuousLinearMap.proj ⟨p u, by simp⟩ - ContinuousLinearMap.proj ⟨q u, by simp⟩,
    fun ω => ?_⟩
  simp [Finset.restrict_def]

/-- If `G` is independent of `Y`, has no atoms, and `Φ` is measurable, then `P {G = Φ Y} = 0`. -/
lemma measure_gap_eq_zero {β : Type*} [MeasurableSpace β] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Ω → ℝ} {Y : Ω → β} {Φ : β → ℝ} (hG : AEMeasurable G μ)
    (hY : AEMeasurable Y μ) (hΦ : Measurable Φ) (hind : IndepFun G Y μ)
    (hatom : ∀ x : ℝ, μ.map G {x} = 0) :
    μ {ω | G ω = Φ (Y ω)} = 0 := by
  have hD : MeasurableSet {p : ℝ × β | p.1 = Φ p.2} :=
    measurableSet_eq_fun measurable_fst (hΦ.comp measurable_snd)
  have hmap : μ {ω | G ω = Φ (Y ω)} = (μ.map fun ω => (G ω, Y ω)) {p : ℝ × β | p.1 = Φ p.2} := by
    rw [Measure.map_apply_of_aemeasurable (hG.prodMk hY) hD]
    rfl
  rw [hmap, (indepFun_iff_map_prod_eq_prod_map_map hG hY).1 hind, Measure.prod_apply_symm hD]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  have hset : (fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × β | p.1 = Φ p.2} = {Φ y} := by
    ext x
    simp
  rw [hset]
  exact hatom _

/-- Abstract separated-interval minimum: for a centred continuous Gaussian process with kernel
`twoSidedMin`, and `a < b < c < d`, the minima of `X` over `[a, b]` and over `[c, d]` are
almost surely unequal. -/
theorem ae_separated_minima_ne_of_gaussian {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} (hX : IsGaussianProcess X μ)
    (hcov : ∀ s t, cov[X s, X t; μ] = twoSidedMin s t)
    (hcont : ∀ ω, Continuous fun t => X t ω) {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∀ᵐ ω ∂μ, (⨅ s : Icc a b, X s ω) ≠ ⨅ s : Icc c d, X s ω := by
  have hae : ∀ t, AEMeasurable (X t) μ := hX.aemeasurable
  have hGae : AEMeasurable (fun ω => X c ω - X b ω) μ := (hae c).sub (hae b)
  have hGlaw : HasGaussianLaw (fun ω => X c ω - X b ω) μ := hX.hasGaussianLaw_fun_sub
  have hvar : Var[fun ω => X c ω - X b ω; μ] = c - b := by
    rw [← covariance_self hGae, cov_sub_sub_of_kernel hX hcov, gap_var hbc]
  have hv : (c - b).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    linarith
  have hatom : ∀ x : ℝ, μ.map (fun ω => X c ω - X b ω) {x} = 0 := by
    intro x
    rw [hGlaw.map_eq_gaussianReal, hvar]
    exact gaussianReal_absolutelyContinuous _ hv Real.volume_singleton
  -- the increments that define the two minima, indexed by rational times
  let Y : RatIcc a b ⊕ RatIcc c d → Ω → ℝ :=
    Sum.elim (fun q ω => X (q.1 : ℝ) ω - X b ω) (fun r ω => X (r.1 : ℝ) ω - X c ω)
  have hYi : ∀ t, AEMeasurable (Y t) μ := by
    rintro (q | r)
    · exact (hae _).sub (hae _)
    · exact (hae _).sub (hae _)
  have hYae : AEMeasurable (fun ω (t : RatIcc a b ⊕ RatIcc c d) => Y t ω) μ :=
    aemeasurable_pi_iff.2 hYi
  -- joint Gaussianity of the gap increment with the increments
  let tp : Unit ⊕ (RatIcc a b ⊕ RatIcc c d) → ℝ :=
    Sum.elim (fun _ => c) (Sum.elim (fun q => (q.1 : ℝ)) (fun r => (r.1 : ℝ)))
  let tq : Unit ⊕ (RatIcc a b ⊕ RatIcc c d) → ℝ :=
    Sum.elim (fun _ => b) (Sum.elim (fun _ => b) (fun _ => c))
  have hGP : IsGaussianProcess (Sum.elim (fun _ : Unit => fun ω => X c ω - X b ω) Y) μ := by
    have hfun : Sum.elim (fun _ : Unit => fun ω => X c ω - X b ω) Y
        = fun u ω => X (tp u) ω - X (tq u) ω := by
      funext u ω
      cases u with
      | inl _ => rfl
      | inr v => cases v <;> rfl
    rw [hfun]
    exact isGaussianProcess_sub_pair hX tp tq
  -- the gap increment is uncorrelated with every increment defining the minima
  have hcov0 : ∀ (s : Unit) (t : RatIcc a b ⊕ RatIcc c d),
      cov[(fun _ : Unit => fun ω => X c ω - X b ω) s, Y t; μ] = 0 := by
    intro s t
    rcases t with q | r
    · exact (cov_sub_sub_of_kernel hX hcov c b (q.1 : ℝ) b).trans
        (gap_cov_left_zero q.2.2 hbc)
    · exact (cov_sub_sub_of_kernel hX hcov c b (r.1 : ℝ) c).trans
        (gap_cov_right_zero hbc r.2.1)
  have hind := IsGaussianProcess.indepFun_of_covariance_eq_zero hGP (fun _ => hGae) hYi hcov0
  have hindG : IndepFun (fun ω => X c ω - X b ω)
      (fun ω (t : RatIcc a b ⊕ RatIcc c d) => Y t ω) μ :=
    hind.comp (measurable_pi_apply ()) measurable_id
  -- the event that the minima agree is the event `G = A - C`
  let Φ : (RatIcc a b ⊕ RatIcc c d → ℝ) → ℝ := fun y =>
    (⨅ q : RatIcc a b, y (Sum.inl q)) - ⨅ r : RatIcc c d, y (Sum.inr r)
  have hΦ : Measurable Φ := by
    show Measurable fun y : RatIcc a b ⊕ RatIcc c d → ℝ =>
      (⨅ q : RatIcc a b, y (Sum.inl q)) - ⨅ r : RatIcc c d, y (Sum.inr r)
    exact Measurable.sub (Measurable.iInf fun q => measurable_pi_apply _)
      (Measurable.iInf fun r => measurable_pi_apply _)
  have hzero := measure_gap_eq_zero hGae hYae hΦ hindG hatom
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) hzero)
  have hω' : (⨅ s : Icc a b, X s ω) = ⨅ s : Icc c d, X s ω := by
    have hω0 : ¬ ((⨅ s : Icc a b, X s ω) ≠ ⨅ s : Icc c d, X s ω) := hω
    exact not_not.1 hω0
  have e1 : (⨅ s : Icc a b, X s ω) = (⨅ q : RatIcc a b, (X (q.1 : ℝ) ω - X b ω)) + X b ω :=
    iInf_Icc_eq_shift (hcont ω) hab (X b ω)
  have e2 : (⨅ s : Icc c d, X s ω) = (⨅ r : RatIcc c d, (X (r.1 : ℝ) ω - X c ω)) + X c ω :=
    iInf_Icc_eq_shift (hcont ω) hcd (X c ω)
  show X c ω - X b ω = (⨅ q : RatIcc a b, (X (q.1 : ℝ) ω - X b ω))
      - ⨅ r : RatIcc c d, (X (r.1 : ℝ) ω - X c ω)
  linarith

end Gaussian

/-! ### The correlated Brownian pair -/

/-- Continuity of a path of the two-sided correlated Brownian pair in the time variable. -/
lemma lrCoord_continuous (i : Fin 2) (ω : Path2) : Continuous fun t => lrCoord i t ω := by
  unfold lrCoord
  split_ifs
  · exact continuous_fst.comp ω.continuous
  · exact continuous_snd.comp ω.continuous

/-- A single coordinate of `IsCorrelatedBM2` is a centred Gaussian process in time. -/
lemma isGaussianProcess_coord {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) : IsGaussianProcess (fun t : ℝ => lrCoord i t) μ :=
  hμ.isGaussianProcess.comp_right (fun t : ℝ => ((i, t) : Fin 2 × ℝ))

/-- The covariance of one coordinate of `IsCorrelatedBM2` is `twoSidedMin`. -/
lemma cov_coord {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (s t : ℝ) :
    cov[lrCoord i s, lrCoord i t; μ] = twoSidedMin s t := by
  have h := hμ.covariance_eq i i s t
  rw [lrCov_self, one_mul] at h
  exact h

/-- **Separated-interval minima of the correlated Brownian pair.** For `a < b < c < d`, almost
surely the minimum of a coordinate of `IsCorrelatedBM2` over `[a, b]` differs from its minimum
over `[c, d]`. The intervals may straddle zero. -/
theorem ae_separated_minima_ne {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∀ᵐ ω ∂μ, (⨅ s : Icc a b, lrCoord i (s : ℝ) ω) ≠ ⨅ s : Icc c d, lrCoord i (s : ℝ) ω := by
  have := hμ.isProbabilityMeasure
  exact ae_separated_minima_ne_of_gaussian (X := fun t ω => lrCoord i t ω)
    (isGaussianProcess_coord hμ i) (fun s t => cov_coord hμ i s t)
    (fun ω => lrCoord_continuous i ω) hab hbc hcd

end MatedCRTHarmonic.MatedCRT.SeparatedMinimum
