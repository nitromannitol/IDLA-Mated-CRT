import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyDrop
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraReflection
import LatticeProb.Topology.ContinuousMapBorel
import LatticeProb.Prob.BrownianMax
import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.Prob.CorrelatedBMWindowIndependence
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Analysis.CorrelatedBMHolder

/-!
# The upper bound for the first occupied cell in Shimura's argument

For the `γ`-correlated two-sided Brownian pair `(L, R)`, the mesh `1/n`, the cell
`I_k = [(k - 1)/n, k/n]` and `U_k = R(k/n) - min_{I_k} R` (`cellDropR`), this file proves
`OccupancyUpper γ`: `P(B_k) ≤ E[1_{C_k ∩ F} U_k] + P(Fᶜ)` (the constant is `K = 1`).

* On the first occupied cell the right test at `k` forces the
  future `R(u) - R(k/n)`, `u ∈ [k/n, (k - 1)/n + 2]`, to stay above `-U_k`
  (`firstCellEvent_subset_pastFut`).
* The past event `C_k`, the event `F` and the drop `U_k` depend only on the increments of `(L, R)`
  over the window `[k/n - 3, k/n]` (`priorCellsFail_shift`, `cellDropR_winPath`), while the future
  depends only on the increments over `[k/n, (k - 1)/n + 2]`; the two windows have disjoint
  interiors, so these data are independent (`indep_window_events`, from
  `iIndepFun_increment_windows`).
* Cutting `C_k ∩ F` into the level sets `⌊U_k / h⌋ = m`, the future survival has probability at most
  `(m + 2) h` by the reflection barrier (`measure_futSet_le`), and summing over `m` bounds the
  probability by `E[1_{C_k ∩ F} U_k] + 2 h`; then `h → 0`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2 lrCoord shiftedCoordinate
  shiftedCoordinate_isBrownianReal)
open LatticeProb.CorrelatedBM (coneIncr iIndepFun_increment_windows)

/-! ### Windows of a path -/

/-- The path `ω` read on `[l, r]` (constant outside), started at `0` at time `l`. -/
noncomputable def winPath (l r : ℝ) (ω : Path2) : Path2 :=
  ⟨fun t => ω (max l (min r t)) - ω l,
    (ω.continuous.comp (continuous_const.max (continuous_const.min continuous_id))).sub
      continuous_const⟩

/-- The value of `winPath l r ω` at `t`. -/
lemma winPath_apply (l r : ℝ) (ω : Path2) (t : ℝ) :
    winPath l r ω t = ω (max l (min r t)) - ω l := rfl

/-- On `[l, r]` the path `winPath l r ω` is `ω t - ω l`. -/
lemma winPath_of_mem {l r t : ℝ} (ht : t ∈ Icc l r) (ω : Path2) :
    winPath l r ω t = ω t - ω l := by
  rw [winPath_apply, min_eq_right ht.2, max_eq_right ht.1]

/-- A Borel set of paths is the trace of a product-measurable set of functions. -/
lemma measurableSet_exists_pi {E : Set Path2} (hE : MeasurableSet E) :
    ∃ E' : Set (ℝ → ℝ × ℝ), MeasurableSet E' ∧ (fun (ω : Path2) (t : ℝ) => ω t) ⁻¹' E' = E := by
  have hle : (inferInstance : MeasurableSpace Path2) ≤
      MeasurableSpace.comap (fun (ω : Path2) (t : ℝ) => ω t) inferInstance := by
    refine (LatticeProb.ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval
      (X := ℝ) (Y := ℝ × ℝ)).le.trans (iSup_le fun t => ?_)
    calc MeasurableSpace.comap (fun b : Path2 => b t) (inferInstance : MeasurableSpace (ℝ × ℝ))
        = MeasurableSpace.comap (fun (ω : Path2) (t : ℝ) => ω t)
            (MeasurableSpace.comap (fun f : ℝ → ℝ × ℝ => f t) inferInstance) :=
          by rw [MeasurableSpace.comap_comp]; rfl
      _ ≤ _ := MeasurableSpace.comap_mono (measurable_pi_apply t).comap_le
  exact MeasurableSpace.measurableSet_comap.1 (hle _ hE)

/-- Events determined by the increments of `(L, R)` over two windows with disjoint interiors are
independent. -/
lemma indep_window_events {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {l₀ r₀ l₁ r₁ : ℝ} (h0 : l₀ ≤ r₀) (h1 : l₁ ≤ r₁) (hsep : r₀ ≤ l₁)
    {E₀ E₁ : Set Path2} (hE₀ : MeasurableSet E₀) (hE₁ : MeasurableSet E₁) :
    μ (winPath l₀ r₀ ⁻¹' E₀ ∩ winPath l₁ r₁ ⁻¹' E₁) =
      μ (winPath l₀ r₀ ⁻¹' E₀) * μ (winPath l₁ r₁ ⁻¹' E₁) := by
  let l : Fin 2 → ℝ := ![l₀, l₁]
  let r : Fin 2 → ℝ := ![r₀, r₁]
  have hsep' : ∀ i j : Fin 2, i ≠ j → r i ≤ l j ∨ r j ≤ l i := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl hsep
    · exact Or.inr hsep
    · exact absurd rfl hij
  have hle : ∀ i, l i ≤ r i := by
    intro i
    fin_cases i
    exacts [h0, h1]
  let g : ∀ i : Fin 2, (Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)} → ℝ) → ℝ → ℝ × ℝ :=
    fun i x t =>
      (x (0, ⟨max (l i) (min (r i) t), le_max_left _ _, max_le (hle i) (min_le_left _ _)⟩),
        x (1, ⟨max (l i) (min (r i) t), le_max_left _ _, max_le (hle i) (min_le_left _ _)⟩))
  have hg : ∀ i, Measurable (g i) := fun i =>
    measurable_pi_iff.2 fun t => (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hind := (iIndepFun_increment_windows hμ l r hsep').comp g hg
  have hI := hind.indepFun (show (0 : Fin 2) ≠ 1 by decide)
  obtain ⟨E₀', hE₀', rfl⟩ := measurableSet_exists_pi hE₀
  obtain ⟨E₁', hE₁', rfl⟩ := measurableSet_exists_pi hE₁
  have key := hI.measure_inter_preimage_eq_mul E₀' E₁' hE₀' hE₁'
  have hcoe : ∀ i ω, (fun t => winPath (l i) (r i) ω t) =
      g i (fun p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)} => coneIncr p.1 p.2.1 (l i) ω) := by
    intro i ω
    funext t
    refine Prod.ext ?_ ?_
    · simp [g, winPath_apply, coneIncr, lrCoord]
    · simp [g, winPath_apply, coneIncr, lrCoord]
  have e0 : winPath l₀ r₀ ⁻¹' ((fun (ω : Path2) (t : ℝ) => ω t) ⁻¹' E₀') =
      ((fun i => g i ∘ fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
        coneIncr p.1 p.2.1 (l i) ω) 0) ⁻¹' E₀' := by
    ext ω
    exact Iff.of_eq (congrArg (· ∈ E₀') (hcoe 0 ω))
  have e1 : winPath l₁ r₁ ⁻¹' ((fun (ω : Path2) (t : ℝ) => ω t) ⁻¹' E₁') =
      ((fun i => g i ∘ fun ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)}) =>
        coneIncr p.1 p.2.1 (l i) ω) 1) ⁻¹' E₁' := by
    ext ω
    exact Iff.of_eq (congrArg (· ∈ E₁') (hcoe 1 ω))
  rw [e0, e1]
  exact key

/-! ### Invariance of the tests under restriction to a window -/

/-- The left test at `i` is unchanged by adding a constant on a window containing its times. -/
lemma cellLeft_shift {n i : ℕ} (hn : 1 ≤ n) {X X' : ℝ → ℝ} {c l r : ℝ}
    (hX : ∀ t ∈ Icc l r, X' t = X t - c) (hl : l ≤ (i : ℝ) / n - 2) (hr : (i : ℝ) / n ≤ r) :
    ShimuraCellLeft n i X' ↔ ShimuraCellLeft n i X := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have h1n0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hsub : ((i : ℝ) - 1) / n = (i : ℝ) / n - 1 / n := by ring
  have hs : ∀ s ∈ Icc (((i : ℝ) - 1) / n) ((i : ℝ) / n), s ∈ Icc l r := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hu : ∀ u ∈ Icc ((i : ℝ) / n - 2) (((i : ℝ) - 1) / n), u ∈ Icc l r := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  constructor
  · rintro ⟨s, hs', h⟩
    refine ⟨s, hs', fun u hu' => ?_⟩
    have := h u hu'
    rw [hX s (hs s hs'), hX u (hu u hu')] at this
    linarith
  · rintro ⟨s, hs', h⟩
    refine ⟨s, hs', fun u hu' => ?_⟩
    have := h u hu'
    rw [hX s (hs s hs'), hX u (hu u hu')]
    linarith

/-- The right test at `i` is unchanged by adding a constant on a window containing its times. -/
lemma cellRight_shift {n i : ℕ} (hn : 1 ≤ n) {Y Y' : ℝ → ℝ} {c l r d : ℝ}
    (hY : ∀ t ∈ Icc l r, Y' t = Y t - c) (hl : l ≤ ((i : ℝ) - 1) / n) (hr : (i : ℝ) / n ≤ r)
    (hd : d ≤ r) : ShimuraCellRightUpTo n i d Y' ↔ ShimuraCellRightUpTo n i d Y := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : ((i : ℝ) - 1) / n = (i : ℝ) / n - 1 / n := by ring
  have h1n0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hs : ∀ s ∈ Icc (((i : ℝ) - 1) / n) ((i : ℝ) / n), s ∈ Icc l r := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hu : ∀ u ∈ Icc ((i : ℝ) / n) d, u ∈ Icc l r := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  constructor
  · rintro ⟨s, hs', h⟩
    refine ⟨s, hs', fun u hu' => ?_⟩
    have := h u hu'
    rw [hY s (hs s hs'), hY u (hu u hu')] at this
    linarith
  · rintro ⟨s, hs', h⟩
    refine ⟨s, hs', fun u hu' => ?_⟩
    have := h u hu'
    rw [hY s (hs s hs'), hY u (hu u hu')]
    linarith

/-- The past event at `k` is unchanged by adding constants on `[k/n - 3, k/n]`. -/
lemma priorCellsFail_shift {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) {X X' Y Y' : ℝ → ℝ}
    {cX cY : ℝ} (hX : ∀ t ∈ Icc ((k : ℝ) / n - 3) ((k : ℝ) / n), X' t = X t - cX)
    (hY : ∀ t ∈ Icc ((k : ℝ) / n - 3) ((k : ℝ) / n), Y' t = Y t - cY) :
    priorCellsFail n k X' Y' ↔ priorCellsFail n k X Y := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (k : ℝ) / n ≤ 1 := by
    rw [div_le_one hnR]; exact_mod_cast hkn
  have hleft : ∀ i : ℕ, i ≤ k → (ShimuraCellLeft n i X' ↔ ShimuraCellLeft n i X) := by
    intro i hik
    refine cellLeft_shift hn hX ?_ ?_
    · have : (0 : ℝ) ≤ (i : ℝ) / n := by positivity
      linarith
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hik) hnR.le
  have hright : ∀ i : ℕ, i ≤ k →
      (ShimuraCellRightUpTo n i ((k : ℝ) / n) Y' ↔ ShimuraCellRightUpTo n i ((k : ℝ) / n) Y) := by
    intro i hik
    refine cellRight_shift hn hY ?_ ?_ le_rfl
    · have h1 : (0 : ℝ) ≤ (i : ℝ) / n := by positivity
      have h2 : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
      have : ((i : ℝ) - 1) / n = (i : ℝ) / n - 1 / n := by ring
      linarith
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hik) hnR.le
  unfold priorCellsFail
  refine and_congr (hleft k le_rfl) (forall₂_congr fun i hi => not_congr ?_)
  have hik : i ≤ k := (Finset.mem_Ico.1 hi).2.le
  exact and_congr (hleft i hik) (hright i hik)

/-- The drop `U_k` depends only on the increments over `[k/n - 3, k/n]`. -/
lemma cellDropR_winPath {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) (ω : Path2) :
    cellDropR n k (winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω) = cellDropR n k ω := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (k : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hkn
  have hsub : ((k : ℝ) - 1) / n = (k : ℝ) / n - 1 / n := by ring
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have h1n0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hka : (k : ℝ) / n ∈ Icc ((k : ℝ) / n - 3) ((k : ℝ) / n) := ⟨by linarith, le_rfl⟩
  unfold cellDropR
  refine iSup_congr fun s => ?_
  have hs : (s : ℝ) ∈ Icc ((k : ℝ) / n - 3) ((k : ℝ) / n) :=
    ⟨by linarith [s.2.1], s.2.2⟩
  rw [winPath_of_mem hka, winPath_of_mem hs]
  simp only [Prod.snd_sub]
  ring

/-- The drop `V_k` depends only on the increments over `[k/n - 3, k/n]`. -/
lemma cellDropL_winPath {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) (ω : Path2) :
    cellDropL n k (winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω) = cellDropL n k ω := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (k : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hkn
  have hsub : ((k : ℝ) - 1) / n = (k : ℝ) / n - 1 / n := by ring
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have h1n0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hka : (k : ℝ) / n ∈ Icc ((k : ℝ) / n - 3) ((k : ℝ) / n) := ⟨by linarith, le_rfl⟩
  unfold cellDropL
  refine iSup_congr fun s => ?_
  have hs : (s : ℝ) ∈ Icc ((k : ℝ) / n - 3) ((k : ℝ) / n) :=
    ⟨by linarith [s.2.1], s.2.2⟩
  rw [winPath_of_mem hka, winPath_of_mem hs]
  simp only [Prod.fst_sub]
  ring

/-! ### The events of the upper bound -/

/-- The future of `R` after `k/n`, up to `(k - 1)/n + 2`, stays above `-b` relative to `R(k/n)`. -/
private def futSet (n k : ℕ) (b : ℝ) : Set Path2 :=
  {p | ∀ u ∈ Icc ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2), -b ≤ (p u).2 - (p ((k : ℝ) / n)).2}

/-- The future of `R` after `k/n` stays above `-U_k`. -/
private def futDrop (n k : ℕ) : Set Path2 :=
  {p | ∀ u ∈ Icc ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2),
    -cellDropR n k p ≤ (p u).2 - (p ((k : ℝ) / n)).2}

private lemma measurableSet_futSet (n k : ℕ) (b : ℝ) : MeasurableSet (futSet n k b) := by
  have : futSet n k b = ⋂ u ∈ Icc ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2),
      {p : Path2 | -b ≤ (p u).2 - (p ((k : ℝ) / n)).2} := by
    ext p
    simp [futSet]
  rw [this]
  refine (isClosed_biInter fun u _ => ?_).measurableSet
  exact isClosed_le continuous_const
    ((continuous_snd.comp (continuous_eval_const u)).sub
      (continuous_snd.comp (continuous_eval_const _)))

private lemma winPath_mem_futSet (n k : ℕ) (b : ℝ) (hn : 1 ≤ n) (ω : Path2) :
    winPath ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2) ω ∈ futSet n k b ↔ ω ∈ futSet n k b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((k : ℝ) - 1) / n = (k : ℝ) / n - 1 / n := by ring
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have hle : (k : ℝ) / n ≤ ((k : ℝ) - 1) / n + 2 := by linarith
  have ha : (k : ℝ) / n ∈ Icc ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2) := ⟨le_rfl, hle⟩
  unfold futSet
  simp only [mem_ofPred_eq]
  refine forall₂_congr fun u hu => ?_
  rw [winPath_of_mem hu, winPath_of_mem ha]
  simp only [Prod.snd_sub]
  constructor <;> intro h <;> linarith

/-- The probability that the future of `R` after `k/n` stays above `-b` is at most `b + e`. -/
private lemma measure_futSet_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {n k : ℕ}
    (hn : 1 ≤ n) {b e : ℝ} (hb : 0 ≤ b) (he : 0 < e) :
    μ (futSet n k b) ≤ ENNReal.ofReal (b + e) := by
  have := hμ.isProbabilityMeasure
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((k : ℝ) - 1) / n = (k : ℝ) / n - 1 / n := by ring
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have hca : 1 ≤ (((k : ℝ) - 1) / n + 2) - (k : ℝ) / n := by rw [hsub]; linarith
  have hTc : ((Real.toNNReal ((((k : ℝ) - 1) / n + 2) - (k : ℝ) / n) : ℝ≥0) : ℝ) =
      (((k : ℝ) - 1) / n + 2) - (k : ℝ) / n := Real.coe_toNNReal _ (by linarith)
  have hT : 0 < Real.toNNReal ((((k : ℝ) - 1) / n + 2) - (k : ℝ) / n) :=
    Real.toNNReal_pos.2 (by linarith)
  have hB := shiftedCoordinate_isBrownianReal hμ 1 ((k : ℝ) / n)
  have hbe : 0 ≤ b + e := by linarith
  refine (measure_mono ?_).trans ((measure_forall_gt_neg_le hB hT hbe).trans ?_)
  · intro ω hω s hs
    have hs' : (s : ℝ) ≤ (((k : ℝ) - 1) / n + 2) - (k : ℝ) / n := by
      have := NNReal.coe_le_coe.2 hs
      rwa [hTc] at this
    have h1 := hω ((k : ℝ) / n + s) ⟨by linarith [NNReal.coe_nonneg s], by linarith⟩
    have h0 : shiftedCoordinate 1 ((k : ℝ) / n) 0 ω = 0 := by simp [shiftedCoordinate]
    have hsub' : shiftedCoordinate 1 ((k : ℝ) / n) s ω =
        (ω ((k : ℝ) / n + s)).2 - (ω ((k : ℝ) / n)).2 := by
      simp [shiftedCoordinate, lrCoord]
    show -(b + e) < shiftedCoordinate 1 ((k : ℝ) / n) s ω - shiftedCoordinate 1 ((k : ℝ) / n) 0 ω
    rw [h0, hsub', sub_zero]
    linarith
  · apply ENNReal.ofReal_le_ofReal
    refine mul_le_of_le_one_right hbe ?_
    refine Real.sqrt_le_one.2 ?_
    rw [hTc, div_le_one (by nlinarith [Real.pi_gt_three])]
    nlinarith [Real.pi_gt_three]

/-- On the first occupied cell the past event holds and the future of `R` stays above `-U_k`. -/
private lemma firstCellEvent_subset_pastFut {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) :
    firstCellEvent n k ⊆ pastEvent n k ∩ futDrop n k := by
  intro p hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hprior, s, hs, hR⟩ := (mem_firstCellEvent_iff hn (by omega) p).1 hp
  refine ⟨hprior, fun u hu => ?_⟩
  have hU : (p ((k : ℝ) / n)).2 - (p s).2 ≤ cellDropR n k p :=
    le_ciSup (bddAbove_cellDropR n k p) (⟨s, hs⟩ : Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n))
  have := hR u hu
  linarith

/-! ### The bound for a fixed level width -/

private lemma measure_inter_futDrop_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {n k : ℕ} (j : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n) {h : ℝ} (hh : 0 < h) :
    μ (pastEvent n k ∩ tameEvent n k j ∩ futDrop n k) ≤
      ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ +
        ENNReal.ofReal (2 * h) := by
  have := hμ.isProbabilityMeasure
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (k : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hkn
  have hsub : ((k : ℝ) - 1) / n = (k : ℝ) / n - 1 / n := by ring
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have h1n0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hSm : MeasurableSet (pastEvent n k ∩ tameEvent n k j) :=
    (measurableSet_pastEvent n k).inter (measurableSet_tameEvent n k j)
  let A : ℕ → Set Path2 := fun m =>
    (pastEvent n k ∩ tameEvent n k j) ∩ {p | ⌊cellDropR n k p / h⌋₊ = m}
  have hAm : ∀ m, MeasurableSet (A m) := fun m =>
    hSm.inter ((Nat.measurable_floor.comp ((measurable_cellDropR n k).div_const h))
      (measurableSet_singleton m))
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro m m' hne
    refine Set.disjoint_left.2 fun p hp hp' => hne ?_
    have h1 : ⌊cellDropR n k p / h⌋₊ = m := hp.2
    have h2 : ⌊cellDropR n k p / h⌋₊ = m' := hp'.2
    exact h1.symm.trans h2
  -- invariance of the level events under the window map
  have hwin : ∀ m ω, winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω ∈ A m ↔ ω ∈ A m := by
    intro m ω
    have hpast : winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω ∈ pastEvent n k ↔
        ω ∈ pastEvent n k :=
      priorCellsFail_shift hn hkn (cX := (ω ((k : ℝ) / n - 3)).1) (cY := (ω ((k : ℝ) / n - 3)).2)
        (fun t ht => by simp only [winPath_of_mem ht, Prod.fst_sub])
        (fun t ht => by simp only [winPath_of_mem ht, Prod.snd_sub])
    have hR := cellDropR_winPath hn hkn ω
    have hL := cellDropL_winPath hn hkn ω
    simp only [A, mem_inter_iff, mem_ofPred_eq, tameEvent, hpast, hR, hL]
  have hfut : ∀ m : ℕ, ∀ ω, winPath ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2) ω ∈
      futSet n k (((m : ℝ) + 1) * h) ↔ ω ∈ futSet n k (((m : ℝ) + 1) * h) := fun m ω =>
    winPath_mem_futSet n k _ hn ω
  have hind : ∀ m : ℕ, μ (A m ∩ futSet n k (((m : ℝ) + 1) * h)) =
      μ (A m) * μ (futSet n k (((m : ℝ) + 1) * h)) := by
    intro m
    have e0 : winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ⁻¹' A m = A m :=
      Set.ext fun ω => hwin m ω
    have e1 : winPath ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2) ⁻¹' futSet n k (((m : ℝ) + 1) * h) =
        futSet n k (((m : ℝ) + 1) * h) := Set.ext fun ω => hfut m ω
    have := indep_window_events hμ (l₀ := (k : ℝ) / n - 3) (r₀ := (k : ℝ) / n)
      (l₁ := (k : ℝ) / n) (r₁ := ((k : ℝ) - 1) / n + 2)
      (by linarith) (by rw [hsub]; linarith) le_rfl (hAm m)
      (measurableSet_futSet n k (((m : ℝ) + 1) * h))
    rwa [e0, e1] at this
  -- the cover by the levels
  have hcover : (pastEvent n k ∩ tameEvent n k j) ∩ futDrop n k ⊆
      ⋃ m : ℕ, A m ∩ futSet n k (((m : ℝ) + 1) * h) := by
    intro p hp
    have hU0 := cellDropR_nonneg n k p
    have hlt : cellDropR n k p < (((⌊cellDropR n k p / h⌋₊ : ℕ) : ℝ) + 1) * h := by
      have := Nat.lt_floor_add_one (cellDropR n k p / h)
      rw [div_lt_iff₀ hh] at this
      exact this
    refine mem_iUnion.2 ⟨⌊cellDropR n k p / h⌋₊, ⟨hp.1, rfl⟩, fun u hu => ?_⟩
    have := hp.2 u hu
    linarith
  -- the bound on each level
  have hlev : ∀ m : ℕ, μ (A m ∩ futSet n k (((m : ℝ) + 1) * h)) ≤
      μ (A m) * ENNReal.ofReal ((m : ℝ) * h) + μ (A m) * ENNReal.ofReal (2 * h) := by
    intro m
    rw [hind m, ← mul_add]
    refine mul_le_mul' le_rfl ?_
    refine (measure_futSet_le hμ hn (k := k) (b := ((m : ℝ) + 1) * h) (e := h)
      (by positivity) hh).trans ?_
    rw [← ENNReal.ofReal_add (p := (m : ℝ) * h) (q := 2 * h) (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
  have hsumA : ∑' m, μ (A m) ≤ 1 := by
    rw [← measure_iUnion hAd hAm]
    exact prob_le_one
  have hint : ∑' m, μ (A m) * ENNReal.ofReal ((m : ℝ) * h) ≤
      ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ := by
    calc ∑' m, μ (A m) * ENNReal.ofReal ((m : ℝ) * h)
        = ∑' m, ∫⁻ p in A m, ENNReal.ofReal ((m : ℝ) * h) ∂μ := by
          refine tsum_congr fun m => ?_
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∑' m, ∫⁻ p in A m, ENNReal.ofReal (cellDropR n k p) ∂μ := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          refine setLIntegral_mono' (hAm m) fun p hp => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hpm : ⌊cellDropR n k p / h⌋₊ = m := hp.2
          have hfl : (m : ℝ) ≤ cellDropR n k p / h := by
            rw [← hpm]
            exact Nat.floor_le (div_nonneg (cellDropR_nonneg n k p) hh.le)
          rwa [le_div_iff₀ hh] at hfl
      _ = ∫⁻ p in ⋃ m, A m, ENNReal.ofReal (cellDropR n k p) ∂μ :=
          (lintegral_iUnion hAm hAd _).symm
      _ ≤ ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ :=
          lintegral_mono_set (iUnion_subset fun m => inter_subset_left)
  calc μ ((pastEvent n k ∩ tameEvent n k j) ∩ futDrop n k)
      ≤ μ (⋃ m : ℕ, A m ∩ futSet n k (((m : ℝ) + 1) * h)) := measure_mono hcover
    _ ≤ ∑' m, μ (A m ∩ futSet n k (((m : ℝ) + 1) * h)) := measure_iUnion_le _
    _ ≤ ∑' m, (μ (A m) * ENNReal.ofReal ((m : ℝ) * h) + μ (A m) * ENNReal.ofReal (2 * h)) :=
        ENNReal.tsum_le_tsum hlev
    _ = ∑' m, μ (A m) * ENNReal.ofReal ((m : ℝ) * h) +
          (∑' m, μ (A m)) * ENNReal.ofReal (2 * h) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ +
          1 * ENNReal.ofReal (2 * h) :=
        add_le_add hint (mul_le_mul' hsumA le_rfl)
    _ = ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ +
          ENNReal.ofReal (2 * h) := by
        rw [one_mul]

/-- **The upper bound for the first occupied cell**: `P(B_k) ≤ E[1_{C_k ∩ F} U_k] +
P(Fᶜ)`. -/
theorem occupancyUpper_holds (γ : ℝ) : OccupancyUpper γ := by
  refine ⟨1, one_pos, 1, fun μ hμ n hn k j hk1 hkn _ _ => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hh : (0 : ℝ) < (ε : ℝ) / 2 := by
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    positivity
  have h1 : μ (firstCellEvent n k) ≤
      μ (pastEvent n k ∩ tameEvent n k j ∩ futDrop n k) + μ (tameEvent n k j)ᶜ := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro p hp
    obtain ⟨hpast, hfut⟩ := firstCellEvent_subset_pastFut hn hkn hp
    by_cases ht : p ∈ tameEvent n k j
    · exact Or.inl ⟨⟨hpast, ht⟩, hfut⟩
    · exact Or.inr ht
  have h2 := measure_inter_futDrop_le hμ j hn hkn hh
  have h3 : ENNReal.ofReal (2 * ((ε : ℝ) / 2)) = (ε : ℝ≥0∞) := by
    rw [show 2 * ((ε : ℝ) / 2) = ε by ring, ENNReal.ofReal_coe_nnreal]
  rw [h3] at h2
  calc μ (firstCellEvent n k)
      ≤ (∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ +
          (ε : ℝ≥0∞)) + μ (tameEvent n k j)ᶜ := h1.trans (add_le_add h2 le_rfl)
    _ = (∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ +
          μ (tameEvent n k j)ᶜ) + (ε : ℝ≥0∞) := by
        rw [add_right_comm]

end MatedCRT.PeanosphereTriplePoints
