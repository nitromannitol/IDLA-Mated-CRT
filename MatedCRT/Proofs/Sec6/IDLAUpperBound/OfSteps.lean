import MatedCRT.Proofs.Sec6.IDLAUpperBound.Quenched
import MatedCRT.Proofs.Sec6.IDLAUpperBound.BoundaryLayer
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma
import MatedCRT.Proofs.Sec6.IterativeBound.Walk
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.IDLA.Walkers
import MatedCRT.Proofs.IDLA.Counts
import MatedCRT.Proofs.IDLA.UpperEventMeasurable

/-!
# Proposition 6.1 (prop:IDLA-upper-bound, line 2252): the proof from Lemma 6.10, Proposition 5.1 and a measurability step

`iDLAUpperBound_of_steps`: Lemma 6.10 (`IterativeBoundStmt`), the stopped conjunct of Proposition 5.1
(`IDLALowerBoundStmt`) and `BoundaryLayerMeasurableStep` imply `IDLAUpperBoundStmt`. Lemma 6.3, the walk path property,
the measurability of `σ(h)` and the smallness of cells are used in their proved forms. See
MatedCRT/Steps/Sec6/IDLAUpperBound.lean for the departures from the printed proof.

Bookkeeping: the deterministic parameters are `s₀ = δ/4`, the cell size `d = δ/16`, then `δ₀` (small for
`C δ₀^β ≤ δ/4` and `P[𝛅₀ ≤ δ₀]` small), then `δ₁` (`P[t < T, μ_h(Λ_t \ B⁻_{δ₁}(Λ_t)) ≥ δ₀]` small); the annealed
outer probability of the bad event is at most that of the failure of Proposition 5.1, plus the outer integral of
Lemma 6.10, plus the probability of the bad environments (`outerLIntegral_le_add_add`).
-/

namespace MatedCRT

namespace IDLAUpperBound

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-! ### Outer integrals -/

theorem outerLIntegral_le_of_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ≥0∞}
    (hg : Measurable g) (hfg : f ≤ g) : outerLIntegral P f ≤ ∫⁻ ω, g ω ∂P :=
  iInf_le_of_le g (iInf_le_of_le hg (iInf_le_of_le hfg le_rfl))

theorem outerLIntegral_le_add_of_forall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f f₁ : Ω → ℝ≥0∞}
    {c : ℝ≥0∞} (H : ∀ g : Ω → ℝ≥0∞, Measurable g → f₁ ≤ g → outerLIntegral P f ≤ ∫⁻ ω, g ω ∂P + c) :
    outerLIntegral P f ≤ outerLIntegral P f₁ + c := by
  show _ ≤ (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f₁ ≤ g), ∫⁻ ω, g ω ∂P) + c
  rw [ENNReal.iInf_add]
  refine le_iInf fun g => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hg => ?_
  rw [ENNReal.iInf_add]
  exact le_iInf fun hfg => H g hg hfg

/-- Union bound for outer integrals: if `f ≤ 1` and `f ≤ f₁ + f₂` off `B`, then
`∫* f ≤ ∫* f₁ + ∫* f₂ + P*(B)`. -/
theorem outerLIntegral_le_add_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f f₁ f₂ : Ω → ℝ≥0∞)
    (B : Set Ω) (hf1 : ∀ ω, f ω ≤ 1) (h : ∀ ω, ω ∉ B → f ω ≤ f₁ ω + f₂ ω) :
    outerLIntegral P f ≤ outerLIntegral P f₁ + outerLIntegral P f₂ + P B := by
  set g₃ : Ω → ℝ≥0∞ := (toMeasurable P B).indicator 1 with hg₃
  have hg₃m : Measurable g₃ := measurable_one.indicator (measurableSet_toMeasurable P B)
  have hg₃i : ∫⁻ ω, g₃ ω ∂P = P B := by
    rw [hg₃, lintegral_indicator_one (measurableSet_toMeasurable P B), measure_toMeasurable]
  have key : ∀ g₁ : Ω → ℝ≥0∞, Measurable g₁ → f₁ ≤ g₁ → ∀ g₂ : Ω → ℝ≥0∞, Measurable g₂ → f₂ ≤ g₂ →
      outerLIntegral P f ≤ ∫⁻ ω, g₁ ω ∂P + ∫⁻ ω, g₂ ω ∂P + P B := by
    intro g₁ hg₁ hfg₁ g₂ hg₂ hfg₂
    refine (outerLIntegral_le_of_le P ((hg₁.add hg₂).add hg₃m) ?_).trans ?_
    · intro ω
      by_cases hω : ω ∈ B
      · have h1 : g₃ ω = 1 := by
          rw [hg₃, indicator_of_mem (subset_toMeasurable P B hω), Pi.one_apply]
        simp only [Pi.add_apply, h1]
        exact (hf1 ω).trans le_add_self
      · exact (h ω hω).trans ((add_le_add (hfg₁ ω) (hfg₂ ω)).trans le_self_add)
    · apply le_of_eq
      calc ∫⁻ ω, (g₁ + g₂ + g₃) ω ∂P = ∫⁻ ω, (g₁ + g₂) ω ∂P + ∫⁻ ω, g₃ ω ∂P :=
            lintegral_add_left (hg₁.add hg₂) g₃
        _ = ∫⁻ ω, g₁ ω ∂P + ∫⁻ ω, g₂ ω ∂P + ∫⁻ ω, g₃ ω ∂P :=
            congrArg (· + ∫⁻ ω, g₃ ω ∂P) (lintegral_add_left hg₁ g₂)
        _ = ∫⁻ ω, g₁ ω ∂P + ∫⁻ ω, g₂ ω ∂P + P B := by rw [hg₃i]
  rw [add_assoc]
  refine outerLIntegral_le_add_of_forall P fun g₁ hg₁ hfg₁ => ?_
  rw [add_left_comm]
  refine outerLIntegral_le_add_of_forall P fun g₂ hg₂ hfg₂ => ?_
  calc outerLIntegral P f ≤ ∫⁻ ω, g₁ ω ∂P + ∫⁻ ω, g₂ ω ∂P + P B := key g₁ hg₁ hfg₁ g₂ hg₂ hfg₂
    _ = ∫⁻ ω, g₂ ω ∂P + (∫⁻ ω, g₁ ω ∂P + P B) := by ring

/-! ### Choice of the parameters -/

/-- For a measurable positive `s`, `P[s ≤ δ₀]` is as small as we like for some `δ₀ ∈ (0, r]`. -/
theorem exists_prob_le_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (s : Ω → ℝ)
    (hs : Measurable s) (hpos : ∀ ω, 0 < s ω) {e : ℝ≥0∞} (he : 0 < e) {r : ℝ} (hr : 0 < r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ r ∧ P {ω | s ω ≤ δ₀} ≤ e := by
  set A : ℕ → Set Ω := fun n => {ω | s ω ≤ 1 / ((n : ℝ) + 1)} with hA
  have hanti : Antitone A := fun i j hij ω (hω : s ω ≤ _) => le_trans hω (one_div_succ_anti hij)
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (measurableSet_le hs measurable_const).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ n, A n) = ∅ := by
    ext ω
    simp only [hA, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact exists_nat_one_div_lt (hpos ω)
  rw [hempty, measure_empty] at hlim
  have h1 := ENNReal.tendsto_nhds_zero.1 hlim e he
  have h2 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ r :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)).mono fun _ hn => hn.le
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn2, hn1⟩

/-- On `{t < T}`, `Λ_t ⊆ B_{ρ/3}` (the family is increasing). -/
theorem subset_ball_of_lt_clusterExitTime {Λ : ℝ → Set ℂ} {ρ t : ℝ} (hmono : MonotoneOn Λ (Ioi 0))
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) : Λ t ⊆ ball 0 (ρ / 3) := by
  unfold clusterExitTime at hT
  have hne : {t' : ℝ | 0 < t' ∧ Λ t' ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hT
    linarith
  obtain ⟨t', ⟨ht'0, ht'⟩, htt'⟩ := exists_lt_of_lt_csSup hne hT
  exact fun x hx => ht' (hmono ht ht'0 htt'.le hx)

/-! ### The conclusion of Lemma 6.10 as a function of the environment -/

/-- The supremum, over the clusters, widths, numbers of walkers and starting sites allowed by Lemma 6.10 (with
`s₀`, `C`, `β` and the radius `dd`), of the conditional probability that its conclusion fails. -/
noncomputable def iterativeBoundSup {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ C β : ℝ)
    (dd : Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (Θ : Set ℤ) (_ : closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2))
    (_ : ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ) (δ₀ : ℝ) (_ : 0 < δ₀) (_ : δ₀ < dd ω) (j : ℕ)
    (_ : j ≤ ⌈δ₀ / ε⌉₊) (a : Fin j → ℤ) (_ : ∀ i, a i ∈ vClosure (S.mult ε ω) Θ),
      walkersLaw (S.mult ε ω) a {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
        cellVertices ε (S.η ω) (outerNbhd (C * δ₀ ^ β) (fillCells ε (S.η ω) Θ)) ∧
        cellVertices ε (S.η ω) (outerNbhd (C * δ₀ ^ β) (fillCells ε (S.η ω) Θ)) ⊆
          cellVertices ε (S.η ω) (ball 0 ρ))}

theorem le_iterativeBoundSup {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ C β : ℝ) (dd : Ω → ℝ)
    (ε : ℝ) (ω : Ω) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hdd : δ₀ < dd ω) (Θ : Set ℤ)
    (hcl : closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2)) (hball : ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ)
    (j : ℕ) (hj : j ≤ ⌈δ₀ / ε⌉₊) (a : Fin j → ℤ) (ha : ∀ i, a i ∈ vClosure (S.mult ε ω) Θ) :
    walkersLaw (S.mult ε ω) a {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
        cellVertices ε (S.η ω) (outerNbhd (C * δ₀ ^ β) (fillCells ε (S.η ω) Θ)) ∧
        cellVertices ε (S.η ω) (outerNbhd (C * δ₀ ^ β) (fillCells ε (S.η ω) Θ)) ⊆
          cellVertices ε (S.η ω) (ball 0 ρ))} ≤ iterativeBoundSup S ρ s₀ C β dd ε ω := by
  unfold iterativeBoundSup
  exact le_iSup_of_le Θ (le_iSup_of_le hcl (le_iSup_of_le hball (le_iSup_of_le δ₀ (le_iSup_of_le hδ₀
    (le_iSup_of_le hdd (le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le a (le_iSup_of_le ha le_rfl)))))))))

/-! ### The bound for one environment, in terms of the walker sequence -/

/-- `quenched_bound` for the first `⌊t ε⁻¹⌋` walkers of the walker sequence. -/
theorem walkerSequenceLaw_bad_le (m : ℤ → ℤ → ℕ) (hsrw : IsSrwPathLaw m) {ε t δ δ₀ δ₁ ρ d r : ℝ} (F : ℝ≥0∞)
    {η : ℝ → ℂ} {μ : Measure ℂ} {L : Set ℂ} (hε : 0 < ε) (ht : 0 < t) (hδ₀ : 0 < δ₀) (hρ : 0 < ρ)
    (hδρ : δ < ρ) (harea : IsAreaParametrized μ η) (h0L : 0 ∈ L) (hLρ : L ⊆ ball 0 (ρ / 3))
    (hμL : μ L = ENNReal.ofReal t) (hmass : μ (L \ innerNbhd δ₁ L) < ENNReal.ofReal δ₀)
    (hcells : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ d) (hd : 0 ≤ d) (hdρ : d < ρ / 6)
    (hr : 0 ≤ r) (hsum : d + (r + (d + δ / 4)) ≤ δ) (hδ : 0 < δ)
    (hF : ∀ Θ : Set ℤ, closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2) → ball 0 (δ / 4) ⊆ fillCells ε η Θ →
      ∀ j : ℕ, j ≤ ⌈δ₀ / ε⌉₊ → ∀ a : Fin j → ℤ, (∀ i, a i ∈ vClosure m Θ) →
        walkersLaw m a {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
          cellVertices ε η (outerNbhd r (fillCells ε η Θ)) ∧
          cellVertices ε η (outerNbhd r (fillCells ε η Θ)) ⊆ cellVertices ε η (ball 0 ρ))} ≤ F) :
    walkerSequenceLaw m 0 {xs | ¬ fillCells ε η (idlaCluster xs ⌊t / ε⌋₊) ⊆ outerNbhd δ L} ≤
      walkerSequenceLaw m 0
        {xs | ¬ innerNbhd δ₁ L ⊆ fillCells ε η (stoppedIDLACluster (cellVertices ε η L) xs ⌊t / ε⌋₊)} + F := by
  set n := ⌊t / ε⌋₊ with hn
  have hmap := walkerSequenceLaw_map_fin m 0 n
  have hE : MeasurableSet {ys : Fin n → ℕ → ℤ |
      ¬ fillCells ε η (idlaAggregate ∅ univ (List.ofFn ys)) ⊆ outerNbhd δ L} :=
    AbelianIDLA.measurableSet_foldl_idlaStep univ n (∅, []) fun s => ¬ fillCells ε η s.1 ⊆ outerNbhd δ L
  have hE₁ : MeasurableSet {ys : Fin n → ℕ → ℤ |
      ¬ innerNbhd δ₁ L ⊆ fillCells ε η (idlaAggregate ∅ (cellVertices ε η L) (List.ofFn ys))} :=
    AbelianIDLA.measurableSet_foldl_idlaStep (cellVertices ε η L) n (∅, []) fun s =>
      ¬ innerNbhd δ₁ L ⊆ fillCells ε η s.1
  have h1 : walkerSequenceLaw m 0 {xs | ¬ fillCells ε η (idlaCluster xs n) ⊆ outerNbhd δ L} =
      walkersLaw m (fun _ : Fin n => (0 : ℤ))
        {ys | ¬ fillCells ε η (idlaAggregate ∅ univ (List.ofFn ys)) ⊆ outerNbhd δ L} := by
    rw [← hmap, Measure.map_apply (measurable_restrictFin n) hE]
    rfl
  have h2 : walkerSequenceLaw m 0
      {xs | ¬ innerNbhd δ₁ L ⊆ fillCells ε η (stoppedIDLACluster (cellVertices ε η L) xs n)} =
      walkersLaw m (fun _ : Fin n => (0 : ℤ))
        {ys | ¬ innerNbhd δ₁ L ⊆ fillCells ε η (idlaAggregate ∅ (cellVertices ε η L) (List.ofFn ys))} := by
    rw [← hmap, Measure.map_apply (measurable_restrictFin n) hE₁]
    rfl
  rw [h1, h2]
  exact quenched_bound m hsrw F hε ht hδ₀ hρ hδρ harea h0L hLρ hμL hmass hcells hd hdρ hr hsum hδ hF

/-! ### Proposition 6.1 -/

/-- **Proposition 6.1** (prop:IDLA-upper-bound, line 2252) from Lemma 6.10, Proposition 5.1 and the null
measurability of the boundary layer events. -/
theorem iDLAUpperBoundSectionwise_of_steps (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hm : BoundaryLayerMeasurableStep 𝒮) : IDLAUpperBoundSectionwiseStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨β, C, hβ, hC, h610'⟩ := h610 γ hγ hγ2 ρ hρ hρ1
  have hs₀ : 0 < δ / 4 := by linarith
  have hs₀1 : δ / 4 < 1 := by linarith
  obtain ⟨dd, hddm, hddpos, hlim610⟩ := h610' (δ / 4) hs₀ hs₀1 Ω S hS
  have hlim : Tendsto (fun ε => outerLIntegral S.P (iterativeBoundSup S ρ (δ / 4) C β dd ε)) (𝓝[>] 0) (𝓝 0) :=
    hlim610
  have hddm' : Measurable dd := hddm.mono (fieldSigmaMeasurableStep 𝒮 γ hγ hγ2 Ω S hS) le_rfl
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  set e' : ℝ≥0∞ := e / 5 with he'
  have he'pos : 0 < e' := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  -- the cell size and `δ₀`
  set d : ℝ := δ / 16 with hd
  have hd0 : 0 < d := by positivity
  set r₀ : ℝ := (δ / (4 * C)) ^ β⁻¹ with hr₀
  have hr₀pos : 0 < r₀ := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨δ₀, hδ₀, hδ₀r, hδ₀P⟩ := exists_prob_le_le S.P dd hddm' hddpos he'pos hr₀pos
  have hCδ₀ : C * δ₀ ^ β ≤ δ / 4 := by
    have h1 : δ₀ ^ β ≤ r₀ ^ β := Real.rpow_le_rpow hδ₀.le hδ₀r hβ.le
    rw [hr₀, Real.rpow_inv_rpow (by positivity) hβ.ne'] at h1
    calc C * δ₀ ^ β ≤ C * (δ / (4 * C)) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = δ / 4 := by rw [← mul_div_assoc, mul_comm C δ, mul_div_mul_right _ _ hC.ne']
  have hr0 : 0 ≤ C * δ₀ ^ β := mul_nonneg hC.le (Real.rpow_nonneg hδ₀.le _)
  -- `δ₁`
  have hae : ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → IsOpen (Λ ω t) ∧ S.μ ω (Λ ω t) ≠ ⊤ := by
    filter_upwards [hΛ] with ω hω _
    exact ⟨(hω.1 t ht).1, (hω.1 t ht).2.2.2.1.ne⟩
  obtain ⟨δ₁', hδ₁', hδ₁'P⟩ := exists_boundaryLayer_prob_le S.P S.μ (fun ω => Λ ω t)
    (fun ω => t < clusterExitTime (Λ ω) ρ) hae hδ₀
    (fun δ₁ hδ₁ => hm γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t δ₁ δ₀ ht hδ₁) he'pos
  set δ₁ : ℝ := min δ₁' (ρ / 2) with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min hδ₁' (by linarith)
  have hδ₁ρ : δ₁ < ρ := (min_le_right _ _).trans_lt (by linarith)
  have hlayer : S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
      ENNReal.ofReal δ₀ ≤ S.μ ω (Λ ω t \ innerNbhd δ₁ (Λ ω t))} ≤ e' := by
    refine (measure_mono ?_).trans hδ₁'P
    intro ω hω
    exact ⟨hω.1, hω.2.trans (measure_mono (boundaryLayer_mono (min_le_left _ _)))⟩
  -- eventually in `ε`
  have hLB : Tendsto (fun ε => S.idlaSectionProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
      ¬ innerNbhd δ₁ (Λ p.1 t) ⊆ fillCells ε (S.η p.1)
        (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)})
      (𝓝[>] 0) (𝓝 0) := (h51 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ₁ t hδ₁pos hδ₁ρ ht).2
  have hcellsP := hS.probTendsToOne_small_cells ρ d hd0
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hLB e' he'pos, ENNReal.tendsto_nhds_zero.1 hlim e' he'pos,
    ENNReal.tendsto_nhds_zero.1 hcellsP e' he'pos, self_mem_nhdsWithin] with ε hεLB hε610 hεcells hε
  have hε0 : 0 < ε := hε
  set N : Set Ω := {ω | ¬ (IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω))}
    with hN
  have hN0 : S.P N = 0 := ae_iff.1 (hΛ.and hS.isAreaParametrized)
  set B : Set Ω := N ∪ {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), diam (cell ε (S.η ω) k) ≤ d}ᶜ ∪
    {ω | dd ω ≤ δ₀} ∪ {ω | t < clusterExitTime (Λ ω) ρ ∧
      ENNReal.ofReal δ₀ ≤ S.μ ω (Λ ω t \ innerNbhd δ₁ (Λ ω t))} with hB
  have hBP : S.P B ≤ 0 + e' + e' + e' :=
    (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add hN0.le hεcells)) hδ₀P)) hlayer)
  -- the bound for one environment
  have hpt : ∀ ω, ω ∉ B →
      walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℕ → ℤ) | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)}) ≤
      walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℕ → ℤ) | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ₁ (Λ p.1 t) ⊆ fillCells ε (S.η p.1)
          (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)}) +
      iterativeBoundSup S ρ (δ / 4) C β dd ε ω := by
    intro ω hω
    rw [hB, mem_union, mem_union, mem_union, not_or, not_or, not_or] at hω
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
    have hgood : IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) := not_not.1 h1
    have hcells : ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), diam (cell ε (S.η ω) k) ≤ d := not_not.1 h2
    have hdd : δ₀ < dd ω := not_le.1 h3
    by_cases hT : t < clusterExitTime (Λ ω) ρ
    · have hmass : S.μ ω (Λ ω t \ innerNbhd δ₁ (Λ ω t)) < ENNReal.ofReal δ₀ := not_le.1 fun h => h4 ⟨hT, h⟩
      obtain ⟨hfam, harea⟩ := hgood
      calc walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℕ → ℤ) |
            t < clusterExitTime (Λ p.1) ρ ∧
            ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)})
          ≤ walkerSequenceLaw (S.mult ε ω) 0
            {xs | ¬ fillCells ε (S.η ω) (idlaCluster xs ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ ω t)} :=
            measure_mono fun xs hxs => hxs.2
        _ ≤ walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ innerNbhd δ₁ (Λ ω t) ⊆
              fillCells ε (S.η ω) (stoppedIDLACluster (cellVertices ε (S.η ω) (Λ ω t)) xs ⌊t / ε⌋₊)} +
            iterativeBoundSup S ρ (δ / 4) C β dd ε ω :=
            walkerSequenceLaw_bad_le (S.mult ε ω) (srwPathStep (S.mult ε ω))
              (iterativeBoundSup S ρ (δ / 4) C β dd ε ω) hε0 ht hδ₀ hρ hδρ harea
              (hfam.2.1.mem t ht) (subset_ball_of_lt_clusterExitTime hfam.2.1.monotoneOn ht hT)
              (hfam.2.1.measure_eq t ht) hmass hcells hd0.le (by linarith) hr0 (by linarith) hδ
              fun Θ hcl hball j hj a ha =>
                le_iterativeBoundSup S ρ (δ / 4) C β dd ε ω hδ₀ hdd Θ hcl hball j hj a ha
        _ ≤ _ := by
            refine add_le_add (measure_mono ?_) le_rfl
            intro xs hxs
            exact ⟨hT, hxs⟩
    · refine le_trans (le_of_eq (measure_mono_null ?_ measure_empty)) zero_le
      intro xs hxs
      exact absurd hxs.1 hT
  have hbound := outerLIntegral_le_add_add S.P
    (fun ω => walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℕ → ℤ) |
      t < clusterExitTime (Λ p.1) ρ ∧
      ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)}))
    (fun ω => walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℕ → ℤ) |
      t < clusterExitTime (Λ p.1) ρ ∧
      ¬ innerNbhd δ₁ (Λ p.1 t) ⊆ fillCells ε (S.η p.1)
        (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)}))
    (iterativeBoundSup S ρ (δ / 4) C β dd ε) B (fun ω => prob_le_one) hpt
  calc S.idlaSectionProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t)}
      ≤ e' + e' + (0 + e' + e' + e') := hbound.trans (add_le_add (add_le_add hεLB hε610) hBP)
    _ = e' * 5 := by ring
    _ = e := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

/-- The sectionwise estimate supplies the present formulation of Proposition 6.1. -/
theorem iDLAUpperBound_of_steps (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hm : BoundaryLayerMeasurableStep 𝒮) : IDLAUpperBoundStmt 𝒮 :=
  iDLAUpperBoundSectionwise_of_steps 𝒮 h610 h51 hm

end IDLAUpperBound

end MatedCRT
