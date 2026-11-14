import MatedCRT.FirstPass.Derived.UniformStartStopTransfer

/-!
# Uniform transfer to stopped paths for a family of random paths, and the nested-disc case

For a family `Y z` of random continuous paths indexed by start points `z` of a compact set `K`, the transfer of
one-sided Lévy–Prokhorov bounds to the paths stopped at their exit time from an open set `U` holds uniformly in
`z ∈ K` under three conditions:
* at each centre `c ∈ K` the quantitative good event `GoodStopN U N ε (Y c)` has probability tending to `1`;
* the distance `cmpEDist (Y z) (Y y)` of curves modulo time parametrization is uniformly small in measure for
  nearby `y ∈ K` and `z`;
* the same holds for the paths stopped at their exit time from `U`.

The main application is planar Brownian motion stopped at its exit time from a larger disc `B_r(0)`, `R < r`,
with `U = B_R(0)`: then stopping at `B_R(0)` after stopping at `B_r(0)` is stopping at `B_R(0)`, and the bound
compares paths stopped at the larger radius with Brownian motion stopped at `B_R(0)`. This is the form needed
when an invariance principle controls the walk and the Brownian motion only up to their exit times from a larger
disc, as for the local metric on curves modulo time parametrization.

## Main statements
* `MatedCRT.StopAtExitCmp.tendsto_measure_not_goodStopN_of_family`: the good event for a measurable family.
* `MatedCRT.StopAtExitCmp.exists_forall_measure_preimage_stopAtExit_le_of_family`: the uniform transfer.
* `MatedCRT.StopAtExitCmp.exists_forall_measure_stoppedSupDist_le`: uniform smallness in measure of the uniform
  distance of stopped Brownian translates.
* `MatedCRT.StopAtExitCmp.exists_forall_planarBrownianMotion_preimage_stopAtExit_nested_le`: the nested-disc case.
* `MatedCRT.StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le_nested`: transfer of one-sided bounds between
  paths stopped at `B_r(0)` and Brownian motion stopped at `B_r(0)` to the paths stopped at `B_R(0)`.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- **The good event for a family of random paths.** For a finite measure and a family `F ω` of continuous paths
with measurable coordinates and measurable exit time from the open set `U`, which almost surely leaves `U` at a
finite time and exits it regularly, the probability of the complement of `GoodStopN U N ε (F ω)` tends to `0`. -/
theorem tendsto_measure_not_goodStopN_of_family {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U) {F : Ω → ℝ≥0 → ℂ} (hFc : ∀ ω, Continuous (F ω))
    (hF : ∀ t, Measurable fun ω => F ω t) (hτ : Measurable fun ω => pathExitTime U (F ω))
    (hae : ∀ᵐ ω ∂μ, pathExitTime U (F ω) ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U (F ω))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => μ {ω | ¬ GoodStopN U N ε (F ω)}) atTop (𝓝 0) := by
  have hmeas : ∀ N : ℕ, MeasurableSet {ω | ¬ GoodStopN U N ε (F ω)} :=
    fun N => (measurableSet_setOfPred.2 (measurable_goodStopN N ε hF hτ)).compl
  have hanti : Antitone fun N : ℕ => {ω | ¬ GoodStopN U N ε (F ω)} :=
    fun N N' hNN' ω hω hω' => hω (goodStopN_mono hNN' hω')
  have hzero : μ (⋂ N : ℕ, {ω | ¬ GoodStopN U N ε (F ω)}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro ω hω hgood
    obtain ⟨N, hN⟩ := exists_goodStopN_of_regularExit hU (hFc ω) hgood.1 hgood.2 hε
    exact mem_iInter.1 hω N hN
  rw [← hzero]
  exact tendsto_measure_iInter_atTop (fun N => (hmeas N).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩

/-- **Uniform transfer to the stopped paths for a family.** Let `K` be compact and `Y z` a family of random
continuous paths such that at every centre `c ∈ K` the good event `GoodStopN U N ε (Y c)` has probability tending
to `1` for every `ε > 0`, and such that `cmpEDist (Y z) (Y y)` and `cmpEDist (stop_U (Y z)) (stop_U (Y y))` are
uniformly small in measure for `y ∈ K` and `z` near `y`. Then for all `ε, θ > 0` there is `δ > 0` such that for
all `z ∈ K` and all sets `A` of paths, the probability that `Y z` is at distance less than `δ` from a path `g` with
`stop_U g ∈ A` is at most the probability that `stop_U (Y z)` is at distance less than `ε` from `A`, plus `θ`. -/
theorem exists_forall_measure_preimage_stopAtExit_le_of_family {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {K : Set ℂ} (hK : IsCompact K) {U : Set ℂ} {Y : ℂ → Ω → ℝ≥0 → ℂ}
    (hYc : ∀ z ω, Continuous (Y z ω))
    (hgood : ∀ c ∈ K, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ => μ {ω | ¬ GoodStopN U N ε (Y c ω)}) atTop (𝓝 0))
    (hpath : ∀ κ θ : ℝ, 0 < κ → 0 < θ → ∃ δ > 0, ∀ y ∈ K, ∀ z, dist z y < δ →
      μ {ω | ENNReal.ofReal κ ≤ cmpEDist (Y z ω) (Y y ω)} ≤ ENNReal.ofReal θ)
    (hstop : ∀ κ θ : ℝ, 0 < κ → 0 < θ → ∃ δ > 0, ∀ y ∈ K, ∀ z, dist z y < δ →
      μ {ω | ENNReal.ofReal κ ≤ cmpEDist (stopAtExit U (Y z ω)) (stopAtExit U (Y y ω))} ≤
        ENNReal.ofReal θ)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ K, ∀ A : Set (ℝ≥0 → ℂ),
      μ {ω | ∃ g : ℝ≥0 → ℂ, stopAtExit U g ∈ A ∧ cmpEDist (Y z ω) g < ENNReal.ofReal δ} ≤
        μ {ω | ∃ f ∈ A, cmpEDist (stopAtExit U (Y z ω)) f < ENNReal.ofReal ε} + ENNReal.ofReal θ := by
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / 4 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = θ / 3 := ⟨_, rfl⟩
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  obtain ⟨δ₁, hδ₁, hst⟩ := hstop ε' θ' hε'0 hθ'0
  -- a good-event index at each centre
  have hN : ∀ c ∈ K, ∃ N : ℕ, 1 ≤ N ∧ μ {ω | ¬ GoodStopN U N ε' (Y c ω)} < ENNReal.ofReal θ' := fun c hc =>
    ((eventually_ge_atTop 1).and ((hgood c hc ε' hε'0).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ'0)))).exists
  choose! N hN1 hNθ using hN
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ → ℝ, ∀ c, κ c = min ε' ((N c : ℝ)⁻¹) / 2 := ⟨_, fun _ => rfl⟩
  have hκ0 : ∀ c ∈ K, 0 < κ c := fun c hc => by
    rw [hκ c]
    exact half_pos (lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 c hc))))
  -- the path distance to the centre is small with high probability near each centre
  have hδ₂ : ∀ c ∈ K, ∃ δ₂ > 0, ∀ z, dist z c < δ₂ →
      μ {ω | ENNReal.ofReal (κ c) ≤ cmpEDist (Y z ω) (Y c ω)} ≤ ENNReal.ofReal θ' := fun c hc => by
    obtain ⟨δ₂, hδ₂, h⟩ := hpath (κ c) θ' (hκ0 c hc) hθ'0
    exact ⟨δ₂, hδ₂, fun z hz => h c hc z hz⟩
  choose! δ₂ hδ₂0 hδ₂ using hδ₂
  obtain ⟨r, hr⟩ : ∃ r : ℂ → ℝ, ∀ c, r c = min δ₁ (min (δ₂ c) (κ c)) := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ c ∈ K, 0 < r c := fun c hc => by
    rw [hr c]
    exact lt_min hδ₁ (lt_min (hδ₂0 c hc) (hκ0 c hc))
  -- a finite cover of `K` by discs with adapted radii
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : K => ball (c : ℂ) (r c)) (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr0 z hz)⟩)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i ∈ t, δ < r i :=
    ((Filter.eventually_all_finset t).2 fun i _ => gt_mem_nhds (hr0 i i.2)).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨δ, hδr, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : 0 < δ := hδ0
  refine ⟨δ, hδ0', fun z hz A => ?_⟩
  obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.1 (ht hz)
  have hcK : (i : ℂ) ∈ K := i.2
  have hzc : dist z (i : ℂ) < r i := mem_ball.1 hzi
  have hδc : δ < r i := hδr i hit
  have hri := hr i
  have hκi := hκ i
  have hm1 := min_le_left δ₁ (min (δ₂ i) (κ i))
  have hm2 := min_le_right δ₁ (min (δ₂ i) (κ i))
  have hm3 := min_le_left (δ₂ i) (κ i)
  have hm4 := min_le_right (δ₂ i) (κ i)
  have hzδ₁ : dist z (i : ℂ) < δ₁ := by linarith [hzc, hri, hm1]
  have hzδ₂ : dist z (i : ℂ) < δ₂ i := by linarith [hzc, hri, hm2, hm3]
  have hδκ : δ < κ i := by linarith [hδc, hri, hm2, hm4]
  have hmin0 : 0 < min ε' ((N i : ℝ)⁻¹) := lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 i hcK)))
  have h2κ : δ + κ i < min ε' ((N i : ℝ)⁻¹) := by linarith [hδκ, hκi]
  -- the bad set lies in the good set or one of three small events at the centre
  have hsub : {ω | ∃ g : ℝ≥0 → ℂ, stopAtExit U g ∈ A ∧ cmpEDist (Y z ω) g < ENNReal.ofReal δ} ⊆
      (({ω | ∃ f ∈ A, cmpEDist (stopAtExit U (Y z ω)) f < ENNReal.ofReal ε} ∪
          {ω | ¬ GoodStopN U (N i) ε' (Y (i : ℂ) ω)}) ∪
        {ω | ENNReal.ofReal ε' ≤ cmpEDist (stopAtExit U (Y z ω)) (stopAtExit U (Y (i : ℂ) ω))}) ∪
        {ω | ENNReal.ofReal (κ i) ≤ cmpEDist (Y z ω) (Y (i : ℂ) ω)} := by
    intro ω hω
    obtain ⟨g, hgA, hg⟩ := hω
    by_cases hp : ENNReal.ofReal (κ i) ≤ cmpEDist (Y z ω) (Y (i : ℂ) ω)
    · exact Or.inr hp
    by_cases hs : ENNReal.ofReal ε' ≤ cmpEDist (stopAtExit U (Y z ω)) (stopAtExit U (Y (i : ℂ) ω))
    · exact Or.inl (Or.inr hs)
    by_cases hgd : GoodStopN U (N i) ε' (Y (i : ℂ) ω)
    · refine Or.inl (Or.inl (Or.inl ⟨stopAtExit U g, hgA, ?_⟩))
      have h2 : cmpEDist g (Y (i : ℂ) ω) < ENNReal.ofReal (min ε' ((N i : ℝ)⁻¹)) := by
        calc cmpEDist g (Y (i : ℂ) ω)
            ≤ cmpEDist g (Y z ω) + cmpEDist (Y z ω) (Y (i : ℂ) ω) := cmpEDist_triangle _ _ _
          _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (κ i) := by
              refine add_le_add ?_ (not_le.1 hp).le
              rw [cmpEDist_comm]
              exact hg.le
          _ = ENNReal.ofReal (δ + κ i) := (ENNReal.ofReal_add hδ0'.le (hκ0 i hcK).le).symm
          _ < ENNReal.ofReal (min ε' ((N i : ℝ)⁻¹)) := (ENNReal.ofReal_lt_ofReal_iff hmin0).2 h2κ
      have h3 := cmpEDist_stopAtExit_le_of_goodStopN (hYc (i : ℂ) ω) hgd h2
      calc cmpEDist (stopAtExit U (Y z ω)) (stopAtExit U g)
          ≤ cmpEDist (stopAtExit U (Y z ω)) (stopAtExit U (Y (i : ℂ) ω)) +
              cmpEDist (stopAtExit U (Y (i : ℂ) ω)) (stopAtExit U g) := cmpEDist_triangle _ _ _
        _ ≤ ENNReal.ofReal ε' + ENNReal.ofReal (2 * ε') := by
            refine add_le_add (not_le.1 hs).le ?_
            rw [cmpEDist_comm]
            exact h3
        _ = ENNReal.ofReal (3 * ε') := by
            rw [← ENNReal.ofReal_add hε'0.le (by linarith)]
            congr 1
            ring
        _ < ENNReal.ofReal ε := by
            rw [ENNReal.ofReal_lt_ofReal_iff hε, hε']
            linarith
    · exact Or.inl (Or.inl (Or.inr hgd))
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ μ {ω | ∃ f ∈ A, cmpEDist (stopAtExit U (Y z ω)) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ' + ENNReal.ofReal θ' + ENNReal.ofReal θ' := by
        refine add_le_add ((measure_union_le _ _).trans (add_le_add ?_ (hst _ hcK z hzδ₁)))
          (hδ₂ _ hcK z hzδ₂)
        exact (measure_union_le _ _).trans (add_le_add le_rfl (hNθ _ hcK).le)
    _ = _ := by
        simp only [add_assoc]
        rw [← ENNReal.ofReal_add hθ'0.le hθ'0.le,
          ← ENNReal.ofReal_add hθ'0.le (by linarith), show θ' + (θ' + θ') = θ by rw [hθ']; ring]

/-- **Uniform smallness in measure of the stopped uniform distance.** For `ρ < r` and `κ, θ > 0` there is `δ > 0`
such that for `y ∈ closedBall 0 ρ` and `dist z y < δ`, the uniform distance between the translates by `z` and by
`y` of planar Brownian motion from `0`, each stopped at its exit time from `B_r(0)`, is at least `κ` with
probability at most `θ`. -/
theorem exists_forall_measure_stoppedSupDist_le {ρ r : ℝ} (hρr : ρ < r) {κ θ : ℝ} (hκ : 0 < κ)
    (hθ : 0 < θ) :
    ∃ δ > 0, ∀ y ∈ closedBall (0 : ℂ) ρ, ∀ z, dist z y < δ →
      planarBrownianMotion 0 {b | ENNReal.ofReal κ ≤ stoppedSupDist (ball (0 : ℂ) r) y z b} ≤
        ENNReal.ofReal θ :=
  LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae
    (μ := planarBrownianMotion 0) (isCompact_closedBall (0 : ℂ) ρ)
    (F := stoppedSupDist (ball (0 : ℂ) r)) (stoppedSupDist_le_add (ball (0 : ℂ) r))
    (fun y z => (measurable_stoppedSupDist isOpen_ball y z).aemeasurable)
    (fun _ hc _ hu => ae_tendsto_stoppedSupDist_ball
      (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hc) hρr)) hu)
    (ENNReal.ofReal_pos.2 hκ) (ENNReal.ofReal_pos.2 hθ)

/-- **Uniform transfer, nested discs.** Let `ρ < R < r`. For all `ε, θ > 0` there is `δ > 0` such that for every
start point `z ∈ closedBall 0 ρ` and every set `A` of paths, the probability under planar Brownian motion from `z`
that `stop_r b` is at `cmpEDist`-distance less than `δ` from a path `g` with `stop_R g ∈ A` is at most the
probability that `stop_R b` is at distance less than `ε` from `A`, plus `θ`. Here `stop_s` is stopping at the exit
time from `B_s(0)`. -/
theorem exists_forall_planarBrownianMotion_preimage_stopAtExit_nested_le {ρ R r : ℝ} (hρR : ρ < R)
    (hRr : R < r) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ A : Set (ℝ≥0 → ℂ),
      planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑b) g < ENNReal.ofReal δ} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  have hsub : ball (0 : ℂ) R ⊆ ball (0 : ℂ) r := ball_subset_ball hRr.le
  have hcl : closure (ball (0 : ℂ) R) ⊆ interior (ball (0 : ℂ) r) := by
    rw [isOpen_ball.interior_eq]
    exact (closure_ball_subset_closedBall).trans (closedBall_subset_ball hRr)
  have hKR : ∀ c ∈ closedBall (0 : ℂ) ρ, c ∈ ball (0 : ℂ) R := fun c hc =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hc) hρR)
  have hnest : ∀ (z : ℂ) (b : ContinuousPath ℂ),
      stopAtExit (ball (0 : ℂ) R) (stopAtExit (ball (0 : ℂ) r) ⇑(translatePath z b)) =
        stopAtExit (ball (0 : ℂ) R) ⇑(translatePath z b) := fun z b =>
    stopAtExit_stopAtExit_of_subset isOpen_ball hsub (translatePath z b).continuous
  obtain ⟨δ, hδ, h⟩ := exists_forall_measure_preimage_stopAtExit_le_of_family
    (μ := planarBrownianMotion 0) (isCompact_closedBall (0 : ℂ) ρ) (U := ball (0 : ℂ) R)
    (Y := fun z b => stopAtExit (ball (0 : ℂ) r) ⇑(translatePath z b))
    (fun z b => continuous_stopAtExit (translatePath z b).continuous)
    (fun c hc ε' hε' => by
      refine tendsto_measure_not_goodStopN_of_family isOpen_ball
        (fun b => continuous_stopAtExit (translatePath c b).continuous)
        (fun t => (measurable_stopAtExit_apply isOpen_ball t).comp (translatePath c).measurable) ?_ ?_ hε'
      · convert (ContinuousPath.measurable_exitTime (ball (0 : ℂ) R) isOpen_ball).comp
          (translatePath c).measurable using 1
        funext b
        exact pathExitTime_stopAtExit_of_subset isOpen_ball hsub (translatePath c b).continuous
      · have hc' : ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion c, b 0 = c ∧
            (pathExitTime (ball (0 : ℂ) R) ⇑b ≠ ⊤ ∧
              MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) R) ⇑b) :=
          (ae_planarBrownianMotion_eval_zero c).and (ae_regularExit_ball_planarBrownian (hKR c hc))
        rw [← map_translatePath_planarBrownianMotion c] at hc'
        filter_upwards [ae_of_ae_map (translatePath c).measurable.aemeasurable hc'] with b hb
        exact regularExit_stopAtExit isOpen_ball hcl (translatePath c b).continuous
          (by rw [hb.1]; exact hKR c hc) hb.2.1 hb.2.2)
    (fun κ θ' hκ hθ' => by
      obtain ⟨δ', hδ', h'⟩ := exists_forall_measure_stoppedSupDist_le (hρR.trans hRr) hκ hθ'
      refine ⟨δ', hδ', fun y hy z hz => (measure_mono fun b hb => ?_).trans (h' y hy z hz)⟩
      have hb0 : ENNReal.ofReal κ ≤ cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑(translatePath z b))
          (stopAtExit (ball (0 : ℂ) r) ⇑(translatePath y b)) := hb
      show ENNReal.ofReal κ ≤ stoppedSupDist (ball (0 : ℂ) r) y z b
      exact hb0.trans (cmpEDist_le_iSup_edist _ _))
    (fun κ θ' hκ hθ' => by
      obtain ⟨δ', hδ', h'⟩ := exists_forall_measure_stoppedSupDist_le hρR hκ hθ'
      refine ⟨δ', hδ', fun y hy z hz => (measure_mono fun b hb => ?_).trans (h' y hy z hz)⟩
      have hb' : ENNReal.ofReal κ ≤ cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath z b))
          (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath y b)) := by
        rw [← hnest z b, ← hnest y b]
        exact hb
      show ENNReal.ofReal κ ≤ stoppedSupDist (ball (0 : ℂ) R) y z b
      exact hb'.trans (cmpEDist_le_iSup_edist _ _))
    hε hθ
  refine ⟨δ, hδ, fun z hz A => ?_⟩
  have hz := h z hz A
  simp only [hnest] at hz
  rw [planarBrownianMotion_apply_eq_translatePath z, planarBrownianMotion_apply_eq_translatePath z]
  exact hz

/-- **Transfer of one-sided Lévy–Prokhorov bounds, nested discs.** Let `ρ < R < r` and `ε, θ > 0`. There is
`δ > 0` such that for every start point `z ∈ closedBall 0 ρ` and every random path `W` under a measure `ν`: if
`ν(W ∈ S) ≤ P_z(stop_r b is at cmpEDist-distance < δ from S) + δ` for every set `S` of paths, then for every set
`A`, `ν(stop_R W ∈ A) ≤ P_z(stop_R b is at distance < ε from A) + θ`. The hypothesis is typically applied to
`W = stop_r W'`, since `stop_R ∘ stop_r = stop_R` on continuous paths. -/
theorem exists_forall_stopAtExit_le_of_forall_le_nested {Ω' : Type*} [MeasurableSpace Ω'] {ρ R r : ℝ}
    (hρR : ρ < R) (hRr : R < r) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ (ν : Measure Ω') (W : Ω' → ℝ≥0 → ℂ),
      (∀ S : Set (ℝ≥0 → ℂ), ν {w | W w ∈ S} ≤
        planarBrownianMotion z {b | ∃ g ∈ S, cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑b) g < ENNReal.ofReal δ} +
          ENNReal.ofReal δ) →
      ∀ A : Set (ℝ≥0 → ℂ), ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  obtain ⟨δ₀, hδ₀, h⟩ :=
    exists_forall_planarBrownianMotion_preimage_stopAtExit_nested_le hρR hRr hε (half_pos hθ)
  refine ⟨min δ₀ (θ / 2), lt_min hδ₀ (half_pos hθ), fun z hz ν W hW A => ?_⟩
  have hS := hW (stopAtExit (ball (0 : ℂ) R) ⁻¹' A)
  have hsub : {b : ContinuousPath ℂ | ∃ g ∈ stopAtExit (ball (0 : ℂ) R) ⁻¹' A,
        cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑b) g < ENNReal.ofReal (min δ₀ (θ / 2))} ⊆
      {b | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧
        cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑b) g < ENNReal.ofReal δ₀} := by
    intro b hb
    obtain ⟨g, hgA, hlt⟩ := hb
    exact ⟨g, hgA, hlt.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
  calc ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A}
      ≤ _ := hS
    _ ≤ planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑b) g < ENNReal.ofReal δ₀} +
          ENNReal.ofReal (θ / 2) :=
        add_le_add (measure_mono hsub) (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    _ ≤ planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        add_le_add (h z hz A) le_rfl
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add (half_pos hθ).le (half_pos hθ).le, add_halves]

end MatedCRT.StopAtExitCmp
