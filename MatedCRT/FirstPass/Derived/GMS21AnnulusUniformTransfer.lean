import MatedCRT.FirstPass.Derived.UniformStartVariableRadiusTransfer
import MatedCRT.FirstPass.Derived.GMS21AnnulusRegularExit

/-!
# Uniform transfer to paths stopped at the exit of an annulus

Let `U` be a bounded open set, `U ⊆ B_R(0)`, from which planar Brownian motion started at the points of a compact set
`K ⊆ U` exits regularly. For planar Brownian motion `b` started at `z ∈ K`, closeness of a continuous path `g` to `b`
after both are stopped at their exit times from SOME disc `B_r(0)` with `r > R + κ` controls the two paths stopped at
their exit times from `U`, uniformly in the start `z ∈ K`. This is the form of
`UniformStartVariableRadiusTransfer.lean` (there `U = B_R(0)`) used in the proof of Gwynne–Miller–Sheffield
(arXiv:1705.11161), Theorem 3.4, case 1, where the walk and Brownian motion are stopped at their exits from the annulus
`B_R(0) \ closedBall 0 α` and the starts range over `closedBall 0 ρ \ B_b(0)`, `0 < α < b < ρ < R`: the regular exit
from the annulus is `ae_regularExit_annulus_planarBrownian`.

## Main statements
* `ae_tendsto_stoppedSupDist_of_regularExit`: almost sure continuity in the start of the stopped Brownian path.
* `exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le_of_regularExit`: the uniform bound.
* `exists_forall_stopAtExit_le_of_forall_le_variable_of_regularExit`: transfer of one-sided Lévy–Prokhorov bounds
  stated at variable radii to the paths stopped at the exit of `U`.
* `exists_forall_stopAtExit_le_of_forall_le_variable_annulus`: the same for the annulus.
-/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- **Almost sure continuity in the start point.** If planar Brownian motion from `c` exits the open set `U` regularly
at a finite time almost surely, then for every sequence of starts `u n → c` the paths from `u n` and from `c`, built
from the same Brownian increments and stopped at their exits from `U`, are uniformly close almost surely. -/
theorem ae_tendsto_stoppedSupDist_of_regularExit {U : Set ℂ} (hU : IsOpen U) {c : ℂ}
    (hc : ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion c,
      pathExitTime U ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U ⇑b)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (𝓝 c)) :
    ∀ᵐ b ∂planarBrownianMotion 0,
      Tendsto (fun n => stoppedSupDist U c (u n) b) atTop (𝓝 0) := by
  have h := hc
  rw [← map_translatePath_planarBrownianMotion c] at h
  have h0 := ae_of_ae_map (translatePath c).measurable.aemeasurable h
  filter_upwards [h0] with b hb
  have hv : Tendsto (fun n => u n - c) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 hu
  have hfun : ∀ n, ⇑(translatePath (u n) b) = fun s => ⇑(translatePath c b) s + (u n - c) := by
    intro n
    funext s
    simp only [translatePath_apply]
    ring
  have key := tendsto_iSup_edist_stopAtExit_add_const_of_regularExit hU
    (translatePath c b).continuous hb hv
  refine key.congr fun n => ?_
  simp only [stoppedSupDist, hfun n]

/-- **Uniform transfer from a variable larger radius, for an open set with regular exit.** Let `U ⊆ B_R(0)` be open,
`K ⊆ U` compact, `κ > 0`, and let planar Brownian motion from every point of `K` exit `U` regularly at a finite time
almost surely. For all `ε, θ > 0` there is `δ > 0` such that for every start `z ∈ K` and every set `A` of paths, the
probability under planar Brownian motion from `z` that some continuous path `g` with `stopAtExit U g ∈ A` is, for
some radius `r > R + κ`, at `cmpEDist`-distance less than `δ` from `b` after both are stopped at their exit times
from `B_r(0)`, is at most the probability that `stopAtExit U b` is at distance less than `ε` from `A`, plus `θ`. -/
theorem exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le_of_regularExit {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {R κ : ℝ} (hUR : U ⊆ ball (0 : ℂ) R) (hκ : 0 < κ)
    (hreg : ∀ c ∈ K, ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion c,
      pathExitTime U ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U ⇑b)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ K, ∀ A : Set (ℝ≥0 → ℂ),
      planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit U g ∈ A ∧ ∃ r : ℝ, R + κ < r ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min (ε / 4) (κ / 2) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min (by linarith) (by linarith)
  have hε'ε : ε' ≤ ε / 4 := by rw [hε']; exact min_le_left _ _
  have hε'κ : ε' ≤ κ / 2 := by rw [hε']; exact min_le_right _ _
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = θ / 2 := ⟨_, rfl⟩
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  obtain ⟨δ₁, hδ₁, hssd⟩ := LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae
    (μ := planarBrownianMotion 0) hK
    (F := stoppedSupDist U) (stoppedSupDist_le_add U)
    (fun y z => (measurable_stoppedSupDist hU y z).aemeasurable)
    (fun c hc u hu => ae_tendsto_stoppedSupDist_of_regularExit hU (hreg c hc) hu)
    (ENNReal.ofReal_pos.2 hε'0) (ENNReal.ofReal_pos.2 hθ'0)
  -- a good-event index at each centre, together with the start of the path
  have hN : ∀ c ∈ K, ∃ N : ℕ, 1 ≤ N ∧
      planarBrownianMotion c {b | ¬ (GoodStopN U N ε' ⇑b ∧ b 0 = c)} < ENNReal.ofReal θ' := by
    intro c hc
    obtain ⟨N, hN1, hNlt⟩ := ((eventually_ge_atTop 1).and
      ((tendsto_measure_not_goodStopN hU (hreg c hc) hε'0).eventually
        (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ'0)))).exists
    refine ⟨N, hN1, lt_of_le_of_lt ?_ hNlt⟩
    have h0 : planarBrownianMotion c {b | ¬ b 0 = c} = 0 := ae_iff.1 (ae_planarBrownianMotion_eval_zero c)
    calc planarBrownianMotion c {b | ¬ (GoodStopN U N ε' ⇑b ∧ b 0 = c)}
        ≤ planarBrownianMotion c ({b | ¬ GoodStopN U N ε' ⇑b} ∪ {b | ¬ b 0 = c}) :=
          measure_mono fun b hb => not_and_or.1 hb
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [h0, add_zero]
  choose! N hN1 hNθ using hN
  obtain ⟨r, hr⟩ : ∃ r : ℂ → ℝ, ∀ c, r c = min δ₁ (min ε' ((N c : ℝ)⁻¹)) / 2 := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ c ∈ K, 0 < r c := by
    intro c hc
    rw [hr c]
    exact half_pos (lt_min hδ₁ (lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 c hc)))))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : K => ball (c : ℂ) (r c)) (fun _ => isOpen_ball)
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
  have hrc := hr i
  have hm1 := min_le_left δ₁ (min ε' ((N i : ℝ)⁻¹))
  have hm2 := min_le_right δ₁ (min ε' ((N i : ℝ)⁻¹))
  have hm3 := min_le_left ε' ((N i : ℝ)⁻¹)
  have hzcδ₁ : dist z (i : ℂ) < δ₁ := by linarith [hzc, hrc, hm1]
  have hsum : δ + dist z (i : ℂ) < min ε' ((N i : ℝ)⁻¹) := by linarith [hzc, hδc, hrc, hm2]
  have hzcε' : dist z (i : ℂ) < ε' := by linarith [hzc, hrc, hm2, hm3, hδc, hδ0']
  have hmin0 : 0 < min ε' ((N i : ℝ)⁻¹) := lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 i hcK)))
  have hsub : translatePath z ⁻¹'
        {b : ContinuousPath ℂ | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit U g ∈ A ∧
          ∃ r : ℝ, R + κ < r ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} ⊆
      (translatePath z ⁻¹' {b : ContinuousPath ℂ | ∃ f ∈ A,
          cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal ε} ∪
        {b | ¬ (GoodStopN U (N i) ε' ⇑(translatePath (i : ℂ) b) ∧
          translatePath (i : ℂ) b 0 = (i : ℂ))}) ∪
        {b | ENNReal.ofReal ε' ≤ stoppedSupDist U (i : ℂ) z b} := by
    intro b hb
    obtain ⟨g, hgc, hgA, r', hr', hg⟩ := hb
    by_cases hgood : GoodStopN U (N i) ε' ⇑(translatePath (i : ℂ) b) ∧
        translatePath (i : ℂ) b 0 = (i : ℂ)
    · by_cases hs : ENNReal.ofReal ε' ≤ stoppedSupDist U (i : ℂ) z b
      · exact Or.inr hs
      · refine Or.inl (Or.inl ⟨stopAtExit U g, hgA, ?_⟩)
        have h2 : cmpEDist (stopAtExit (ball (0 : ℂ) r') g)
            (stopAtExit (ball ((i : ℂ) - z) r') ⇑(translatePath (i : ℂ) b)) <
              ENNReal.ofReal (min ε' ((N i : ℝ)⁻¹)) := by
          calc cmpEDist (stopAtExit (ball (0 : ℂ) r') g)
                (stopAtExit (ball ((i : ℂ) - z) r') ⇑(translatePath (i : ℂ) b))
              ≤ cmpEDist (stopAtExit (ball (0 : ℂ) r') g)
                    (stopAtExit (ball (0 : ℂ) r') ⇑(translatePath z b)) +
                  cmpEDist (stopAtExit (ball (0 : ℂ) r') ⇑(translatePath z b))
                    (stopAtExit (ball ((i : ℂ) - z) r') ⇑(translatePath (i : ℂ) b)) :=
                cmpEDist_triangle _ _ _
            _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (dist z (i : ℂ)) :=
                add_le_add hg.le ((cmpEDist_stopAtExit_translatePath_le b z (i : ℂ) r').trans
                  (edist_dist _ _).le)
            _ = ENNReal.ofReal (δ + dist z (i : ℂ)) := (ENNReal.ofReal_add hδ0'.le dist_nonneg).symm
            _ < ENNReal.ofReal (min ε' ((N i : ℝ)⁻¹)) := (ENNReal.ofReal_lt_ofReal_iff hmin0).2 hsum
        have hR : 0 < R := pos_of_mem_ball (hUR (hKU hcK))
        have hUV : cthickening ε' U ⊆ ball ((i : ℂ) - z) r' := by
          refine (cthickening_subset_of_subset ε' hUR).trans ?_
          rw [cthickening_ball hε'0.le hR]
          refine closedBall_subset_ball' ?_
          have hd : dist (0 : ℂ) ((i : ℂ) - z) = dist z (i : ℂ) := by
            rw [dist_comm, dist_zero_right, ← dist_eq_norm, dist_comm]
          rw [hd]
          linarith
        have h0 : translatePath (i : ℂ) b 0 ∈ U := by
          rw [hgood.2]
          exact hKU hcK
        have h3 := cmpEDist_stopAtExit_le_of_goodStopN_of_cthickening_subset hU
          (translatePath (i : ℂ) b).continuous h0 hUV hgood.1 h2
        rw [stopAtExit_stopAtExit_of_subset hU (hUR.trans (ball_subset_ball (by linarith))) hgc] at h3
        have h4 : cmpEDist (stopAtExit U ⇑(translatePath z b))
            (stopAtExit U ⇑(translatePath (i : ℂ) b)) ≤
              stoppedSupDist U (i : ℂ) z b :=
          cmpEDist_le_iSup_edist _ _
        calc cmpEDist (stopAtExit U ⇑(translatePath z b)) (stopAtExit U g)
            ≤ cmpEDist (stopAtExit U ⇑(translatePath z b))
                  (stopAtExit U ⇑(translatePath (i : ℂ) b)) +
                cmpEDist (stopAtExit U ⇑(translatePath (i : ℂ) b))
                  (stopAtExit U g) := cmpEDist_triangle _ _ _
          _ ≤ ENNReal.ofReal ε' + ENNReal.ofReal (2 * ε') := by
              refine add_le_add (h4.trans (not_le.1 hs).le) ?_
              rw [cmpEDist_comm]
              exact h3
          _ = ENNReal.ofReal (3 * ε') := by
              rw [← ENNReal.ofReal_add hε'0.le (by linarith)]
              congr 1
              ring
          _ < ENNReal.ofReal ε := by
              rw [ENNReal.ofReal_lt_ofReal_iff hε]
              linarith
    · exact Or.inl (Or.inr hgood)
  have hT2 : planarBrownianMotion 0
      {b | ¬ (GoodStopN U (N i) ε' ⇑(translatePath (i : ℂ) b) ∧
        translatePath (i : ℂ) b 0 = (i : ℂ))} ≤ ENNReal.ofReal θ' := by
    have h := (hNθ i hcK).le
    rw [planarBrownianMotion_apply_eq_translatePath (i : ℂ)] at h
    exact h
  rw [planarBrownianMotion_apply_eq_translatePath z, planarBrownianMotion_apply_eq_translatePath z]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ planarBrownianMotion 0 (translatePath z ⁻¹' {b : ContinuousPath ℂ | ∃ f ∈ A,
          cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal ε}) +
          ENNReal.ofReal θ' + ENNReal.ofReal θ' :=
        add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl hT2)) (hssd _ hcK z hzcδ₁)
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add hθ'0.le hθ'0.le, hθ', add_halves]

/-- **Transfer of one-sided Lévy–Prokhorov bounds at variable radii, for an open set with regular exit.** Under the
hypotheses of `exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le_of_regularExit`, for all
`ε, θ > 0` there is `δ > 0` such that for every start `z ∈ K` and every random continuous path `W` under a measure
`ν`: if, for every set `S` of paths, `ν(W ∈ S)` is at most `δ` plus the probability under planar Brownian motion from
`z` that some `g ∈ S` is at `cmpEDist`-distance less than `δ` from `b` after both are stopped at their exit times
from some disc `B_r(0)` with `r > R + κ`, then for every set `A` of paths,
`ν(stopAtExit U W ∈ A) ≤ P_z(stopAtExit U b is at distance < ε from A) + θ`. -/
theorem exists_forall_stopAtExit_le_of_forall_le_variable_of_regularExit {Ω' : Type*} [MeasurableSpace Ω']
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {R κ : ℝ} (hUR : U ⊆ ball (0 : ℂ) R)
    (hκ : 0 < κ)
    (hreg : ∀ c ∈ K, ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion c,
      pathExitTime U ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U ⇑b)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ K, ∀ (ν : Measure Ω') (W : Ω' → ℝ≥0 → ℂ), (∀ w, Continuous (W w)) →
      (∀ S : Set (ℝ≥0 → ℂ), ν {w | W w ∈ S} ≤
        planarBrownianMotion z {b | ∃ g ∈ S, ∃ r : ℝ, R + κ < r ∧
          cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} +
          ENNReal.ofReal δ) →
      ∀ A : Set (ℝ≥0 → ℂ), ν {w | stopAtExit U (W w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  obtain ⟨δ₀, hδ₀, h⟩ :=
    exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le_of_regularExit hU hK hKU hUR hκ hreg hε
      (half_pos hθ)
  refine ⟨min δ₀ (θ / 2), lt_min hδ₀ (half_pos hθ), fun z hz ν W hWc hW A => ?_⟩
  have hS := hW {g | Continuous g ∧ stopAtExit U g ∈ A}
  have hWS : {w | stopAtExit U (W w) ∈ A} ⊆
      {w | W w ∈ {g | Continuous g ∧ stopAtExit U g ∈ A}} :=
    fun w hw => ⟨hWc w, hw⟩
  have hsub : {b : ContinuousPath ℂ | ∃ g ∈ {g : ℝ≥0 → ℂ | Continuous g ∧ stopAtExit U g ∈ A},
        ∃ r : ℝ, R + κ < r ∧ cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) <
          ENNReal.ofReal (min δ₀ (θ / 2))} ⊆
      {b | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit U g ∈ A ∧ ∃ r : ℝ, R + κ < r ∧
        cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ₀} := by
    intro b hb
    obtain ⟨g, ⟨hgc, hgA⟩, r, hr, hlt⟩ := hb
    exact ⟨g, hgc, hgA, r, hr, hlt.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
  calc ν {w | stopAtExit U (W w) ∈ A}
      ≤ _ := measure_mono hWS
    _ ≤ _ := hS
    _ ≤ planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit U g ∈ A ∧ ∃ r : ℝ, R + κ < r ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) <
              ENNReal.ofReal δ₀} + ENNReal.ofReal (θ / 2) :=
        add_le_add (measure_mono hsub) (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    _ ≤ planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit U ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        add_le_add (h z hz A) le_rfl
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add (half_pos hθ).le (half_pos hθ).le, add_halves]

/-- The starts `closedBall 0 ρ \ B_b(0)` lie in the annulus `B_R(0) \ closedBall 0 α` for `α < b` and `ρ < R`. -/
theorem annulusStarts_subset {α b ρ R : ℝ} (hαb : α < b) (hρR : ρ < R) :
    closedBall (0 : ℂ) ρ \ ball 0 b ⊆ ball (0 : ℂ) R \ closedBall 0 α := by
  intro z hz
  have h1 : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.1 hz.1
  have h2 : b ≤ ‖z‖ := not_lt.1 fun h => hz.2 (mem_ball_zero_iff.2 h)
  exact ⟨mem_ball_zero_iff.2 (by linarith), fun h => by linarith [mem_closedBall_zero_iff.1 h]⟩

/-- **Transfer of one-sided Lévy–Prokhorov bounds at variable radii to the exit of an annulus.** Let
`0 < α < b`, `ρ < R` and `κ > 0`. For all `ε, θ > 0` there is `δ > 0` such that for every start
`z ∈ closedBall 0 ρ \ B_b(0)` and every random continuous path `W` whose law is, in the one-sided sense at variable
radii `r > R + κ`, within `δ` of planar Brownian motion from `z`, the path `W` stopped at its exit from the annulus
`B_R(0) \ closedBall 0 α` satisfies the one-sided bound with `ε, θ` against Brownian motion stopped at the same exit. -/
theorem exists_forall_stopAtExit_le_of_forall_le_variable_annulus {Ω' : Type*} [MeasurableSpace Ω']
    {α b ρ R κ : ℝ} (hα : 0 < α) (hαb : α < b) (hbρ : b < ρ) (hρR : ρ < R) (hκ : 0 < κ) {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ \ ball 0 b, ∀ (ν : Measure Ω') (W : Ω' → ℝ≥0 → ℂ),
      (∀ w, Continuous (W w)) →
      (∀ S : Set (ℝ≥0 → ℂ), ν {w | W w ∈ S} ≤
        planarBrownianMotion z {b | ∃ g ∈ S, ∃ r : ℝ, R + κ < r ∧
          cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} +
          ENNReal.ofReal δ) →
      ∀ A : Set (ℝ≥0 → ℂ), ν {w | stopAtExit (ball (0 : ℂ) R \ closedBall 0 α) (W w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R \ closedBall 0 α) ⇑b) f <
              ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  have hKU := annulusStarts_subset hαb hρR
  have hαR : α < R := by linarith
  exact exists_forall_stopAtExit_le_of_forall_le_variable_of_regularExit (isOpen_annulus α R)
    ((isCompact_closedBall (0 : ℂ) ρ).diff isOpen_ball) hKU sdiff_subset hκ
    (fun c hc => ae_regularExit_annulus_planarBrownian hα hαR (hKU hc)) hε hθ

end MatedCRT.StopAtExitCmp
