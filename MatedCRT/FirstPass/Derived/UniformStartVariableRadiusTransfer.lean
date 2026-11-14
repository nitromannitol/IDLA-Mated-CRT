import MatedCRT.FirstPass.Derived.StopAtExitVariableRadius

/-!
# Uniform transfer to stopped paths from closeness at a variable larger radius

Let `ρ < R` and `κ > 0`. For planar Brownian motion `b` started at `z ∈ closedBall 0 ρ`, closeness of a continuous
path `g` to `b` after both are stopped at their exit times from SOME disc `B_r(0)` with `r > R + κ` (the radius may
depend on `g` and `b`) controls the paths stopped at their exit times from `B_R(0)`, uniformly in the start `z`:
for all `ε, θ > 0` there is `δ > 0` such that the probability that such a `g` within `cmpEDist`-distance `δ` has
`stopAtExit (ball 0 R) g ∈ A` is at most the probability that `stopAtExit (ball 0 R) b` is at distance less than `ε`
from `A`, plus `θ`.

This is the Brownian half of the passage from the local metric on curves modulo time parametrization
(Gwynne-Miller-Sheffield, arXiv:1705.11161, (2.2)), whose smallness gives closeness of the stopped curves only for
some radius of an interval, to the distance of the curves stopped at a fixed disc.

The proof follows `exists_forall_planarBrownianMotion_preimage_stopAtExit_le`: good exit events at finitely many
centres `c`, with `cmpEDist_stopAtExit_le_of_goodStopN_of_cthickening_subset` applied to `c + b` and the disc
`B_r(c - z)`, at whose exit `c + b` stops exactly when `z + b` stops at its exit from `B_r(0)`.

## Main statements
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_translatePath_le`: stopped translates at translated discs.
* `MatedCRT.StopAtExitCmp.exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le`: the uniform bound.
* `MatedCRT.StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le_variable`: transfer of one-sided Lévy-Prokhorov
  bounds stated at variable radii to the paths stopped at `B_R(0)`.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The translate `z + b`, stopped at its exit from `B_r(0)`, and the translate `c + b`, stopped at its exit from
`B_r(c - z)`, stop at the same time, so they are at uniform distance `|z - c|`. -/
theorem cmpEDist_stopAtExit_translatePath_le (b : ContinuousPath ℂ) (z c : ℂ) (r : ℝ) :
    cmpEDist (stopAtExit (ball (0 : ℂ) r) ⇑(translatePath z b))
      (stopAtExit (ball (c - z) r) ⇑(translatePath c b)) ≤ edist z c := by
  have hmem : ∀ t, (translatePath z b t ∈ ball (0 : ℂ) r ↔ translatePath c b t ∈ ball (c - z) r) := by
    intro t
    rw [translatePath_apply, translatePath_apply, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm]
    have h : b t + c - (c - z) = b t + z - 0 := by ring
    rw [h]
  have hE : pathExitTime (ball (0 : ℂ) r) ⇑(translatePath z b) =
      pathExitTime (ball (c - z) r) ⇑(translatePath c b) := by
    unfold pathExitTime
    simp only [hmem]
  refine (cmpEDist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  unfold stopAtExit
  rw [hE]
  simp only [translatePath_apply, edist_add_left, le_refl]

/-- **Uniform transfer from a variable larger radius.** Let `ρ < R` and `κ > 0`. For all `ε, θ > 0` there is
`δ > 0` such that for every start point `z ∈ closedBall 0 ρ` and every set `A` of paths, the probability under
planar Brownian motion from `z` that some continuous path `g` with `stopAtExit (ball 0 R) g ∈ A` is, for some radius
`r > R + κ`, at `cmpEDist`-distance less than `δ` from `b` after both are stopped at their exit times from
`B_r(0)`, is at most the probability that `stopAtExit (ball 0 R) b` is at distance less than `ε` from `A`, plus
`θ`. -/
theorem exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le {ρ R κ : ℝ} (hρR : ρ < R)
    (hκ : 0 < κ) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ A : Set (ℝ≥0 → ℂ),
      planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A ∧ ∃ r : ℝ, R + κ < r ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  have hKU : ∀ c ∈ closedBall (0 : ℂ) ρ, c ∈ ball (0 : ℂ) R := fun c hc =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hc) hρR)
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min (ε / 4) (κ / 2) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min (by linarith) (by linarith)
  have hε'ε : ε' ≤ ε / 4 := by rw [hε']; exact min_le_left _ _
  have hε'κ : ε' ≤ κ / 2 := by rw [hε']; exact min_le_right _ _
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = θ / 2 := ⟨_, rfl⟩
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  obtain ⟨δ₁, hδ₁, hssd⟩ := LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae
    (μ := planarBrownianMotion 0) (isCompact_closedBall (0 : ℂ) ρ)
    (F := stoppedSupDist (ball (0 : ℂ) R)) (stoppedSupDist_le_add (ball (0 : ℂ) R))
    (fun y z => (measurable_stoppedSupDist isOpen_ball y z).aemeasurable)
    (fun c hc u hu => ae_tendsto_stoppedSupDist_ball (hKU c hc) hu)
    (ENNReal.ofReal_pos.2 hε'0) (ENNReal.ofReal_pos.2 hθ'0)
  -- a good-event index at each centre, together with the start of the path
  have hN : ∀ c ∈ closedBall (0 : ℂ) ρ, ∃ N : ℕ, 1 ≤ N ∧
      planarBrownianMotion c {b | ¬ (GoodStopN (ball (0 : ℂ) R) N ε' ⇑b ∧ b 0 = c)} < ENNReal.ofReal θ' := by
    intro c hc
    obtain ⟨N, hN1, hNlt⟩ := ((eventually_ge_atTop 1).and
      ((tendsto_planarBrownianMotion_not_goodStopN_ball (hKU c hc) hε'0).eventually
        (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ'0)))).exists
    refine ⟨N, hN1, lt_of_le_of_lt ?_ hNlt⟩
    have h0 : planarBrownianMotion c {b | ¬ b 0 = c} = 0 := ae_iff.1 (ae_planarBrownianMotion_eval_zero c)
    calc planarBrownianMotion c {b | ¬ (GoodStopN (ball (0 : ℂ) R) N ε' ⇑b ∧ b 0 = c)}
        ≤ planarBrownianMotion c ({b | ¬ GoodStopN (ball (0 : ℂ) R) N ε' ⇑b} ∪ {b | ¬ b 0 = c}) :=
          measure_mono fun b hb => not_and_or.1 hb
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [h0, add_zero]
  choose! N hN1 hNθ using hN
  obtain ⟨r, hr⟩ : ∃ r : ℂ → ℝ, ∀ c, r c = min δ₁ (min ε' ((N c : ℝ)⁻¹)) / 2 := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ c ∈ closedBall (0 : ℂ) ρ, 0 < r c := by
    intro c hc
    rw [hr c]
    exact half_pos (lt_min hδ₁ (lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 c hc)))))
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) ρ).elim_finite_subcover
    (fun c : closedBall (0 : ℂ) ρ => ball (c : ℂ) (r c)) (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr0 z hz)⟩)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i ∈ t, δ < r i :=
    ((Filter.eventually_all_finset t).2 fun i _ => gt_mem_nhds (hr0 i i.2)).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨δ, hδr, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : 0 < δ := hδ0
  refine ⟨δ, hδ0', fun z hz A => ?_⟩
  obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.1 (ht hz)
  have hcK : (i : ℂ) ∈ closedBall (0 : ℂ) ρ := i.2
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
        {b : ContinuousPath ℂ | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A ∧
          ∃ r : ℝ, R + κ < r ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} ⊆
      (translatePath z ⁻¹' {b : ContinuousPath ℂ | ∃ f ∈ A,
          cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} ∪
        {b | ¬ (GoodStopN (ball (0 : ℂ) R) (N i) ε' ⇑(translatePath (i : ℂ) b) ∧
          translatePath (i : ℂ) b 0 = (i : ℂ))}) ∪
        {b | ENNReal.ofReal ε' ≤ stoppedSupDist (ball (0 : ℂ) R) (i : ℂ) z b} := by
    intro b hb
    obtain ⟨g, hgc, hgA, r', hr', hg⟩ := hb
    by_cases hgood : GoodStopN (ball (0 : ℂ) R) (N i) ε' ⇑(translatePath (i : ℂ) b) ∧
        translatePath (i : ℂ) b 0 = (i : ℂ)
    · by_cases hs : ENNReal.ofReal ε' ≤ stoppedSupDist (ball (0 : ℂ) R) (i : ℂ) z b
      · exact Or.inr hs
      · refine Or.inl (Or.inl ⟨stopAtExit (ball (0 : ℂ) R) g, hgA, ?_⟩)
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
        have hR : 0 < R := pos_of_mem_ball (hKU _ hcK)
        have hUV : cthickening ε' (ball (0 : ℂ) R) ⊆ ball ((i : ℂ) - z) r' := by
          rw [cthickening_ball hε'0.le hR]
          refine closedBall_subset_ball' ?_
          have hd : dist (0 : ℂ) ((i : ℂ) - z) = dist z (i : ℂ) := by
            rw [dist_comm, dist_zero_right, ← dist_eq_norm, dist_comm]
          rw [hd]
          linarith
        have h0 : translatePath (i : ℂ) b 0 ∈ ball (0 : ℂ) R := by
          rw [hgood.2]
          exact hKU _ hcK
        have h3 := cmpEDist_stopAtExit_le_of_goodStopN_of_cthickening_subset isOpen_ball
          (translatePath (i : ℂ) b).continuous h0 hUV hgood.1 h2
        rw [stopAtExit_stopAtExit_of_subset isOpen_ball (ball_subset_ball (by linarith)) hgc] at h3
        have h4 : cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath z b))
            (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath (i : ℂ) b)) ≤
              stoppedSupDist (ball (0 : ℂ) R) (i : ℂ) z b :=
          cmpEDist_le_iSup_edist _ _
        calc cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath z b)) (stopAtExit (ball (0 : ℂ) R) g)
            ≤ cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath z b))
                  (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath (i : ℂ) b)) +
                cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑(translatePath (i : ℂ) b))
                  (stopAtExit (ball (0 : ℂ) R) g) := cmpEDist_triangle _ _ _
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
      {b | ¬ (GoodStopN (ball (0 : ℂ) R) (N i) ε' ⇑(translatePath (i : ℂ) b) ∧
        translatePath (i : ℂ) b 0 = (i : ℂ))} ≤ ENNReal.ofReal θ' := by
    have h := (hNθ i hcK).le
    rw [planarBrownianMotion_apply_eq_translatePath (i : ℂ)] at h
    exact h
  rw [planarBrownianMotion_apply_eq_translatePath z, planarBrownianMotion_apply_eq_translatePath z]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ planarBrownianMotion 0 (translatePath z ⁻¹' {b : ContinuousPath ℂ | ∃ f ∈ A,
          cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε}) +
          ENNReal.ofReal θ' + ENNReal.ofReal θ' :=
        add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl hT2)) (hssd _ hcK z hzcδ₁)
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add hθ'0.le hθ'0.le, hθ', add_halves]

/-- **Transfer of one-sided Lévy-Prokhorov bounds at variable radii.** Let `ρ < R`, `κ > 0` and `ε, θ > 0`. There
is `δ > 0` such that for every start point `z ∈ closedBall 0 ρ` and every random continuous path `W` under a
measure `ν`: if, for every set `S` of paths, `ν(W ∈ S)` is at most `δ` plus the probability under planar Brownian
motion from `z` that some `g ∈ S` is at `cmpEDist`-distance less than `δ` from `b` after both are stopped at their
exit times from some disc `B_r(0)` with `r > R + κ`, then for every set `A` of paths,
`ν(stopAtExit (ball 0 R) W ∈ A) ≤ P_z(stopAtExit (ball 0 R) b is at distance < ε from A) + θ`. -/
theorem exists_forall_stopAtExit_le_of_forall_le_variable {Ω' : Type*} [MeasurableSpace Ω'] {ρ R κ : ℝ}
    (hρR : ρ < R) (hκ : 0 < κ) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ (ν : Measure Ω') (W : Ω' → ℝ≥0 → ℂ), (∀ w, Continuous (W w)) →
      (∀ S : Set (ℝ≥0 → ℂ), ν {w | W w ∈ S} ≤
        planarBrownianMotion z {b | ∃ g ∈ S, ∃ r : ℝ, R + κ < r ∧
          cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ} +
          ENNReal.ofReal δ) →
      ∀ A : Set (ℝ≥0 → ℂ), ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  obtain ⟨δ₀, hδ₀, h⟩ :=
    exists_forall_planarBrownianMotion_preimage_stopAtExit_variable_le hρR hκ hε (half_pos hθ)
  refine ⟨min δ₀ (θ / 2), lt_min hδ₀ (half_pos hθ), fun z hz ν W hWc hW A => ?_⟩
  have hS := hW {g | Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A}
  have hWS : {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A} ⊆
      {w | W w ∈ {g | Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A}} :=
    fun w hw => ⟨hWc w, hw⟩
  have hsub : {b : ContinuousPath ℂ | ∃ g ∈ {g : ℝ≥0 → ℂ | Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A},
        ∃ r : ℝ, R + κ < r ∧ cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) <
          ENNReal.ofReal (min δ₀ (θ / 2))} ⊆
      {b | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A ∧ ∃ r : ℝ, R + κ < r ∧
        cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) < ENNReal.ofReal δ₀} := by
    intro b hb
    obtain ⟨g, ⟨hgc, hgA⟩, r, hr, hlt⟩ := hb
    exact ⟨g, hgc, hgA, r, hr, hlt.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
  calc ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A}
      ≤ _ := measure_mono hWS
    _ ≤ _ := hS
    _ ≤ planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, Continuous g ∧ stopAtExit (ball (0 : ℂ) R) g ∈ A ∧ ∃ r : ℝ, R + κ < r ∧
            cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) ⇑b) <
              ENNReal.ofReal δ₀} + ENNReal.ofReal (θ / 2) :=
        add_le_add (measure_mono hsub) (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    _ ≤ planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        add_le_add (h z hz A) le_rfl
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add (half_pos hθ).le (half_pos hθ).le, add_halves]

end MatedCRT.StopAtExitCmp
