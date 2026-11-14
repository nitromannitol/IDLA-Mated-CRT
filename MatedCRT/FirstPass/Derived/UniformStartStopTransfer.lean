import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import MatedCRT.FirstPass.Derived.StopAtExitGoodEventBM
import LatticeProb.Prob.UniformReparamComparison

/-!
# Uniform transfer of path bounds to planar Brownian motion stopped at the exit of a disc

Let `0 < ρ < R`, or more generally `ρ < R`. For all `ε, θ > 0` there is `δ > 0` such that for every start point
`z ∈ closedBall 0 ρ` and every set `A` of paths, the planar Brownian motion `b` from `z` is within
`cmpEDist`-distance `δ` of some path `g` with `stopAtExit (ball 0 R) g ∈ A` with probability at most `θ` plus the
probability that `stopAtExit (ball 0 R) b` is within distance `ε` of `A`. Consequently, a one-sided Lévy–Prokhorov
bound at level `δ` between an arbitrary random path `W` and planar Brownian motion from `z`, for curves modulo time
parametrization, gives the one-sided bound at level `(ε, θ)` between the two paths stopped at their exit times from
`B_R(0)`, uniformly in the start point `z ∈ closedBall 0 ρ`.

The stopping map is not continuous, but it is continuous at almost every Brownian path; the uniformity in the start
point comes from three ingredients:
* the quantitative good event `GoodStopN` (a path in it moves by at most `2ε` under stopping, for every path at
  distance less than `min ε (1/N)` from it), whose probability tends to `1` under planar Brownian motion from a fixed
  point of the disc;
* the uniform distance `stoppedSupDist` of the stopped translates of one Brownian path, which is uniformly small in
  measure for nearby start points (`LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae`);
* a finite cover of the compact disc `closedBall 0 ρ` by discs whose radii are adapted to the good-event index of
  their centres.

This is the step from the unstopped (or stopped at a larger domain) form of the invariance principle to the form
stopped at the exit of `B_R(0)` used in `MatedCRT.GMS21UniformStartInput`.

## Main statements
* `MatedCRT.StopAtExitCmp.cmpEDist_translatePath_le`: translates by `z` and `c` are at distance at most `|z - c|`.
* `MatedCRT.StopAtExitCmp.exists_forall_planarBrownianMotion_preimage_stopAtExit_le`: the uniform transfer.
* `MatedCRT.StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le`: the transfer of one-sided Lévy–Prokhorov
  bounds from a random path to the stopped paths.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The triangle inequality of `cmpEDist` (it is the library's `reparamEDist`). -/
theorem cmpEDist_triangle (f g h : ℝ≥0 → ℂ) : cmpEDist f h ≤ cmpEDist f g + cmpEDist g h :=
  LatticeProb.ReparamEDist.reparamEDist_triangle f g h

/-- `cmpEDist` is symmetric. -/
theorem cmpEDist_comm (f g : ℝ≥0 → ℂ) : cmpEDist f g = cmpEDist g f :=
  LatticeProb.ReparamEDist.reparamEDist_comm f g

/-- `cmpEDist` is at most the uniform distance. -/
theorem cmpEDist_le_iSup_edist (f g : ℝ≥0 → ℂ) : cmpEDist f g ≤ ⨆ t, edist (f t) (g t) :=
  LatticeProb.ReparamEDist.reparamEDist_le_iSup_edist f g

/-- The translates by `z` and by `c` of one path are at `cmpEDist`-distance at most `|z - c|`. -/
theorem cmpEDist_translatePath_le (b : ContinuousPath ℂ) (z c : ℂ) :
    cmpEDist ⇑(translatePath z b) ⇑(translatePath c b) ≤ edist z c := by
  refine (cmpEDist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  simp only [translatePath_apply, edist_add_left, le_refl]

/-- **Uniform transfer to the stopped path.** Let `ρ < R`. For all `ε, θ > 0` there is `δ > 0` such that for every
start point `z ∈ closedBall 0 ρ` and every set `A` of paths, the probability under planar Brownian motion from `z`
that `b` is at `cmpEDist`-distance less than `δ` from a path `g` whose path stopped at its exit time from `B_R(0)`
lies in `A` is at most the probability that `stopAtExit (ball 0 R) b` is at distance less than `ε` from `A`, plus
`θ`. -/
theorem exists_forall_planarBrownianMotion_preimage_stopAtExit_le {ρ R : ℝ} (hρR : ρ < R) {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ A : Set (ℝ≥0 → ℂ),
      planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧ cmpEDist ⇑b g < ENNReal.ofReal δ} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  have hKU : ∀ c ∈ closedBall (0 : ℂ) ρ, c ∈ ball (0 : ℂ) R := fun c hc =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hc) hρR)
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / 4 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = θ / 2 := ⟨_, rfl⟩
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  -- the stopped uniform distance is uniformly small in measure for nearby start points
  obtain ⟨δ₁, hδ₁, hssd⟩ := LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae
    (μ := planarBrownianMotion 0) (isCompact_closedBall (0 : ℂ) ρ)
    (F := stoppedSupDist (ball (0 : ℂ) R)) (stoppedSupDist_le_add (ball (0 : ℂ) R))
    (fun y z => (measurable_stoppedSupDist isOpen_ball y z).aemeasurable)
    (fun c hc u hu => ae_tendsto_stoppedSupDist_ball (hKU c hc) hu)
    (ENNReal.ofReal_pos.2 hε'0) (ENNReal.ofReal_pos.2 hθ'0)
  -- a good-event index at each centre
  have hN : ∀ c ∈ closedBall (0 : ℂ) ρ, ∃ N : ℕ, 1 ≤ N ∧
      planarBrownianMotion c {b | ¬ GoodStopN (ball (0 : ℂ) R) N ε' ⇑b} < ENNReal.ofReal θ' := by
    intro c hc
    exact ((eventually_ge_atTop 1).and
      ((tendsto_planarBrownianMotion_not_goodStopN_ball (hKU c hc) hε'0).eventually
        (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ'0)))).exists
  choose! N hN1 hNθ using hN
  obtain ⟨r, hr⟩ : ∃ r : ℂ → ℝ, ∀ c, r c = min δ₁ (min ε' ((N c : ℝ)⁻¹)) / 2 := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ c ∈ closedBall (0 : ℂ) ρ, 0 < r c := by
    intro c hc
    rw [hr c]
    exact half_pos (lt_min hδ₁ (lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 c hc)))))
  -- a finite cover of the compact disc by discs with adapted radii
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
  have hzcδ₁ : dist z (i : ℂ) < δ₁ := by linarith [hzc, hrc, hm1]
  have hsum : δ + dist z (i : ℂ) < min ε' ((N i : ℝ)⁻¹) := by linarith [hzc, hδc, hrc, hm2]
  have hmin0 : 0 < min ε' ((N i : ℝ)⁻¹) := lt_min hε'0 (inv_pos.2 (Nat.cast_pos.2 (hN1 i hcK)))
  -- the bad set lies in the good set, the failure of the good event at the centre, or a large stopped distance
  have hsub : translatePath z ⁻¹'
        {b : ContinuousPath ℂ | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧
          cmpEDist ⇑b g < ENNReal.ofReal δ} ⊆
      (translatePath z ⁻¹' {b : ContinuousPath ℂ | ∃ f ∈ A,
          cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} ∪
        {b | ¬ GoodStopN (ball (0 : ℂ) R) (N i) ε' ⇑(translatePath (i : ℂ) b)}) ∪
        {b | ENNReal.ofReal ε' ≤ stoppedSupDist (ball (0 : ℂ) R) (i : ℂ) z b} := by
    intro b hb
    obtain ⟨g, hgA, hg⟩ := hb
    by_cases hgood : GoodStopN (ball (0 : ℂ) R) (N i) ε' ⇑(translatePath (i : ℂ) b)
    · by_cases hs : ENNReal.ofReal ε' ≤ stoppedSupDist (ball (0 : ℂ) R) (i : ℂ) z b
      · exact Or.inr hs
      · refine Or.inl (Or.inl ⟨stopAtExit (ball (0 : ℂ) R) g, hgA, ?_⟩)
        have h2 : cmpEDist g ⇑(translatePath (i : ℂ) b) < ENNReal.ofReal (min ε' ((N i : ℝ)⁻¹)) := by
          calc cmpEDist g ⇑(translatePath (i : ℂ) b)
              ≤ cmpEDist g ⇑(translatePath z b) +
                  cmpEDist ⇑(translatePath z b) ⇑(translatePath (i : ℂ) b) := cmpEDist_triangle _ _ _
            _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (dist z (i : ℂ)) := by
                refine add_le_add ?_ ((cmpEDist_translatePath_le b z (i : ℂ)).trans (edist_dist _ _).le)
                rw [cmpEDist_comm]
                exact hg.le
            _ = ENNReal.ofReal (δ + dist z (i : ℂ)) := (ENNReal.ofReal_add hδ0'.le dist_nonneg).symm
            _ < ENNReal.ofReal (min ε' ((N i : ℝ)⁻¹)) := (ENNReal.ofReal_lt_ofReal_iff hmin0).2 hsum
        have h3 := cmpEDist_stopAtExit_le_of_goodStopN (translatePath (i : ℂ) b).continuous hgood h2
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
              rw [ENNReal.ofReal_lt_ofReal_iff hε, hε']
              linarith
    · exact Or.inl (Or.inr hgood)
  have hT2 : planarBrownianMotion 0
      {b | ¬ GoodStopN (ball (0 : ℂ) R) (N i) ε' ⇑(translatePath (i : ℂ) b)} ≤ ENNReal.ofReal θ' := by
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

/-- **Transfer of one-sided Lévy–Prokhorov bounds to the stopped paths.** Let `ρ < R` and `ε, θ > 0`. There is
`δ > 0` such that for every start point `z ∈ closedBall 0 ρ` and every random path `W` under a measure `ν`: if
`ν(W ∈ S) ≤ P_z(b is at cmpEDist-distance < δ from S) + δ` for every set `S` of paths, then for every set `A` of
paths, `ν(stopAtExit (ball 0 R) W ∈ A) ≤ P_z(stopAtExit (ball 0 R) b is at distance < ε from A) + θ`. -/
theorem exists_forall_stopAtExit_le_of_forall_le {Ω' : Type*} [MeasurableSpace Ω'] {ρ R : ℝ} (hρR : ρ < R)
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ (ν : Measure Ω') (W : Ω' → ℝ≥0 → ℂ),
      (∀ S : Set (ℝ≥0 → ℂ), ν {w | W w ∈ S} ≤
        planarBrownianMotion z {b | ∃ g ∈ S, cmpEDist ⇑b g < ENNReal.ofReal δ} + ENNReal.ofReal δ) →
      ∀ A : Set (ℝ≥0 → ℂ), ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A} ≤
        planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_forall_planarBrownianMotion_preimage_stopAtExit_le hρR hε (half_pos hθ)
  refine ⟨min δ₀ (θ / 2), lt_min hδ₀ (half_pos hθ), fun z hz ν W hW A => ?_⟩
  have hS := hW (stopAtExit (ball (0 : ℂ) R) ⁻¹' A)
  have hsub : {b : ContinuousPath ℂ | ∃ g ∈ stopAtExit (ball (0 : ℂ) R) ⁻¹' A,
        cmpEDist ⇑b g < ENNReal.ofReal (min δ₀ (θ / 2))} ⊆
      {b | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧ cmpEDist ⇑b g < ENNReal.ofReal δ₀} := by
    intro b hb
    obtain ⟨g, hgA, hlt⟩ := hb
    exact ⟨g, hgA, hlt.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
  calc ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A}
      ≤ _ := hS
    _ ≤ planarBrownianMotion z
          {b | ∃ g : ℝ≥0 → ℂ, stopAtExit (ball (0 : ℂ) R) g ∈ A ∧ cmpEDist ⇑b g < ENNReal.ofReal δ₀} +
          ENNReal.ofReal (θ / 2) :=
        add_le_add (measure_mono hsub) (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    _ ≤ planarBrownianMotion z
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        add_le_add (h z hz A) le_rfl
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add (half_pos hθ).le (half_pos hθ).le, add_halves]

end MatedCRT.StopAtExitCmp
