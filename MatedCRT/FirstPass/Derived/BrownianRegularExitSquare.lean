import MatedCRT.FirstPass.Derived.BrownianRegularExitBall

/-!
# Regular exit of planar Brownian motion from sets with exterior half-planes, and from squares

Let `U ⊆ ℂ` be a bounded open set carrying a measurable *exterior normal field*: at every frontier point `p` of `U`
a nonzero vector `v p` such that the open half-plane `{q | ⟪v p, q - p⟫ > 0}` does not meet the closure of `U`.
Planar Brownian motion started at a point of `U` then leaves `U` at a finite time almost surely, and it exits
regularly (`MatedCRT.TruncatedLaws.RegularExit`): right after its exit time it visits the complement of the closure
of `U` at arbitrarily small positive times. The proof is the one for discs (`BrownianRegularExitBall.lean`) with the
radial direction replaced by `v`: by the strong Markov property at the exit time
(`MatedCRT.ExitRestart.exit_restart_planar`) the post-exit increments form a planar Brownian motion independent of
the exit point, hence of `v` at the exit point, and Blumenthal's zero-one law gives a positive pairing with
`v (B_τ)` at arbitrarily small times (`LatticeProb.PlanarBrownian.ae_frequently_pos_of_indepFun`; Mörters–Peres,
*Brownian Motion*, Theorems 2.7 and 2.16).

Open axis-parallel squares `{z | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}` carry such a field (the outward
normal of a side containing the frontier point). This is the Brownian half of condition 1 in the proof of
Lemma 3.14 of Gwynne–Miller–Sheffield, *An invariance principle for ergodic scale-free random environments*
(arXiv 1807.07515): the exit point of the stopped path from a square is a continuous function of the path at almost
every Brownian path.

## Main statements

* `MatedCRT.StopAtExitCmp.ae_regularExit_planarBrownian_of_exteriorNormal`: the general statement.
* `MatedCRT.StopAtExitCmp.ae_regularExit_openSquare_planarBrownian`: open squares.
* `MatedCRT.StopAtExitCmp.ae_cmpEDist_stopAtExit_openSquare_planarBrownian`: almost surely the stopping map at the
  exit of an open square is `cmpEDist`-continuous at the Brownian path.
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal InnerProductSpace

namespace MatedCRT.StopAtExitCmp

/-- **Regular exit from a set with exterior half-planes.** Planar Brownian motion started at a point of a bounded
open set `U` with a measurable exterior normal field `v` almost surely leaves `U` at a finite time and exits it
regularly. -/
theorem ae_regularExit_planarBrownian_of_exteriorNormal {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {v : ℂ → ℂ} (hv : Measurable v)
    (hvU : ∀ p ∈ frontier U, v p ≠ 0 ∧ ∀ q : ℂ, 0 < ⟪v p, q - p⟫_ℝ → q ∉ closure U)
    {x : ℂ} (hx : x ∈ U) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x,
      pathExitTime U ⇑b ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U ⇑b := by
  have hfin : ∀ᵐ b ∂planarBrownianMotion x, ContinuousPath.exitTime U b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top x hUb).mono fun _ hb => hb.ne
  obtain ⟨hW, hind, hBτ⟩ := ExitRestart.exit_restart_planar hU x hfin
  have hBlum := fun A hA =>
    LatticeProb.PlanarBrownian.isTrivialSigma_iInf_pathSigmaTo_planar hW
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.re fun t => Complex.measurable_re.comp (hW.measurable t))
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.im fun t => Complex.measurable_im.comp (hW.measurable t)) A hA
  have hfr : ∀ᵐ b ∂planarBrownianMotion x, b (ExitRestart.exitNN U b) ∈ frontier U := by
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero x] with b hb hb0
    exact ContinuousPath.coordinate_exitTime_mem_frontier U hU b (hb0 ▸ hx) hb
  have hN0 : ∀ᵐ b ∂planarBrownianMotion x, v (b (ExitRestart.exitNN U b)) ≠ 0 :=
    hfr.mono fun b hb => (hvU _ hb).1
  have hfreq := LatticeProb.PlanarBrownian.ae_frequently_pos_of_indepFun hW hBlum
    (hv.comp_aemeasurable hBτ) (hind.comp hv measurable_id) hN0
  filter_upwards [hfreq, hfin, hfr] with b hb hbfin hbfr
  refine ⟨hbfin, Or.inr ?_⟩
  set τ : ℝ≥0 := ExitRestart.exitNN U b with hτ
  have hT : Tendsto (fun s : ℝ≥0 => τ + s) (𝓝[>] 0) (𝓝[>] τ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ≥0 => τ + s) (𝓝 0) (𝓝 (τ + 0)) :=
        tendsto_const_nhds.add tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact lt_add_of_pos_right _ (show (0 : ℝ≥0) < s from hs)
  have hout : ∃ᶠ s in 𝓝[>] (0 : ℝ≥0), b (τ + s) ∉ closure U :=
    hb.mono fun s hs => (hvU _ hbfr).2 _ (by rw [LatticeProb.PlanarBrownian.inner_eq_pairing]; exact hs)
  exact hT.frequently (p := fun t => b t ∉ closure U) hout

/-- The outward normal of an axis-parallel square with centre `c` at the point `p`: the horizontal displacement
`p.re - c.re` when it dominates, the vertical displacement `(p.im - c.im) i` otherwise. -/
noncomputable def squareNormal (c p : ℂ) : ℂ :=
  if |p.im - c.im| ≤ |p.re - c.re| then ((p.re - c.re : ℝ) : ℂ) else ((p.im - c.im : ℝ) : ℂ) * Complex.I

theorem measurable_squareNormal (c : ℂ) : Measurable (squareNormal c) := by
  unfold squareNormal
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

theorem isOpen_openSquare (c : ℂ) (a : ℝ) :
    IsOpen {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} :=
  show IsOpen ({z : ℂ | |z.re - c.re| < a / 2} ∩ {z : ℂ | |z.im - c.im| < a / 2}) from
  (isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop) continuous_const)

theorem isBounded_openSquare (c : ℂ) (a : ℝ) :
    Bornology.IsBounded {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} := by
  refine (isBounded_closedBall (x := c) (r := a)).subset fun z hz => ?_
  rw [mem_closedBall, dist_eq_norm]
  have h := Complex.norm_le_abs_re_add_abs_im (z - c)
  simp only [Complex.sub_re, Complex.sub_im] at h
  linarith [hz.1, hz.2]

/-- The closure of the open square lies in the closed square. -/
theorem closure_openSquare_subset (c : ℂ) (a : ℝ) :
    closure {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} ⊆
      {z : ℂ | |z.re - c.re| ≤ a / 2 ∧ |z.im - c.im| ≤ a / 2} :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (show IsClosed ({z : ℂ | |z.re - c.re| ≤ a / 2} ∩ {z : ℂ | |z.im - c.im| ≤ a / 2}) from
      (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const))

/-- If `|d| = h > 0` and `|u| ≤ h`, then `d * (u - d) ≤ 0`: a point of the closed slab has nonpositive pairing with
the outward displacement `d` of a frontier point. -/
private theorem not_pos_mul_sub_of_abs_le {d u h : ℝ} (hd : |d| = h) (hh : 0 < h) (hu : |u| ≤ h)
    (hpos : 0 < d * (u - d)) : False := by
  rcases (abs_eq hh.le).1 hd with hd' | hd' <;> rcases abs_le.1 hu with ⟨h1, h2⟩ <;> subst hd' <;> nlinarith

/-- **Regular exit from an open square.** Planar Brownian motion started in the open square of centre `c` and
side `a` almost surely leaves it at a finite time and exits it regularly. -/
theorem ae_regularExit_openSquare_planarBrownian {c x : ℂ} {a : ℝ}
    (hx : x ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x,
      pathExitTime {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} ⇑b ≠ ⊤ ∧
        MatedCRT.TruncatedLaws.RegularExit {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} ⇑b := by
  have ha : 0 < a / 2 := lt_of_le_of_lt (abs_nonneg _) hx.1
  refine ae_regularExit_planarBrownian_of_exteriorNormal (isOpen_openSquare c a) (isBounded_openSquare c a)
    (measurable_squareNormal c) (fun p hp => ?_) hx
  have hpS := closure_openSquare_subset c a (frontier_subset_closure hp)
  have hpU : p ∉ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} := by
    have := hp.2
    rwa [(isOpen_openSquare c a).interior_eq] at this
  have hmax : |p.im - c.im| ≤ |p.re - c.re| → |p.re - c.re| = a / 2 := fun hle => by
    by_contra hne
    exact hpU ⟨lt_of_le_of_ne hpS.1 hne, lt_of_le_of_lt hle (lt_of_le_of_ne hpS.1 hne)⟩
  have hmax' : ¬ |p.im - c.im| ≤ |p.re - c.re| → |p.im - c.im| = a / 2 := fun hle => by
    by_contra hne
    exact hpU ⟨lt_of_lt_of_le (not_le.1 hle) hpS.2, lt_of_le_of_ne hpS.2 hne⟩
  by_cases hle : |p.im - c.im| ≤ |p.re - c.re|
  · have hd := hmax hle
    have hv : squareNormal c p = ((p.re - c.re : ℝ) : ℂ) := by simp only [squareNormal, hle, ↓reduceIte]
    refine ⟨?_, fun q hq hqS => ?_⟩
    · rw [hv]
      intro h0
      rw [Complex.ofReal_eq_zero] at h0
      rw [h0, abs_zero] at hd
      exact ha.ne hd
    · have hqS' := closure_openSquare_subset c a hqS
      have e : LatticeProb.PlanarBrownian.pairing ((p.re - c.re : ℝ) : ℂ) (q - p) =
          (p.re - c.re) * ((q.re - c.re) - (p.re - c.re)) := by
        simp [LatticeProb.PlanarBrownian.pairing]
      rw [hv, LatticeProb.PlanarBrownian.inner_eq_pairing, e] at hq
      exact not_pos_mul_sub_of_abs_le hd ha hqS'.1 hq
  · have hd := hmax' hle
    have hv : squareNormal c p = ((p.im - c.im : ℝ) : ℂ) * Complex.I := by
      simp only [squareNormal, hle, ↓reduceIte]
    refine ⟨?_, fun q hq hqS => ?_⟩
    · rw [hv]
      intro h0
      rw [mul_eq_zero, Complex.ofReal_eq_zero] at h0
      rcases h0 with h0 | h0
      · rw [h0, abs_zero] at hd
        exact ha.ne hd
      · exact Complex.I_ne_zero h0
    · have hqS' := closure_openSquare_subset c a hqS
      have e : LatticeProb.PlanarBrownian.pairing (((p.im - c.im : ℝ) : ℂ) * Complex.I) (q - p) =
          (p.im - c.im) * ((q.im - c.im) - (p.im - c.im)) := by
        simp [LatticeProb.PlanarBrownian.pairing]
      rw [hv, LatticeProb.PlanarBrownian.inner_eq_pairing, e] at hq
      exact not_pos_mul_sub_of_abs_le hd ha hqS'.2 hq

/-- For almost every planar Brownian path `b` started in an open square, stopping at the exit time of the square
is continuous at `b` for the distance `cmpEDist` of curves modulo time parametrization. -/
theorem ae_cmpEDist_stopAtExit_openSquare_planarBrownian {c x : ℂ} {a : ℝ}
    (hx : x ∈ {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2}) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → ℂ,
      cmpEDist g ⇑b < ENNReal.ofReal δ →
        cmpEDist (stopAtExit {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} g)
          (stopAtExit {z : ℂ | |z.re - c.re| < a / 2 ∧ |z.im - c.im| < a / 2} ⇑b) < ENNReal.ofReal ε := by
  filter_upwards [ae_regularExit_openSquare_planarBrownian hx] with b hb ε hε
  exact cmpEDist_stopAtExit_lt_of_regularExit (isOpen_openSquare c a) b.continuous hb.1 hb.2 hε

end MatedCRT.StopAtExitCmp

/-! ## Audit -/

#print axioms MatedCRT.StopAtExitCmp.ae_regularExit_planarBrownian_of_exteriorNormal
#print axioms MatedCRT.StopAtExitCmp.ae_regularExit_openSquare_planarBrownian
#print axioms MatedCRT.StopAtExitCmp.ae_cmpEDist_stopAtExit_openSquare_planarBrownian
