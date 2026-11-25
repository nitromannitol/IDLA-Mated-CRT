import MatedCRT.FirstPass.Derived.KilledOccupationEnergy
import MatedCRT.FirstPass.Derived.LQGClockApproxAdapted

/-!
# A maximal inequality for occupation functionals of killed planar Brownian motion

For an open set `D` and Borel rates `f, g ≥ 0`, let `A^f_t = ∫_0^{t ∧ τ_D} f(B_s) ds` be the occupation functional
of planar Brownian motion killed on exiting `D`, read at the time `t` (`killedOccupationUpTo`). If the potentials
`u_f, u_g` are at most `M < ∞` and differ by at most `δ` on `D`, then for every start `w ∈ D`, every `η > 0` and every
increasing finite family of times `t_0 ≤ … ≤ t_N`,

`η² P_w(max_{j ≤ N} |A^f_{t_j} - A^g_{t_j}| ≥ η) ≤ 32 δ M`

(`mul_measure_exists_le_abs_killedOccupationGapUpTo_le`), and the same bound holds for all dyadic times at once
(`mul_measure_iUnion_dyadic_le_abs_killedOccupationGapUpTo_le`) and for all times at once
(`mul_measure_exists_lt_abs_killedOccupationGapUpTo_le`, by left-continuity of the finite functionals in `t`).

The proof is the first-entrance argument for additive functionals: on the event that the grid value `|A^f - A^g|`
first reaches `η` at the time `t_j` (an event of the canonical filtration at `t_j`, since the occupation functional
up to a time `t` only reads the path up to `t`), either the terminal gap `|A^f_{τ_D} - A^g_{τ_D}|` is at least `η/2`,
or the gap of the remaining functionals after `t_j` is at least `η/2`. The first event is controlled by Chebyshev's
inequality and the energy estimate `E_w[(A^f - A^g)²] ≤ 2 δ (u_f(w) + u_g(w))`
(`lintegral_sq_killedOccupation_sub_le`); the second by the simple Markov property of planar Brownian motion at the
fixed time `t_j` (`setLIntegral_shift_planarBrownianMotion`) and the same estimate from the start `B_{t_j} ∈ D`.
This is the maximal inequality behind the identification of a time change of killed Brownian motion through the
potential of its Revuz measure (Fukushima–Oshima–Takeda (2011), §5.1; Berestycki (2015), Theorem 1.3).
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MatedCRT

open MarkovProcess HarmonicBalls

/-! ### The occupation functional up to a time -/

/-- The occupation functional `A^f_t = ∫_0^{t ∧ τ_D(b)} f(b_s) ds` of the path `b` killed at its exit from `D`, read
at the time `t`. -/
noncomputable def killedOccupationUpTo (D : Set ℂ) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, (Iic t).indicator (killedRate D f b) s

/-- The gap `A^f_{τ_D} - A^g_{τ_D}` of two occupation functionals of the killed path (real parts). -/
noncomputable def killedOccupationGap (D : Set ℂ) (f g : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ :=
  (killedOccupation D f b).toReal - (killedOccupation D g b).toReal

/-- The gap `A^f_t - A^g_t` of two occupation functionals of the killed path at the time `t` (real parts). -/
noncomputable def killedOccupationGapUpTo (D : Set ℂ) (f g : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (t : ℝ) : ℝ :=
  (killedOccupationUpTo D f b t).toReal - (killedOccupationUpTo D g b t).toReal

variable {D : Set ℂ}

/-- The occupation functional splits at the time `t` into the part up to `t` and the tail after `t`. -/
theorem killedOccupationUpTo_add_killedTail (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (t : ℝ) :
    killedOccupationUpTo D f b t + killedTail D f b t = killedOccupation D f b := by
  unfold killedOccupationUpTo killedTail killedOccupation
  rw [lintegral_indicator measurableSet_Iic, lintegral_indicator measurableSet_Ioi, ← compl_Iic]
  exact lintegral_add_compl _ measurableSet_Iic

/-- After the exit time nothing more is collected: the tail after a time `t ≥ τ_D(b)` vanishes. -/
theorem killedTail_eq_zero_of_exitTime_le (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) {t : ℝ}
    (h : ContinuousPath.exitTime D b ≤ ENNReal.ofReal t) : killedTail D f b t = 0 := by
  have hz : ∀ r, (Ioi t).indicator (killedRate D f b) r = 0 := by
    intro r
    by_cases hr : r ∈ Ioi t
    · rw [Set.indicator_of_mem hr, killedRate, Set.indicator_of_notMem]
      exact fun hk => absurd hk.2 (not_lt.2 (h.trans (ENNReal.ofReal_le_ofReal (mem_Ioi.1 hr).le)))
    · exact Set.indicator_of_notMem hr _
  unfold killedTail
  simp only [hz, lintegral_zero]

/-- From the exit time on, the occupation functional up to `t` is the whole occupation functional. -/
theorem killedOccupationUpTo_eq_of_exitTime_le (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) {t : ℝ}
    (h : ContinuousPath.exitTime D b ≤ ENNReal.ofReal t) :
    killedOccupationUpTo D f b t = killedOccupation D f b := by
  rw [← killedOccupationUpTo_add_killedTail (D := D) f b t, killedTail_eq_zero_of_exitTime_le f b h, add_zero]

/-- From the exit time on, the gap up to `t` is the terminal gap. -/
theorem killedOccupationGapUpTo_eq_of_exitTime_le (f g : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) {t : ℝ}
    (h : ContinuousPath.exitTime D b ≤ ENNReal.ofReal t) :
    killedOccupationGapUpTo D f g b t = killedOccupationGap D f g b := by
  unfold killedOccupationGapUpTo killedOccupationGap
  rw [killedOccupationUpTo_eq_of_exitTime_le f b h, killedOccupationUpTo_eq_of_exitTime_le g b h]

/-- **The terminal gap after a time `t` before the exit time** is the gap up to `t` plus the terminal gap of the path
shifted by `t`, when both occupation functionals are finite. -/
theorem killedOccupationGap_eq_add {f g : ℂ → ℝ≥0∞} {b : ContinuousPath ℂ}
    (hfb : killedOccupation D f b ≠ ⊤) (hgb : killedOccupation D g b ≠ ⊤) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ContinuousPath.exitTime D b) :
    killedOccupationGap D f g b =
      killedOccupationGapUpTo D f g b t + killedOccupationGap D f g (ContinuousPath.shift t b) := by
  have hsplit : ∀ h : ℂ → ℝ≥0∞, killedOccupation D h b ≠ ⊤ →
      (killedOccupation D h b).toReal =
        (killedOccupationUpTo D h b t).toReal + (killedOccupation D h (ContinuousPath.shift t b)).toReal := by
    intro h hh
    have ht' : ENNReal.ofReal (t : ℝ) < ContinuousPath.exitTime D b := by
      rwa [ENNReal.ofReal_coe_nnreal]
    have htail := killedTail_eq_killedOccupation_shift h b (NNReal.coe_nonneg t) ht'
    rw [Real.toNNReal_coe] at htail
    rw [← killedOccupationUpTo_add_killedTail (D := D) h b t] at hh ⊢
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.1 hh).1 (ENNReal.add_ne_top.1 hh).2, htail]
  unfold killedOccupationGap killedOccupationGapUpTo
  rw [hsplit f hfb, hsplit g hgb]
  ring

/-! ### Adaptedness -/

/-- **Events up to time `q` do not see stopping after `q`.** A set of the canonical filtration at time `q` contains a
path if and only if it contains the path stopped at any time `t ≥ q`. -/
theorem stoppedPath_mem_iff_of_measurableSet {q t : ℝ≥0} (hqt : q ≤ t) {S : Set (ContinuousPath ℂ)}
    (hS : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) q] S) (b : ContinuousPath ℂ) :
    ContinuousPath.stoppedPath t b ∈ S ↔ b ∈ S := by
  have hle : ContinuousPath.canonicalFiltration (alpha := ℂ) q ≤
      MeasurableSpace.comap (ContinuousPath.stoppedPath (alpha := ℂ) t) inferInstance := by
    show ⨆ s : Set.Iic q, MeasurableSpace.comap (ContinuousPath.coordinateProcess (alpha := ℂ) s)
      inferInstance ≤ _
    refine iSup_le fun s => ?_
    have hs : (s : ℝ≥0) ≤ t := (show (s : ℝ≥0) ≤ q from s.2).trans hqt
    have heq : ContinuousPath.coordinateProcess (alpha := ℂ) (s : ℝ≥0) =
        ContinuousPath.coordinateProcess (alpha := ℂ) (s : ℝ≥0) ∘ ContinuousPath.stoppedPath t := by
      funext ω
      show ω s = ContinuousPath.stoppedPath t ω s
      rw [ContinuousPath.stoppedPath_apply_of_le t ω s hs]
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (ContinuousPath.measurable_coordinateProcess _).comap_le
  obtain ⟨S', -, hS'⟩ := hle S hS
  rw [← hS']
  simp only [mem_preimage, ContinuousPath.stoppedPath_stoppedPath, min_self]

/-- The killed rate at a time `s ≤ t` is unchanged when the path is stopped at `t`. -/
theorem killedRate_stoppedPath (hD : IsOpen D) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) {t : ℝ≥0} {s : ℝ}
    (hst : s ≤ t) : killedRate D f (ContinuousPath.stoppedPath t b) s = killedRate D f b s := by
  by_cases hs : 0 < s
  · have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hst
    have hA := ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration D hD s.toNNReal
    have hmem : s ∈ killedTimes D (ContinuousPath.stoppedPath t b) ↔ s ∈ killedTimes D b :=
      and_congr_right fun _ => stoppedPath_mem_iff_of_measurableSet hst' hA b
    simp only [killedRate]
    by_cases hb : s ∈ killedTimes D b
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (hmem.2 hb),
        ContinuousPath.stoppedPath_apply_of_le t b _ hst']
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (fun h => hb (hmem.1 h))]
  · simp only [killedRate]
    rw [Set.indicator_of_notMem (fun h : s ∈ killedTimes D _ => hs h.1),
      Set.indicator_of_notMem (fun h : s ∈ killedTimes D b => hs h.1)]

/-- The occupation functional up to `t` only reads the path up to `t`. -/
theorem killedOccupationUpTo_stoppedPath (hD : IsOpen D) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    killedOccupationUpTo D f (ContinuousPath.stoppedPath t b) t = killedOccupationUpTo D f b t := by
  unfold killedOccupationUpTo
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ Iic (t : ℝ)
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, killedRate_stoppedPath hD f b hs]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

theorem measurable_killedOccupationUpTo (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p : ContinuousPath ℂ × ℝ => killedOccupationUpTo D f p.1 p.2) := by
  have hS : MeasurableSet {q : (ContinuousPath ℂ × ℝ) × ℝ | q.2 ≤ q.1.2} :=
    measurableSet_le measurable_snd (measurable_snd.comp measurable_fst)
  have hF : Measurable (fun q : (ContinuousPath ℂ × ℝ) × ℝ =>
      (Iic q.1.2).indicator (killedRate D f q.1.1) q.2) :=
    ((measurable_killedRate hD hf).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hS
  exact hF.lintegral_prod_right'

/-- **Adaptedness of the occupation functional.** `b ↦ A^f_t(b)` is measurable for the canonical filtration at
time `t`. -/
theorem measurable_killedOccupationUpTo_canonicalFiltration (hD : IsOpen D) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) (t : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (fun b => killedOccupationUpTo D f b t) := by
  have hborel : Measurable (fun b : ContinuousPath ℂ => killedOccupationUpTo D f b t) :=
    (measurable_killedOccupationUpTo hD hf).comp (measurable_id.prodMk measurable_const)
  have heq : (fun b : ContinuousPath ℂ => killedOccupationUpTo D f b t) =
      (fun b : ContinuousPath ℂ => killedOccupationUpTo D f b t) ∘ ContinuousPath.stoppedPath t := by
    funext b
    exact (killedOccupationUpTo_stoppedPath hD f b t).symm
  rw [heq]
  exact hborel.comp (LQGClockApproxAdapted.measurable_stoppedPath_canonicalFiltration t)

theorem measurable_killedOccupationGapUpTo_canonicalFiltration (hD : IsOpen D) {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (t : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (fun b => killedOccupationGapUpTo D f g b t) := by
  unfold killedOccupationGapUpTo
  exact (measurable_killedOccupationUpTo_canonicalFiltration hD hf t).ennreal_toReal.sub
    (measurable_killedOccupationUpTo_canonicalFiltration hD hg t).ennreal_toReal

theorem measurable_killedOccupationGap (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) : Measurable (killedOccupationGap D f g) := by
  unfold killedOccupationGap
  exact (measurable_killedOccupation hD hf).ennreal_toReal.sub (measurable_killedOccupation hD hg).ennreal_toReal

/-! ### Chebyshev's inequality and the Markov property at a fixed time -/

/-- **Chebyshev's inequality for the terminal gap.** Under the hypotheses of the energy estimate, for every start
`x ∈ D` and `c > 0`, `c² P_x(|A^f - A^g| ≥ c) ≤ 2 δ (M + M)`. -/
theorem mul_measure_le_abs_killedOccupationGap_le (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) {M δ : ℝ≥0∞} (hM : M ≠ ⊤) (hMf : ∀ y ∈ D, killedPotential D f y ≤ M)
    (hMg : ∀ y ∈ D, killedPotential D g y ≤ M)
    (hfg : ∀ y ∈ D, killedPotential D f y ≤ killedPotential D g y + δ)
    (hgf : ∀ y ∈ D, killedPotential D g y ≤ killedPotential D f y + δ) {x : ℂ} (hx : x ∈ D) {c : ℝ}
    (hc : 0 < c) :
    ENNReal.ofReal (c ^ 2) * planarBrownianMotion x {b | c ≤ |killedOccupationGap D f g b|} ≤
      2 * δ * (M + M) := by
  have hY := measurable_killedOccupationGap hD hf hg
  have hF : Measurable fun b => ENNReal.ofReal (killedOccupationGap D f g b ^ 2) :=
    ENNReal.measurable_ofReal.comp (hY.pow_const 2)
  calc ENNReal.ofReal (c ^ 2) * planarBrownianMotion x {b | c ≤ |killedOccupationGap D f g b|}
      ≤ ENNReal.ofReal (c ^ 2) * planarBrownianMotion x
          {b | ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal (killedOccupationGap D f g b ^ 2)} := by
        refine mul_le_mul_of_nonneg_left (measure_mono fun b hb => ?_) zero_le
        have hb' : c ≤ |killedOccupationGap D f g b| := hb
        show ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal (killedOccupationGap D f g b ^ 2)
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_le_mul hb' hb' hc.le (abs_nonneg (killedOccupationGap D f g b)),
          sq_abs (killedOccupationGap D f g b)]
    _ ≤ ∫⁻ b, ENNReal.ofReal (killedOccupationGap D f g b ^ 2) ∂planarBrownianMotion x :=
        mul_meas_ge_le_lintegral₀ hF.aemeasurable _
    _ ≤ 2 * δ * (killedPotential D f x + killedPotential D g x) :=
        lintegral_sq_killedOccupation_sub_le hD hf hg hM hMf hMg hfg hgf hx
    _ ≤ 2 * δ * (M + M) := mul_le_mul_of_nonneg_left (add_le_add (hMf x hx) (hMg x hx)) zero_le

/-- **The Markov property at a fixed time, for an event of the shifted path.** Let `S` be an event of the canonical
filtration at time `t` on which `B_t ∈ D`, and let `B` be a Borel event of paths with `a P_x(B) ≤ K` for every start
`x ∈ D`. Then `a P_w(S ∩ {θ_t b ∈ B}) ≤ K P_w(S)`. -/
theorem mul_measure_inter_shift_preimage_le {t : ℝ≥0} {S : Set (ContinuousPath ℂ)}
    (hS : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] S) (hSD : ∀ b ∈ S, b t ∈ D)
    {B : Set (ContinuousPath ℂ)} (hB : MeasurableSet B) {a K : ℝ≥0∞} (ha : a ≠ ⊤)
    (hK : ∀ x ∈ D, a * planarBrownianMotion x B ≤ K) (w : ℂ) :
    a * planarBrownianMotion w (S ∩ ContinuousPath.shift t ⁻¹' B) ≤ K * planarBrownianMotion w S := by
  have hSb : MeasurableSet S := (ContinuousPath.canonicalFiltration (alpha := ℂ)).le t _ hS
  have hpre : MeasurableSet (ContinuousPath.shift t ⁻¹' B) :=
    (ContinuousPath.continuous_shift_fixed t).measurable hB
  have hG : Measurable (B.indicator (1 : ContinuousPath ℂ → ℝ≥0∞)) := measurable_one.indicator hB
  have hmk := setLIntegral_shift_planarBrownianMotion w t hS hG
  have hL : ∫⁻ b in S, B.indicator 1 (ContinuousPath.shift t b) ∂planarBrownianMotion w =
      planarBrownianMotion w (S ∩ ContinuousPath.shift t ⁻¹' B) := by
    calc ∫⁻ b in S, B.indicator 1 (ContinuousPath.shift t b) ∂planarBrownianMotion w
        = ∫⁻ b in S, (ContinuousPath.shift t ⁻¹' B).indicator 1 b ∂planarBrownianMotion w :=
          lintegral_congr fun b => rfl
      _ = planarBrownianMotion w (S ∩ ContinuousPath.shift t ⁻¹' B) := by
          rw [lintegral_indicator_one hpre, Measure.restrict_apply hpre, Set.inter_comm]
  have hR : ∫⁻ b in S, (∫⁻ b', B.indicator 1 b' ∂planarBrownianMotion (b t)) ∂planarBrownianMotion w =
      ∫⁻ b in S, planarBrownianMotion (b t) B ∂planarBrownianMotion w :=
    lintegral_congr fun b => lintegral_indicator_one hB
  calc a * planarBrownianMotion w (S ∩ ContinuousPath.shift t ⁻¹' B)
      = a * ∫⁻ b in S, planarBrownianMotion (b t) B ∂planarBrownianMotion w := by
        rw [← hL, hmk, hR]
    _ = ∫⁻ b in S, a * planarBrownianMotion (b t) B ∂planarBrownianMotion w :=
        (lintegral_const_mul' _ _ ha).symm
    _ ≤ ∫⁻ _ in S, K ∂planarBrownianMotion w := setLIntegral_mono' hSb fun b hb => hK _ (hSD b hb)
    _ = K * planarBrownianMotion w S := setLIntegral_const _ _

/-! ### First entrance along a grid -/

/-- The first entrance of the grid values `X_0, X_1, …` into `{|x| ≥ η}` happens at the index `j`: `|X_j| ≥ η` and
`|X_i| < η` for all `i < j`. -/
def gridFirstEntrance {Ω : Type*} (X : ℕ → Ω → ℝ) (η : ℝ) (j : ℕ) : Set Ω :=
  {ω | η ≤ |X j ω|} ∩ ⋂ i ∈ Finset.range j, {ω | |X i ω| < η}

theorem pairwiseDisjoint_gridFirstEntrance {Ω : Type*} (X : ℕ → Ω → ℝ) (η : ℝ) (s : Set ℕ) :
    s.PairwiseDisjoint (gridFirstEntrance X η) := by
  intro i _ j _ hij
  show Disjoint (gridFirstEntrance X η i) (gridFirstEntrance X η j)
  rw [Set.disjoint_left]
  intro ω hωi hωj
  rcases lt_or_gt_of_ne hij with h | h
  · exact absurd (show η ≤ |X i ω| from hωi.1)
      (not_le.2 (show |X i ω| < η from Set.mem_iInter₂.1 hωj.2 i (Finset.mem_range.2 h)))
  · exact absurd (show η ≤ |X j ω| from hωj.1)
      (not_le.2 (show |X j ω| < η from Set.mem_iInter₂.1 hωi.2 j (Finset.mem_range.2 h)))

theorem exists_mem_gridFirstEntrance {Ω : Type*} {X : ℕ → Ω → ℝ} {η : ℝ} {N : ℕ} {ω : Ω}
    (h : ∃ j ≤ N, η ≤ |X j ω|) : ∃ j ≤ N, ω ∈ gridFirstEntrance X η j := by
  classical
  have hex : ∃ j, j ≤ N ∧ η ≤ |X j ω| := h
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  refine Set.mem_iInter₂.2 fun i hi => ?_
  have hi' : i < Nat.find hex := Finset.mem_range.1 hi
  have hmin := Nat.find_min hex hi'
  exact lt_of_not_ge fun h' => hmin ⟨hi'.le.trans (Nat.find_spec hex).1, h'⟩

/-! ### The maximal inequality -/

/-- **Maximal inequality on a grid.** Let the potentials of the Borel rates `f, g` be at most `M < ∞` and differ by
at most `δ` on the open set `D`. Then for every start `w ∈ D`, every `η > 0`, every increasing family of times `t_j`
and every `N`, `η² P_w(∃ j ≤ N, |A^f_{t_j} - A^g_{t_j}| ≥ η) ≤ 32 δ M`. -/
theorem mul_measure_exists_le_abs_killedOccupationGapUpTo_le (hD : IsOpen D) {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {M δ : ℝ≥0∞} (hM : M ≠ ⊤)
    (hMf : ∀ y ∈ D, killedPotential D f y ≤ M) (hMg : ∀ y ∈ D, killedPotential D g y ≤ M)
    (hfg : ∀ y ∈ D, killedPotential D f y ≤ killedPotential D g y + δ)
    (hgf : ∀ y ∈ D, killedPotential D g y ≤ killedPotential D f y + δ) {w : ℂ} (hw : w ∈ D)
    {η : ℝ} (hη : 0 < η) {t : ℕ → ℝ≥0} (ht : Monotone t) (N : ℕ) :
    ENNReal.ofReal (η ^ 2) * planarBrownianMotion w
        {b | ∃ j ≤ N, η ≤ |killedOccupationGapUpTo D f g b (t j)|} ≤ 32 * δ * M := by
  set c : ℝ := η / 2 with hc
  have hc0 : 0 < c := half_pos hη
  have hcheb : ∀ x ∈ D, ENNReal.ofReal (c ^ 2) *
      planarBrownianMotion x {b | c ≤ |killedOccupationGap D f g b|} ≤ 2 * δ * (M + M) :=
    fun x hx => mul_measure_le_abs_killedOccupationGap_le hD hf hg hM hMf hMg hfg hgf hx hc0
  have hBm : MeasurableSet {b : ContinuousPath ℂ | c ≤ |killedOccupationGap D f g b|} :=
    (continuous_abs.measurable.comp (measurable_killedOccupationGap hD hf hg)) measurableSet_Ici
  -- almost surely both occupation functionals are finite
  have hfin : ∀ᵐ b ∂planarBrownianMotion w,
      killedOccupation D f b ≠ ⊤ ∧ killedOccupation D g b ≠ ⊤ := by
    have h1 := ae_lt_top (μ := planarBrownianMotion w) (measurable_killedOccupation hD hf)
      (ne_top_of_le_ne_top hM (hMf w hw))
    have h2 := ae_lt_top (μ := planarBrownianMotion w) (measurable_killedOccupation hD hg)
      (ne_top_of_le_ne_top hM (hMg w hw))
    filter_upwards [h1, h2] with b hb1 hb2
    exact ⟨hb1.ne, hb2.ne⟩
  have hnull := ae_iff.1 hfin
  -- the first-entrance events are adapted
  have hXm : ∀ i j, i ≤ j → Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) (t j)]
      (fun b => killedOccupationGapUpTo D f g b (t i)) := fun i j hij =>
    (measurable_killedOccupationGapUpTo_canonicalFiltration hD hf hg (t i)).mono
      ((ContinuousPath.canonicalFiltration (alpha := ℂ)).mono (ht hij)) le_rfl
  have hEm : ∀ j, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) (t j)]
      (gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j) := by
    intro j
    refine MeasurableSet.inter ((continuous_abs.measurable.comp (hXm j j le_rfl)) measurableSet_Ici) ?_
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    exact (continuous_abs.measurable.comp (hXm i j (Finset.mem_range.1 hi).le)) measurableSet_Iio
  have hSm : ∀ j, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) (t j)]
      (gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j ∩
        {b | ((t j : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}) := fun j =>
    (hEm j).inter (ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration D hD (t j))
  -- the covering of the grid event
  have hcover : {b | ∃ j ≤ N, η ≤ |killedOccupationGapUpTo D f g b (t j)|} ⊆
      ({b | c ≤ |killedOccupationGap D f g b|} ∪
        {b | ¬(killedOccupation D f b ≠ ⊤ ∧ killedOccupation D g b ≠ ⊤)}) ∪
        ⋃ j ∈ Finset.range (N + 1),
          ((gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j ∩
            {b | ((t j : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}) ∩
            ContinuousPath.shift (t j) ⁻¹' {b | c ≤ |killedOccupationGap D f g b|}) := by
    intro b hb
    by_cases hB : c ≤ |killedOccupationGap D f g b|
    · exact Or.inl (Or.inl hB)
    by_cases hG : killedOccupation D f b ≠ ⊤ ∧ killedOccupation D g b ≠ ⊤
    swap
    · exact Or.inl (Or.inr hG)
    right
    obtain ⟨j, hjN, hjE⟩ := exists_mem_gridFirstEntrance
      (X := fun i b => killedOccupationGapUpTo D f g b (t i)) (η := η) (N := N) (ω := b) hb
    have hj : η ≤ |killedOccupationGapUpTo D f g b (t j)| := hjE.1
    have hτ : ((t j : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b := by
      by_contra hτ
      have hle : ContinuousPath.exitTime D b ≤ ENNReal.ofReal (t j : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact not_lt.1 hτ
      rw [killedOccupationGapUpTo_eq_of_exitTime_le f g b hle] at hj
      exact hB (by linarith)
    refine Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hjN), ⟨hjE, hτ⟩, ?_⟩
    show c ≤ |killedOccupationGap D f g (ContinuousPath.shift (t j) b)|
    have hsplit := killedOccupationGap_eq_add hG.1 hG.2 hτ
    have hYb : |killedOccupationGap D f g b| < c := lt_of_not_ge hB
    have heq : killedOccupationGap D f g (ContinuousPath.shift (t j) b) =
        killedOccupationGap D f g b - killedOccupationGapUpTo D f g b (t j) := by
      linarith
    rw [heq]
    have h3 := abs_sub_abs_le_abs_sub (killedOccupationGapUpTo D f g b (t j)) (killedOccupationGap D f g b)
    rw [abs_sub_comm] at h3
    linarith
  -- each first-entrance term
  have hterm : ∀ j, ENNReal.ofReal (c ^ 2) * planarBrownianMotion w
      ((gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j ∩
          {b | ((t j : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}) ∩
        ContinuousPath.shift (t j) ⁻¹' {b | c ≤ |killedOccupationGap D f g b|}) ≤
      2 * δ * (M + M) * planarBrownianMotion w
        (gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j) := by
    intro j
    refine (mul_measure_inter_shift_preimage_le (hSm j)
      (fun b hb => ContinuousPath.mem_of_lt_exitTime D b (t j) hb.2) hBm ENNReal.ofReal_ne_top hcheb w).trans ?_
    exact mul_le_mul_of_nonneg_left (measure_mono Set.inter_subset_left) zero_le
  have hEb : ∀ j ∈ Finset.range (N + 1),
      MeasurableSet (gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j) :=
    fun j _ => (ContinuousPath.canonicalFiltration (alpha := ℂ)).le (t j) _ (hEm j)
  have hmain : ENNReal.ofReal (c ^ 2) * planarBrownianMotion w
      {b | ∃ j ≤ N, η ≤ |killedOccupationGapUpTo D f g b (t j)|} ≤
      2 * δ * (M + M) + 2 * δ * (M + M) := by
    calc ENNReal.ofReal (c ^ 2) * planarBrownianMotion w
          {b | ∃ j ≤ N, η ≤ |killedOccupationGapUpTo D f g b (t j)|}
        ≤ ENNReal.ofReal (c ^ 2) * (planarBrownianMotion w {b | c ≤ |killedOccupationGap D f g b|} +
            planarBrownianMotion w {b | ¬(killedOccupation D f b ≠ ⊤ ∧ killedOccupation D g b ≠ ⊤)} +
            ∑ j ∈ Finset.range (N + 1), planarBrownianMotion w
              ((gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j ∩
                {b | ((t j : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}) ∩
                ContinuousPath.shift (t j) ⁻¹' {b | c ≤ |killedOccupationGap D f g b|})) := by
          refine mul_le_mul_of_nonneg_left ((measure_mono hcover).trans ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)))) zero_le
      _ = ENNReal.ofReal (c ^ 2) * planarBrownianMotion w {b | c ≤ |killedOccupationGap D f g b|} +
            ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (c ^ 2) * planarBrownianMotion w
              ((gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j ∩
                {b | ((t j : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b}) ∩
                ContinuousPath.shift (t j) ⁻¹' {b | c ≤ |killedOccupationGap D f g b|}) := by
          rw [hnull, add_zero, mul_add, Finset.mul_sum]
      _ ≤ 2 * δ * (M + M) + ∑ j ∈ Finset.range (N + 1), 2 * δ * (M + M) * planarBrownianMotion w
            (gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j) :=
          add_le_add (hcheb w hw) (Finset.sum_le_sum fun j _ => hterm j)
      _ = 2 * δ * (M + M) + 2 * δ * (M + M) * planarBrownianMotion w
            (⋃ j ∈ Finset.range (N + 1),
              gridFirstEntrance (fun i b => killedOccupationGapUpTo D f g b (t i)) η j) := by
          rw [← Finset.mul_sum, measure_biUnion_finset
            (pairwiseDisjoint_gridFirstEntrance _ η _) hEb]
      _ ≤ 2 * δ * (M + M) + 2 * δ * (M + M) * 1 := by
          gcongr
          exact prob_le_one
      _ = 2 * δ * (M + M) + 2 * δ * (M + M) := by rw [mul_one]
  have h4 : ENNReal.ofReal (η ^ 2) = 4 * ENNReal.ofReal (c ^ 2) := by
    rw [show η ^ 2 = 4 * c ^ 2 by rw [hc]; ring, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal (η ^ 2) * planarBrownianMotion w
        {b | ∃ j ≤ N, η ≤ |killedOccupationGapUpTo D f g b (t j)|}
      = 4 * (ENNReal.ofReal (c ^ 2) * planarBrownianMotion w
          {b | ∃ j ≤ N, η ≤ |killedOccupationGapUpTo D f g b (t j)|}) := by rw [h4, mul_assoc]
    _ ≤ 4 * (2 * δ * (M + M) + 2 * δ * (M + M)) := mul_le_mul_of_nonneg_left hmain zero_le
    _ = 32 * δ * M := by ring

/-- **Maximal inequality at all dyadic times.** Under the hypotheses of the grid inequality, the gap
`|A^f_t - A^g_t|` reaches `η` at some dyadic time `t = j / 2^m` (`j ≤ m 2^m`) with `P_w`-probability at most
`32 δ M / η²`. -/
theorem mul_measure_iUnion_dyadic_le_abs_killedOccupationGapUpTo_le (hD : IsOpen D) {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {M δ : ℝ≥0∞} (hM : M ≠ ⊤)
    (hMf : ∀ y ∈ D, killedPotential D f y ≤ M) (hMg : ∀ y ∈ D, killedPotential D g y ≤ M)
    (hfg : ∀ y ∈ D, killedPotential D f y ≤ killedPotential D g y + δ)
    (hgf : ∀ y ∈ D, killedPotential D g y ≤ killedPotential D f y + δ) {w : ℂ} (hw : w ∈ D)
    {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal (η ^ 2) * planarBrownianMotion w
        (⋃ m : ℕ, {b | ∃ j ≤ m * 2 ^ m,
          η ≤ |killedOccupationGapUpTo D f g b (((j : ℝ≥0) / 2 ^ m : ℝ≥0) : ℝ)|}) ≤ 32 * δ * M := by
  have hmono : Monotone (fun m : ℕ => {b : ContinuousPath ℂ | ∃ j ≤ m * 2 ^ m,
      η ≤ |killedOccupationGapUpTo D f g b (((j : ℝ≥0) / 2 ^ m : ℝ≥0) : ℝ)|}) := by
    refine monotone_nat_of_le_succ fun m b hb => ?_
    obtain ⟨j, hj, hjb⟩ := hb
    refine ⟨2 * j, ?_, ?_⟩
    · have h1 : 2 * j ≤ 2 * (m * 2 ^ m) := Nat.mul_le_mul_left 2 hj
      have h2 : 2 * (m * 2 ^ m) ≤ (m + 1) * 2 ^ (m + 1) := by
        rw [pow_succ]
        nlinarith [Nat.zero_le (2 ^ m)]
      exact h1.trans h2
    · have htime : ((2 * j : ℕ) : ℝ≥0) / 2 ^ (m + 1) = (j : ℝ≥0) / 2 ^ m := by
        rw [Nat.cast_mul, Nat.cast_ofNat, pow_succ', mul_div_mul_left _ _ two_ne_zero]
      rw [htime]
      exact hjb
  rw [hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  have htm : Monotone (fun j : ℕ => (j : ℝ≥0) / 2 ^ m) := by
    intro i j hij
    show (i : ℝ≥0) / 2 ^ m ≤ (j : ℝ≥0) / 2 ^ m
    gcongr
  exact mul_measure_exists_le_abs_killedOccupationGapUpTo_le hD hf hg hM hMf hMg hfg hgf hw hη htm (m * 2 ^ m)

/-! ### All times -/

/-- The dyadic time `⌊t 2^m⌋ / 2^m` below `t`. -/
noncomputable def dyadicFloor (t : ℝ) (m : ℕ) : ℝ≥0 :=
  ((⌊t * 2 ^ m⌋₊ : ℕ) : ℝ≥0) / 2 ^ m

theorem coe_dyadicFloor (t : ℝ) (m : ℕ) :
    ((dyadicFloor t m : ℝ≥0) : ℝ) = (⌊t * 2 ^ m⌋₊ : ℝ) / 2 ^ m := by
  simp [dyadicFloor]

theorem dyadicFloor_le {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : ((dyadicFloor t m : ℝ≥0) : ℝ) ≤ t := by
  rw [coe_dyadicFloor, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (mul_nonneg ht (by positivity))

theorem sub_inv_lt_dyadicFloor (t : ℝ) (m : ℕ) : t - ((2 : ℝ) ^ m)⁻¹ < ((dyadicFloor t m : ℝ≥0) : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [coe_dyadicFloor, lt_div_iff₀ h2, sub_mul, inv_mul_cancel₀ h2.ne']
  linarith [Nat.lt_floor_add_one (t * 2 ^ m)]

theorem tendsto_dyadicFloor {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m : ℕ => ((dyadicFloor t m : ℝ≥0) : ℝ)) atTop (𝓝 t) := by
  have h : Tendsto (fun m : ℕ => t - ((2 : ℝ) ^ m)⁻¹) atTop (𝓝 t) := by
    have := (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))).const_sub t
    simpa only [Function.comp_apply, sub_zero] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds
    (fun m => (sub_inv_lt_dyadicFloor t m).le) (fun m => dyadicFloor_le ht m)

/-- Before the time `0` the occupation functional vanishes. -/
theorem killedOccupationUpTo_of_nonpos (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) {t : ℝ} (ht : t ≤ 0) :
    killedOccupationUpTo D f b t = 0 := by
  unfold killedOccupationUpTo
  refine (lintegral_congr fun s => ?_).trans lintegral_zero
  by_cases hs : s ∈ Iic t
  · rw [indicator_of_mem hs]
    exact indicator_of_notMem (fun h : s ∈ killedTimes D b => absurd h.1 (not_lt.2 ((mem_Iic.1 hs).trans ht))) _
  · exact indicator_of_notMem hs _

theorem killedOccupationUpTo_le_killedOccupation (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (t : ℝ) :
    killedOccupationUpTo D f b t ≤ killedOccupation D f b :=
  lintegral_mono fun s => indicator_le_self' (fun _ _ => zero_le) s

/-- If the occupation functional is finite, its values at the dyadic times below `t ≥ 0` converge to its value at
`t` (dominated convergence; the time `t` itself is a null set). -/
theorem tendsto_killedOccupationUpTo_dyadicFloor (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    {b : ContinuousPath ℂ} (hfin : killedOccupation D f b ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m : ℕ => killedOccupationUpTo D f b (dyadicFloor t m)) atTop
      (𝓝 (killedOccupationUpTo D f b t)) := by
  unfold killedOccupationUpTo
  refine tendsto_lintegral_of_dominated_convergence (killedRate D f b)
    (fun m => (measurable_killedRate_path hD hf b).indicator measurableSet_Iic)
    (fun m => Eventually.of_forall fun s => indicator_le_self' (fun _ _ => zero_le) s) hfin ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton t)] with s hs
  have hs' : s ≠ t := hs
  rcases lt_or_gt_of_ne hs' with hst | hst
  · have hev : ∀ᶠ m : ℕ in atTop, s < ((dyadicFloor t m : ℝ≥0) : ℝ) :=
      (tendsto_dyadicFloor ht).eventually (lt_mem_nhds hst)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with m hm
    simp only [indicator_of_mem (show s ∈ Iic t from hst.le),
      indicator_of_mem (show s ∈ Iic ((dyadicFloor t m : ℝ≥0) : ℝ) from hm.le)]
  · have h0 : ∀ m : ℕ, (Iic ((dyadicFloor t m : ℝ≥0) : ℝ)).indicator (killedRate D f b) s = 0 := fun m =>
      indicator_of_notMem (fun h => (not_le.2 hst) ((mem_Iic.1 h).trans (dyadicFloor_le ht m))) _
    have h1 : (Iic t).indicator (killedRate D f b) s = 0 :=
      indicator_of_notMem (fun h => (not_le.2 hst) (mem_Iic.1 h)) _
    simp only [h0, h1]
    exact tendsto_const_nhds

theorem tendsto_killedOccupationGapUpTo_dyadicFloor (hD : IsOpen D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) {b : ContinuousPath ℂ} (hfb : killedOccupation D f b ≠ ⊤)
    (hgb : killedOccupation D g b ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m : ℕ => killedOccupationGapUpTo D f g b (dyadicFloor t m)) atTop
      (𝓝 (killedOccupationGapUpTo D f g b t)) := by
  have h1 := (ENNReal.tendsto_toReal ((killedOccupationUpTo_le_killedOccupation f b t).trans_lt
    hfb.lt_top).ne).comp (tendsto_killedOccupationUpTo_dyadicFloor hD hf hfb ht)
  have h2 := (ENNReal.tendsto_toReal ((killedOccupationUpTo_le_killedOccupation g b t).trans_lt
    hgb.lt_top).ne).comp (tendsto_killedOccupationUpTo_dyadicFloor hD hg hgb ht)
  exact h1.sub h2

/-- **Maximal inequality at all times.** Under the hypotheses of the grid inequality, the gap `|A^f_t - A^g_t|`
exceeds `η` at some time `t` with `P_w`-probability at most `32 δ M / η²`: almost surely both functionals are finite
(their expectations are the potentials at `w`), so the gap is left-continuous in `t` and is read off the dyadic
times. -/
theorem mul_measure_exists_lt_abs_killedOccupationGapUpTo_le (hD : IsOpen D) {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {M δ : ℝ≥0∞} (hM : M ≠ ⊤)
    (hMf : ∀ y ∈ D, killedPotential D f y ≤ M) (hMg : ∀ y ∈ D, killedPotential D g y ≤ M)
    (hfg : ∀ y ∈ D, killedPotential D f y ≤ killedPotential D g y + δ)
    (hgf : ∀ y ∈ D, killedPotential D g y ≤ killedPotential D f y + δ) {w : ℂ} (hw : w ∈ D)
    {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal (η ^ 2) * planarBrownianMotion w
        {b | ∃ t : ℝ, η < |killedOccupationGapUpTo D f g b t|} ≤ 32 * δ * M := by
  have h1 := ae_lt_top (measurable_killedOccupation hD hf) ((hMf w hw).trans_lt hM.lt_top).ne
  have h2 := ae_lt_top (measurable_killedOccupation hD hg) ((hMg w hw).trans_lt hM.lt_top).ne
  refine le_trans (mul_le_mul_of_nonneg_left (measure_mono_ae ?_) zero_le)
    (mul_measure_iUnion_dyadic_le_abs_killedOccupationGapUpTo_le hD hf hg hM hMf hMg hfg hgf hw hη)
  filter_upwards [h1, h2] with b hb1 hb2 hbt
  obtain ⟨t, ht⟩ := hbt
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have hle : t ≤ 0 := (not_le.1 hneg).le
    have h0 : killedOccupationGapUpTo D f g b t = 0 := by
      unfold killedOccupationGapUpTo
      rw [killedOccupationUpTo_of_nonpos f b hle, killedOccupationUpTo_of_nonpos g b hle, sub_self]
    rw [h0, abs_zero] at ht
    exact absurd ht (not_lt.2 hη.le)
  have hlim := (tendsto_killedOccupationGapUpTo_dyadicFloor hD hf hg hb1.ne hb2.ne ht0).abs
  obtain ⟨m, hm1, hm2⟩ := ((hlim.eventually (lt_mem_nhds ht)).and
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop t)).exists
  have hj : ⌊t * 2 ^ m⌋₊ ≤ m * 2 ^ m := by
    have hle : t * 2 ^ m ≤ ((m * 2 ^ m : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right hm2 (by positivity)
    exact Nat.cast_le.1 ((Nat.floor_le (mul_nonneg ht0 (by positivity))).trans hle)
  exact mem_iUnion.2 ⟨m, ⌊t * 2 ^ m⌋₊, hj, hm1.le⟩

end MatedCRT
