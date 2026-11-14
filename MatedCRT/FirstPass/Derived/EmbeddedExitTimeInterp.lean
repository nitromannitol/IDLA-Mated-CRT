import MatedCRT.FirstPass.Derived.MepsScalingOfCdfBounds

/-!
# Step count versus linear interpolation in the definition of `m_ε`

Berestycki-Gwynne (arXiv:2003.10320, (1.7)) define `m_ε` as the median exit time of the *linearly interpolated*
embedded walk `η(X^{0,ε})` from the ball `B_{1/2}`; `MatedCRTEnv.mε` is the median of the *number of steps*
(`embeddedExitTime`) before the walk leaves `B_{1/2}`.  Since the ball is convex, a linear interpolation
between two consecutive vertices inside the ball stays inside the ball, so the two exit times differ by at
most one step:
`τ_interp ≤ τ_steps ≤ τ_interp + 1`.  Consequently the two medians differ by at most `1`, and, as both are of
order `ε⁻¹`, their ratio tends to `1` (the consumer takes `ε⁻¹ ≲ m_ε` from `MepsScalingInput`).

## Main results

* `interpExitTime`: the exit time of the linearly interpolated embedded walk from `U`.
* `interpExitTime_le_embeddedExitTime`, `embeddedExitTime_le_interpExitTime_add_one`: the pathwise comparison
  for convex `U`.
* `MatedCRTEnv.mεInterpCdf`, `MatedCRTEnv.mεCdf_le_mεInterpCdf`, `MatedCRTEnv.mεInterpCdf_le_mεCdf_add_one`: the
  annealed distribution functions of the interpolated exit time and of the step count.
* `medianOf_le_medianOf_add_one`: monotone sandwiching `F ≤ G ≤ F(· + 1)` of distribution functions moves the
  lower median by at most `1`.
* `MatedCRTEnv.mεInterp_le_mε`, `MatedCRTEnv.mε_le_mεInterp_add_one`, `MatedCRTEnv.abs_mε_sub_mεInterp_le_one`:
  the medians differ by at most `1`.
-/

set_option autoImplicit false

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace MatedCRT

/-- The exit time from `U` of the linearly interpolated embedded walk `t ↦ η(x_t)` (time scale `1`,
`interpolatedWalk ε η 1 x`), the quantity of Berestycki-Gwynne (1.7). -/
noncomputable def interpExitTime (ε : ℝ) (η : ℝ → ℂ) (U : Set ℂ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  HarmonicBalls.pathExitTime U (interpolatedWalk ε η 1 x)

/-- At integer times the interpolated walk is the embedded walk. -/
theorem interpolatedWalk_natCast (ε : ℝ) (η : ℝ → ℂ) (x : ℕ → ℤ) (n : ℕ) :
    interpolatedWalk ε η 1 x (n : ℝ≥0) = vertexPoint ε η (x n) := by
  simp [interpolatedWalk]

/-- If the interpolated walk is outside a convex set `U` at time `t`, one of the two vertices between which it
interpolates is outside `U`. -/
theorem exists_vertex_not_mem_of_interpolatedWalk_not_mem {U : Set ℂ} (hU : Convex ℝ U) (ε : ℝ)
    (η : ℝ → ℂ) (x : ℕ → ℤ) (t : ℝ≥0) (ht : interpolatedWalk ε η 1 x t ∉ U) :
    ∃ k : ℕ, k ≤ ⌊(t : ℝ)⌋₊ + 1 ∧ vertexPoint ε η (x k) ∉ U := by
  by_contra hcon
  push Not at hcon
  have h0 : vertexPoint ε η (x ⌊(t : ℝ)⌋₊) ∈ U := hcon _ (Nat.le_succ _)
  have h1 : vertexPoint ε η (x (⌊(t : ℝ)⌋₊ + 1)) ∈ U := hcon _ le_rfl
  apply ht
  have hθ0 : 0 ≤ (t : ℝ) - ⌊(t : ℝ)⌋₊ := sub_nonneg.2 (Nat.floor_le t.2)
  have hθ1 : (t : ℝ) - ⌊(t : ℝ)⌋₊ ≤ 1 := by
    have := Nat.lt_floor_add_one (t : ℝ)
    linarith
  have := hU h0 h1 (a := 1 - ((t : ℝ) - ⌊(t : ℝ)⌋₊)) (b := (t : ℝ) - ⌊(t : ℝ)⌋₊) (by linarith) hθ0
    (by ring)
  simpa [interpolatedWalk, Complex.real_smul] using this

/-- The first exit from a convex set happens no later by interpolation: `τ_interp ≤ τ_steps`. -/
theorem interpExitTime_le_embeddedExitTime (ε : ℝ) (η : ℝ → ℂ) (U : Set ℂ) (x : ℕ → ℤ) :
    interpExitTime ε η U x ≤ (embeddedExitTime ε η U x : ℝ≥0∞) := by
  classical
  unfold embeddedExitTime vExitTime interpExitTime HarmonicBalls.pathExitTime
  split_ifs with h
  · have hN := Nat.find_spec h
    refine sInf_le ⟨(Nat.find h : ℝ≥0), by simp, ?_⟩
    rw [interpolatedWalk_natCast]
    exact hN
  · simp

/-- For convex `U`, the step count exceeds the interpolated exit time by less than one step:
`τ_steps ≤ τ_interp + 1`. -/
theorem embeddedExitTime_le_interpExitTime_add_one {U : Set ℂ} (hU : Convex ℝ U) (ε : ℝ)
    (η : ℝ → ℂ) (x : ℕ → ℤ) :
    (embeddedExitTime ε η U x : ℝ≥0∞) ≤ interpExitTime ε η U x + 1 := by
  classical
  unfold interpExitTime
  unfold HarmonicBalls.pathExitTime
  rw [ENNReal.sInf_add]
  refine le_iInf₂ fun s hs => ?_
  obtain ⟨t, rfl, ht⟩ := hs
  obtain ⟨k, hk, hkU⟩ := exists_vertex_not_mem_of_interpolatedWalk_not_mem hU ε η x t ht
  have hex : ∃ n, x n ∉ {k : ℤ | vertexPoint ε η k ∈ U} := ⟨k, hkU⟩
  have hle : embeddedExitTime ε η U x ≤ (k : ℕ∞) := by
    unfold embeddedExitTime vExitTime
    split_ifs
    exact_mod_cast Nat.find_min' hex hkU
  have h1 : (embeddedExitTime ε η U x : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by
    have := ENat.toENNReal_le.2 hle
    simpa using this
  refine h1.trans ?_
  have hk' : (k : ℝ≥0∞) ≤ ((⌊(t : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hk
  refine hk'.trans ?_
  have hfl : ((⌊(t : ℝ)⌋₊ : ℕ) : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
    have : (⌊(t : ℝ)⌋₊ : ℝ≥0) ≤ t := by
      have h := Nat.floor_le t.2
      exact_mod_cast h
    exact_mod_cast this
  push_cast
  exact add_le_add hfl le_rfl

/-- **A monotone sandwich of distribution functions moves the lower median by at most one.** If
`F s ≤ G s` and `G s ≤ F (s + 1)` for `s ≥ 0`, and `F` reaches `1/2` at some `x ≥ 0`, then
`medianOf G ≤ medianOf F ≤ medianOf G + 1`. -/
theorem medianOf_le_medianOf_add_one {F G : ℝ → ℝ≥0∞} (hFG : ∀ s, F s ≤ G s)
    (hGF : ∀ s, 0 ≤ s → G s ≤ F (s + 1)) (hne : ∃ x, 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ F x) :
    medianOf G ≤ medianOf F ∧ medianOf F ≤ medianOf G + 1 := by
  obtain ⟨x, hx0, hx⟩ := hne
  have hbdG : BddBelow {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ G m} := ⟨0, fun _ h => h.1⟩
  have hsub : {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ F m} ⊆ {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ G m} :=
    fun m hm => ⟨hm.1, hm.2.trans (hFG m)⟩
  have hneG : {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ G m}.Nonempty := ⟨x, hsub ⟨hx0, hx⟩⟩
  refine ⟨csInf_le_csInf hbdG ⟨x, hx0, hx⟩ hsub, ?_⟩
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨m, hm, hmlt⟩ := exists_lt_of_csInf_lt hneG
    (show sInf {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ G m} < sInf {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ G m} + δ
      by linarith)
  have hmF : medianOf F ≤ m + 1 :=
    medianOf_le_of_half_le (by linarith [hm.1]) (hm.2.trans (hGF m hm.1))
  unfold medianOf at hmF ⊢
  linarith

namespace MatedCRTEnv

/-- The annealed distribution function of the exit time from `B_{1/2}` of the *interpolated* embedded walk
`η(X^{0,ε})` started from `a^ε_0` (Berestycki-Gwynne (1.7)). -/
noncomputable def mεInterpCdf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (s : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
    {x | interpExitTime ε (S.η ω) (ball 0 (1 / 2)) x ≤ ENNReal.ofReal s} ∂S.P

/-- The median of the exit time of the interpolated embedded walk from `B_{1/2}`. -/
noncomputable def mεInterp {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) : ℝ :=
  medianOf (S.mεInterpCdf ε)

/-- The step count is stochastically larger than the interpolated exit time. -/
theorem mεCdf_le_mεInterpCdf {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε s : ℝ) :
    S.mεCdf ε s ≤ S.mεInterpCdf ε s := by
  refine lintegral_mono fun ω => measure_mono fun x hx => ?_
  exact (interpExitTime_le_embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x).trans hx

/-- The step count is at most one more than the interpolated exit time. -/
theorem mεInterpCdf_le_mεCdf_add_one {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : S.mεInterpCdf ε s ≤ S.mεCdf ε (s + 1) := by
  refine lintegral_mono fun ω => measure_mono fun x hx => ?_
  have h1 := embeddedExitTime_le_interpExitTime_add_one (convex_ball (0 : ℂ) (1 / 2)) ε (S.η ω) x
  refine h1.trans ?_
  have : ENNReal.ofReal (s + 1) = ENNReal.ofReal s + 1 := by
    rw [ENNReal.ofReal_add hs zero_le_one]; simp
  rw [this]
  exact add_le_add (show interpExitTime ε (S.η ω) (ball 0 (1 / 2)) x ≤ ENNReal.ofReal s from hx) le_rfl

/-- A positive median forces the distribution function to reach `1/2` (the empty set has infimum `0`). -/
theorem exists_half_le_mεCdf_of_pos {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    (h : 0 < S.mε ε) : ∃ x, 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ S.mεCdf ε x := by
  by_contra hcon
  push Not at hcon
  have : {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ S.mεCdf ε m} = ∅ :=
    Set.eq_empty_of_forall_notMem fun m hm => (hcon m hm.1).not_ge hm.2
  have h0 : S.mε ε = 0 := by
    rw [S.mε_eq_medianOf_mεCdf]
    unfold medianOf
    rw [this, Real.sInf_empty]
  linarith

/-- The interpolated median is at most the step median. -/
theorem mεInterp_le_mε {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    (h : 0 < S.mε ε) : S.mεInterp ε ≤ S.mε ε :=
  (medianOf_le_medianOf_add_one (S.mεCdf_le_mεInterpCdf ε) (fun _ hs => S.mεInterpCdf_le_mεCdf_add_one ε hs)
    (S.exists_half_le_mεCdf_of_pos ε h)).1

/-- The step median is at most one more than the interpolated median. -/
theorem mε_le_mεInterp_add_one {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    (h : 0 < S.mε ε) : S.mε ε ≤ S.mεInterp ε + 1 :=
  (medianOf_le_medianOf_add_one (S.mεCdf_le_mεInterpCdf ε) (fun _ hs => S.mεInterpCdf_le_mεCdf_add_one ε hs)
    (S.exists_half_le_mεCdf_of_pos ε h)).2

/-- **The two definitions of `m_ε` agree up to one step**: `|m_ε - m_ε^{interp}| ≤ 1`. -/
theorem abs_mε_sub_mεInterp_le_one {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    (h : 0 < S.mε ε) : |S.mε ε - S.mεInterp ε| ≤ 1 := by
  have h1 := S.mεInterp_le_mε ε h
  have h2 := S.mε_le_mεInterp_add_one ε h
  rw [abs_le]
  constructor <;> linarith

end MatedCRTEnv

end MatedCRT
