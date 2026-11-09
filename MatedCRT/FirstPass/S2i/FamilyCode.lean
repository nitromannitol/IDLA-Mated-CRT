import MatedCRT.Defs.Setting

/-! # Countable code and decoder of a cone harmonic-ball family (fp-S2i, z2)

For a family `Λ` with the regularity, monotonicity and Hausdorff continuity of `SatisfiesHarmonicBallConditionsOn`, the
family is coded by `codeFamily T Λ = (T, a)` with `a i k = true` iff `q_i < T` and `z_k ∈ Λ_{q_i}`, along two fixed dense
sequences `q` (positive times) and `z` (centres). The decoder `decodeFamily` reads the whole process `(t, x) ↦ (0 < t < T ∧
x ∈ Λ_t)` back from the code (notes `CHATGPT-q1-open-steps.md` §6, C1–C3). Every operation is a countable quantifier over
the code, so the decoder is measurable in the code (`codeCl_measurable`, `decodeFamily_measurable`).
Key steps: closure of `Λ_t` is the closure of the countable union of `Λ_{q_i}`, `q_i < t` (Hausdorff continuity from the
left), and regular openness gives `Λ_t = interior (closure Λ_t)`. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- A dense sequence of positive times (separability of `(0, ∞)`). -/
theorem exists_dense_posTime : ∃ q : ℕ → Ioi (0 : ℝ), DenseRange q :=
  TopologicalSpace.exists_dense_seq _

/-- The fixed dense sequence `q` of positive times used in the code. -/
noncomputable def posTime : ℕ → Ioi (0 : ℝ) := Classical.choose exists_dense_posTime

theorem denseRange_posTime : DenseRange posTime := Classical.choose_spec exists_dense_posTime

/-- A dense sequence of centres in `ℂ` (the points `ℚ + iℚ` are one such sequence). -/
theorem exists_dense_centre : ∃ z : ℕ → ℂ, DenseRange z :=
  TopologicalSpace.exists_dense_seq _

/-- The fixed dense sequence `z` of centres used in the code. -/
noncomputable def centre : ℕ → ℂ := Classical.choose exists_dense_centre

theorem denseRange_centre : DenseRange centre := Classical.choose_spec exists_dense_centre

open Classical in
/-- The code of a family `Λ` stopped at `T`: `(T, a)` with `a i k = true` iff `q_i < T` and `z_k ∈ Λ_{q_i}`. -/
noncomputable def codeFamily (T : ℝ) (Λ : ℝ → Set ℂ) : ℝ × (ℕ → ℕ → Bool) :=
  (T, fun i k => decide ((posTime i : ℝ) < T ∧ centre k ∈ Λ (posTime i)))

/-- The closure test at time `t` and point `z`: for every `n` some centre `z_k` within `1/(n+1)` of `z` is marked
(`z_k ∈ Λ_{q_i}` for some `q_i < t`). For a genuine family this is `z ∈ closure Λ_t` (`codeCl_codeFamily_iff`). -/
def CodeCl (y : ℝ × (ℕ → ℕ → Bool)) (t : ℝ) (z : ℂ) : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, dist (centre k) z < 1 / ((n : ℝ) + 1) ∧
    ∃ i : ℕ, (posTime i : ℝ) < t ∧ y.2 i k = true

/-- The decoder: `(t, x)` lies in the decoded process when `0 < t < T` and some ball of centres around `x` passes the
closure test at `t`. -/
def decodeFamily (y : ℝ × (ℕ → ℕ → Bool)) : ℝ × ℂ → Prop :=
  fun p => 0 < p.1 ∧ p.1 < y.1 ∧
    ∃ m : ℕ, ∀ k : ℕ, dist (centre k) p.2 < 1 / ((m : ℝ) + 1) → CodeCl y p.1 (centre k)

/-- Regular open sets of a family are open. -/
theorem isOpen_of_isRegularOpen {s : Set ℂ} (h : IsRegularOpen s) : IsOpen s := by
  rw [← h]
  exact isOpen_interior

/-- Closure test of a genuine family: for `t ∈ (0, T)`, `CodeCl (codeFamily T Λ) t z ↔ z ∈ closure (Λ t)`. The forward
direction uses monotonicity; the backward direction uses Hausdorff continuity from the left at `t`, regular openness of
`Λ_{q}` and density of the centres. -/
theorem codeCl_codeFamily_iff {μ : Measure ℂ} {T t : ℝ} {Λ : ℝ → Set ℂ}
    (h : SatisfiesHarmonicBallConditionsOn μ Λ 0 T) (ht : t ∈ Ioo 0 T) (z : ℂ) :
    CodeCl (codeFamily T Λ) t z ↔ z ∈ closure (Λ t) := by
  constructor
  · intro hC
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk, i, hi, hmem⟩ := hC n
    have hmem' : (posTime i : ℝ) < T ∧ centre k ∈ Λ (posTime i) := by
      simpa [codeFamily] using hmem
    have hqs : (posTime i : ℝ) ∈ Ioo 0 T := ⟨(posTime i).2, lt_trans hi ht.2⟩
    have hsub : Λ (posTime i) ⊆ Λ t := h.monotoneOn hqs ht hi.le
    exact ⟨centre k, hsub hmem'.2, by rw [dist_comm]; exact lt_of_lt_of_le hk hn.le⟩
  · intro hz n
    have hεpos : (0 : ℝ) < 1 / (4 * ((n : ℝ) + 1)) := by positivity
    have hHc := h.hausdorffContinuousOn t ht (ENNReal.ofReal (1 / (4 * ((n : ℝ) + 1))))
      (ENNReal.ofReal_pos.mpr hεpos)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hHc
    obtain ⟨δ, hδ, hball⟩ := hHc
    have hδ'pos : 0 < min δ t := lt_min hδ ht.1
    have hδ'le : min δ t ≤ t := min_le_right _ _
    have hU : IsOpen ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo (t - min δ t) t) :=
      isOpen_Ioo.preimage continuous_subtype_val
    have hne : ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioo (t - min δ t) t).Nonempty := by
      refine ⟨⟨t - min δ t / 2, ?_⟩, ?_⟩
      · show 0 < t - min δ t / 2
        linarith [ht.1]
      · show t - min δ t < t - min δ t / 2 ∧ t - min δ t / 2 < t
        constructor <;> linarith
    obtain ⟨i, hi⟩ := denseRange_posTime.exists_mem_open hU hne
    have hi' : (posTime i : ℝ) ∈ Ioo (t - min δ t) t := hi
    have hsi : (posTime i : ℝ) ∈ Ioo 0 T := ⟨(posTime i).2, lt_trans hi'.2 ht.2⟩
    have hdist : dist (posTime i : ℝ) t < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hi'.1, hi'.2, min_le_left δ t]
    have hHs := hball hdist hsi
    have h0 : Metric.infEDist z (Λ t) = 0 := Metric.mem_closure_iff_infEDist_zero.mp hz
    have hinf : Metric.infEDist z (Λ (posTime i : ℝ)) < ENNReal.ofReal (1 / (4 * ((n : ℝ) + 1))) := by
      calc Metric.infEDist z (Λ (posTime i : ℝ))
          ≤ Metric.infEDist z (Λ t) + hausdorffEDist (Λ t) (Λ (posTime i : ℝ)) :=
            Metric.infEDist_le_infEDist_add_hausdorffEDist
        _ < ENNReal.ofReal (1 / (4 * ((n : ℝ) + 1))) := by
            rw [h0, zero_add, hausdorffEDist_comm]; exact hHs
    obtain ⟨w, hwΛ, hzw⟩ := Metric.infEDist_lt_iff.mp hinf
    have hopen : IsOpen (Λ (posTime i : ℝ)) := isOpen_of_isRegularOpen (h.isRegularOpen _ hsi)
    obtain ⟨r, hr, hballw⟩ := Metric.isOpen_iff.mp hopen w hwΛ
    have hzw' : dist z w < 1 / (4 * ((n : ℝ) + 1)) := by
      rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hεpos] at hzw
    have hρ : 0 < min r (1 / (2 * ((n : ℝ) + 1))) := lt_min hr (by positivity)
    obtain ⟨k, hk⟩ := denseRange_centre.exists_mem_open isOpen_ball
      ⟨w, mem_ball_self hρ⟩
    have hk' : dist (centre k) w < min r (1 / (2 * ((n : ℝ) + 1))) := hk
    have hkr : centre k ∈ ball w r := lt_of_lt_of_le hk' (min_le_left _ _)
    have hkey : min r (1 / (2 * ((n : ℝ) + 1))) + 1 / (4 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
      have h2 : min r (1 / (2 * ((n : ℝ) + 1))) ≤ 1 / (2 * ((n : ℝ) + 1)) := min_le_right _ _
      have e : 1 / (2 * ((n : ℝ) + 1)) + 1 / (4 * ((n : ℝ) + 1)) = (3 / 4) * (1 / ((n : ℝ) + 1)) := by
        field_simp
        ring
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    refine ⟨k, ?_, i, hi'.2, ?_⟩
    · calc dist (centre k) z ≤ dist (centre k) w + dist w z := dist_triangle _ _ _
        _ < min r (1 / (2 * ((n : ℝ) + 1))) + 1 / (4 * ((n : ℝ) + 1)) := by
            rw [dist_comm w z]; exact add_lt_add hk' hzw'
        _ < 1 / ((n : ℝ) + 1) := hkey
    · simp only [codeFamily, decide_eq_true_eq]
      exact ⟨lt_trans hi'.2 ht.2, hballw hkr⟩

/-- **Decoding identity.** For a family satisfying the harmonic-ball conditions on `(0, T)`, the decoder reads back the
whole space-time process: `decodeFamily (codeFamily T Λ) = familyProcess Λ T` (notes §6, eq. (22)). -/
theorem decodeFamily_codeFamily_eq {μ : Measure ℂ} {T : ℝ} {Λ : ℝ → Set ℂ}
    (h : SatisfiesHarmonicBallConditionsOn μ Λ 0 T) :
    decodeFamily (codeFamily T Λ) = familyProcess Λ T := by
  funext p
  obtain ⟨t, x⟩ := p
  apply propext
  simp only [decodeFamily, familyProcess, mem_Ioo, and_assoc]
  constructor
  · rintro ⟨ht0, htT, m, hm⟩
    have ht : t ∈ Ioo 0 T := ⟨ht0, htT⟩
    have hsub : ∀ k : ℕ, dist (centre k) x < 1 / ((m : ℝ) + 1) → centre k ∈ closure (Λ t) := fun k hk =>
      (codeCl_codeFamily_iff h ht (centre k)).mp (hm k hk)
    have hmpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hball_sub : ball x (1 / ((m : ℝ) + 1)) ⊆ closure (Λ t) := by
      intro y hy
      have hsub2 : ball x (1 / ((m : ℝ) + 1)) ∩ range centre ⊆ closure (Λ t) := by
        rintro _ ⟨hk, ⟨k, rfl⟩⟩
        exact hsub k hk
      exact closure_minimal hsub2 isClosed_closure
        (denseRange_centre.open_subset_closure_inter isOpen_ball hy)
    have hxint : x ∈ interior (closure (Λ t)) :=
      interior_maximal hball_sub isOpen_ball (mem_ball_self hmpos)
    have hreg : interior (closure (Λ t)) = Λ t := h.isRegularOpen t ht
    rw [hreg] at hxint
    exact ⟨ht0, htT, hxint⟩
  · rintro ⟨ht0, htT, hx⟩
    have ht : t ∈ Ioo 0 T := ⟨ht0, htT⟩
    obtain ⟨r, hr, hballr⟩ :=
      Metric.isOpen_iff.mp (isOpen_of_isRegularOpen (h.isRegularOpen t ht)) x hx
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
    refine ⟨ht0, htT, m, fun k hk => ?_⟩
    exact (codeCl_codeFamily_iff h ht (centre k)).mpr (subset_closure (hballr (lt_trans hk hm)))

end MatedCRT
