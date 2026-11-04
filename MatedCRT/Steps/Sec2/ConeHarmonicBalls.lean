import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec2.ConeFamily

/-!
# Theorem 2.3 from Lemmas 2.4 and 2.5

The proof of Theorem 2.3 (line 587): by Lemma 2.5 at the scales `b = n + 1`, a.s. there are families of harmonic balls
with the properties of Theorem 2.3 up to the times `(n+1) T^{n+1}`; since `T^b =d T` and `T > 0`, `sup_n (n+1) T^{n+1}`
is a.s. infinite, and the families glue (`exists_isConeHarmonicBallFamily_of_seq`). Uniqueness is deterministic:
condition (c) determines every bounded `Λ_t` (`IsConeHarmonicBallFamily.eqOn`).

`T^b =d T` is read off the equality of joint laws of Lemma 2.5 through the measurable events
`{T > s} = {∃ q ∈ ℚ, q > s, (q, 0) ∈ family process}` (`familyTimeExceeds`). A law `P.map F` carries this information
only if `F` is a random variable (for non-`AEMeasurable` `F`, Mathlib's `P.map F` is a Dirac mass at an arbitrary
point). The step `ConeFamilyAEMeasurableStep` (the field and the harmonic balls of Lemmas 2.4 and 2.5 form random
variables) is implicit in the paper (lines 553, 562 speak of the law of `{Λ_t}`); it is not a consequence of the
drafted Lemmas 2.4 and 2.5.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Step (measurability of the harmonic balls of the cone).** (i) For every random family `(T, {Λ_t}_{0<t<T})`
with the properties of Lemma 2.4 almost surely, the pair (circle average process of `h`, family process of `Λ`) is a
random variable; (ii) for `b > 0` and every random family `(T^b, {Λ^b_t}_{0<t<bT^b})` with the properties of Lemma
2.5 almost surely, the pair (circle average process of `h(R_b ·) + Q log R_b - γ⁻¹ log b`, family process of
`R_b⁻¹ Λ^b_{b ·}`) is a random variable. Implicit in the paper (the laws of lines 553, 562); expected from the
measurable dependence of harmonic balls on the field (HB22), it is neither stated nor proved there. -/
def ConeFamilyAEMeasurableStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  (∀ (T : Ω → ℝ) (Λ : Ω → ℝ → Set ℂ),
    (∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧ IsStoppedAtHalfBall (Λ ω) (T ω)) →
    AEMeasurable (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω))) P) ∧
  ∀ b : ℝ, 0 < b → ∀ (Tb : Ω → ℝ) (Λb : Ω → ℝ → Set ℂ),
    (∀ᵐ ω ∂P, 0 < Tb ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λb ω) (b * Tb ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Λb ω) (coneScaleRadius γ (hcirc ω) b) b) (Tb ω)) →
    AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      familyProcess (rescaledFamily (Λb ω) (coneScaleRadius γ (hcirc ω) b) b) (Tb ω))) P

/-- The event `{T > s}` of a family process: some rational time `q > s` has `(q, 0)` in the process. -/
def familyTimeExceeds (s : ℝ) : Set (ℝ × ℂ → Prop) :=
  {X | ∃ q : ℚ, s < q ∧ X ((q : ℝ), 0)}

theorem measurableSet_familyTimeExceeds (s : ℝ) : MeasurableSet (familyTimeExceeds s) :=
  measurableSet_setOfPred.2 (Measurable.exists fun _ => measurable_const.and (measurable_pi_apply _))

theorem familyTimeExceeds_anti {s s' : ℝ} (h : s ≤ s') : familyTimeExceeds s' ⊆ familyTimeExceeds s :=
  fun _ ⟨q, hq, hX⟩ => ⟨q, h.trans_lt hq, hX⟩

/-- For a family containing `0` on `(0, T)`, the family process lies in `familyTimeExceeds s` iff `s < T` (`s ≥ 0`). -/
theorem familyProcess_mem_familyTimeExceeds_iff {Λ : ℝ → Set ℂ} {T s : ℝ} (hs : 0 ≤ s)
    (h0 : ∀ t ∈ Ioo 0 T, (0 : ℂ) ∈ Λ t) : familyProcess Λ T ∈ familyTimeExceeds s ↔ s < T := by
  constructor
  · rintro ⟨q, hsq, hq, -⟩
    exact hsq.trans hq.2
  · intro hsT
    obtain ⟨q, hsq, hqT⟩ := exists_rat_btwn hsT
    exact ⟨q, hsq, ⟨hs.trans_lt hsq, hqT⟩, h0 q ⟨hs.trans_lt hsq, hqT⟩⟩

/-- **Theorem 2.3** from **Lemma 2.4**, **Lemma 2.5** and `ConeFamilyAEMeasurableStep`. -/
theorem coneHarmonicBalls_of_steps (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt) (hmeas : ConeFamilyAEMeasurableStep) :
    ConeHarmonicBallsStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  have : IsProbabilityMeasure P := hcone.1
  -- Lemma 2.4: a family up to the fixed time, chosen pointwise
  have hex : ∀ᵐ ω ∂P, ∃ y : ℝ × (ℝ → Set ℂ),
      0 < y.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) y.2 y.1 ∧ IsStoppedAtHalfBall y.2 y.1 := by
    filter_upwards [h24 γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hω
    obtain ⟨T, hT, Λ, hΛ, hst, -⟩ := hω
    exact ⟨(T, Λ), hT, hΛ, hst⟩
  obtain ⟨x, hx⟩ : ∃ x : Ω → ℝ × (ℝ → Set ℂ), ∀ᵐ ω ∂P, 0 < (x ω).1 ∧
      IsConeHarmonicBallFamilyOn (μ ω) (x ω).2 (x ω).1 ∧ IsStoppedAtHalfBall (x ω).2 (x ω).1 :=
    ⟨fun ω => Classical.epsilon fun y : ℝ × (ℝ → Set ℂ) =>
        0 < y.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) y.2 y.1 ∧ IsStoppedAtHalfBall y.2 y.1,
      by filter_upwards [hex] with ω hω; exact Classical.epsilon_spec hω⟩
  -- Lemma 2.5 at the scales `b = n + 1`
  choose Tb Λb hTb hlaw using fun n : ℕ =>
    h25 γ hγ0 hγ2 Ω P hC hcirc μ hcone (fun ω => (x ω).1) (fun ω => (x ω).2) hx ((n : ℝ) + 1) (by positivity)
  let F : Ω → ((Ioi (0 : ℝ)) × ℂ → ℝ) × (ℝ × ℂ → Prop) :=
    fun ω => (circleProcess (hcirc ω), familyProcess (x ω).2 (x ω).1)
  let G : ℕ → Ω → ((Ioi (0 : ℝ)) × ℂ → ℝ) × (ℝ × ℂ → Prop) := fun n ω =>
    (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)),
      familyProcess (rescaledFamily (Λb n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1)) (Tb n ω))
  have hlaw' : ∀ n, P.map F = P.map (G n) := hlaw
  have hF : AEMeasurable F P :=
    (hmeas γ hγ0 hγ2 Ω P hC hcirc μ hcone).1 (fun ω => (x ω).1) (fun ω => (x ω).2) hx
  have hG : ∀ n, AEMeasurable (G n) P := fun n =>
    (hmeas γ hγ0 hγ2 Ω P hC hcirc μ hcone).2 ((n : ℝ) + 1) (by positivity) (Tb n) (Λb n)
      (by filter_upwards [hTb n] with ω hω; exact ⟨hω.1, hω.2.1, hω.2.2.1⟩)
  have hCmeas : ∀ s : ℝ, MeasurableSet
      (Prod.snd ⁻¹' (familyTimeExceeds s)ᶜ : Set (((Ioi (0 : ℝ)) × ℂ → ℝ) × (ℝ × ℂ → Prop))) :=
    fun s => measurable_snd (measurableSet_familyTimeExceeds s).compl
  -- `P[T ≤ s] = P[T^{n+1} ≤ s]`
  have hEq : ∀ (n : ℕ) (s : ℝ), P (F ⁻¹' (Prod.snd ⁻¹' (familyTimeExceeds s)ᶜ)) =
      P (G n ⁻¹' (Prod.snd ⁻¹' (familyTimeExceeds s)ᶜ)) := by
    intro n s
    rw [← Measure.map_apply_of_aemeasurable hF (hCmeas s), ← Measure.map_apply_of_aemeasurable (hG n) (hCmeas s),
      hlaw' n]
  -- `P[(n+1) T^{n+1} ≤ M for all n] = 0`
  have hBM : ∀ M : ℕ, P {ω | ∀ k : ℕ, ((k : ℝ) + 1) * Tb k ω ≤ M} = 0 := by
    intro M
    have hanti : Antitone fun n : ℕ => F ⁻¹' (Prod.snd ⁻¹' (familyTimeExceeds ((M : ℝ) / ((n : ℝ) + 1)))ᶜ) := by
      intro n m hnm
      refine preimage_mono (preimage_mono (compl_subset_compl.mpr (familyTimeExceeds_anti ?_)))
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      gcongr
    have hnull : P (⋂ n : ℕ, F ⁻¹' (Prod.snd ⁻¹' (familyTimeExceeds ((M : ℝ) / ((n : ℝ) + 1)))ᶜ)) = 0 := by
      refine measure_mono_null_ae ?_ (measure_empty (μ := P))
      filter_upwards [hx] with ω hω hmem
      have hT := hω.1
      obtain ⟨n, hn⟩ := exists_nat_gt ((M : ℝ) / (x ω).1)
      have hle : ¬ ((M : ℝ) / ((n : ℝ) + 1) < (x ω).1) :=
        (familyProcess_mem_familyTimeExceeds_iff (by positivity)
          (fun t ht => hω.2.1.2.1.mem t ht)).not.mp (mem_iInter.mp hmem n)
      apply hle
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hT] at hn
      nlinarith
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun n : ℕ => hF.nullMeasurableSet_preimage (hCmeas ((M : ℝ) / ((n : ℝ) + 1)))) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hnull] at hlim
    refine le_antisymm (ge_of_tendsto' hlim fun n => ?_) zero_le
    calc P {ω | ∀ k : ℕ, ((k : ℝ) + 1) * Tb k ω ≤ M}
        ≤ P (G n ⁻¹' (Prod.snd ⁻¹' (familyTimeExceeds ((M : ℝ) / ((n : ℝ) + 1)))ᶜ)) := by
          refine measure_mono_ae ?_
          filter_upwards [hTb n] with ω hω hB
          have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have h0 : ∀ t ∈ Ioo 0 (Tb n ω), (0 : ℂ) ∈
              rescaledFamily (Λb n ω) (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1)) ((n : ℝ) + 1) t := by
            intro t ht
            show (coneScaleRadius γ (hcirc ω) ((n : ℝ) + 1) : ℂ) * 0 ∈ Λb n ω (((n : ℝ) + 1) * t)
            rw [mul_zero]
            exact hω.2.1.2.1.mem _ ⟨mul_pos hb ht.1, mul_lt_mul_of_pos_left ht.2 hb⟩
          have hk : ((n : ℝ) + 1) * Tb n ω ≤ M := hB n
          show familyProcess _ (Tb n ω) ∉ familyTimeExceeds ((M : ℝ) / ((n : ℝ) + 1))
          rw [familyProcess_mem_familyTimeExceeds_iff (by positivity) h0, not_lt, le_div_iff₀ hb]
          linarith
      _ = P (F ⁻¹' (Prod.snd ⁻¹' (familyTimeExceeds ((M : ℝ) / ((n : ℝ) + 1)))ᶜ)) := (hEq n _).symm
  -- `sup_n (n+1) T^{n+1} = ∞` almost surely
  have hunb : ∀ᵐ ω ∂P, ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ((n : ℝ) + 1) * Tb n ω := by
    have h0 : P (⋃ M : ℕ, {ω | ∀ k : ℕ, ((k : ℝ) + 1) * Tb k ω ≤ M}) = 0 := measure_iUnion_null hBM
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    have hω' : ¬ ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ((n : ℝ) + 1) * Tb n ω := hω
    simp only [not_forall, not_exists, not_lt] at hω'
    obtain ⟨M, hM⟩ := hω'
    exact mem_iUnion.2 ⟨M, hM⟩
  -- gluing and uniqueness
  filter_upwards [hunb, ae_all_iff.2 fun n => hTb n] with ω hω hTω
  obtain ⟨Λ', hΛ'⟩ := exists_isConeHarmonicBallFamily_of_seq (S := fun n => ((n : ℝ) + 1) * Tb n ω)
    (Λ := fun n => Λb n ω) (fun n => (hTω n).2.1) fun M => by
      obtain ⟨n, hn⟩ := hω ⌈M⌉₊
      exact ⟨n, (Nat.le_ceil M).trans_lt hn⟩
  exact ⟨Λ', hΛ', fun Λ'' h'' => hΛ'.eqOn h''⟩

end MatedCRT
