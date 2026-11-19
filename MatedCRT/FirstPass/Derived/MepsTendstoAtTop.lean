import MatedCRT.FirstPass.S6j.ExitTimeLowerTail
import MatedCRT.FirstPass.Derived.IdentificationTransfer
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.ExitNull68

/-!
# `m_ε → ∞` from the lower half of the scaling of `m_ε`

The lower half of eq:meps-scaling (Berestycki-Gwynne arXiv:2003.10320, (1.8)) bounds the annealed
distribution function `F_ε(s) = E[P^{h,η}(τ ≤ s)]` of the exit time of the embedded walk from `B_{1/2}`:
`F_ε(c₁ ε⁻¹) < 1/2` for all small `ε`. Since `m_ε` is the lower median of `F_ε`, this gives
`m_ε ≥ c₁ ε⁻¹` as soon as `F_ε` reaches `1/2` at some time. For a valid environment it does: the vertices
embedded in `B_{1/2}` form a finite set, and the walk on `ℤ` with locally finite edge multiplicities and
`m k (k+1) ≠ 0` leaves every finite set almost surely, so `F_ε(s) → 1` as `s → ∞` by monotone convergence.

## Main results

* `exists_half_le_mεCdf`: for a valid environment and `ε > 0`, `F_ε(s) ≥ 1/2` for some `s ≥ 0`.
* `tendsto_mε_atTop_of_mεCdf_lower`: the bound `F_ε(c₁ ε⁻¹) < 1/2` for small `ε` gives `m_{ε_n} → ∞`
  along every sequence `ε_n → 0` of positive numbers.
* `tendsto_mε_atTop_of_uniformStart`: `m_{ε_n} → ∞` from Lemma 2.13, Lemma 2.14 and the uniform-start
  invariance principle (`mεCdf_lower_of_uniformStart`).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **The annealed exit-time distribution function reaches `1/2`.** For `0 < γ < 2`, a valid environment and
`ε > 0`, almost surely in the environment the embedded walk from `a^ε_0` leaves `B_{1/2}` in finitely many steps
almost surely, so `F_ε(s) → 1` as `s → ∞` and `F_ε(s) ≥ 1/2` for some `s ≥ 0`. -/
theorem exists_half_le_mεCdf {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ S.mεCdf ε x := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨η', hη'm, hη'⟩ := hS.exists_curveVersion
  obtain ⟨V, hV, hVe⟩ := exists_measurable_vertexOf_curve hε
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
    {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ ENNReal.ofReal n} with hf
  have hmeas : ∀ n, AEMeasurable (f n) S.P := by
    intro n
    refine ((measurable_embeddedExitTime_le (ε := ε) hV (n : ℝ)).comp
      (hη'm.prodMk (hS.measurable_mult_array ε))).aemeasurable.congr ?_
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hη'] with ω hap hcoc hω
    show srwLaw (S.mult ε ω) (V (η' ω, 0))
      {y | (embeddedExitTime ε (⇑(η' ω)) (ball 0 (1 / 2)) y : ℝ≥0∞) ≤ ENNReal.ofReal (n : ℝ)} = f n ω
    rw [hVe (η' ω) 0 (by rw [hω]; exact hcoc) (by rw [hω]; exact hap.2.2.1), hω]
  have hmono : ∀ ω, Monotone fun n => f n ω := fun ω n k hnk =>
    measure_mono fun x hx => le_trans hx (ENNReal.ofReal_le_ofReal (Nat.cast_le.2 hnk))
  have hlim : ∀ᵐ ω ∂S.P, 1 ≤ ⨆ n, f n ω := by
    filter_upwards [Uniform68Env.ae_envInputs hγ hγ2 hS] with ω ⟨hc, hp, hadj⟩
    obtain ⟨hlf, hsucc, -⟩ := Uniform68Env.envAt S hε ω hc hp hadj
    set A : Set ℤ := {k | vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) (1 / 2)} with hA
    have hAfin : A.Finite := by
      refine (cellVertices_finite_of_isCompact hc hp hε
        (isCompact_closedBall (0 : ℂ) (1 / 2))).subset ?_
      intro k hk
      refine ⟨S.η ω (ε * k), ⟨⟨ε * k, ⟨?_, le_rfl⟩, rfl⟩, ?_⟩⟩
      · nlinarith
      · exact ball_subset_closedBall hk
    have hT : srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0) {x | vExitTime A x = ⊤} = 0 :=
      ExitNull68.exit_null_of_finite hlf hsucc hAfin (vertexOf ε (S.η ω) 0)
    set E : ℕ → Set (ℕ → ℤ) := fun n =>
      {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ ENNReal.ofReal n} with hE
    have hEmono : Monotone E := fun n k hnk x hx =>
      le_trans hx (ENNReal.ofReal_le_ofReal (Nat.cast_le.2 hnk))
    have hcover : (univ : Set (ℕ → ℤ)) ⊆ (⋃ n, E n) ∪ {x | vExitTime A x = ⊤} := by
      intro x _
      by_cases htop : vExitTime A x = ⊤
      · exact Or.inr htop
      · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 htop
        have he : embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x = (k : ℕ∞) := hk.symm
        refine Or.inl (mem_iUnion.2 ⟨k, ?_⟩)
        show ((embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (k : ℝ)
        rw [he, ENNReal.ofReal_natCast]
        simp
    calc (1 : ℝ≥0∞) = srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0) univ := measure_univ.symm
      _ ≤ srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0) ((⋃ n, E n) ∪ {x | vExitTime A x = ⊤}) :=
          measure_mono hcover
      _ ≤ srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0) (⋃ n, E n) +
          srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0) {x | vExitTime A x = ⊤} := measure_union_le _ _
      _ = ⨆ n, f n ω := by
          rw [hT, add_zero]
          exact hEmono.measure_iUnion
  have h1 : (1 : ℝ≥0∞) ≤ ⨆ n : ℕ, S.mεCdf ε n :=
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂S.P := by simp
      _ ≤ ∫⁻ ω, ⨆ n, f n ω ∂S.P := lintegral_mono_ae hlim
      _ = ⨆ n, ∫⁻ ω, f n ω ∂S.P := lintegral_iSup' hmeas (ae_of_all _ hmono)
      _ = ⨆ n : ℕ, S.mεCdf ε n := rfl
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 (lt_of_lt_of_le (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top) h1)
  exact ⟨n, n.cast_nonneg, hn.le⟩

/-- **`m_{ε_n} → ∞` from the lower bound on the annealed exit-time distribution function.** If there is
`c₁ > 0` such that, for every valid environment, `F_ε(c₁ ε⁻¹) < 1/2` for all small `ε` (the conclusion of
`mεCdf_lower_of_uniformStart`), then `m_ε ≥ c₁ ε⁻¹` for small `ε`, and `m_{ε_n} → ∞` along every sequence of
positive `ε_n → 0`. -/
theorem tendsto_mε_atTop_of_mεCdf_lower {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hlow : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.mεCdf ε (c₁ * ε⁻¹) < 1 / 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => S.mε (ε n)) atTop atTop := by
  obtain ⟨c₁, hc₁, hlow⟩ := hlow
  obtain ⟨ε₀, hε₀, hlowS⟩ := hlow Ω S hS
  have hev : ∀ᶠ n in atTop, c₁ * (ε n)⁻¹ ≤ S.mε (ε n) := by
    filter_upwards [hε.eventually (gt_mem_nhds hε₀)] with n hn
    rw [MatedCRTEnv.mε_eq_medianOf_mεCdf]
    exact le_medianOf_of_lt_half (S.mεCdf_mono _) (hlowS _ (hε0 n) hn)
      (exists_half_le_mεCdf hγ hγ2 hS (hε0 n))
  have hinv : Tendsto (fun n => (ε n)⁻¹) atTop atTop :=
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp
      (tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩)
  exact tendsto_atTop_mono' atTop hev (hinv.const_mul_atTop hc₁)

/-- **`m_{ε_n} → ∞` from the uniform-start invariance principle.** For `0 < γ < 2`, from the Green kernel lower
bound (Lemma 2.13), the exit-time upper bound (Lemma 2.14) and the uniform-start invariance principle
([GMS21, Theorem 3.4]), `m_{ε_n} → ∞` for every valid environment along every sequence of positive `ε_n → 0`. -/
theorem tendsto_mε_atTop_of_uniformStart {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => S.mε (ε n)) atTop atTop :=
  tendsto_mε_atTop_of_mεCdf_lower hγ hγ2
    (ExitTimeLowerTail.mεCdf_lower_of_uniformStart h213 h214 hN4 γ hγ hγ2) hS hε0 hε

end MatedCRT.FirstPass.Derived
