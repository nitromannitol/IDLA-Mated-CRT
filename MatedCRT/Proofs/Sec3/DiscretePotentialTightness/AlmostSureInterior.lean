import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedInteriorEvent
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.SelectionStep
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-! Almost-sure interior tightness along polynomially summable scales. -/

namespace MatedCRT
open MeasureTheory Filter Topology Set Metric

/-- The interior part of Lemma 3.1 with eventually almost-sure bounds, from the
normalization and the cited exit-time and discrete Hölder estimates. -/
theorem discretePotentialTightnessAeStep_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮) :
    DiscretePotentialTightnessAeStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS D hDρ hDo hDc e he E u C hEm hEe hEt hum hCm hCp hgood
  have hmod := ae_prepared_interior_vertex_modulus 𝒮 h217 h218 hH hγ hγ2 hρ hρ1 S hS e he
  obtain ⟨Cm, hCm1, hmS⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmS Ω S hS
  have hCm : 0 < Cm := one_pos.trans hCm1
  have hEpos : ∀ ω n, 0 < E ω n := fun ω n => by
    obtain ⟨j, hj⟩ := hEe ω n
    rw [← hj]
    exact he.1 j
  have hmev : ∀ ω, ∀ᶠ n in atTop, 0 ≤ (S.mε (E ω n))⁻¹ ∧ (S.mε (E ω n))⁻¹ ≤ Cm * E ω n := by
    intro ω
    filter_upwards [(hEt ω).eventually (gt_mem_nhds hε₀)] with n hn
    have h := (hmε (E ω n) (hEpos ω n) hn).1
    have hpos : 0 < Cm⁻¹ * (E ω n)⁻¹ := mul_pos (inv_pos.2 hCm) (inv_pos.2 (hEpos ω n))
    refine ⟨inv_nonneg.2 (hpos.le.trans h), ?_⟩
    have h2 := inv_anti₀ hpos h
    rwa [mul_inv, inv_inv, inv_inv] at h2
  set y : Ω → ℕ → ℕ → ℝ := fun ω n c =>
    Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω) n c with hy_def
  have hy : ∀ n c, Measurable[S.envSigma] fun ω => y ω n c := by
    intro n c
    exact @Tightness.measurable_comp_range Ω S.envSigma e (fun ω => E ω n) (hEm n) (fun ω => hEe ω n)
      (fun ε ω => Tightness.proxyValue ε (S.η ω) D (TopologicalSpace.denseSeq ℂ c.unpair.1)
        (1 / ((c.unpair.2 : ℝ) + 1)) fun a => (S.mε ε)⁻¹ * u ω n a)
      fun j => @Tightness.measurable_proxyValue Ω S.envSigma S.η (fun ω a => (S.mε (e j))⁻¹ * u ω n a)
        (Tightness.measurable_eta_of_envSigma S) (fun a => (hum n a).const_mul _) D hDo.measurableSet
        (e j) _ _
  obtain ⟨Φ, hΦm, hΦ⟩ := @Tightness.exists_measurable_diagonal_subseq Ω S.envSigma y hy
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hgood, hmod, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hbdω hmodω hη hp
  have hEQ : ∀ K : Set ℂ, IsCompact K → K ⊆ D →
      IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) K := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbdω
    let u' : ℕ → ℤ → ℝ := fun n => if n < N then 0 else u ω n
    have hlap : ∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
        |matedLaplacian (S.mult (E ω n) ω) (u' n) a| ≤ C ω := by
      intro n a ha
      by_cases hn : n < N
      · simpa [u', hn, matedLaplacian, mLaplacian] using (hCp ω).le
      · simpa [u', hn] using (hN n (Nat.le_of_not_gt hn)).1 a ha
    have hbound : ∀ n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |u' n a| ≤ C ω / E ω n := by
      intro n a ha
      by_cases hn : n < N
      · simpa [u', hn] using (div_nonneg (hCp ω).le (hEpos ω n).le)
      · simpa [u', hn] using (hN n (Nat.le_of_not_gt hn)).2 a ha
    intro K hK hKD k hk
    obtain ⟨δ, hδ, hδevent⟩ := hmodω (E ω) (hEe ω) (hEt ω) D K u' (C ω)
      hDo hDρ hK hKD (hCp ω).le hlap hbound k hk
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hδevent, Filter.eventually_ge_atTop N] with n hn hnN a ha b hb hab
    simpa [u', Nat.not_lt_of_ge hnN] using hn a ha b hb hab
  obtain ⟨hmono, hconvY⟩ := hΦ ω
  have hbddY : ∀ c, ∃ M, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
    intro c
    refine ⟨Cm * C ω, ?_⟩
    filter_upwards [hmev ω, hbdω] with n hn hbdn
    have hC := hCp ω
    refine Tightness.abs_proxyValue_le (mul_pos hCm hC).le fun k hk => ?_
    have hkD : k ∈ cellVertices (E ω n) (S.η ω) D := Tightness.mem_cellVertices_of_vertexPoint_mem (hEpos ω n) hk
    show |(S.mε (E ω n))⁻¹ * u ω n k| ≤ Cm * C ω
    have hE := hEpos ω n
    rw [abs_mul, abs_of_nonneg hn.1]
    calc (S.mε (E ω n))⁻¹ * |u ω n k| ≤ (Cm * E ω n) * (C ω / E ω n) :=
          mul_le_mul hn.2 (hbdn.2 k hkD) (abs_nonneg _) (mul_pos hCm hE).le
      _ = Cm * C ω * (E ω n * (E ω n)⁻¹) := by ring
      _ = Cm * C ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
  have hY : ∀ c, ∃ l, Tendsto (fun k => Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω)
      (Φ ω k) c) atTop (𝓝 l) := fun c => hconvY c (hbddY c)
  obtain ⟨ubar, h1, h2, h3⟩ := Tightness.tightness_of_proxies hDo (isBounded_ball.subset hDρ) hη.1 hp hη.2.2.1
    (hEpos ω) (hEt ω) hCm (hmev ω) hEQ hmono hY
  exact ⟨hmono, ubar, h1, h2⟩

end MatedCRT

#print axioms MatedCRT.discretePotentialTightnessAeStep_of_inputs
