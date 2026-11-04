import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Convergence
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Selection
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.External.SLE

/-!
# Lemma 3.1: proof of `TightnessSelectionStep` (Arzelà-Ascoli with a measurable subsequence)

`tightnessSelectionStep_of_meps` proves the step from eq:meps-scaling (`MepsScalingInput`, `m_ε⁻¹ ≤ C ε`).

* The proxies `proxyCoord` are `σ(h, η)`-measurable (`measurable_proxyValue`). They read `η` only at the times
  `εk`, and `ε = E(ω, n)` ranges over the countable set `{e_j}` (`measurable_comp_range`).
* The proxies are eventually bounded by `C_m C`.
* The measurable diagonal subsequence (`exists_measurable_diagonal_subseq`) makes all of them converge. Almost
  surely `η` is continuous, surjective and proper (`IsAreaParametrized`, `IsValid.ae_tendsto_cocompact`), and
  `tightness_of_proxies` concludes.

`discretePotentialTightness_of_equicontinuity` gives Lemma 3.1 (corrected) from `MepsScalingInput` and
`TightnessEquicontinuityStep`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

namespace Tightness

variable {Ω : Type*}

/-- A function of a measurable random scale with values in a countable set `{e_j}` is measurable as soon as it is
measurable at each fixed scale `e_j`. -/
theorem measurable_comp_range [MeasurableSpace Ω] {e : ℕ → ℝ} {g : Ω → ℝ} (hg : Measurable g)
    (hge : ∀ ω, g ω ∈ range e) {F : ℝ → Ω → ℝ} (hF : ∀ j, Measurable (F (e j))) :
    Measurable fun ω => F (g ω) ω := by
  intro s hs
  have h : (fun ω => F (g ω) ω) ⁻¹' s = ⋃ j, g ⁻¹' {e j} ∩ F (e j) ⁻¹' s := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro hω
      obtain ⟨j, hj⟩ := hge ω
      refine ⟨j, hj.symm, ?_⟩
      rw [hj]
      exact hω
    · rintro ⟨j, hj, hω⟩
      rw [hj]
      exact hω
  rw [h]
  exact MeasurableSet.iUnion fun j => (hg (measurableSet_singleton _)).inter (hF j hs)

/-- The proxies are measurable when the curve is measurable at each time and the function at each vertex. -/
theorem measurable_proxyValue [MeasurableSpace Ω] {ηω : Ω → ℝ → ℂ} {U : Ω → ℤ → ℝ}
    (hη : ∀ s, Measurable fun ω => ηω ω s) (hU : ∀ a, Measurable fun ω => U ω a) {D : Set ℂ}
    (hD : MeasurableSet D) (ε : ℝ) (q : ℂ) (r : ℝ) :
    Measurable fun ω => proxyValue ε (ηω ω) D q r (U ω) := by
  have hP : ∀ k : ℤ, MeasurableSet {ω | IsProxyVertex ε (ηω ω) D q r k} := fun k =>
    (hη (ε * k) hD).inter (measurableSet_lt (((hη (ε * k)).sub measurable_const).norm) measurable_const)
  have hidx : Measurable fun ω => proxyIndex ε (ηω ω) D q r := by
    refine @measurable_natFind Ω _ (fun ω n => IsProxyVertex ε (ηω ω) D q r (intEnum n) ∨
      ∀ m, ¬ IsProxyVertex ε (ηω ω) D q r (intEnum m)) (fun ω => Classical.decPred _)
      (fun ω => exists_proxyIndex ε (ηω ω) D q r) fun n => ?_
    have h : {ω | IsProxyVertex ε (ηω ω) D q r (intEnum n) ∨ ∀ m, ¬ IsProxyVertex ε (ηω ω) D q r (intEnum m)} =
        {ω | IsProxyVertex ε (ηω ω) D q r (intEnum n)} ∪
          ⋂ m, {ω | IsProxyVertex ε (ηω ω) D q r (intEnum m)}ᶜ := by
      ext ω
      simp
    rw [h]
    exact (hP _).union (MeasurableSet.iInter fun m => (hP _).compl)
  have hex : MeasurableSet {ω | ∃ k, IsProxyVertex ε (ηω ω) D q r k} := by
    have h : {ω | ∃ k, IsProxyVertex ε (ηω ω) D q r k} = ⋃ k, {ω | IsProxyVertex ε (ηω ω) D q r k} := by
      ext ω
      simp
    rw [h]
    exact MeasurableSet.iUnion hP
  unfold proxyValue
  exact Measurable.ite hex (measurable_comp_nat (fun n => hU (intEnum n)) hidx) measurable_const

/-- The proxy is bounded by any bound of `U` at the vertices whose vertex point lies in `D`. -/
theorem abs_proxyValue_le {ε : ℝ} {η : ℝ → ℂ} {D : Set ℂ} {q : ℂ} {r : ℝ} {U : ℤ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hU : ∀ k, vertexPoint ε η k ∈ D → |U k| ≤ M) : |proxyValue ε η D q r U| ≤ M := by
  rcases proxyValue_spec ε η D q r U with ⟨k, hk, h⟩ | ⟨-, h⟩
  · rw [h]
    exact hU k hk.1
  · rw [h, abs_zero]
    exact hM0

/-- The curve is `σ(h, η)`-measurable at each time. -/
theorem measurable_eta_of_envSigma {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (s : ℝ) :
    Measurable[S.envSigma] fun ω => S.η ω s := by
  rw [measurable_iff_comap_le]
  exact le_sup_of_le_right (le_iSup (fun s : ℝ => MeasurableSpace.comap (fun ω => S.η ω s) inferInstance) s)

end Tightness

/-- **`TightnessSelectionStep`** from eq:meps-scaling. -/
theorem tightnessSelectionStep_of_meps {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) :
    TightnessSelectionStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS D hDρ hDo hDc e he E u C hdata hae
  obtain ⟨hEm, hEe, hEt, hum, -, hCp, -, hbd⟩ := hdata
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
  filter_upwards [hae, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hω hη hp
  obtain ⟨hmono, hconvY⟩ := hΦ ω
  have hbddY : ∀ c, ∃ M, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
    intro c
    refine ⟨Cm * C ω, ?_⟩
    filter_upwards [hmev ω] with n hn
    have hC := hCp ω
    refine Tightness.abs_proxyValue_le (mul_pos hCm hC).le fun k hk => ?_
    have hkD : k ∈ cellVertices (E ω n) (S.η ω) D := Tightness.mem_cellVertices_of_vertexPoint_mem (hEpos ω n) hk
    show |(S.mε (E ω n))⁻¹ * u ω n k| ≤ Cm * C ω
    have hE := hEpos ω n
    rw [abs_mul, abs_of_nonneg hn.1]
    calc (S.mε (E ω n))⁻¹ * |u ω n k| ≤ (Cm * E ω n) * (C ω / E ω n) :=
          mul_le_mul hn.2 (hbd ω n k hkD) (abs_nonneg _) (mul_pos hCm hE).le
      _ = Cm * C ω * (E ω n * (E ω n)⁻¹) := by ring
      _ = Cm * C ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
  have hY : ∀ c, ∃ l, Tendsto (fun k => Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω)
      (Φ ω k) c) atTop (𝓝 l) := fun c => hconvY c (hbddY c)
  obtain ⟨ubar, h1, h2, h3⟩ := Tightness.tightness_of_proxies hDo (isBounded_ball.subset hDρ) hη.1 hp hη.2.2.1
    (hEpos ω) (hEt ω) hCm (hmev ω) hω.1 hmono hY
  exact ⟨hmono, ubar, h1, h2, fun hH => h3 (hω.2 hH)⟩

/-- **Lemma 3.1 (corrected)** from eq:meps-scaling and the analytic step. -/
theorem discretePotentialTightness_of_equicontinuity {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (hEq : TightnessEquicontinuityStep 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightness_of_steps 𝒮 hEq (tightnessSelectionStep_of_meps hm)

end MatedCRT
