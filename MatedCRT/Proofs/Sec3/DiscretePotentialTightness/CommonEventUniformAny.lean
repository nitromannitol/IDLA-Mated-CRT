import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.TwoMeshUniformSelection
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.CommonEventVertex

/-! # Common-event uniform selection without continuity of boundary limits -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

theorem boundedArctan_dist_le_four (x y : ℝ) :
    dist (boundedArctan x) (boundedArctan y) ≤ 4 := by
  change dist (Real.arctan x) (Real.arctan y) ≤ 4
  rw [Real.dist_eq]
  apply abs_le.mpr
  have hx := (boundedArctan x).property
  have hy := (boundedArctan y).property
  change -2 ≤ Real.arctan x ∧ Real.arctan x ≤ 2 at hx
  change -2 ≤ Real.arctan y ∧ Real.arctan y ≤ 2 at hy
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- One full-measure event supports uniform selection on arbitrary compact
    sets, without a continuity assumption on their limiting functions. -/
theorem MatedCRTEnv.IsValid.exists_commonEvent_uniform_rescale_any
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ B : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ B) ∧
      ∀ (e : ℕ → ℝ), (∀ n, 0 < e n) →
      ∀ (E : Ω → ℕ → ℝ), (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
        (∀ ω n, E ω n ∈ range e) →
      ∀ (u : ℕ → Ω → ℕ → ℤ → ℝ),
        (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
      ∀ (K : ℕ → Set ℂ), (∀ j, IsCompact (K j)) → ∀ (P : Ω → ℕ → Prop),
        (∀ ω ∈ B, ∀ j, P ω j → ∀ ψ : ℕ → ℕ, StrictMono ψ →
          ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
            TendstoUniformlyOn (fun n => rescale (S.mε (E ω (ψ (θ n))))
              (E ω (ψ (θ n))) (S.η ω) (u j ω (ψ (θ n)))) w atTop (K j)) →
      ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
        ∀ ω ∈ B, StrictMono (Φ ω) ∧ ∀ j, P ω j → ∃ w : ℂ → ℝ,
          TendstoUniformlyOn (fun n => rescale (S.mε (E ω (Φ ω n)))
            (E ω (Φ ω n)) (S.η ω) (u j ω (Φ ω n))) w atTop (K j) := by
  classical
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  let B : Set Ω := {ω | (η ω : ℝ → ℂ) = S.η ω ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ Function.Surjective (S.η ω)}
  have hB : ∀ᵐ ω ∂S.P, ω ∈ B := by
    filter_upwards [hη, hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hω hp ha
    exact ⟨hω, hp, ha.2.2.1⟩
  refine ⟨B, hB, ?_⟩
  intro e he E hEm hEr u hu K hK P hc
  have hex : ∀ ω n, ∃ j, E ω n = e j := fun ω n => by
    obtain ⟨j, hj⟩ := hEr ω n
    exact ⟨j, hj.symm⟩
  let I : Ω → ℕ → ℕ := fun ω n => Nat.find (hex ω n)
  have hI : ∀ n, Measurable[S.envSigma] fun ω => I ω n := by
    intro n
    let : MeasurableSpace Ω := S.envSigma
    exact Tightness.measurable_natFind (fun ω => hex ω n)
      (fun j => hEm n (measurableSet_singleton (e j)))
  have hIe : ∀ ω n, E ω n = e (I ω n) := fun ω n => Nat.find_spec (hex ω n)
  let v : Ω → ℕ → ℕ → ℤ → ℝ := fun ω j n a => (S.mε (E ω n))⁻¹ * u j ω n a
  have hvm : ∀ j n a, Measurable[S.envSigma] fun ω => v ω j n a := by
    intro j n a
    have hm : Measurable[S.envSigma] (fun ω => (S.mε (E ω n))⁻¹) :=
      @Tightness.measurable_comp_range Ω S.envSigma e (fun ω => E ω n) (hEm n)
        (fun ω => hEr ω n) (fun ε _ => (S.mε ε)⁻¹) (fun _ => measurable_const)
    exact hm.mul (hu j n a)
  let P' : Ω → ℕ → Prop := fun ω j => ω ∈ B ∧ P ω j
  have he' : ∀ n (k : ℤ), (Icc (e n * (k - 1)) (e n * k)).Nonempty := by
    intro n k
    exact ⟨_, le_rfl, mul_le_mul_of_nonneg_left (by linarith) (he n).le⟩
  obtain ⟨Φ, hΦm, hΦ⟩ := @exists_measurable_subsequence_two_mesh_uniform Ω (Icc (-2 : ℝ) 2)
    S.envSigma _ _ _ _ _ η hηm e he' I hI
    K hK v hvm boundedArctan boundedArctan_uniformContinuous boundedArctan_injective
    4 (by norm_num) boundedArctan_dist_le_four P' (by
      intro ω j hP n
      have hpos : 0 < E ω n := by rw [hIe]; exact he _
      have hfin := Tightness.cellVertices_finite (by rw [← hP.1.1]; exact (η ω).continuous)
        hP.1.2.1 hpos (hK j).isBounded
      obtain ⟨N, hN⟩ := hfin.bddBelow
      constructor
      · refine ⟨N, ?_⟩
        intro a ha x hx hcell
        have haN : N ≤ a := hN ⟨x, by simpa [hIe ω n, hP.1.1] using hcell, hx⟩
        exact (not_lt_of_ge haN) ha
      · intro x hx
        rw [← hIe ω n, hP.1.1]
        exact Tightness.mem_cell_vertexOf (by rw [← hP.1.1]; exact (η ω).continuous)
          hP.1.2.1 hP.1.2.2 hpos x) (by
      intro ω j hP ψ hψ
      obtain ⟨θ, hθ, w, hw⟩ := hc ω hP.1 j hP.2 ψ hψ
      refine ⟨θ, hθ, w, ?_⟩
      change TendstoUniformlyOn (fun n x => (S.mε (E ω (ψ (θ n))))⁻¹ *
        u j ω (ψ (θ n)) (vertexOf (E ω (ψ (θ n))) (S.η ω) x)) w atTop (K j) at hw
      simpa only [v, ← hIe, hP.1.1] using hw)
  refine ⟨Φ, hΦm, ?_⟩
  intro ω hω
  refine ⟨(hΦ ω).1, ?_⟩
  intro j hP
  obtain ⟨w, hw⟩ := (hΦ ω).2 j ⟨hω, hP⟩
  refine ⟨w, ?_⟩
  change TendstoUniformlyOn (fun n x => (S.mε (E ω (Φ ω n)))⁻¹ *
    u j ω (Φ ω n) (vertexOf (E ω (Φ ω n)) (S.η ω) x)) w atTop (K j)
  simpa only [v, ← hIe, hω.1] using hw

end MatedCRT
