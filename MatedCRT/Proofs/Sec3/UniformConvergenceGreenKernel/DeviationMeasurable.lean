import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OscillationMeasurable
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentKernel
import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel

/-! # Measurable versions of uniform deviation events for the rescaled Green kernel

The event `{sup_{x ∈ K} |ḡ^ε(x) - V(x)| > δ}` for a compact `K` and a function `V` continuous on
`K` has a `σ(h, η)`-measurable version. The supremum is reduced to countably many events: a cell
index `a`, a rational level `q` separating `ḡ^ε` on the cell from `V ± δ`, and the compact sets
`K ∩ {V ≤ q - δ}`, `K ∩ {V ≥ q + δ}` (closed-set events of the curve, `FiniteCellEvents`). -/

namespace MatedCRT

open Set MeasureTheory Topology Metric Filter

/-- The countable form of the deviation event is measurable. -/
theorem measurableSet_bounded_index_deviation
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (u : Ω → ℤ → ℝ) (hu : ∀ a, Measurable fun ω => u ω a)
    (ε δ : ℝ) (K : Set ℂ) (hK : IsCompact K) (V : ℂ → ℝ) (hV : ContinuousOn V K)
    (hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty) :
    MeasurableSet {ω | ∃ N a : ℤ, ∃ q : ℚ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      (((q : ℝ) < u ω a ∧ ∃ x ∈ K ∩ V ⁻¹' Iic ((q : ℝ) - δ), x ∈ cell ε (η ω) a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∨
        (u ω a < (q : ℝ) ∧ ∃ x ∈ K ∩ V ⁻¹' Ici ((q : ℝ) + δ), x ∈ cell ε (η ω) a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j))} := by
  have hbound : ∀ N : ℤ, MeasurableSet {ω | ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j} := by
    intro N
    have h : ∀ j : ℤ, MeasurableSet {ω | ∀ x ∈ K, x ∉ cell ε (η ω) j} := by
      intro j
      convert ((isClosed_curve_cell_meets_compact ε j K hK).measurableSet.preimage hη).compl using 1
      ext ω
      simp
    convert MeasurableSet.iInter (fun j : ℤ => MeasurableSet.iInter fun (_ : j < N) => h j) using 1
    ext ω
    simp
  have hsingle : ∀ K' : Set ℂ, IsCompact K' → ∀ N a : ℤ, MeasurableSet {ω | ∃ x ∈ K',
      x ∈ cell ε (η ω) a ∧ ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j} := by
    intro K' hK' N a
    convert (measurableSet_exists_pair_mem_cells_avoiding ε 1 a a (Finset.Ico N a)
      (Finset.Ico N a) K' hK' hI).preimage hη using 1
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, hxa, hav⟩
      exact ⟨x, hx, x, hx, hxa, hxa, by simp, hav, hav⟩
    · rintro ⟨x, hx, _, _, hxa, _, _, hav, _⟩
      exact ⟨x, hx, hxa, hav⟩
  have hK1 : ∀ c : ℝ, IsCompact (K ∩ V ⁻¹' Iic c) := fun c =>
    hK.of_isClosed_subset (hV.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic)
      inter_subset_left
  have hK2 : ∀ c : ℝ, IsCompact (K ∩ V ⁻¹' Ici c) := fun c =>
    hK.of_isClosed_subset (hV.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  convert MeasurableSet.iUnion (fun N : ℤ => MeasurableSet.iUnion fun a : ℤ =>
    MeasurableSet.iUnion fun q : ℚ => (hbound N).inter
      (((measurableSet_lt (measurable_const : Measurable fun _ : Ω => (q : ℝ)) (hu a)).inter
        (hsingle _ (hK1 ((q : ℝ) - δ)) N a)).union
      ((measurableSet_lt (hu a) (measurable_const : Measurable fun _ : Ω => (q : ℝ))).inter
        (hsingle _ (hK2 ((q : ℝ) + δ)) N a)))) using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_union]

/-- On a compact region with a lower bound for cell indices, the deviation event of the
least-index cell map from `V` is equivalent to its countable form. -/
theorem bounded_index_deviation_iff
    (η : ℝ → ℂ) (u : ℤ → ℝ) (ε δ : ℝ) (K : Set ℂ) (V : ℂ → ℝ)
    (hbound : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε η j)
    (hsel : ∀ x ∈ K, x ∈ cell ε η (vertexOf ε η x)) :
    (∃ x ∈ K, δ < |u (vertexOf ε η x) - V x|) ↔
    ∃ N a : ℤ, ∃ q : ℚ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε η j) ∧
      (((q : ℝ) < u a ∧ ∃ x ∈ K ∩ V ⁻¹' Iic ((q : ℝ) - δ), x ∈ cell ε η a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε η j) ∨
        (u a < (q : ℝ) ∧ ∃ x ∈ K ∩ V ⁻¹' Ici ((q : ℝ) + δ), x ∈ cell ε η a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε η j)) := by
  classical
  have hbdd : ∀ N : ℤ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε η j) →
      ∀ x ∈ K, BddBelow {j : ℤ | x ∈ cell ε η j} := by
    intro N hN x hx
    refine ⟨N, ?_⟩
    intro j hj
    exact le_of_not_gt (fun hjN => hN j hjN x hx hj)
  have heq : ∀ N : ℤ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε η j) → ∀ x ∈ K, ∀ a : ℤ,
      x ∈ cell ε η a → (∀ j ∈ Finset.Ico N a, x ∉ cell ε η j) → vertexOf ε η x = a := by
    intro N hN z hz k hzk hexcl
    apply le_antisymm
    · exact csInf_le (hbdd N hN z hz) hzk
    · by_contra h
      have hlt : vertexOf ε η z < k := lt_of_not_ge h
      by_cases hn : vertexOf ε η z < N
      · exact hN _ hn z hz (hsel z hz)
      · exact hexcl _ (Finset.mem_Ico.mpr ⟨le_of_not_gt hn, hlt⟩) (hsel z hz)
  constructor
  · rintro ⟨x, hx, hdev⟩
    obtain ⟨N, hN⟩ := hbound
    have hav : ∀ j ∈ Finset.Ico N (vertexOf ε η x), x ∉ cell ε η j := by
      intro j hj hjx
      exact (not_lt_of_ge (csInf_le (hbdd N hN x hx) hjx)) (Finset.mem_Ico.mp hj).2
    rcases lt_abs.1 hdev with h | h
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show V x + δ < u (vertexOf ε η x) by linarith)
      exact ⟨N, vertexOf ε η x, q, hN, Or.inl ⟨hq2, x, ⟨hx, by
        show V x ≤ (q : ℝ) - δ
        linarith⟩, hsel x hx, hav⟩⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u (vertexOf ε η x) < V x - δ by linarith)
      exact ⟨N, vertexOf ε η x, q, hN, Or.inr ⟨hq1, x, ⟨hx, by
        show (q : ℝ) + δ ≤ V x
        linarith⟩, hsel x hx, hav⟩⟩
  · rintro ⟨N, a, q, hN, h | h⟩
    · obtain ⟨hq, x, ⟨hx, hVx⟩, hxa, hav⟩ := h
      have hVx' : V x ≤ (q : ℝ) - δ := hVx
      refine ⟨x, hx, ?_⟩
      rw [heq N hN x hx a hxa hav]
      exact lt_abs.2 (Or.inl (by linarith))
    · obtain ⟨hq, x, ⟨hx, hVx⟩, hxa, hav⟩ := h
      have hVx' : (q : ℝ) + δ ≤ V x := hVx
      refine ⟨x, hx, ?_⟩
      rw [heq N hN x hx a hxa hav]
      exact lt_abs.2 (Or.inr (by linarith))

/-- The uniform deviation event of the rescaled Green kernel of Lemma 3.3 from a function
continuous on a compact set has a `σ(h, η)`-measurable version. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_greenKernel_deviation
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) (z y : ℂ) (K : Set ℂ) (hK : IsCompact K)
    (V : ℂ → ℝ) (hV : ContinuousOn V K) (δ : ℝ) :
    ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∃ x ∈ K, δ < |rescaledBallGreenKernel S r z y ε ω x - V x|) := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  obtain ⟨g, hgm, hg⟩ := hS.exists_envSigma_measurable_greenKernel_vertexOf hε (ball z r)
    (Or.inl isOpen_ball) y
  let u : Ω → ℤ → ℝ := fun ω a => (S.mε ε)⁻¹ * (ε⁻¹ * g ω a)
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a :=
    fun a => measurable_const.mul (measurable_const.mul (hgm a))
  have hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty := by
    intro k
    exact ⟨ε * (k - 1), le_rfl, mul_le_mul_of_nonneg_left (by linarith) hε.le⟩
  let A : Set Ω := {ω | ∃ N a : ℤ, ∃ q : ℚ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      (((q : ℝ) < u ω a ∧ ∃ x ∈ K ∩ V ⁻¹' Iic ((q : ℝ) - δ), x ∈ cell ε (η ω) a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∨
        (u ω a < (q : ℝ) ∧ ∃ x ∈ K ∩ V ⁻¹' Ici ((q : ℝ) + δ), x ∈ cell ε (η ω) a ∧
          ∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j))}
  refine ⟨A, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    exact measurableSet_bounded_index_deviation η hηm u hum ε δ K hK V hV hI
  · filter_upwards [hη, hg, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
      with ω hηω hgω harea hp
    have hfin := Tightness.cellVertices_finite harea.1 hp hε hK.isBounded
    obtain ⟨N, hN⟩ := hfin.bddBelow
    have hbound : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j := by
      refine ⟨N, ?_⟩
      intro j hj x hx hcell
      have hjN : N ≤ j := hN ⟨x, by simpa [hηω] using hcell, hx⟩
      exact (not_lt_of_ge hjN) hj
    have hsel : ∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x) := by
      intro x hx
      rw [hηω]
      exact Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
    have hiff := bounded_index_deviation_iff (η ω) (u ω) ε δ K V hbound hsel
    change (∃ N a : ℤ, ∃ q : ℚ, _) ↔ _
    rw [← hiff]
    simp only [hηω, u, hgω, rescale, rescaledBallGreenKernel]

end MatedCRT
