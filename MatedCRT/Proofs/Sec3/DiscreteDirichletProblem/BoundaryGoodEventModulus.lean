import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryModulusProbability
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryPairLocal

/-! Boundary-pair moduli with measurable versions on high-probability events. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A dyadic pathwise modulus yields a probability modulus if the bad events
are null measurable after restriction to events of probability tending to one. -/
theorem mesh_modulus_of_ae_dyadic_modulus_on_good_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℝ → ℝ → Set Ω) (G : ℝ → Set Ω)
    (hmono : ∀ δ δ' ε, δ ≤ δ' → E δ ε ⊆ E δ' ε)
    (hnull : ∀ δ ε : ℝ, 0 < ε → NullMeasurableSet (E δ ε ∩ G ε) P)
    (hgood : Tendsto (fun ε => P (G ε)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hpath : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ω ∉ E δ (ε n))
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (E δ ε) ≤ e := by
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨δ, hδ, hmod⟩ := mesh_modulus_of_ae_dyadic_modulus P
    (fun δ ε => E δ ε ∩ G ε)
    (fun δ δ' ε hδ ω hω => ⟨hmono δ δ' ε hδ hω.1, hω.2⟩) hnull
    (by
      intro ε hε
      filter_upwards [hpath ε hε] with ω ⟨δ, hδ, hω⟩
      exact ⟨δ, hδ, hω.mono fun _ hn hmem => hn hmem.1⟩) he2
  have hsmall := ENNReal.tendsto_nhds_zero.1 hgood (e / 2) he2
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmod, hsmall] with ε hmodε hsmallε
  calc
    P (E δ ε) ≤ P (E δ ε ∩ G ε ∪ (G ε)ᶜ) :=
      measure_mono (fun ω hω => by by_cases hg : ω ∈ G ε <;> simp_all)
    _ ≤ P (E δ ε ∩ G ε) + P (G ε)ᶜ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hmodε hsmallε
    _ = e := ENNReal.add_halves e

/-- On a null-measurable good event, local agreement with an environment-
measurable vertex field makes the boundary-pair event null measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_rescale_boundary_pair_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (F v : Ω → ℤ → ℝ)
    (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a)
    (G : Set Ω) (hG : NullMeasurableSet G S.P)
    (K B : Set ℂ) (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K)
    (hv : ∀ᵐ ω ∂S.P, ω ∈ G →
      ∀ a ∈ cellVertices ε (S.η ω) K, v ω a = F ω a) (δ t : ℝ) :
    NullMeasurableSet ({ω | ∃ x ∈ K, ∃ y ∈ B, dist x y < δ ∧
      t < |rescale (S.mε ε) ε (S.η ω) (F ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ω) y|} ∩ G) S.P := by
  have hm := hS.nullMeasurableSet_rescale_boundary_pair_local ε hε v v hvm K B hK hB hBK
    (Filter.Eventually.of_forall fun _ _ _ => rfl) δ t
  apply (hm.inter hG).congr
  filter_upwards [hv, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hvω harea hp
  have heq : ω ∈ G → ∀ x ∈ K,
      rescale (S.mε ε) ε (S.η ω) (v ω) x =
        rescale (S.mε ε) ε (S.η ω) (F ω) x := by
    intro hg x hx
    have hcell := Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
    have ha : vertexOf ε (S.η ω) x ∈ cellVertices ε (S.η ω) K := ⟨x, hcell, hx⟩
    simp only [rescale, hvω hg _ ha]
  apply propext
  by_cases hg : ω ∈ G
  · simp only [Set.mem_inter_iff, hg, and_true, mem_ofPred_eq]
    constructor <;> rintro ⟨x, hx, y, hy, hxy, hval⟩ <;>
      exact ⟨x, hx, y, hy, hxy, by simpa only [heq hg x hx, heq hg y (hBK hy)] using hval⟩
  · simp [hg]

end MatedCRT

#print axioms MatedCRT.mesh_modulus_of_ae_dyadic_modulus_on_good_events
#print axioms MatedCRT.MatedCRTEnv.IsValid.nullMeasurableSet_rescale_boundary_pair_on_event
