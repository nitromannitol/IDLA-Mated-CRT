import MatedCRT.Proofs.IDLA.RandomOpenCell
import MatedCRT.FirstPass.S5r.ExistsCorrected
import MatedCRT.FirstPass.S2b

/-!
# Null-measurability of cell vertices for the corrected Lemma 2.4 (fp-S5r)

Copy of `MatedCRTEnv.IsValid.nullMeasurableSet_cellVertices_coneFamily` (Proofs/IDLA/RandomOpenCell.lean:53) with `h24`
retyped to `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (FirstPass/S2b.lean:43) and the family process taken from
`exists_measurable_familyProcess_corrected` (FirstPass/S5r/ExistsCorrected.lean). The uniqueness used in the proof comes
from `IsConeHarmonicBallFamily` (`hΛ`), not from Lemma 2.4. The original file is not edited.
-/

namespace MatedCRT

open Set MeasureTheory Metric Topology Filter
open Classical

theorem MatedCRTEnv.IsValid.nullMeasurableSet_cellVertices_coneFamily_corrected
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hfam : ConeFamilyAEMeasurableStep)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {t : ℝ} (ht : 0 < t) (ε : ℝ) (hε : 0 ≤ ε) (k : ℤ) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      k ∈ cellVertices ε (S.η ω) (Λ ω t)} S.P := by
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess_corrected hγ hγ2 hfam h24c
  obtain ⟨Y, Y₀, hIG₀, B, B', B₀, B₀', W, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let V : Ω → Set ℂ := fun ω => {z | X ω (t, z)}
  let U : Ω → Set ℂ := fun ω => openSetOfTrace (V ω)
  have hV (j : ℕ) : MeasurableSet {ω | densePoint j ∈ V ω} :=
    measurableSet_setOfPred.2 (hXm (t, densePoint j))
  have hE : MeasurableSet {ω | k ∈ cellVertices ε (η' ω) (U ω)} :=
    measurableSet_cellVertices_openSetOfTrace ε hε k η' hc.measurable_curves.2.1 V hV
  have hF := measurableSet_exitTest hXm t ρ
  refine (hF.inter hE).nullMeasurableSet.congr ?_
  filter_upwards [hΛ, hX, hbridge] with ω hΛω hXω hηω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  obtain ⟨hcl, htT⟩ := lt_clusterExitTime_iff_of_familyProcess hΛω hT hΛ' hstop hXω hρ hρ1 ht
  have heq : EqOn Λ' (Λ ω) (Ioo 0 T) := by
    have h := (hΛω.isConeHarmonicBallFamilyOn hT).eqOn hΛ'
    rwa [min_self] at h
  have hU : t < clusterExitTime (Λ ω) ρ → U ω = Λ ω t := by
    intro hx
    have ht' := htT hx
    have htrace : V ω = Λ ω t := by
      ext z
      change X ω (t, z) ↔ z ∈ Λ ω t
      rw [hXω t z, heq ht']
      exact and_iff_right ht'
    have hreg := hΛω.2.1.isRegularOpen t ht
    change openSetOfTrace (V ω) = Λ ω t
    rw [htrace]
    apply openSetOfTrace_eq
    · rw [← hreg]; exact isOpen_interior
    · exact hreg
  apply propext
  change ((∃ q : ℚ, t < q ∧ X ω ((q : ℝ), 0) ∧
      ∀ j, X ω ((q : ℝ), densePoint j) → ‖densePoint j‖ ≤ ρ / 3) ∧ _) ↔ _
  rw [← hcl]
  constructor <;> rintro ⟨hx, hy⟩ <;> refine ⟨hx, ?_⟩
  · simpa [hU hx, hηω.1] using hy
  · simpa [hU hx, hηω.1] using hy


end MatedCRT
