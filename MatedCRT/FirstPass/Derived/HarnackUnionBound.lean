import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Derived.HarnackAssembly
import MatedCRT.FirstPass.Derived.HarnackAlmostSure
import MatedCRT.FirstPass.Derived.HarnackGridCount
import MatedCRT.FirstPass.Derived.GreenUpperBoundOfInputs
import LatticeProb.Probability.PolyHighProbUnionFamily
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly

/-!
# Union bound over the grid circles of the Harnack inequality

Berestycki–Gwynne (2020), Proposition 3.8, from the ring events of Lemma 3.10.  The ring event
`RingSeparates` at a grid circle `∂B_{s'}(z')` fails with probability at most `C ε^{α₀}` as soon as
`ε^{β₀} ≤ s'` and `2 s' ≤ ρ' - |z'|` (Lemma 3.10, taken as the hypothesis `hRing`).  The grid
`z' = h (m + n i)`, `s' = (√2)^a` with `h = ε^{2β}`, `s₀ = ε^β` has at most `125 ε^{-5β}` indices, so for
`10 β < α₀` all ring events hold simultaneously with polynomially high probability.  Together with the cell
size estimate (cells meeting `B_ρ` have diameter at most `ε^{1/(2+γ)²}`) and the almost-sure qualitative
properties of a valid environment, the deterministic step `greenKernel_le_inv_mul_of_ringEvents` gives the
Harnack inequality for the Green kernel on circles with constant `p⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace MatedCRT

/-- Admissible indices of grid circles: centre `z' = h (m + n i)` of norm `< ρ'`, radius `s' = (√2)^a ≥ s₀`,
and `2 s' ≤ ρ' - |z'|`. -/
def RingIdxOk (ρ' h s₀ : ℝ) (i : ℤ × ℤ × ℤ) : Prop :=
  ‖latticePt h i.1 i.2.1‖ < ρ' ∧ s₀ ≤ sqrt2Pow i.2.2 ∧
    2 * sqrt2Pow i.2.2 ≤ ρ' - ‖latticePt h i.1 i.2.1‖

/-- **Union bound over the grid circles.**  If the ring event fails with probability at most `C ε^{α₀}` at every
admissible circle of radius at least `ε^{β₀}`, and `5 β < α₀`, `β ≤ β₀`, then with polynomially high probability
all ring events at admissible grid circles (`h = ε^{2β}`, `s₀ = ε^β`) hold. -/
theorem polyHighProb_ringEvents {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (m : ℝ → Ω → ℤ → ℤ → ℕ) (η : Ω → ℝ → ℂ) {β β₀ α₀ ρ' p C : ℝ} (hβ : 0 < β) (hββ₀ : β ≤ β₀)
    (h5 : 5 * β < α₀) (hC : 0 ≤ C)
    (hbad : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
      2 * s' ≤ ρ' - ‖z'‖ →
      P {ω | ¬ RingSeparates (m ε ω) ε (η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    PolyHighProb P fun ε => {ω | ∀ i ∈ gridIndexBox (ε ^ (2 * β)) (ε ^ β),
      RingIdxOk ρ' (ε ^ (2 * β)) (ε ^ β) i →
        RingSeparates (m ε ω) ε (η ω) p (latticePt (ε ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2)} := by
  refine Gauss.polyHighProb_forall_mem_finset P (fun ε => gridIndexBox (ε ^ (2 * β)) (ε ^ β))
    (fun ε i => {ω | RingIdxOk ρ' (ε ^ (2 * β)) (ε ^ β) i →
      RingSeparates (m ε ω) ε (η ω) p (latticePt (ε ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2)})
    (K := 125) (c := 5 * β) (C := C) (α := α₀) (by norm_num) hC h5
    (fun r hr hr1 => card_gridIndexBox_rpow_le hβ hr hr1) (fun r hr hr1 i _ => ?_)
  by_cases hok : RingIdxOk ρ' (r ^ (2 * β)) (r ^ β) i
  · refine (measure_mono ?_).trans (hbad r hr hr1 _ hok.1 _ ?_ hok.2.2)
    · intro ω hω hring
      exact hω fun _ => hring
    · exact (Real.rpow_le_rpow_of_exponent_ge hr hr1.le hββ₀).trans hok.2.1
  · have hempty : ({ω | RingIdxOk ρ' (r ^ (2 * β)) (r ^ β) i →
        RingSeparates (m r ω) r (η ω) p (latticePt (r ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2)})ᶜ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hω ?_
      show RingIdxOk _ _ _ i → _
      exact fun h => absurd h hok
    rw [hempty, measure_empty]
    exact zero_le

/-- The qualitative almost-sure properties of a valid environment used by the Harnack step. -/
def HarnackQual {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) : Prop :=
  Continuous (S.η ω) ∧ ∀ ε : ℝ, 0 < ε →
    IsLocallyFiniteMult (S.mult ε ω) ∧ (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧
    (∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
    ∀ R : ℝ, (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) R)).Finite

/-- **Harnack inequality for the Green kernel on circles** (Berestycki–Gwynne 2020, Proposition 3.8) from the cell
size estimate and the ring events of Lemma 3.10 (`hRing`). -/
theorem hHarn_of_ring {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ s : ℝ,
        ε ^ β ≤ s → s ≤ (1 - ρ) / 8 →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) b) s)),
        ∀ y ∈ cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) b) s)),
          greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) a b ≤
            C₁ * greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) y b} := by
  intro γ hγ hγ2
  obtain ⟨β₀, α₀, hβ₀, hα₀, hring⟩ := hRing γ hγ hγ2
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have h2e : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he]
    ring
  set β : ℝ := min β₀ (min (e / 2) (α₀ / 10)) with hβdef
  have hβ0 : 0 < β := lt_min hβ₀ (lt_min (by positivity) (by positivity))
  have hββ₀ : β ≤ β₀ := min_le_left _ _
  have hβe : β ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hβα : β ≤ α₀ / 10 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨β, hβ0, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨p, hp0, hp1, hringp⟩ := hring ((1 + ρ) / 2) (by linarith) (by linarith)
  refine ⟨p⁻¹, inv_pos.2 hp0, fun Ω _ S hS => ?_⟩
  obtain ⟨C, hC⟩ := hringp Ω S hS
  have hU : Gauss.PolyHighProb S.P _ := polyHighProb_ringEvents (P := S.P) S.mult S.η hβ0 hββ₀ (ρ' := (1 + ρ) / 2) (p := p)
    (C := max C 0) (by linarith) (le_max_right _ _) (fun ε hε hε1 z' hz s' hs hs2 =>
      (hC ε hε hε1 z' hz s' hs hs2).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _))))
  have hsz : Gauss.PolyHighProb S.P _ := hsize γ hγ hγ2 e ρ he0 he1 hρ hρ1 Ω S hS
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | HarnackQual S ω} := hS.ae_harnack_inputs hγ hγ2
  have h2 := polyHighProb_inter_ae (polyHighProb_inter hU hsz) hW
  obtain ⟨r₁, hr₁, hr₁t⟩ := exists_rpow_le_of_small hβ0 (show (0 : ℝ) < 1 / 10 by norm_num)
  refine polyHighProb_mono_of_eventually h2 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r₁ 1 from lt_min hr₁ one_pos)] with ε hε
  rintro ω ⟨⟨hUω, hSzω⟩, hWω⟩
  obtain ⟨hηc, hall⟩ := hWω
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hεr : ε < r₁ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  obtain ⟨hlf, hcons, hedge, hfin⟩ := hall ε hε0
  have ht : ε ^ β ≤ 1 / 10 := hr₁t ε hε0 hεr
  have ht0 : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have ht2 : ε ^ (2 * β) = (ε ^ β) ^ 2 := by
    rw [show 2 * β = β * 2 by ring, Real.rpow_mul hε0.le, Real.rpow_two]
  have hδ : ε ^ e ≤ (ε ^ β) ^ 2 := by
    rw [← ht2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have hbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε (S.η ω) k) := fun k =>
    (isCompact_Icc.image hηc).isBounded
  refine greenKernel_le_inv_mul_of_ringEvents (ρ := ρ) (δ := ε ^ e) (h := ε ^ (2 * β))
    (s₀ := ε ^ β) (p := p) hε0.le hηc hlf hcons hedge hρ (Real.rpow_pos_of_pos hε0 _) hp0
    (hfin _) ?_ ?_ ?_ ?_
  · intro b hb x hx x' hx'
    have hd := (hSzω b hb).2
    rw [h2e] at hd
    exact (Metric.dist_le_diam_of_mem (hbdd b) hx hx').trans hd
  · rw [ht2]
    nlinarith
  · rw [ht2]
    nlinarith
  · intro m' n' a' hz hs hs2
    have hn := norm_nonneg (latticePt (ε ^ (2 * β)) m' n')
    exact hUω (m', n', a') (mem_gridIndexBox (Real.rpow_pos_of_pos hε0 _) ht0 (by linarith) hs
      (by linarith)) ⟨hz, hs, hs2⟩

/-- **The crude Green kernel upper bound** (Berestycki–Gwynne 2020, Lemma 5.4) with the Harnack inequality on
circles (`hHarn`) derived from the ring events of Lemma 3.10 (`hRing`) and the cell size estimate. -/
theorem greenKernelUpperBoundStmt_of_ring {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hsum : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ s : ℝ,
        ε ^ β ≤ s → s ≤ (1 - ρ) / 8 →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)) ∧
            k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) b) s)) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) *
            (diam (cell ε (S.η ω) k) /
              infDist (vertexPoint ε (S.η ω) b) (cell ε (S.η ω) k)) ^ 2 ≤
            C₂ * Real.log (1 / s)})
    (hpath : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)),
        ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).IsChain
            fun a c => S.mult ε ω a c ≠ 0) ∧
        (∀ᵐ θ ∂uniformDirection, ∃ p,
          segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ = b :: p ∧
          (∀ v ∈ b :: p, v ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) ∧
          (b :: p).getLast (List.cons_ne_nil b p) ∉
            interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)))}) :
    GreenKernelUpperBoundStmt 𝒮 :=
  greenKernelUpperBoundStmt_of_inputs hsize (hHarn_of_ring hsize hRing) hsum hpath

end MatedCRT
