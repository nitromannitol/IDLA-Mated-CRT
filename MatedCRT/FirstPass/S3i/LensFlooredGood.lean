import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.FirstPass.S3i.LensFloored

/-!
# The floored common good event (MQ-li-9 steps 1 and 3)

The good event of Lemma 3 (plan section 3) under the floored boundary estimate. The one-sided boundary clause
is the floored one `FP36OneSidedBEFlooredAt` at the floor exponent `β`, and the cell exponent `b` is only required to
satisfy `b ≤ β` and `b ≤ 2 / (2 + γ) ^ 2 - b`,
so that `b := min (1 / (2 + γ) ^ 2) β` is admissible. The inequality replaces the equality only at the mesh bound
`ε ^ (2 / (2 + γ) ^ 2 - b) ≤ ε ^ b`, which holds for `0 < ε ≤ 1`.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The floored one-sided boundary estimate at the fixed floor exponent `β`, in the form used by the lens step:
for every `ρ`, `Ω`, `S`, there are exponents and a polynomially high probability event on which
`FP36OneSidedBEFlooredAt` holds at radius `ρ`. -/
def FlooredBEFixedBeta (𝒮 : SpaceFillingSLEModel) (γ β : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ κ ν A b : ℝ, 0 < κ ∧ 0 < ν ∧ 0 < A ∧ 0 < b ∧
  PolyHighProb S.P fun ε => {ω | FP36OneSidedBEFlooredAt (S.mult ε ω) ε (S.η ω) ρ ν A β}

/-- The uniform form gives the fixed-`β` form for the `β` of its existential. -/
theorem flooredBEFixedBeta_of_uniform {𝒮 : SpaceFillingSLEModel}
    (hU : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ FlooredBEFixedBeta 𝒮 γ β := by
  obtain ⟨β, hβ0, hβ1, hbody⟩ := hU γ hγ0 hγ2
  exact ⟨β, hβ0, hβ1, hbody⟩

/-- **Lemma 3 core, floored (MQ-li-9).** At fixed `γ`, `β`, `b`, `ρ`, `ρ₀`, `ρ₁`: the good event is the intersection of
the cell-size event (`CellSizeEstimateStmt` at `ζ = b`, radius `ρ₁`), the floored one-sided boundary event at radius
`ρ₁`, the area-parametrization event and the regular-map event. -/
theorem fp36_good_core_floored {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    (hm : MepsScalingInput 𝒮) {γ β : ℝ} (hBE : FlooredBEFixedBeta 𝒮 γ β)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {b ρ ρ₀ ρ₁ : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hble : b ≤ 2 / (2 + γ) ^ 2 - b)
    (hρ0 : 0 < ρ) (hρρ₀ : ρ < ρ₀) (hρ₀ρ₁ : ρ₀ < ρ₁) (hρ₁1 : ρ₁ < 1) (hmid : (1 + ρ₀) / 2 = ρ₁)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (r : ℝ) (z y : ℂ) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) :
    ∃ ν A κ C₁ ε₀ : ℝ, 0 < ν ∧ 0 < A ∧ 0 < κ ∧ 0 ≤ C₁ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∃ G : ℝ → Set Ω, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < S.mε ε ∧ 8 * ε ^ b < r ∧ 64 * ε ^ b ≤ ε ^ (b / 2) ∧
      closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ ∧
      S.P (G ε)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ κ) ∧
      ∀ ω ∈ G ε, FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω := by
  have hρ₀0 : 0 < ρ₀ := by linarith
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₀1 : ρ₀ < 1 := by linarith
  obtain ⟨-, ν, A, -, -, hν, hA, -, hBEP⟩ := hBE ρ₁ hρ₁0 hρ₁1 Ω S hS
  let Ecell : ℝ → Set Ω := fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + b) ≤ diam (cell ε (S.η ω) k) ∧
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - b)}
  let Ebe : ℝ → Set Ω := fun ε => {ω | FP36OneSidedBEFlooredAt (S.mult ε ω) ε (S.η ω) ρ₁ ν A β}
  let Area : Set Ω := {ω | IsAreaParametrized (S.μ ω) (S.η ω)}
  let Reg : Set Ω := {ω | ∀ ε : ℝ, 0 < ε → IsRegularMatedMap (S.mult ε ω) ε (S.η ω)}
  let G : ℝ → Set Ω := fun ε => (Ecell ε ∩ Ebe ε) ∩ (Area ∩ Reg)
  have hcellP : PolyHighProb S.P Ecell := h28 γ hγ0 hγ2 b ρ₁ hb hb1 hρ₁0 hρ₁1 Ω S hS
  have hbeP : PolyHighProb S.P Ebe := hBEP
  have harea : ∀ᵐ ω ∂S.P, ω ∈ Area := hS.isAreaParametrized
  have hreg : ∀ᵐ ω ∂S.P, ω ∈ Reg := ae_isRegularMatedMap (adjacentCellsMeetAeStep 𝒮) hγ0 hγ2 hS
  have hgood : PolyHighProb S.P G :=
    polyHighProb_inter (polyHighProb_inter hcellP hbeP)
      (polyHighProb_inter (polyHighProb_const_of_ae harea) (polyHighProb_const_of_ae hreg))
  obtain ⟨κ, hκ, C, r₀, hr₀, hPb⟩ := hgood
  obtain ⟨Cm, hCm, hmev⟩ := hm γ hγ0 hγ2
  obtain ⟨εm, hεm, hmS⟩ := hmev Ω S hS
  obtain ⟨δ1, hδ1, h1⟩ := rpow_lt_of_small hb (div_pos hr (by norm_num : (0 : ℝ) < 8))
  obtain ⟨δ2, hδ2, h2⟩ := rpow_lt_of_small (half_pos hb) (by norm_num : (0 : ℝ) < 1 / 64)
  have hd0 : 0 < r - dist y z := by
    rw [mem_ball] at hy
    linarith
  obtain ⟨δ3, hδ3, h3⟩ := rpow_lt_of_small hb hd0
  obtain ⟨δ4, hδ4, h4⟩ := rpow_lt_of_small hb (by linarith : (0 : ℝ) < (ρ₀ - ρ) / 4)
  have hnorm : ‖z‖ + r ≤ ρ := norm_add_le_of_ball_subset hr hball
  have hε₀ : 0 < min r₀ (min εm (min δ1 (min δ2 (min δ3 (min δ4 1))))) :=
    lt_min hr₀ (lt_min hεm (lt_min hδ1 (lt_min hδ2 (lt_min hδ3 (lt_min hδ4 one_pos)))))
  have hε₀le : min r₀ (min εm (min δ1 (min δ2 (min δ3 (min δ4 1))))) ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨ν, A, κ, max C 0, min r₀ (min εm (min δ1 (min δ2 (min δ3 (min δ4 1))))), hν, hA, hκ,
    le_max_right C 0, hε₀, hε₀le, G, ?_⟩
  intro ε hε hεε₀
  obtain ⟨hεr₀, hεrest⟩ := lt_min_iff.1 hεε₀
  obtain ⟨hεm', hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε1, hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε2, hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε3, hεrest⟩ := lt_min_iff.1 hεrest
  obtain ⟨hε4, hε5⟩ := lt_min_iff.1 hεrest
  have hmpos : 0 < S.mε ε :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 (by linarith)) (inv_pos.2 hε)) ((hmS ε hε hεm').1)
  have hδ8 : 8 * ε ^ b < r := by linarith [h1 ε hε hε1]
  have hsb : ε ^ b = ε ^ (b / 2) * ε ^ (b / 2) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  have hs64 : 64 * ε ^ b ≤ ε ^ (b / 2) := by
    have hsn : 0 ≤ ε ^ (b / 2) := Real.rpow_nonneg hε.le _
    have hs1 : ε ^ (b / 2) < 1 / 64 := h2 ε hε hε2
    calc 64 * ε ^ b = (64 * ε ^ (b / 2)) * ε ^ (b / 2) := by rw [hsb]; ring
      _ ≤ 1 * ε ^ (b / 2) := mul_le_mul_of_nonneg_right (by linarith) hsn
      _ = ε ^ (b / 2) := one_mul _
  have hcl : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ := by
    have h4' : ε ^ b < (ρ₀ - ρ) / 4 := h4 ε hε hε4
    refine (closure_ball_subset_closedBall).trans ?_
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    have htri : dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
    have hz0 : dist z 0 = ‖z‖ := dist_zero_right z
    linarith
  have hprob : S.P (G ε)ᶜ ≤ ENNReal.ofReal (max C 0 * ε ^ κ) :=
    (hPb ε hε (lt_of_lt_of_le hεr₀ le_rfl)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hε.le κ)))
  refine ⟨hmpos, hδ8, hs64, hcl, hprob, ?_⟩
  intro ω hω
  obtain ⟨⟨hcellω, hbeω⟩, ⟨hareaω, hregω⟩⟩ := hω
  have hreg' : IsRegularMatedMap (S.mult ε ω) ε (S.η ω) := hregω ε hε
  have hsurj : Function.Surjective (S.η ω) := hareaω.2.2.1
  have hmesh : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ b := by
    intro k hk
    exact (hcellω k hk).2.trans (Real.rpow_le_rpow_of_exponent_ge hε hε5.le hble)
  have hmesh' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ((1 + ρ₀) / 2)).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ b := by
    rw [hmid]
    exact hmesh
  have hfe : ∀ U : Set ℂ, closure U ⊆ ball 0 ρ₀ →
      FiniteExitData (S.mult ε ω) (cellVertices ε (S.η ω) U) ∧
      FiniteExitData (S.mult ε ω) (interiorCellVertices ε (S.η ω) U) := by
    intro U hU
    have hUb : Bornology.IsBounded U := isBounded_ball.subset (subset_closure.trans hU)
    have hfin : (cellVertices ε (S.η ω) U).Finite :=
      cellVertices_finite_of_proper hreg'.continuous hreg'.proper hε hUb
    have hint : (interiorCellVertices ε (S.η ω) U).Finite :=
      hfin.subset (fun x hx => (show x ∈ cellVertices ε (S.η ω) U \ cellVertices ε (S.η ω) (frontier U) from hx).1)
    exact ⟨finiteExitData_of_finite hreg'.succ hreg'.locallyFinite hfin,
      finiteExitData_of_finite hreg'.succ hreg'.locallyFinite hint⟩
  have hballρ₀ : ball z r ⊆ ball 0 ρ₀ := hball.trans (Metric.ball_subset_ball hρρ₀.le)
  have hmarg : dist y z + ε ^ b < r := by linarith [h3 ε hε hε3]
  have hint0 : vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) :=
    TruncatedLaws.vertexOf_mem_interiorCellVertices_of_mesh hreg'.continuous hsurj hreg'.proper hε
      hballρ₀ hρ₀1 hy hmesh' hmarg
  unfold FP36GoodEnvFloored
  dsimp only
  exact ⟨hareaω, fun j k hjk => hreg'.cells_meet j k hjk, hmesh, hfe, hint0, hbeω⟩

/-- **Lemma 3, floored.** Under the uniform floored input, for each `γ`
there are a floor exponent `β` and a cell exponent `b ≤ β`, with `b := min (1 / (2 + γ) ^ 2) β`, such that the common
good event is the floored good event `FP36GoodEnvFloored` for every `ρ`, `Ω`, `S`. -/
theorem commonGood_fp36_floored {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (hU : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ β b : ℝ, 0 < β ∧ 0 < b ∧ b ≤ β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ y ∈ ball z r,
    let ρ₀ := (2 * ρ + 1) / 3
    let ρ₁ := (ρ + 2) / 3
    ρ < ρ₀ ∧ ρ₀ < ρ₁ ∧ ρ₁ < 1 ∧
    ∃ ν A κ C₁ ε₀ : ℝ,
      0 < ν ∧ 0 < A ∧ 0 < κ ∧ 0 ≤ C₁ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∃ G : ℝ → Set Ω,
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      let δ := ε ^ b
      let s := ε ^ (b / 2)
      0 < S.mε ε ∧
      8 * δ < r ∧
      64 * δ ≤ s ∧
      closure (ball z (r + 4 * δ)) ⊆ ball 0 ρ₀ ∧
      S.P (G ε)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ κ) ∧
      ∀ ω ∈ G ε,
        FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω := by
  intro γ hγ0 hγ2
  obtain ⟨β, hβ0, hβ1, hfix⟩ := flooredBEFixedBeta_of_uniform hU γ hγ0 hγ2
  have hpos4 : (0 : ℝ) < (2 + γ) ^ 2 := pow_pos (by linarith) 2
  have hb0 : 0 < min (1 / (2 + γ) ^ 2) β := lt_min (one_div_pos.2 hpos4) hβ0
  have hbβ : min (1 / (2 + γ) ^ 2) β ≤ β := min_le_right _ _
  have hbX : min (1 / (2 + γ) ^ 2) β ≤ 1 / (2 + γ) ^ 2 := min_le_left _ _
  have hX1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one hpos4]
    nlinarith
  have hbl1 : min (1 / (2 + γ) ^ 2) β < 1 := lt_of_le_of_lt hbX hX1
  have hble : min (1 / (2 + γ) ^ 2) β ≤ 2 / (2 + γ) ^ 2 - min (1 / (2 + γ) ^ 2) β := by
    have h2 : 2 / (2 + γ) ^ 2 = 2 * (1 / (2 + γ) ^ 2) := by ring
    linarith
  refine ⟨β, min (1 / (2 + γ) ^ 2) β, hβ0, hb0, hbβ, fun ρ hρ0 hρ1 Ω _ S hS r z hr hball y hy => ?_⟩
  obtain ⟨s1, s2, s3, s4⟩ := scale_facts hρ1
  exact ⟨s1, s2, s3, fp36_good_core_floored h28 hm hfix hγ0 hγ2 hb0 hbl1 hble hρ0 s1 s2 s3 s4 S hS r z y hr hball hy⟩

end FirstPass36
end MatedCRT
