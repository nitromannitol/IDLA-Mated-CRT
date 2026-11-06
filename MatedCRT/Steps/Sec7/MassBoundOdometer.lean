import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section7
import MatedCRT.Steps.Sec7.OdometerBoundMass
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Sec7.MassBoundOdometer.Count
import MatedCRT.Proofs.Sec7.MassBoundOdometer.PolyHighProb
import MatedCRT.Proofs.WalkPotential.GreenFirstStep

/-!
# Lemma 7.2 (lemma:mass-bound-odometer, line 2991; proof lines 3000-3032): correction and steps

## The printed statement fails below the scale of Lemma 2.16 (ESCALATIONS E-c3-2)

`MassBoundOdometerStmt` (MatedCRT/Draft/Section7.lean) quantifies over all `s > 0`; the printed proof applies
Lemma 2.16 at the radius `s`, which needs `s ≥ ε^{ω₀}`, and it needs `V^ε(B_{𝐜₀ s}(z))` inside
`V^ε(B_s(z)) \ V^ε(∂B_s(z))`, i.e. `s` above the cell size. For `s` below the cell size the statement is false, for
every realization: take `z` in the cell of a vertex `x ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`, `x ∼ 0`, with `z` outside the cell of
`0`. For small `s`, `V^ε(B_s(z)) = V^ε(B_{𝐜₀ s}(z)) = X_z`, the (finitely many) vertices whose cells contain `z`. Let
`Θ` be the component of `0` in `V^ε(B_ρ) \ X_z`: it is connected, contains `0`, and `∂Θ ⊆ X_z ∪ V^ε(B_ρ)ᶜ`, where
`u^ε_t = 0` off `X_z`; so `sup_{∂Θ} u^ε_t ≤ max_{X_z} u^ε_t`. Now `t ↦ u^ε_t` is nondecreasing and continuous
(`u^ε_t ≤ u^ε_{t'} ≤ u^ε_t + (t' - t) ε⁻¹ g^ε_{B_ρ}(0, ·)` for `t < t'`) and `X_z` meets `Λ^ε_t` for large `t`
(`u^ε_t ≥ t ε⁻¹ g^ε_{B_ρ}(0, ·) - q^ε_{B_ρ}`); at times `t` slightly after the first time `X_z` meets `Λ^ε_t`, the left
side is `≥ 1` while `C sup_{∂Θ} u^ε_t < 1`. Hence the event of the lemma fails for every `ε` and the lemma is false.

The proof is correct for `s ≥ ε^β`, `β = β(γ) > 0` (`MassBoundOdometerAboveScaleStmt`), which is how the lemma is used
(proof of Proposition 7.1, lines 3168-3192: `s = r_k/4` with `𝐜₀ r_k/4 ≥ 10 ε^ω`; it suffices to take `ω ≤ β`: the
conclusion of lemma:constant-order-lower-bound-div for all `r ≥ 10 ε^ω` implies it for all `r ≥ 10 ε^{ω'}`,
`ω' ≤ ω`, so `ω` may be decreased there).

## Steps
* `MatedMapStructureStep`, `StoppedOdometerLaplacianStep` (MatedCRT/Steps/Sec7/OdometerBoundMass.lean) and
  `AdjacentCellsMeetAeStep` (MatedCRT/Steps/Infra/MatingOfTrees.lean);
* `GreenFnFirstVariableStep` (eq:discrete-green-laplacian, line 797; Lawler-Limic Prop. 6.2.3): deterministic,
  `Δ G_A(·, b) = -δ_b` on a finite set `A`; proved (`greenFnFirstVariableStep_holds`, first-step analysis), so
  `massBoundOdometerAboveScale_of_inputs` needs only the first three steps. The first two follow from
  `AdjacentCellsMeetAeStep` and Lemma 4.4 (MatedCRT/Steps/Sec7/OdometerBoundMass.lean), so
  `massBoundOdometerAboveScale_of_draft` rests on Lemmas 2.16, 2.8, 4.4 and `AdjacentCellsMeetAeStep` only.
The rest is proved: the maximum principle for `u^ε_t` off `Θ`, the comparison with `∑_b g_D(·, b)` and the counting
(MatedCRT/Proofs/Sec7/MassBoundOdometer).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

/-- **eq:discrete-green-laplacian** (line 797; Lawler-Limic Proposition 6.2.3): for a locally finite multigraph on
`ℤ` with `k ∼ k + 1` and a finite `A`, `Δ G_A(·, b) = -δ_b` on `A` (first-step analysis; deterministic). -/
def GreenFnFirstVariableStep : Prop :=
  ∀ m : ℤ → ℤ → ℕ, (∀ a, {b | m a b ≠ 0}.Finite) → (∀ k : ℤ, m k (k + 1) ≠ 0) →
    ∀ A : Set ℤ, A.Finite → ∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0)

/-- **Lemma 7.2 (corrected)** from Lemmas 2.16, 2.8 and the steps. -/
theorem massBoundOdometerAboveScale_of_steps (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hstr : MatedMapStructureStep 𝒮) (hlap : StoppedOdometerLaplacianStep 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) (hR1 : GreenFnFirstVariableStep) :
    MassBoundOdometerAboveScaleStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1
  obtain ⟨ω₀, hω₀, h216'⟩ := h216 γ hγ hγ2
  obtain ⟨C₁, hC₁, h216''⟩ := h216' ρ hρ hρ1
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = Real.exp (-(3 / 2) * C₁) / 36 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = min q ω₀ / 2 := ⟨_, rfl⟩
  have hqpos : 0 < q := by
    rw [hq]
    positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one (by positivity)]
    nlinarith
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hc₀lt : c₀ < 1 := by
    rw [hc₀]
    have : Real.exp (-(3 / 2) * C₁) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hβpos : 0 < β := by
    rw [hβ]
    exact div_pos (lt_min hqpos hω₀) two_pos
  have hqβ : 0 < q - β := by
    have := min_le_left q ω₀
    rw [hβ]
    linarith
  have hωβ : 0 < ω₀ - β := by
    have := min_le_right q ω₀
    rw [hβ]
    linarith
  have hrpow : ∀ {x K a : ℝ}, 0 ≤ x → 0 ≤ K → 0 < a → x ≤ K ^ a⁻¹ → x ^ a ≤ K := fun hx hK ha h =>
    (Real.rpow_le_rpow hx h ha.le).trans_eq (Real.rpow_inv_rpow hK ha.ne')
  refine ⟨2, c₀, β, two_pos, hc₀pos, hc₀lt, hβpos, fun Ω _ S hS => ?_⟩
  have hE1 := h216'' Ω S hS
  have hE2 := h28 γ hγ hγ2 q ρ hqpos hq1 hρ hρ1 Ω S hS
  have hae : ∀ᵐ ω ∂S.P, (∀ ε : ℝ, 0 < ε → (∀ a : ℤ, {b | S.mult ε ω a b ≠ 0}.Finite) ∧
        ∀ r : ℝ, (cellVertices ε (S.η ω) (closedBall 0 r)).Finite) ∧
      (∀ ε t : ℝ, 0 < ε → 0 < t → ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t, a ≠ 0 →
        matedLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a =
          ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
      (∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
      IsAreaParametrized (S.μ ω) (S.η ω) := by
    filter_upwards [hstr γ hγ hγ2 Ω S hS, hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS, hadj γ hγ hγ2 Ω S hS,
      hS.isAreaParametrized] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine Sec7.polyHighProb_of_inter_ae hE1 hE2 hae
    (lt_min (lt_min (Real.rpow_pos_of_pos hc₀pos (q - β)⁻¹) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
      (ω₀ - β)⁻¹)) (by linarith : (0 : ℝ) < 16 * c₀))
    fun ε hε hεε₁ ω hω1 hω2 hqω => ?_
  obtain ⟨hstrω, hlapω, hadjω, hareaω⟩ := hqω
  obtain ⟨hlf, hfin⟩ := hstrω ε hε
  intro t ht Θ hΘ _ h0 s z hs hsβ hsz
  have hεA : ε ≤ c₀ ^ (q - β)⁻¹ := hεε₁.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεB : ε ≤ (1 / 4 : ℝ) ^ (ω₀ - β)⁻¹ := hεε₁.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεD : ε ≤ 16 * c₀ := hεε₁.le.trans (min_le_right _ _)
  have hεβ : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le _
  have hexp : 2 / (2 + γ) ^ 2 - q = q := by
    rw [hq]
    ring
  have hδ : ε ^ (2 / (2 + γ) ^ 2 - q) ≤ c₀ * s := by
    rw [hexp, show ε ^ q = ε ^ (q - β) * ε ^ β by rw [← Real.rpow_add hε, sub_add_cancel]]
    exact mul_le_mul (hrpow hε.le hc₀pos.le hqβ hεA) hsβ hεβ hc₀pos.le
  have hω : ε ^ ω₀ ≤ s / 4 := by
    rw [show ε ^ ω₀ = ε ^ (ω₀ - β) * ε ^ β by rw [← Real.rpow_add hε, sub_add_cancel]]
    have := mul_le_mul (hrpow hε.le (by norm_num) hωβ hεB) hsβ hεβ (by norm_num)
    linarith
  have hεc : 1 / (16 * c₀) ≤ ε⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le hε hεD
  exact Sec7.ncard_cellVertices_inter_cluster_le hε ht hρ hareaω.1 hareaω.2.2.1 (S.mult_symm ε ω) hlf
    (S.mult_succ_ne_zero hε.le ω) (hfin ρ) (hadjω ε hε) (hlapω ε t hε ht)
    (fun A hA => hR1 _ hlf (S.mult_succ_ne_zero hε.le ω) A hA) hC₁ hc₀ (fun k hk => (hω2 k hk).2)
    (fun a ha r h1 h2 b hb => (hω1 a ha r h1 h2 b hb).2) hΘ h0 hs hδ hω hεc hsz

/-- `GreenFnFirstVariableStep` holds: first-step analysis (MatedCRT/Proofs/WalkPotential/GreenFirstStep.lean). -/
theorem greenFnFirstVariableStep_holds : GreenFnFirstVariableStep :=
  fun _ hlf hcons _ hA b a ha => WalkPotential.mLaplacian_greenFn hlf hcons hA b a ha

/-- **Lemma 7.2 (corrected)** from Lemmas 2.16, 2.8 and the remaining steps (map structure, eq:laplacian-of-uteps,
adjacent cells meet). -/
theorem massBoundOdometerAboveScale_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hstr : MatedMapStructureStep 𝒮) (hlap : StoppedOdometerLaplacianStep 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : MassBoundOdometerAboveScaleStmt 𝒮 :=
  massBoundOdometerAboveScale_of_steps 𝒮 h216 h28 hstr hlap hadj greenFnFirstVariableStep_holds

/-- **Lemma 7.2 (corrected)** from Lemmas 2.16, 2.8, 4.4 (its first conjunct) and `AdjacentCellsMeetAeStep` only:
`MatedMapStructureStep` and `StoppedOdometerLaplacianStep` are discharged in
MatedCRT/Steps/Sec7/OdometerBoundMass.lean (`GreenKernelHarmonicStep` is `greenKernelHarmonicStep_of_steps`). -/
theorem massBoundOdometerAboveScale_of_draft (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (h44 : DiscreteLaplacianBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) : MassBoundOdometerAboveScaleStmt 𝒮 :=
  massBoundOdometerAboveScale_of_inputs 𝒮 h216 h28 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 hadj)
    (stoppedOdometerLaplacianStep_of_draft 𝒮 h44 hadj) hadj

end MatedCRT
