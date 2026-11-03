import MatedCRT.Steps.Sec7.OdometerBoundMass
import MatedCRT.Draft.Section4
import MatedCRT.Proofs.Sec7.CrudeUpperBound.GreedyPath
import MatedCRT.Proofs.Sec7.CrudeUpperBound.PolyHighProb

/-!
# Lemma 7.4 (lemma:crude-upper-bound, line 3058; proof lines 3068-3086; Levine-Peres 2009, Lemma 4.2): steps

## The printed statement and the corrected one

`CrudeUpperBoundStmt` (MatedCRT/Draft/Section7.lean) transcribes the printed statement: increasing paths of the
*stopped* odometer `u^ε_t` from every `a ∈ D_ε(t ε⁻¹) \ {0}` (the divisible sandpile cluster). It is false
(ESCALATIONS.md, entry E-c3-1): `u^ε_t` vanishes off `V^ε(cl(B_ρ))` while `|D_ε(t ε⁻¹)| ≥ t ε⁻¹`, so on the
event `{μ_h(B_{2ρ}) < t/2}`, of positive probability not depending on `ε`, there is `a ∈ D_ε(t ε⁻¹)` all of whose
neighbours lie outside `V^ε(cl(B_ρ))`, and no path from `a` starts with an increase of `u^ε_t`. The printed proof also
applies `Δ^ε u^ε_t = (deg^ε)⁻¹` at `a_0 ∈ D_ε(t ε⁻¹) \ Λ^ε_t` (line 3076), where it fails. The lemma is used
(line 3240) for paths starting from the support of `u^ε_t`, i.e. from `Λ^ε_t` (`mem_matedDiscreteCluster_of_stoppedOdometer_pos`);
`CrudeUpperBoundClusterStmt` is that statement (the correction proposed in E-c3-1, pending the operator's ruling; it is
not presented as Lemma 7.4), and is proved here from the steps.

## Steps
* `DegreeBoundStep` (literature: GMS19 Lemma 2.6, eq:degree-bound, line 3071);
* `MatedMapStructureStep`, `StoppedOdometerLaplacianStep` (MatedCRT/Steps/Sec7/OdometerBoundMass.lean);
* Lemma 4.5 (`DiscreteConservationOfMassStmt`): `Λ^ε_t` is finite (line 3085).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

/-- **GMS19 Lemma 2.6** (Gwynne-Miller-Sheffield, *Harmonic functions on mated-CRT maps*, Lemma 2.6; paper
eq:degree-bound, lines 3069-3071): with polynomially high probability as `ε → 0`,
`max_{a ∈ V^ε(B_ρ)} deg^ε(a) ≤ (log ε⁻¹)²`. -/
def DegreeBoundStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
    (matedDeg ε (S.η ω) a : ℝ) ≤ Real.log ε⁻¹ ^ 2}

/-- **Crude upper bound along the discrete cluster** (the `Λ^ε_t`-version of Lemma 7.4 proposed in E-c3-1, as used
at line 3240; not Lemma 7.4 until the operator rules): for all `t > 0`, with
polynomially high probability as `ε → 0`, for every `a ∈ Λ^ε_t \ {0}` there is a path `a = a₀ ∼ a₁ ∼ ⋯ ∼ a_m = 0` in
`Λ^ε_t` with `u^ε_t(a_{i+1}) ≥ u^ε_t(a_i) + log(ε⁻¹)⁻²`. -/
def CrudeUpperBoundClusterStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t →
  PolyHighProb S.P fun ε => {ω | ∀ a ∈ matedDiscreteCluster ε (S.η ω) ρ t \ {0}, ∃ p : List ℤ,
    IsVPathIn (S.mult ε ω) (matedDiscreteCluster ε (S.η ω) ρ t) p a 0 ∧
    p.IsChain fun c d => stoppedOdometer ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤ stoppedOdometer ε (S.η ω) ρ t d}

/-- The crude upper bound along the discrete cluster (E-c3-1) from its steps. -/
theorem crudeUpperBoundCluster_of_steps (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (hlap : StoppedOdometerLaplacianStep 𝒮) (hdeg : DegreeBoundStep 𝒮) (h45 : DiscreteConservationOfMassStmt 𝒮) :
    CrudeUpperBoundClusterStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht
  refine polyHighProb_mono_ae (hdeg γ hγ hγ2 ρ hρ hρ1 Ω S hS)
    ((hstr γ hγ hγ2 Ω S hS).and ((hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS).and (h45 γ hγ hγ2 ρ hρ hρ1 Ω S hS))) ?_
  rintro ε hε ω hωdeg ⟨hωstr, hωlap, hω45⟩
  have hωdeg' : ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ((mdeg (S.mult ε ω) a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2 := hωdeg
  obtain ⟨hlf, hsucc, -⟩ := hωstr ε hε
  have hΛfin := (hω45 t ε ht hε).1
  have hD : ∀ c, (0 : ℝ) < (mdeg (S.mult ε ω) c : ℕ) := fun c => by
    exact_mod_cast Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf (hsucc c))
  have hstep : ∀ c ∈ matedDiscreteCluster ε (S.η ω) ρ t, c ≠ 0 → ∃ b ∈ matedDiscreteCluster ε (S.η ω) ρ t,
      S.mult ε ω c b ≠ 0 ∧
        stoppedOdometer ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤ stoppedOdometer ε (S.η ω) ρ t b := by
    intro c hc hc0
    have hcV : c ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
      (show c ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from hc).1
    have hL : mLaplacian (S.mult ε ω) (stoppedOdometer ε (S.η ω) ρ t) c =
        ((mdeg (S.mult ε ω) c : ℕ) : ℝ)⁻¹ := hωlap ε t hε ht c hc hc0
    obtain ⟨b, hmb, hub⟩ := exists_nbr_add_inv_le hlf (hsucc c) hL
    have hδle : (Real.log ε⁻¹)⁻¹ ^ 2 ≤ ((mdeg (S.mult ε ω) c : ℕ) : ℝ)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (hD c) (hωdeg' c hcV)
    have hbpos : 0 < stoppedOdometer ε (S.η ω) ρ t b := by
      have h0 := stoppedOdometer_nonneg (η := S.η ω) (ρ := ρ) hε ht c
      have h1 := inv_pos.2 (hD c)
      linarith
    exact ⟨b, mem_matedDiscreteCluster_of_stoppedOdometer_pos hε ht hbpos, hmb, by linarith⟩
  rw [mem_ofPred_eq]
  rintro a ⟨haΛ, ha0⟩
  have haV : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
    (show a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from haΛ).1
  have hδ : 0 < (Real.log ε⁻¹)⁻¹ ^ 2 := by
    rw [inv_pow]
    exact inv_pos.2 ((hD a).trans_le (hωdeg' a haV))
  exact exists_vPath_chain hΛfin hδ hstep a haΛ

end MatedCRT
