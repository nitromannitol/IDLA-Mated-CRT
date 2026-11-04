import MatedCRT.Draft.Section7
import MatedCRT.Draft.Section4
import MatedCRT.Proofs.WalkPotential.Comparison
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian
import MatedCRT.Proofs.Sec7.OdometerBoundMass.MapStructure

/-!
# Lemma 7.3 (lemma:odometer-bound-mass, line 3018; proof lines 3025-3047): steps

The printed proof compares `u^ε_t` with `f = (sup_{∂B} u^ε_t) P^·[X exits B before hitting B \ Λ^ε_t]` by the maximum
principle (line 3046). It uses:

* `MatedMapStructureStep` (literature, implicit in the paper): almost surely, for every `ε > 0`, the mated-CRT map
  `S.mult ε ω` is locally finite and only finitely many cells meet a bounded set. Consecutive vertices `k, k + 1` are
  adjacent for every continuous boundary-length pair (`Sec7.bmEdgeCount_succ_ne_zero`,
  MatedCRT/Proofs/Sec7/OdometerBoundMass/MapStructure.lean), so the map is connected and the maximum principle on
  finite sets applies; without connectivity the lemma would fail (a finite component inside `B ∩ Λ^ε_t` would have
  `P[exit] = 0` and `u^ε_t > 0`).
* `StoppedOdometerLaplacianStep` (eq:laplacian-of-uteps, line 2968, away from the origin): `Δ^ε u^ε_t = (deg^ε)⁻¹` on
  `Λ^ε_t \ {0}`. The paper derives it from eq:discrete-normalized-green-laplacian (line 806) and Lemma 4.4.

The other ingredients are proved without hypothesis: `u^ε_t ≥ 0` and `u^ε_t = 0` on `V^ε(B_ρ) \ Λ^ε_t`
(MatedCRT/Proofs/Sec7/OdometerBoundMass/StoppedOdometer.lean), the harmonicity of the exit probability (Markov property
of simple random walk) and the maximum principle (MatedCRT/Proofs/WalkPotential).
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- **Local structure of the mated-CRT map** (literature; used implicitly throughout the paper). Almost surely, for
every `ε > 0`: every vertex of the map of Definition 1.1 has finitely many neighbours (the boundary-length pair is a
correlated two-sided Brownian motion), and only finitely many cells meet each closed disk `cl(B_r)` (whole-plane
space-filling SLE from `∞` to `∞` is continuous with `|η(t)| → ∞` as `|t| → ∞`). -/
def MatedMapStructureStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε →
    (∀ a : ℤ, {b | S.mult ε ω a b ≠ 0}.Finite) ∧ ∀ r : ℝ, (cellVertices ε (S.η ω) (closedBall 0 r)).Finite

/-- **eq:laplacian-of-uteps** (line 2968) away from the origin: almost surely, for all `ε, t > 0`,
`Δ^ε u^ε_t = (deg^ε)⁻¹` on `Λ^ε_t \ {0}`. -/
def StoppedOdometerLaplacianStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε t : ℝ, 0 < ε → 0 < t → ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t, a ≠ 0 →
    matedLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a = ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹

/-- **Lemma 7.3** from its steps. -/
theorem odometerBoundMass_of_steps (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (hlap : StoppedOdometerLaplacianStep 𝒮) : OdometerBoundMassStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hstr γ hγ hγ2 Ω S hS, hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS] with ω hω hωlap
  intro ε t hε ht B hB b hb
  obtain ⟨hlf, hfin⟩ := hω ε hε
  have hsucc : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := fun k =>
    Sec7.bmEdgeCount_succ_ne_zero hε (S.bm ω).continuous.fst _ k
  have hVfin : (cellVertices ε (S.η ω) (ball 0 ρ)).Finite :=
    (hfin ρ).subset (Sec7.cellVertices_mono ball_subset_closedBall)
  have hBfin : B.Finite := hVfin.subset fun x hx => (hB hx).1
  have hbdry : (vBoundary (S.mult ε ω) B).Finite := by
    refine (hBfin.biUnion fun a _ => hlf a).subset ?_
    rintro c ⟨-, a, ha, hac⟩
    exact mem_biUnion ha hac
  have := hbdry.to_subtype
  have hbdd : BddAbove (range fun c : vBoundary (S.mult ε ω) B => stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) :=
    (Set.finite_range _).bddAbove
  have hU : (B ∩ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite := hBfin.subset inter_subset_left
  refine le_mul_exitBeforeHitProb (L := matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)
    (M := ⨆ c : vBoundary (S.mult ε ω) B, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) hlf hU
    (escape_of_adjacent_succ hsucc hU) (Real.iSup_nonneg fun c => Sec7.stoppedOdometer_nonneg hε ht c)
    (fun c hc => Sec7.stoppedOdometer_eq_zero_of_not_mem_cluster hε ht (hB hc.1).1 hc.2) (fun a ha => ?_)
    (fun c hc => le_ciSup hbdd ⟨c, hc⟩) b hb
  show 0 ≤ matedLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a
  rw [hωlap ε t hε ht a ha.2 fun h => (hB ha.1).2 h]
  exact inv_nonneg.2 (Nat.cast_nonneg _)

/-! ## Reduction of `StoppedOdometerLaplacianStep` to Lemma 4.4 and the Green's kernel identity -/

/-- **eq:discrete-normalized-green-laplacian** (line 806) for `D = B_ρ` and `a = 0`, away from the pole: almost
surely, for every `ε > 0`, `Δ^ε g^ε_{B_ρ}(0, ·) = 0` on `(V^ε(B_ρ) \ V^ε(∂B_ρ)) \ {0}`. (The paper cites
Lawler-Limic Proposition 6.2.3, line 783; it is the last-exit decomposition of the Green's function of the finite set
`V^ε(B_ρ) \ V^ε(∂B_ρ)` together with the reversibility `deg(a) G(a,b) = deg(b) G(b,a)`.) -/
def GreenKernelHarmonicStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ b ∈ ballInterior ε (S.η ω) ρ, b ≠ 0 →
    matedLaplacian (S.mult ε ω) (greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0) b = 0

/-- eq:laplacian-of-uteps away from the origin from Lemma 4.4 (`Δ^ε w̃^ε_t = (deg^ε)⁻¹` on `Λ^ε_t`) and the Green's
kernel identity (lines 2962-2972): `Λ^ε_t ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)` and `Δ^ε u^ε_t = Δ^ε w̃^ε_t + (t ε⁻¹) Δ^ε g`. -/
theorem stoppedOdometerLaplacianStep_of_steps (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (h44 : DiscreteLaplacianBoundStmt 𝒮) (hgreen : GreenKernelHarmonicStep 𝒮) :
    StoppedOdometerLaplacianStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hstr γ hγ hγ2 Ω S hS, h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS, hgreen γ hγ hγ2 ρ hρ hρ1 Ω S hS]
    with ω hω h4 hg
  intro ε t hε ht a ha ha0
  obtain ⟨hlf, -⟩ := hω ε hε
  have haΛ : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧
      matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a < matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a := ha
  have haV : a ∈ ballInterior ε (S.η ω) ρ := by
    by_contra hV
    have haW : a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ) := Sec7.cellVertices_mono ball_subset_closedBall haΛ.1
    have h1 := Sec7.matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior (m := S.mult ε ω) hε ht haW hV
    linarith [haΛ.2]
  have hw : mLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a =
      ((mdeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹ := (h4 t ε ht hε).1 a ha
  have hgr : mLaplacian (S.mult ε ω) (greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0) a =
      0 := hg ε hε a haV ha0
  show mLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a = ((mdeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹
  rw [Sec7.mLaplacian_stoppedOdometer hε ht hlf, hw, hgr, mul_zero, add_zero]

/-- **Lemma 7.3** from the map structure (literature), Lemma 4.4 and the Green's kernel identity. -/
theorem odometerBoundMass_of_inputs (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (h44 : DiscreteLaplacianBoundStmt 𝒮) (hgreen : GreenKernelHarmonicStep 𝒮) : OdometerBoundMassStmt 𝒮 :=
  odometerBoundMass_of_steps 𝒮 hstr (stoppedOdometerLaplacianStep_of_steps 𝒮 hstr h44 hgreen)

end MatedCRT
