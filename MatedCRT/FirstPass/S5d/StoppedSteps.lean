import MatedCRT.Proofs.IDLA.JointStoppedLowerBound
import MatedCRT.FirstPass.S5c.GreenCount
import MatedCRT.FirstPass.S5d.StoppedMono

/-!
# The stopped clause of Proposition 5.1: killing and target sets and the two Green steps (task fp-S5d-5-1-stopped-repair)

Route of the direct repair of the stopped clause (referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md section 5):
the walkers are killed on leaving the strict discrete cluster `Λ^ε_t` intersected with `V^ε(Λ_t)` (the killing set
`I_ε`), and the relaxed Lemma 5.2 (`GeneralIDLALowerBoundRelaxedStep`) is applied with targets `Z_ε = V^ε(B⁻_δ(Λ_t)) ∪ {0}`.
The two Green inequalities that Lemma 5.2 needs on `Z_ε` are the two NEW probabilistic steps `StoppedFirstGreenStep`
(first Green inequality (5.5) with `Z_ε ⊆ I_ε`) and `StoppedSecondGreenStep` (second Green inequality (5.7)). They are
open: their written arguments are referee sections 5.1-5.3 (which use referee sections 1-3) and are not formalized here.

The reduction of the stopped conjunct to these two steps is `MatedCRT.iDLALowerBoundStopped_of_greenSteps`
(MatedCRT/FirstPass/S5d/StoppedReduction.lean).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The killing set `I^ε_t` of the stopped clause (referee section 5, `I_ε = S_ε ∩ A_ε`): the labels of the strict
discrete cluster `matedDiscreteCluster` that lie in `V^ε(Λ_t)`, on the event `{t < T}` (`T` the cluster exit time); empty
off this event, so that `I^ε_t ⊆ V^ε(B_ρ)` for every environment. -/
noncomputable def stoppedKillSet {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ)
    (ρ t ε : ℝ) (ω : Ω) : Set ℤ :=
  {a | t < clusterExitTime (Λ ω) ρ ∧ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ∧
    a ∈ cellVertices ε (S.η ω) (Λ ω t)}

/-- The target set `Z^ε_t = V^ε(B⁻_δ(Λ_t)) ∪ {0}` of the stopped clause (referee section 5, `Z_ε = V^ε(K_δ) ∪ {0}`).
Here `K_δ = B⁻_δ(Λ_t) = innerNbhd δ (Λ_t)` (Defs/Notation.lean:30), the reading under which the referee's distance
statements in section 5 hold; the referee does not define `K_δ` explicitly. -/
def stoppedTargetSet {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (δ t ε : ℝ)
    (ω : Ω) : Set ℤ :=
  cellVertices ε (S.η ω) (innerNbhd δ (Λ ω t)) ∪ {0}

/-- The first Green event of the stopped clause at scale `ε` (the hypothesis of the first Green inequality of
`GeneralIDLALowerBoundRelaxedStep` on the targets `Z^ε_t`): `Z^ε_t ⊆ I^ε_t` and `(1 + s) ∑_{b ∈ I} G_I(b,a) ≤ (t/ε) G_I(0,a)`
for every target `a`, with `G_I` the Green function of the killed walk on `I = I^ε_t` (`greenFn`). -/
def stoppedFirstGreenEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t δ : ℝ)
    (s : Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | stoppedTargetSet S Λ δ t ε ω ⊆ stoppedKillSet S Λ ρ t ε ω ∧
    ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
      (1 + s ω) * ∑' b : stoppedKillSet S Λ ρ t ε ω,
          greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) b a ≤
        t / ε * greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) 0 a}

/-- The second Green event of the stopped clause at scale `ε` (the second Green inequality of Lemma 5.2 with `q = 1/4`):
`ε^{-1/4} ≤ (∑_{b ∈ I} G_I(b,a)) / G_I(a,a)` for every target `a`. -/
def stoppedSecondGreenEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t δ ε : ℝ) :
    Set Ω :=
  {ω | ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
    ε ^ (-(1 / 4 : ℝ)) ≤
      (∑' b : stoppedKillSet S Λ ρ t ε ω, greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) b a) /
        greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a a}

/-- **NEW, OPEN (probabilistic input; referee section 5.1-5.2, equations (5.1), (5.2), (5.4), (5.5)).** On `{t < T}`, with
probability tending to `1` as `ε → 0⁺`, the first Green event holds with a positive measurable random factor `s`
(here `s = c/(2C)` with the random constants `c` of (5.1) and `C` of the exit-time bound). The factor `s` is the same for
all `ε`, as in `GeneralIDLALowerBoundRelaxedStep` (Steps/Sec5/IDLALowerBound.lean:40). -/
def StoppedFirstGreenStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ s : Ω → ℝ, Measurable[S.envSigma] s ∧ (∀ ω, 0 < s ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (stoppedFirstGreenEvent S Λ ρ t δ s)

/-- **NEW, OPEN (probabilistic input; referee section 5.3, equation (5.7)).** On `{t < T}`, with probability tending to
`1` as `ε → 0⁺`, every target satisfies the second Green inequality of Lemma 5.2 with exponent `q = 1/4`. -/
def StoppedSecondGreenStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} (stoppedSecondGreenEvent S Λ ρ t δ)

/-- Deterministic geometry of the stopped clause: on a surjective `η`, the inner neighbourhood `B⁻_δ(X)` is covered by the
cells of the vertices whose cells meet it. -/
theorem innerNbhd_subset_fillCells_cellVertices {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε)
    (hsurj : Function.Surjective η) (δ : ℝ) (X : Set ℂ) :
    innerNbhd δ X ⊆ fillCells ε η (cellVertices ε η (innerNbhd δ X)) := by
  intro y hy
  obtain ⟨k, hk⟩ := MatedCRT.S5c.exists_mem_cell_of_surj hε hsurj y
  exact mem_iUnion₂.2 ⟨k, ⟨y, hk, hy⟩, hk⟩

end MatedCRT
