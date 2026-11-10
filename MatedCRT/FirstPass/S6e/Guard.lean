import Mathlib
import MatedCRT.FirstPass.S6h
import MatedCRT.FirstPass.S6h.Schedule
import MatedCRT.FirstPass.S6e.Final

/-!
# FIRST PASS: the guarded exit bound of Lemma 6.8 from the concrete configuration lemma (task fp-S6e-lemma68-C17, z9)

`Lemma68Concrete.configuration_le_pow_concrete` (z8, `FirstPass/S6h/Schedule.lean`) gives the configuration bound
`∃ N, r^(-ζ)/200 ≤ N ∧ exitQ ≤ (1 - q₀/(1+log(1/r))²)^N` on the admissible configurations, from the per-state
inputs `StateTestInputs` (write-up C4) and the containment `ConcreteC12` (write-up C12), both on `E ε ∩ G`.
This file turns that bound into the probability statement `probTendsToOne_guard_concrete` (write-up (17)), with
`probTendsToOne_uniform_half_guarded` (`S6e/Final.lean`). The hypothesis `hsch` of `probTendsToOne_lemma68_guarded`
is therefore no longer needed.

Named input (a Prop, not proved here): `ConcreteGuardInputStmt 𝒮`, the probabilistic content of C4, C12 and the
environment regularity, for each valid environment. Its existential data are the constants `(R, ζ, p, q⋆, q₀, c₀)`,
the radius `dd`, and the events `E`, `G` (with `ProbTendsToOne S.P E`, `S.P Gᶜ = 0`) on which the inputs hold.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Guard

open Lemma68Config Lemma68Concrete Lemma68Final

/-- The guarded probability bound (write-up (17)) from the concrete configuration lemma. -/
theorem probTendsToOne_guard_concrete {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ s₀ γ : ℝ)
    {E : ℝ → Set Ω} (hE : ProbTendsToOne S.P E) {G : Set Ω} (hG : S.P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε) {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R)
    {ζ p qStar q0 c0 : ℝ} (good : ℝ → Ω → ℂ → ℕ → Prop)
    (hq0def : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq1s : qStar ≤ 1) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (hpζ : p = 2 * ζ + 2) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hq0 : 0 < q0) (hq1 : q0 ≤ 1)
    (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ) (hR1000 : R ≤ (1000 : ℝ) ^ (-1 / ζ)) (hc0 : c0 < 1 / 8)
    (hEnv : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G,
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hstate : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ∃ Good : ℤ → Prop, StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ) qStar c0 Good)
    (hC12 : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ConcreteC12 (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) :
    ProbTendsToOne S.P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}) :=
  probTendsToOne_uniform_half_guarded hE hG hα hdd hq0 hq1 hζ hζ' hR
    (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S)
    (configuration_le_pow_concrete S ρ s₀ γ E G α dd R ζ p qStar q0 c0 good hq0def hq hq1s hq9 hp hpζ hζ hα hdd hR
      hR1000 hc0 hEnv hlf hstate hC12)

/-- Named input (probabilistic content of write-up C4, C12 and of the environment regularity): for every valid
environment, there are a radius `dd` and events `E`, `G` with `P(E)` tending to one and `P(Gᶜ) = 0`, on which the
per-state inputs `StateTestInputs` (C4), the containment `ConcreteC12` (C12), the continuity and escape of `η`, and the
local finiteness of the multiplicities hold, with the guard radius `α ε = 10 ε^ω₀`. Not proved here. -/
def ConcreteGuardInputStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ R ζ p qStar q0 c0 : ℝ, 0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧ R ≤ (1000 : ℝ) ^ (-1 / ζ) ∧
    0 < ζ ∧ ζ < 1 / 2 ∧ 0 < q0 ∧ q0 ≤ 1 ∧ q0 = qStar / 9 ∧ 0 ≤ qStar ∧ qStar ≤ 1 ∧ qStar ≤ 9 ∧
    p ≤ 3 ∧ p = 2 * ζ + 2 ∧ c0 < 1 / 8 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ R) ∧
  ∃ (E : ℝ → Set Ω) (G : Set Ω) (good : ℝ → Ω → ℂ → ℕ → Prop),
    ProbTendsToOne S.P E ∧ S.P Gᶜ = 0 ∧
    (∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G,
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ)) ∧
    (∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧
    (∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ∃ Good : ℤ → Prop, StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ) qStar c0 Good) ∧
    (∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        ConcreteC12 (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r))

/-- The guarded exit bound as a probability statement, for every valid environment (write-up (17)); the form used by
`Lemma68Uniform.uniform_of_guard` (S6e/Uniform.lean). -/
def GuardProbStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ R ζ p qStar q0 : ℝ, 0 < R ∧ R ≤ ρ / 4 ∧ R ≤ Lemma68Cutoff.rAmp q0 ζ ∧
    0 < ζ ∧ ζ < 1 / 2 ∧ 0 < q0 ∧ q0 ≤ 1 ∧ q0 = qStar / 9 ∧ 0 ≤ qStar ∧ qStar ≤ 9 ∧ p ≤ 3 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧ (∀ ω, dd ω ≤ R) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ i : Config68,
      guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}

/-- The concrete input gives the guard probability statement `GuardProbStmt`. -/
theorem guardProb_of_concrete (𝒮 : SpaceFillingSLEModel) (hC : ConcreteGuardInputStmt 𝒮) :
    GuardProbStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ω₀, hω₀, hc⟩ := hC γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨R, ζ, p, qStar, q0, c0, hR0, hRρ, hRz, hR1000, hζ0, hζ1, hq00, hq01, hq0d, hq0', hq1s, hq9, hp3,
    hpζ, hc0, hc2⟩ := hc ρ hρ0 hρ1
  refine ⟨R, ζ, p, qStar, q0, hR0, hRρ, hRz, hζ0, hζ1, hq00, hq01, hq0d, hq0', hq9, hp3, ?_⟩
  intro s₀ hs₀0 hs₀1 Ω _ S hS
  obtain ⟨dd, hdm, hdpos, hddR, E, G, good, hE, hG, hEnv, hlf, hstate, hC12⟩ := hc2 s₀ hs₀0 hs₀1 Ω S hS
  refine ⟨dd, hdm, hdpos, hddR, ?_⟩
  exact probTendsToOne_guard_concrete S ρ s₀ γ hE hG (α := fun ε => 10 * ε ^ ω₀)
    (fun ε hε => by positivity) hddR good hq0d hq0' hq1s hq9 hp3 hpζ hζ0 hζ1 hq00 hq01 hRz hR1000
    hc0 hEnv hlf hstate hC12

end Lemma68Guard
end MatedCRT
