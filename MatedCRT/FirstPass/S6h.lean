import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6e.Final
import MatedCRT.FirstPass.S6h.Schedule

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Config

/-- (Lemma 6.8, the hypothesis `hpt` of `Lemma68Final.probTendsToOne_uniform_half_guarded`, bridge note §4, z9's form)
On `E ε ∩ G`, for every admissible radius `r ∈ [α ε, dd ω]` and every configuration with the guard `FullAdm`, the exit
probability `exitQ` satisfies `(1 - q0/(1+log(1/r))²)^N` for a count `N ≥ r^(-ζ)/200`. This is `configuration_le_pow`
with `ι := Config68`, `Adm := FullAdm`, `exitF := exitQ`; the non-admissible configurations are handled by the guard. -/
theorem probTendsToOne_lemma68_guarded {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (S : MatedCRTEnv Ω)
    (ρ s₀ γ : ℝ) {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R) {ζ p qStar q0 : ℝ}
    (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hq0def : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (sc : ℝ → Ω → ℝ → Config68 → TestSchedule)
    (hsch : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        (sc ε ω r i).Valid (srwLaw (S.mult ε ω) i.a)
          (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) (↑i.A : Set ℤ) r p qStar ζ) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      Lemma68Final.guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}) :=
  Lemma68Final.probTendsToOne_uniform_half_guarded hE hG hα hdd hq0 hq1 hζ hζ' hR
    (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S)
    (configuration_le_pow S ρ s₀ γ E G α dd R ζ p qStar q0 hq0def hq hq9 hp hα hdd hR sc hsch)

/-- (Lemma 6.8, the concrete bridge, the probability statement with the concrete schedule `cfgSchedule` of
`Lemma68Concrete`.) The guarded uniform exit bound `probTendsToOne_lemma68_guarded` with the schedule chosen as in
`configuration_le_pow_concrete`: the named inputs are the environment `hEnv` (η continuous and proper), the local
finiteness `hlf`, the per-state inputs `hstate` (write-up C4, `StateTestInputs`), the containment `hC12` (write-up C12,
`ConcreteC12`, z10), the cutoff `hR1000` (`R ≤ 1000^(-1/ζ)`; implied by `R ≤ r0Min` via `Cutoff.r0Min_le_zeta`) and
`c0 < 1/8`. -/
theorem probTendsToOne_lemma68_concrete {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (S : MatedCRTEnv Ω)
    (ρ s₀ γ : ℝ) {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R)
    {ζ p qStar q0 c0 : ℝ} (good : ℝ → Ω → ℂ → ℕ → Prop)
    (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hR1000 : R ≤ (1000 : ℝ) ^ (-1 / ζ)) (hc0 : c0 < 1 / 8)
    (hq0def : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq1' : qStar ≤ 1) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (hpζ : p = 2 * ζ + 2)
    (hEnv : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G,
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hstate : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
      ∃ Good : ℤ → Prop, Lemma68Concrete.StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ)
        qStar c0 Good)
    (hC12 : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
      Lemma68Concrete.ConcreteC12 (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω)
        (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r)) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      Lemma68Final.guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}) :=
  Lemma68Final.probTendsToOne_uniform_half_guarded hE hG hα hdd hq0 hq1 hζ hζ' hR
    (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S)
    (Lemma68Concrete.configuration_le_pow_concrete S ρ s₀ γ E G α dd R ζ p qStar q0 c0 good hq0def hq hq1' hq9 hp
      hpζ hζ hα hdd hR hR1000 hc0 hEnv hlf hstate hC12)

end Lemma68Config

end MatedCRT
