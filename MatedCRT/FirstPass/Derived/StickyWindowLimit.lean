import MatedCRT.FirstPass.Derived.StickyWindowEvent
import LatticeProb.Prob.StickyPathLimit

/-!
# No sticking for subsequential limits of the interpolated quenched walk laws

The last claim of Proposition 6.1 of Berestycki-Gwynne, for one ball `B(0, ρ)` and one window length `a` and
time horizon `T`.  Let `(D n, P̃^{ε_n})` converge in law to `ν` on `X × C(ℂ, 𝒫(ContinuousPath ℂ))`.  If the
interpolated walk laws give mass at most `r` to the open sets `stickyOpen (B(0, ρ)) a T δ` of paths that nearly
stand still on a window, uniformly over all starting points `z`, with probability at least `1 - c` for small `ε`,
then `ν`-almost surely the limit kernel `z ↦ p z` gives mass `0` to `stickySet (B(0, ρ)) a T`, the paths that are
constant on a window of length `a` that starts before time `T` and ends before they leave `B(0, ρ)`, for every `z`.
The smallness input is `StickyWindowEvent.interpWalkLaw_stickyWindowSet_small`; the passage to the limit is the
portmanteau theorem for the lower semicontinuous functional `p ↦ sup_z p z (stickyOpen ..)`
(`LatticeProb.ae_forall_apply_stickySet_eq_zero_of_tendsto`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived MatedCRT.StickyWindowKernel

namespace MatedCRT
namespace StickyWindowLimit

/-- **No sticking for a subsequential limit** (Berestycki-Gwynne, Proposition 6.1, last claim), for one ball, one
window length `a > 0` and one time horizon `T`.  `hLL` is the failure event of the window event of Proposition 6.14
(output of `NoStickingEvent.limLimSmall_noSticking`) and `hmε` the lower bound `ε m_ε ≥ c₀ > 0` of the speed. -/
theorem ae_apply_stickySet_eq_zero_of_tendsto_law {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν)))
    {ρ : ℝ} {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ}
    (hψ : (∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧
      ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0))
    (hLL : LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
          srwLaw (S.mult ε ω) x
            {X | ¬ ∀ j : ℕ, ((j + ⌊ε⁻¹ * δ ^ q⌋₊ : ℕ) : ℕ∞) ≤
                vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X →
              ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * ⌊ε⁻¹ * δ ^ q⌋₊ ∧
                δ ≤ ‖vertexPoint ε (S.η ω) (X i₂) - vertexPoint ε (S.η ω) (X i₁)‖} ≤
            ENNReal.ofReal (ψ δ)}))
    (hmε : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → c₀ ≤ ε * S.mε ε)
    {a : ℝ≥0} (ha : 0 < a) (T : ℝ≥0) :
    ∀ᵐ p ∂ν, ∀ z : ℂ,
      ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (stickySet (ball (0 : ℂ) ρ) a T) = 0 := by
  have hPS : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hW : ∀ n, AEMeasurable (fun ω => (D n ω, interpWalkLaw S η' (ε n) ω)) S.P := fun n =>
    (hD n).prodMk (aemeasurable_interpWalkLaw hS hη' hae (hε0 n))
  have hνprob : IsProbabilityMeasure ν := by
    have h1 := hlaw (BoundedContinuousFunction.const _ 1)
    have h3 : ∀ n, ∫ ω, (BoundedContinuousFunction.const (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))
        (1 : ℝ)) (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P = 1 := fun n => by simp
    have h4 : Tendsto (fun n => ∫ ω, (BoundedContinuousFunction.const
        (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (1 : ℝ)) (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 1) := by
      simp_rw [h3]
      exact tendsto_const_nhds
    have h5 := tendsto_nhds_unique h1 h4
    simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one] at h5
    exact isProbabilityMeasure_iff_real.2 h5
  let μs : ℕ → ProbabilityMeasure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) := fun n =>
    ⟨S.P.map (fun ω => (D n ω, interpWalkLaw S η' (ε n) ω)), inferInstance⟩
  let μ : ProbabilityMeasure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) := ⟨ν, hνprob⟩
  have hlim : Tendsto μs atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro F
    exact (hlaw F).congr fun n => (integral_map (hW n) F.continuous.aestronglyMeasurable).symm
  have hsmall : ∀ r c : ℝ≥0, 0 < r → 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ((μs n : ProbabilityMeasure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))) :
        Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))))
      {p | (r : ℝ≥0∞) < ⨆ z : (Set.univ : Set ℂ), ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)) (stickyOpen (ball (0 : ℂ) ρ) a T δ)} ≤ c := by
    intro r c hr hc
    obtain ⟨δ, hδ, ε₀, hε₀, hbound⟩ := StickyWindowEvent.interpWalkLaw_stickyWindowSet_small S hS η' hae hq hψ
      hLL hmε ha T (fun δ => (isOpen_stickyOpen isOpen_ball a T δ).measurableSet) Set.univ r hr (c : ℝ)
      (by exact_mod_cast hc)
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hε.eventually (gt_mem_nhds hε₀)] with n hn
    have hlsc := lowerSemicontinuous_iSup_apply (P := fun p : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) => p.2)
      continuous_snd (Set.univ : Set ℂ) (isOpen_stickyOpen isOpen_ball (E := ℂ) a T δ (A := ball (0 : ℂ) ρ))
    have hmeasSet : MeasurableSet {p : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) |
        (r : ℝ≥0∞) < ⨆ z : (Set.univ : Set ℂ), ((p.2 z : ProbabilityMeasure (ContinuousPath ℂ)) :
          Measure (ContinuousPath ℂ)) (stickyOpen (ball (0 : ℂ) ρ) a T δ)} :=
      (lowerSemicontinuous_iff_isOpen_preimage.1 hlsc (r : ℝ≥0∞)).measurableSet
    change S.P.map (fun ω => (D n ω, interpWalkLaw S η' (ε n) ω)) _ ≤ _
    rw [Measure.map_apply_of_aemeasurable (hW n) hmeasSet]
    have := hbound (ε n) (hε0 n) hn
    rwa [ENNReal.ofReal_coe_nnreal] at this
  have hmain := ae_forall_apply_stickySet_eq_zero_of_tendsto (K := Set.univ)
    (P := fun p : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) => p.2) hlim continuous_snd
    (isOpen_ball (x := (0 : ℂ)) (ε := ρ)) a T hsmall
  filter_upwards [hmain] with p hp z
  exact hp z (Set.mem_univ z)

end StickyWindowLimit
end MatedCRT
