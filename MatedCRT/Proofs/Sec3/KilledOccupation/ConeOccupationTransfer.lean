import MatedCRT.Proofs.Sec3.KilledOccupation.ClockOccupationMeasure
import MatedCRT.Proofs.Sec3.KilledOccupation.GmcGreenMeasure
import MatedCRT.Proofs.Sec4.Prop42Closure.RestrictedLaw

/-!
# Transfer of the occupation identity from the whole-plane GFF to the quantum cone

For a family `ψ` of circle averages on the unit disk, a disc `D = B_r(z) ⊆ B_ρ(0)` with `ρ < 1` and a starting point
`y ∈ D`, two measures on the plane are measurable functions of `ψ`:

* `m₁(ψ) = limClockOccupationMeasure γ ε z r P_y ψ`, the expected occupation measure, up to the exit time of `D`, of
  the limit clock of `ψ` along a sequence `ε` of dyadic scales, under planar Brownian motion `P_y` from `y`;
* `m₂(ψ) = gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r ψ`, the Gaussian multiplicative chaos limit of `ψ` weighted by
  `2 · 1_D · G_D(y, ·)`, with `G_D` the Green function of `D`.

The event `E = {ψ : m₁(ψ)(D) < ∞, m₁(ψ) = m₂(ψ) on a countable π-system generating the Borel sets of D}` is
measurable, so its probability depends only on the law of `ψ`. By eq:gff (`ConeUnitDiskGFFLaw`) the circle averages
of the γ-quantum cone on the unit disk have the law of those of `h^ℂ - γ log|·|`, for a whole-plane GFF `h^ℂ`.
Hence the occupation identity for the field `h^ℂ - γ log|·|` and an independent Brownian motion (Garban, Rhodes and
Vargas, *Liouville Brownian motion*; Berestycki, *Diffusion in planar Liouville quantum gravity*) passes to the
cone. On the cone the limit clock is the clock `S.clock` of Liouville Brownian motion and the chaos limit is the
γ-LQG measure `S.μ`, which gives the occupation (Revuz) identity for `(S.clock, S.μ)`.

## Main results

* `map_prod_eq_of_identDistrib_ae`, `clockAnnealedLaw_eq_of_identDistrib`: the coupled law of the circle averages and
  an independent Brownian motion depends only on the law of the circle averages.
* `ae_lintegral_clock_occupation_eq_green_cone`: the occupation identity on the quantum cone, from eq:gff and the
  occupation-agreement event of the whole-plane GFF.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open _root_.HarmonicBalls MarkovProcess

namespace MatedCRT.KilledOccupation

/-- The push-forward of `P ⊗ Q` by `(ω, b) ↦ (X ω, b)` is the product of the law of `X` with `Q`, for an almost
everywhere measurable `X`. -/
lemma map_prod_eq_map_prod_of_aemeasurable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {P : Measure Ω} [SFinite P] {X : Ω → α} (hX : AEMeasurable X P) (Q : Measure β)
    [SFinite Q] : (P.prod Q).map (fun p => (X p.1, p.2)) = (P.map X).prod Q := by
  have h1 : (fun p : Ω × β => (X p.1, p.2)) =ᵐ[P.prod Q] fun p => (hX.mk X p.1, p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (hX.ae_eq_mk : ∀ᵐ x ∂P, X x = hX.mk X x)] with p hp
    rw [hp]
  have hA := Measure.map_prod_map P Q hX.measurable_mk measurable_id
  rw [Measure.map_id] at hA
  rw [Measure.map_congr h1, Measure.map_congr hX.ae_eq_mk]
  exact hA.symm

/-- Equality in law, transported through a product with a fixed measure: the push-forward of `P ⊗ Q` by
`(ω, b) ↦ (X ω, b)` depends only on the law of `X`. No measurability beyond that of `IdentDistrib` is required. -/
lemma map_prod_eq_of_identDistrib_ae {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} {P' : Measure Ω'} [SFinite P] [SFinite P']
    {X : Ω → α} {X' : Ω' → α} (hX : IdentDistrib X X' P P') (Q : Measure β) [SFinite Q] :
    (P.prod Q).map (fun p => (X p.1, p.2)) = (P'.prod Q).map (fun p => (X' p.1, p.2)) := by
  rw [map_prod_eq_map_prod_of_aemeasurable hX.aemeasurable_fst Q,
    map_prod_eq_map_prod_of_aemeasurable hX.aemeasurable_snd Q, hX.map_eq]

/-- Two fields whose circle averages on the unit disk have the same law have the same coupled law with an
independent planar Brownian motion from `y`. -/
theorem clockAnnealedLaw_eq_of_identDistrib {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [SFinite P] [SFinite P'] {hcirc : Ω → ℝ → ℂ → ℝ}
    {hcirc' : Ω' → ℝ → ℂ → ℝ} (h : IdentDistrib (clockPsi hcirc) (clockPsi hcirc') P P') (y : ℂ) :
    clockAnnealedLaw P hcirc y = clockAnnealedLaw P' hcirc' y :=
  map_prod_eq_of_identDistrib_ae h (planarBrownianMotion y)

/-- **Occupation identity on the quantum cone.** Let `S` be a γ-quantum cone environment, `D = B_r(z) ⊆ B_ρ(0)` with
`ρ < 1`, and `y ∈ D`. Assume eq:gff (`hlaw`) and the occupation identity of the whole-plane GFF in the form `hGFF`:
for every whole-plane GFF `hc`, every strictly increasing sequence `n` of dyadic scales along which the consecutive
gaps of the regularized clocks of `h^ℂ - γ log|·|` satisfy the summable bounds, and every countable family `C` of
measurable subsets of `D`, almost surely the expected occupation measure of the limit clock along `n` is finite on `D`
and agrees on `C` with the chaos limit weighted by `2 · 1_D · G_D(y, ·)`.

Then, almost surely, for every family `dA` of measures on the time axis which, for almost every Brownian path `b`
from `y`, has the masses `dA b [0, t] = S.clock ω b (t ∧ σ_D(b))`, the Green potential of the γ-LQG measure is finite,
`∫_D 2 G_D(y, x) μ(dx) < ∞`, and for every measurable `g ≥ 0`
`E_y ∫_{[0, σ_D]} g(b_u) dA b (du) = ∫_D 2 G_D(y, x) g(x) μ(dx)`. -/
theorem ae_lintegral_clock_occupation_eq_green_cone (hlaw : ConeUnitDiskGFFLaw) (𝒮 : SpaceFillingSLEModel)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (r : ℝ) (z y : ℂ) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r)
    (hGFF : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C) :
    ∀ᵐ ω ∂S.P, ∀ dA : ContinuousPath ℂ → Measure ℝ≥0,
      (∀ᵐ b ∂planarBrownianMotion y, ∀ t : ℝ≥0,
        dA b (Iic t) = ENNReal.ofReal (S.clock ω b (min t (exitNN z r b)))) →
      (∫⁻ x in ball z r, 2 * ENNReal.ofReal (greenFunction (ball z r) y x) ∂S.μ ω) < ∞ ∧
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), (ball z r).indicator g (b u) ∂(dA b)
            ∂planarBrownianMotion y =
          ∫⁻ x in ball z r, 2 * ENNReal.ofReal (greenFunction (ball z r) y x) * g x ∂S.μ ω := by
  have hSP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- The good subsequence and the identification of the limit clock on the cone.
  obtain ⟨n, hn, hn0, hbd, hid⟩ :=
    exists_strictMono_ae_limClockFun_eq_clock_cone 𝒮 γ ρ hρ z y r hr hball hy S hS
  -- The whole-plane GFF with the same law of circle averages on the unit disk.
  obtain ⟨Ω', _, P', hC', hc, hP', hgff, hident⟩ := hlaw 𝒮 γ hγ0 hγ2 Ω S hS
  have hident' : IdentDistrib (clockPsi S.hcirc) (clockPsi fun ω' => fieldCircleAverage γ (hc ω')) S.P P' :=
    hident
  have hL5 : clockAnnealedLaw S.P S.hcirc y = clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y :=
    clockAnnealedLaw_eq_of_identDistrib hident' y
  -- A countable π-system of open subsets of the disc generating its Borel sets.
  obtain ⟨C, hCc, hpi, hCo, hDC, hgenC⟩ :=
    MatedCRT.RestrictedLaw.exists_traceSystem ℂ (S := ball z r) isOpen_ball
  have hCm : ∀ A ∈ C, MeasurableSet A := fun A hA => (hCo A hA).1.measurableSet
  have hCD : ∀ A ∈ C, A ⊆ ball z r := fun A hA => (hCo A hA).2
  have hgen : ∀ A, MeasurableSet A → A ⊆ ball z r → MeasurableSet[MeasurableSpace.generateFrom C] A :=
    fun A hA hAD => by
      have h := hgenC A hA
      rwa [inter_eq_left.2 hAD] at h
  -- The agreement event holds for the whole-plane GFF, hence for the cone.
  have hE' := hGFF Ω' P' hC' hc hP' hgff n hn hn0 (fun k => by rw [← hL5]; exact hbd k) C hCc
    (fun A hA => ⟨hCm A hA, hCD A hA⟩)
  have hEm : MeasurableSet (occupationAgreementEvent
      (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
      (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C) :=
    measurableSet_occupationAgreementEvent
      (measurable_limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
      (measurable_gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) hCc hCm measurableSet_ball
  have hE : ∀ᵐ ω ∂S.P, clockPsi S.hcirc ω ∈ occupationAgreementEvent
      (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
      (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C :=
    hident'.symm.ae_mem_snd hEm hE'
  filter_upwards [hE, ae_limClockKernel_Iic_cone 𝒮 γ z y r S hS n hid,
    ae_gmcGreenMeasure_cone S 𝒮 γ hS hρ hball y] with ω hω hκ hm₂ dA hdA
  have heq := eq_of_mem_occupationAgreementEvent hDC hCD hCm hpi hgen hω
  have hm₂' : gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r (clockPsi S.hcirc ω) =
      (S.μ ω).withDensity (greenOccupationDensity z y r) := hm₂
  have hκ' : ∀ᵐ b ∂planarBrownianMotion y, ∀ t : ℝ≥0,
      limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b) (Iic t) =
        dA b (Iic t) := by
    filter_upwards [hκ, hdA] with b h1 h2 t
    rw [h1 t, h2 t]
  have hrestr : (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y)
      (clockPsi S.hcirc ω)).restrict (ball z r) =
      ((S.μ ω).withDensity (greenOccupationDensity z y r)).restrict (ball z r) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, ← hm₂']
    exact heq _ (hA.inter measurableSet_ball) inter_subset_right
  refine ⟨?_, fun g hg => ?_⟩
  · have hfin := hω.1
    rw [heq _ measurableSet_ball subset_rfl, hm₂',
      withDensity_greenOccupationDensity_apply _ z y r measurableSet_ball, inter_self] at hfin
    exact hfin
  · calc ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), (ball z r).indicator g (b u) ∂(dA b)
          ∂planarBrownianMotion y
        = ∫⁻ x, (ball z r).indicator g x ∂(limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r
            (planarBrownianMotion y) (clockPsi S.hcirc ω)) :=
          (lintegral_limClockOccupationMeasure_of_Iic_eq γ (fun k => dyadicScale (n k)) z r
            (planarBrownianMotion y) (clockPsi S.hcirc ω) hκ' (hg.indicator measurableSet_ball)).symm
      _ = ∫⁻ x in ball z r, g x ∂(limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r
            (planarBrownianMotion y) (clockPsi S.hcirc ω)) := lintegral_indicator measurableSet_ball _
      _ = ∫⁻ x in ball z r, g x ∂((S.μ ω).withDensity (greenOccupationDensity z y r)) := by rw [hrestr]
      _ = ∫⁻ x in ball z r, greenOccupationDensity z y r x * g x ∂S.μ ω := by
          refine Eq.trans ?_ (lintegral_withDensity_eq_lintegral_mul _
            (measurable_greenOccupationDensity z y r) hg)
          rw [restrict_withDensity measurableSet_ball]
      _ = ∫⁻ x in ball z r, 2 * ENNReal.ofReal (greenFunction (ball z r) y x) * g x ∂S.μ ω :=
          setLIntegral_congr_fun measurableSet_ball fun x hx => by
            rw [greenOccupationDensity_of_mem hx]

end MatedCRT.KilledOccupation
