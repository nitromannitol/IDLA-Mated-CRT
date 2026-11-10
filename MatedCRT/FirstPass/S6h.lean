import MatedCRT.FirstPass.S6h.Core
import MatedCRT.FirstPass.S6e.Final
import MatedCRT.FirstPass.S6h.Schedule
import MatedCRT.FirstPass.S6m

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

/-- Elementary inclusion for write-up C12: if `closure (fillCells Θ) ⊆ B(0, ρ/2)` and `r ≤ ρ/4`, then the
`r`-thickening of `fillCells Θ` lies in `B(0, ρ)` (so its cell vertices lie in `F0 = V^ε(B_ρ)`). -/
lemma thickening_fill_subset_ball_c12 {ε ρ r : ℝ} {η : ℝ → ℂ} (hρ : 0 < ρ) (hr : r ≤ ρ / 4) {Θ : Set ℤ}
    (hcl : closure (fillCells ε η Θ) ⊆ Metric.ball 0 (ρ / 2)) :
    Metric.thickening r (fillCells ε η Θ) ⊆ Metric.ball 0 ρ := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := Metric.mem_thickening_iff.1 hz
  have hx0 : dist x 0 < ρ / 2 := Metric.mem_ball.1 (hcl (subset_closure hx))
  have htri := dist_triangle z x 0
  rw [Metric.mem_ball]
  linarith

/-- Monotonicity of the cell vertices of a set of the plane (write-up C12). -/
lemma cellVertices_mono_c12 {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun _ hk => Set.Nonempty.mono (Set.inter_subset_inter_right _ h) hk

/-- (Lemma 6.8, the concrete bridge: the guarded probability statement with the concrete test schedule `cfgSchedule`.)
The guarded uniform exit bound `probTendsToOne_lemma68_guarded` with the schedule chosen as in
`configuration_le_pow_concrete`. The containment `hC12` (write-up C12) is DISCHARGED here by `Lemma68C12.concreteC12_killed`
(z10, `S6m.lean`). Named inputs: the environment `hEnv` (η continuous and proper), the local finiteness `hlf`, the cell
adjacency `hadj` of the multiplicity, the cell-size input `hmesh` (the diameters of the cells meeting `B_ρ` are at most
`Δ(p,r)/100` for `r ∈ [α ε, dd ω]`; the cell-size estimate Draft `CellSizeEstimateStmt`, Draft/Section2.lean:131, with
the exponent comparison on `ω₀`), the per-state inputs `hstate` (write-up C4, `StateTestInputs`), the cutoffs `hRρ`
(`R ≤ ρ/100`) and `hR1000` (`R ≤ 1000^(-1/ζ)`; implied by `R ≤ r0Min` via `Cutoff.r0Min_le_zeta`), and `0 < s₀`, `0 < ρ`,
`c0 < 1/8`. -/
theorem probTendsToOne_lemma68_concrete {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (S : MatedCRTEnv Ω)
    (ρ s₀ γ : ℝ) {E : ℝ → Set Ω} (hE : ProbTendsToOne P E) {G : Set Ω} (hG : P Gᶜ = 0)
    {α : ℝ → ℝ} (hα : ∀ ε, 0 < ε → 0 < α ε)
    {dd : Ω → ℝ} {R : ℝ} (hdd : ∀ ω, dd ω ≤ R)
    {ζ p qStar q0 c0 : ℝ} (good : ℝ → Ω → ℂ → ℕ → Prop)
    (hρ0 : 0 < ρ) (hs0 : 0 < s₀) (hRρ : R ≤ ρ / 100)
    (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hR : R ≤ Lemma68Cutoff.rAmp q0 ζ)
    (hR1000 : R ≤ (1000 : ℝ) ^ (-1 / ζ)) (hc0 : c0 < 1 / 8)
    (hq0def : q0 = qStar / 9) (hq : 0 ≤ qStar) (hq1' : qStar ≤ 1) (hq9 : qStar ≤ 9) (hp : p ≤ 3)
    (hpζ : p = 2 * ζ + 2)
    (hEnv : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G,
      Continuous (S.η ω) ∧ Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, IsLocallyFiniteMult (S.mult ε ω) ∧ ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hadj : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmesh : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ Metric.ball (0 : ℂ) ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) k) ≤ Lemma68Scales.Delta p r / 100)
    (hstate : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68, FullAdm S ρ s₀ γ ε ω r i →
      ∃ Good : ℤ → Prop, Lemma68Concrete.StateTestInputs (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω) (↑i.A : Set ℤ)
        qStar c0 Good) :
    ProbTendsToOne P (fun ε => {ω | ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      Lemma68Final.guardedExit (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S) ε ω r i ≤ 1 / 2}) := by
  have hC12 : ∀ ε, 0 < ε → ∀ ω ∈ E ε ∩ G, ∀ r : ℝ, α ε ≤ r → r ≤ dd ω → ∀ i : Config68,
      FullAdm S ρ s₀ γ ε ω r i →
        Lemma68Concrete.ConcreteC12 (S.mult ε ω) i.a ε (S.η ω) p r (good ε ω)
          (Lemma68Admissible.killed ε (S.η ω) i.Θ i.F0 r) := by
    intro ε hε ω hω r hαr hrd i hi
    obtain ⟨hη, hproper⟩ := hEnv ε hε ω hω
    obtain ⟨hlf', hcons⟩ := hlf ε hε ω hω
    obtain ⟨⟨hF0, hcl, hsub⟩, hadm⟩ := hi
    unfold Lemma68Admissible.Admissible at hadm
    have hr0 : 0 < r := (hα ε hε).trans_le hαr
    have hrR : r ≤ R := hrd.trans (hdd ω)
    have hrρ : r ≤ ρ / 100 := hrR.trans hRρ
    have hcut : r ^ ζ ≤ 1 / 1000 := by
      calc r ^ ζ ≤ ((1000 : ℝ) ^ (-1 / ζ)) ^ ζ :=
            Real.rpow_le_rpow hr0.le (hrR.trans hR1000) hζ.le
        _ = 1 / 1000 := by
            rw [← Real.rpow_mul (by norm_num)]
            have h1 : -1 / ζ * ζ = -1 := by field_simp
            rw [h1, Real.rpow_neg_one]
            norm_num
    have hr1 : r < 1 := by
      by_contra h
      have h1 : 1 ≤ r ^ ζ := Real.one_le_rpow (not_lt.1 h) hζ.le
      linarith
    have hp0 : 0 < p := by rw [hpζ]; positivity
    have hK : (fillCells ε (S.η ω) (↑i.Θ : Set ℤ)).Nonempty :=
      ⟨0, hsub (Metric.mem_ball_self hs0)⟩
    have hKb : fillCells ε (S.η ω) (↑i.Θ : Set ℤ) ⊆ Metric.ball 0 (ρ / 2) :=
      subset_closure.trans hcl
    have hr4 : r ≤ ρ / 4 := by linarith
    have hF : cellVertices ε (S.η ω)
        (Metric.thickening r (fillCells ε (S.η ω) (↑i.Θ : Set ℤ))) ⊆ (↑i.F0 : Set ℤ) := by
      rw [hF0]
      exact cellVertices_mono_c12 (thickening_fill_subset_ball_c12 (ε := ε) (r := r) hρ0 hr4 hcl)
    exact Lemma68C12.concreteC12_killed (d := Lemma68Scales.Delta p r / 100) (good ε ω) hε hη hproper hp0 hr0 hr1 hpζ
      hcut hrρ hlf' hcons (hadj ε hε ω hω) hK hKb le_rfl (hmesh ε hε ω hω r hαr hrd) hF
      ⟨by linarith [hadm.1.1], by linarith [hadm.1.2]⟩
  exact Lemma68Final.probTendsToOne_uniform_half_guarded hE hG hα hdd hq0 hq1 hζ hζ' hR
    (fun ε ω r i => FullAdm S ρ s₀ γ ε ω r i) (exitQ S)
    (Lemma68Concrete.configuration_le_pow_concrete S ρ s₀ γ E G α dd R ζ p qStar q0 c0 good hq0def hq hq1' hq9 hp
      hpζ hζ hα hdd hR hR1000 hc0 hEnv hlf hstate hC12)

end Lemma68Config

end MatedCRT
