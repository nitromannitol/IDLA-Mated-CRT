import MatedCRT.FirstPass.Derived.ExitBeforeBallHit
import MatedCRT.FirstPass.Derived.HarnackPairEvents
import MatedCRT.FirstPass.Derived.ValidPeanosphere
import MatedCRT.FirstPass.Derived.ExitTimeLowerBound
import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected

/-!
# Berestycki–Gwynne (2020), Lemma 6.13, last assertion, with polynomially high probability

For `x ∈ V^ε(B_ρ \ B_{ρ-δ})` the walk on the mated-CRT map started at `x` exits `V^ε(B_ρ)` before it hits
`V^ε(∂B_{√δ}(η x))` with probability at least `1 - A δ^ξ`, with polynomially high probability as `ε → 0` in every
valid environment.  The deterministic step is `ExitBeforeBallHit.srwLaw_exit_before_ballHit`; its inputs hold
with polynomially high probability: the disconnection event of Lemma 3.11 at the floor `ε^β` (the hypothesis
`hPair`, whose second conjunct is the one proved by `hPair_of_reference`), the cell diameters (the cell size
estimate), and almost surely the connectivity of the graph and the point-connectedness of the cells (the
Peanosphere of a valid environment).  For `δ` bounded below the estimate is trivial.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitBeforeBallHitEnv

open MeasureTheory Metric Set Filter Topology _root_.HarmonicBalls
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.T15A

/-- **Berestycki–Gwynne (2020), Lemma 6.13, last assertion.**  Given the cell size estimate and the failure bound of
the disconnection event of Lemma 3.11 with floor `ε^{β₀}` in every valid environment: for `γ ∈ (0,2)` and
`ρ ∈ (0,1)` there are `ξ, A > 0` such that for every `δ ∈ (0,1)`, with polynomially high probability as `ε → 0`,
from every `x ∈ V^ε(B_ρ \ B_{ρ-δ})` the walk exits `V^ε(B_ρ)` before hitting `V^ε(∂B_{√δ}(η x))` with probability at
least `1 - A δ^ξ`; moreover, with the same probability, every vertex visited up to the exit time has its cell inside
`B_{√δ}(η x)`. -/
theorem exitBeforeBallHit_polyHighProb_cells (𝒮 : SpaceFillingSLEModel) (h28 : CellSizeEstimateStmt 𝒮)
    (hL311 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₁ : ℝ, 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
          S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X <
            vHitTime (cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}} := by
  intro γ hγ hγ2 ρ hρ hρ1
  obtain ⟨β, α, hβ, hα, hPγ⟩ := hL311 γ hγ hγ2
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ' : ℝ, ρ' = (1 + ρ) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = (1 + ρ') / 2 := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by rw [hρ'def]; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ'def]; linarith
  have hρρ' : ρ < ρ' := by rw [hρ'def]; linarith
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁def]; linarith
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁def]; linarith
  obtain ⟨p₁, hp₁, hPρ⟩ := hPγ ρ' hρ'0 hρ'1
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = min p₁ (1 / 2) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hpdef]; exact lt_min hp₁ (by norm_num)
  have hp1 : p < 1 := by rw [hpdef]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hpp₁ : p ≤ p₁ := by rw [hpdef]; exact min_le_left _ _
  obtain ⟨ξ₀, hξ₀def⟩ : ∃ ξ₀ : ℝ, ξ₀ = t15cXi p := ⟨_, rfl⟩
  have hξ₀ : 0 < ξ₀ := by rw [hξ₀def]; exact t15cXi_pos hp0 hp1
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = (6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ))) ^ ξ₀ := ⟨_, rfl⟩
  have hbase : 0 < 6 * (8 * (3 * ρ + 3 + ρ') / (ρ' - ρ)) := by
    have h1 : 0 < ρ' - ρ := by linarith
    have h2 : 0 < 8 * (3 * ρ + 3 + ρ') := by positivity
    positivity
  have hA₀ : 0 < A₀ := by rw [hA₀def]; exact Real.rpow_pos_of_pos hbase _
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀ : ℝ, s₀ = min (1 / 16) (min (ρ / 4) ((ρ' - ρ) / 2)) := ⟨_, rfl⟩
  have hs₀ : 0 < s₀ := by
    rw [hs₀def]
    exact lt_min (by norm_num) (lt_min (by positivity) (by linarith))
  refine ⟨ξ₀ / 2, A₀ + (s₀ ^ (ξ₀ / 2))⁻¹, by positivity, by positivity, ?_⟩
  intro δ hδ0 hδ1 Ω _ S hS
  by_cases hδ : s₀ ≤ δ
  · -- large `δ`: the bound is trivial
    refine ExitTimeLowerBound.polyHighProb_of_ae_of_small (E := fun _ => (Set.univ : Set Ω)) (G := Set.univ)
      ⟨1, one_pos, 0, 1, one_pos, fun r _ _ => by simp⟩ (ae_of_all _ fun _ => trivial)
      (r₁ := 1) one_pos ?_
    intro r hr hr1 ω _ x hx
    have hpow : s₀ ^ (ξ₀ / 2) ≤ δ ^ (ξ₀ / 2) :=
      Real.rpow_le_rpow hs₀.le hδ (by positivity)
    have hpos : 0 < s₀ ^ (ξ₀ / 2) := Real.rpow_pos_of_pos hs₀ _
    have hge : 1 ≤ (s₀ ^ (ξ₀ / 2))⁻¹ * δ ^ (ξ₀ / 2) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpos]
      linarith
    have hAnn : 0 ≤ A₀ * δ ^ (ξ₀ / 2) := by positivity
    have hnp : 1 - (A₀ + (s₀ ^ (ξ₀ / 2))⁻¹) * δ ^ (ξ₀ / 2) ≤ 0 := by nlinarith
    rw [ENNReal.ofReal_of_nonpos hnp]
    exact zero_le
  · -- small `δ`
    replace hδ := not_le.1 hδ
    have hδ16 : δ < 1 / 16 := lt_of_lt_of_le hδ (by rw [hs₀def]; exact min_le_left _ _)
    have hδρ : δ < ρ / 4 := lt_of_lt_of_le hδ (by rw [hs₀def]; exact (min_le_right _ _).trans (min_le_left _ _))
    have hδρ' : δ < (ρ' - ρ) / 2 :=
      lt_of_lt_of_le hδ (by rw [hs₀def]; exact (min_le_right _ _).trans (min_le_right _ _))
    have hδmin : δ ≤ min (1 / 16) (min (ρ / 4) ((ρ' - ρ) / 2)) := by rw [← hs₀def]; exact hδ.le
    -- the cell radius event on `B_{ρ'}`
    obtain ⟨a, ha, halim, hcellev⟩ := exists_vanishing_closedBall_cellRadius 𝒮 h28 (ρ := ρ₁)
      (r := ρ') (z := 0) hγ hγ2 hρ₁0 hρ₁1 hρ'0
      (by
        intro q hq
        rw [mem_ball_zero_iff] at hq ⊢
        rw [hρ₁def]
        linarith) S hS
    -- the disconnection event of Lemma 3.11
    obtain ⟨C, hC⟩ := hPρ Ω S hS
    have hE : PolyHighProb S.P fun ε => {ω | PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β) p} := by
      refine ⟨α, hα, C, 1, one_pos, fun r hr hr1 => ?_⟩
      refine le_trans (measure_mono ?_) (hC r hr hr1)
      intro ω hω hgood
      exact hω (hgood.mono le_rfl le_rfl hpp₁)
    -- an almost sure Peanosphere and the identity of the cells
    obtain ⟨η', hη'ae, hpeano, hcellEq⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
    have hG : ∀ᵐ ω ∂S.P, ω ∈ {ω : Ω | MatedCRTHarmonic.RouteM.Peanosphere (S.bm ω) (η' ω) ∧
        ∀ ε : ℝ, ∀ x : ℤ, cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)} := by
      filter_upwards [hpeano, hcellEq] with ω h1 h2
      exact ⟨h1, h2⟩
    have hβlim : Tendsto (fun ε : ℝ => ε ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuous_rpow_const hβ.le).tendsto 0
      rw [Real.zero_rpow hβ.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ a < δ / 2 ∧ ε ^ β < δ :=
      (halim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 2))).and
        (hβlim.eventually (Iio_mem_nhds hδ0))
    obtain ⟨r₁, hr₁, hr₁sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ExitTimeLowerBound.polyHighProb_of_ae_of_small (FirstPass36.polyHighProb_inter hE hcellev) hG hr₁ ?_
    rintro r hr hrr ω ⟨⟨hωL, hωC⟩, hωpeano, hωcell⟩ x hx
    obtain ⟨hra, hrβ⟩ := hr₁sub ⟨hr, hrr⟩
    obtain ⟨hlf, H, hHc, h311⟩ := hωL
    have hdiam : ∀ k, (cell r (S.η ω) k ∩ ball (0 : ℂ) ρ').Nonempty →
        ∀ u ∈ cell r (S.η ω) k, ∀ v ∈ cell r (S.η ω) k, dist u v ≤ δ := by
      intro k hk u hu v hv
      obtain ⟨q, hqc, hqb⟩ := hk
      have hk' : k ∈ cellVertices r (S.η ω) (closedBall (0 : ℂ) ρ') := ⟨q, hqc, ball_subset_closedBall hqb⟩
      have h1 := hωC k hk' u hu
      have h2 := hωC k hk' v hv
      have h3 := dist_triangle_left u v (vertexPoint r (S.η ω) k)
      linarith
    have hconn := MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl r (S.bm ω) hlf
    have hLC : H.PointConnected :=
      MatedCRTHarmonic.RouteM.pointConnected_of_peanosphere_holds hωpeano H
        (funext fun k => (congrFun hHc k).trans (hωcell r k))
    have hmain := ExitBeforeBallHit.srwLaw_exit_before_ballHit_cells (ε := r) (ω := S.bm ω) (η := S.η ω) hlf H hHc
      hconn hLC (β := β) (p := p) (ρ := ρ) (ρ' := ρ') hr hρ hρρ' hp0 hp1 h311 hδ0 hδmin hrβ.le hdiam hx
    rw [← hξ₀def, ← hA₀def] at hmain
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
    have hpos : 0 ≤ δ ^ (ξ₀ / 2) := Real.rpow_nonneg hδ0.le _
    have hinv : 0 ≤ (s₀ ^ (ξ₀ / 2))⁻¹ := inv_nonneg.2 (Real.rpow_nonneg hs₀.le _)
    rw [add_mul]
    have := mul_nonneg hinv hpos
    linarith

/-- **Berestycki–Gwynne (2020), Lemma 6.13, last assertion** (event without the localization of the walk):
`exitBeforeBallHit_polyHighProb_cells` for the event `{exit time < hitting time}`. -/
theorem exitBeforeBallHit_polyHighProb (𝒮 : SpaceFillingSLEModel) (h28 : CellSizeEstimateStmt 𝒮)
    (hL311 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₁ : ℝ, 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
          S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X <
            vHitTime (cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X}} := by
  intro γ hγ hγ2 ρ hρ hρ1
  obtain ⟨ξ, A, hξ, hA, h⟩ := exitBeforeBallHit_polyHighProb_cells 𝒮 h28 hL311 γ hγ hγ2 ρ hρ hρ1
  refine ⟨ξ, A, hξ, hA, fun δ hδ0 hδ1 Ω _ S hS => ?_⟩
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := h δ hδ0 hδ1 Ω S hS
  refine ⟨p, hp, C, r₀, hr₀, fun r hr hrr => (measure_mono ?_).trans (hb r hr hrr)⟩
  intro ω hω hgood
  exact hω fun x hx => (hgood x hx).trans (measure_mono fun _ hX => hX.1)

end ExitBeforeBallHitEnv
end MatedCRT
