import MatedCRT.FirstPass.S5d.FloorProof.ConstantStep
import MatedCRT.FirstPass.S5d.FloorProof.Cell
import MatedCRT.FirstPass.S5d.FloorProof.Limit
import MatedCRT.FirstPass.S5d.FloorProof.Radius
import MatedCRT.FirstPass.S5d.FloorCellStep
import MatedCRT.FirstPass.S5d.CellSizeSmall
import MatedCRT.FirstPass.S5d.CoverEvent
import MatedCRT.FirstPass.S4S6c.Uniform68Env
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S5c.HExclusive
import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4
import MatedCRT.External.SLE
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.SourceVertex
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma

/-!
# The floor of the stopped clause: `StoppedFloorCellStep` (task fp-S5d-5-1, floor note Part I; theorem `stoppedFloorCell_proved`)

`stoppedFloorCell_proved` proves the single floor input `StoppedFloorCellStep 𝒮` (S5d/FloorCellStep.lean) from the named
inputs of floor note Part I, Section 1 (`h41`, `h33`, `h28`, `hm`, `hcell`) and the floor constant `FloorConstantStep` (the
output of Steps 4-5, i.e. §4 `StoppedFloorObstacleVersion` (S5k.lean) and §5 with the [C20] gap `HarmonicBallStrictObstacleGapStep`,
supplied by z2 in S5l.lean; it is taken as a named hypothesis here, with the form fixed in its docstring).

Proof (Sections 6-9 of the note): fix `N = n + 1` (localization `L_n = {s ≥ 1/N, M ≤ N}`, (16)-(17)), the radius `r_N`
(`floorRadius`, (18)), `e_N = 1/(4N(1+t))`, `d = min(δ/8, r_N/4)`; on the event `{t < T}` outside the good events
`E_w` (h41), `E_g` (h33, the annulus `r_N ≤ |x| ≤ ρ`), `E_cell` (Lemma 2.8) and the a.s. facts, the cell floor of
`floor_cell_bound` (Cell.lean) holds on every cell meeting `B⁻_{δ/2}(Λ_t)`; the failure probability is at most the sum of
`P(L_N^c)` and the three good-event failure probabilities, so the epsilon-n limit (Limit.lean) gives the conclusion.
The floor constant is `c = C⁻¹ s/2` with `C` from `MepsScalingInput` (`m_ε ≥ C⁻¹ ε⁻¹`, eq:meps-scaling).
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT

namespace FloorProof

/-- The clusters are monotone in `t` and `t < T` gives `Λ_t ⊆ B_{ρ/3}` (floor note (3)): if `t < sup{s : Λ_s ⊆ B_{ρ/3}}`
then `Λ_t ⊆ Λ_u ⊆ B_{ρ/3}` for some admissible `u > t`. -/
theorem subset_third_of_lt_clusterExitTime {Λ : ℝ → Set ℂ} {ρ t : ℝ} (hmono : MonotoneOn Λ (Ioi 0))
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) : Λ t ⊆ ball (0 : ℂ) (ρ / 3) := by
  have hT' : t < sSup {s : ℝ | 0 < s ∧ Λ s ⊆ ball (0 : ℂ) (ρ / 3)} := hT
  have hne : {s : ℝ | 0 < s ∧ Λ s ⊆ ball (0 : ℂ) (ρ / 3)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hT'
    linarith
  obtain ⟨u, ⟨hu0, huΛ⟩, htu⟩ := exists_lt_of_lt_csSup hne hT'
  exact Set.Subset.trans (hmono (Set.mem_Ioi.2 ht) (Set.mem_Ioi.2 hu0) htu.le) huΛ

/-- The localization `L_N = {s ≥ 1/N, M ≤ N}` (floor note (16)-(17)), `N = n + 1`: its complement tends to zero in probability
(as `n → ∞`), since `s > 0` and `M` is finite everywhere. -/
theorem tendsto_Lbad {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {s M : Ω → ℝ}
    (hs : Measurable s) (hM : Measurable M) (hspos : ∀ ω, 0 < s ω) :
    Tendsto (fun n : ℕ => P {ω | ¬ (1 / ((n : ℝ) + 1) ≤ s ω ∧ M ω ≤ (n : ℝ) + 1)}) atTop (𝓝 0) := by
  set L : ℕ → Set Ω := fun n => {ω | ¬ (1 / ((n : ℝ) + 1) ≤ s ω ∧ M ω ≤ (n : ℝ) + 1)} with hLdef
  have hmeas : ∀ n, NullMeasurableSet (L n) P := by
    intro n
    apply MeasurableSet.nullMeasurableSet
    have h1 : MeasurableSet {ω | 1 / ((n : ℝ) + 1) ≤ s ω} := measurableSet_le measurable_const hs
    have h2 : MeasurableSet {ω | M ω ≤ (n : ℝ) + 1} := measurableSet_le hM measurable_const
    exact (h1.inter h2).compl
  have hanti : Antitone L := by
    intro n m hnm ω hω h
    apply hω
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact ⟨le_trans (one_div_le_one_div_of_le hpos (by linarith)) h.1, le_trans h.2 (by linarith)⟩
  have hinter : (⋂ n, L n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro ω hω
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt (hspos ω)
    obtain ⟨n₂, hn₂⟩ := exists_nat_gt (M ω)
    have hmem : ω ∈ L (n₁ + n₂) := Set.mem_iInter.1 hω (n₁ + n₂)
    apply hmem
    have hn1 : (n₁ : ℝ) ≤ ((n₁ + n₂ : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]
    have hn2 : (n₂ : ℝ) ≤ ((n₁ + n₂ : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)]
    refine ⟨?_, ?_⟩
    · exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hn₁.le
    · linarith
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
  rw [hinter, measure_empty] at hlim
  exact hlim

/-- The tolerance `e_N = 1/(4N(1+t))`, `N = n+1`, of floor note Section 7. -/
noncomputable def floorTol (t : ℝ) (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1) * (1 + t))

theorem floorTol_pos {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 < floorTol t n := by
  unfold floorTol
  positivity

/-- **Section 8 of the floor note, pathwise, for one outcome `ω`, one mesh `ε` and one index `N ≥ 1`.** On the good
events `E_w`, `E_g`, `E_cell` and the localization `L_N` at `ω`, every cell meeting `B⁻_{δ/2}(Λ_t)` satisfies the floor
`c/ε ≤ u^ε_t(k)` with `c = C⁻¹ s/2` (equation (24)). -/
theorem floor_point {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {γ ρ t δ ε C N e : ℝ}
    {Λ : Ω → ℝ → Set ℂ} {s M : Ω → ℝ} {ω : Ω}
    (hρ : 0 < ρ) (ht : 0 < t) (hδ : 0 < δ) (hδρ : δ < ρ) (hε : 0 < ε)
    (hmε : C⁻¹ * ε⁻¹ ≤ S.mε ε) (hC : 0 < C⁻¹) (hα : 0 < S.c₀ / 6) (hN1 : 1 ≤ N)
    (he : e = 1 / (4 * N * (1 + t)))
    (hcont : Continuous (S.η ω)) (hprop : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (harea : IsAreaParametrized (S.μ ω) (S.η ω))
    (hv0 : ∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0)
    (hadjω : ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmonoω : MonotoneOn (Λ ω) (Ioi 0)) (hF : t < clusterExitTime (Λ ω) ρ)
    (hsω : 0 < s ω) (hs1 : s ω ≤ 1)
    (hsω' : ∀ x ∈ innerNbhd (δ / 4) (Λ ω t), x ≠ 0 →
      s ω ≤ S.c₀ / 6 * (_root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x +
        t * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x))
    (hMω : ∀ x ∈ closedBall (0 : ℂ) ρ,
      |S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x| ≤ M ω)
    (hL : 1 / N ≤ s ω) (hLM : M ω ≤ N)
    (hEw : ∀ x ∈ ball (0 : ℂ) ρ,
      |rescale (S.mε ε) ε (S.η ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) x -
        S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x| ≤ e)
    (hEg : ∀ x : ℂ, floorRadius ρ (S.c₀ / 6) t N ≤ ‖x‖ → ‖x‖ ≤ ρ →
      |rescale (S.mε ε) ε (S.η ω)
          (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ))
            (vertexOf ε (S.η ω) 0) a) x -
        S.c₀ / 6 * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x| ≤ e)
    (hcs : ∀ j : ℤ, (cell ε (S.η ω) j ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell ε (S.η ω) j) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2))
    (hεθ : ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) < min (δ / 8) (floorRadius ρ (S.c₀ / 6) t N / 4)) :
    ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
      C⁻¹ * s ω / 2 / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hmεpos : 0 < S.mε ε := lt_of_lt_of_le (mul_pos hC (inv_pos.2 hε)) hmε
  -- the cell-diameter tolerance `d` and the radius `r` of floor note Section 7
  have hr : 0 < floorRadius ρ (S.c₀ / 6) t N := floorRadius_pos hρ
  have hr3 : 3 * floorRadius ρ (S.c₀ / 6) t N < ρ := by
    have := floorRadius_le (α := S.c₀ / 6) hρ hα ht hN0
    linarith
  have hsymm : ∀ a b : ℤ, S.mult ε ω a b = S.mult ε ω b a := fun a b => S.mult_symm ε ω a b
  obtain ⟨hlf, hcons, _⟩ := MatedCRT.Uniform68Env.envAt S hε ω hcont hprop hadjω
  have hfin : (ballInterior ε (S.η ω) ρ).Finite :=
    (MatedCRT.TraceInputs68.cellVertices_finite_of_tendsto hε hprop Metric.isBounded_ball).subset
      (fun k hk => hk.1)
  have hexcl : ∀ j : ℤ, ∃ x ∈ cell ε (S.η ω) j, ∀ b : ℤ, x ∈ cell ε (S.η ω) b → b = j :=
    fun j => MatedCRT.S5c.exists_exclusive_mem_cell harea hε j
  have hsmall : ∀ j : ℤ, (cell ε (S.η ω) j ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (cell ε (S.η ω) j) < min (δ / 8) (floorRadius ρ (S.c₀ / 6) t N / 4) :=
    fun j hj => lt_of_le_of_lt (hcs j hj) hεθ
  have hΛ : Λ ω t ⊆ ball (0 : ℂ) (ρ / 3) := subset_third_of_lt_clusterExitTime hmonoω ht hF
  have hden : N ≠ 0 := hNpos.ne'
  have hen : (1 + t) * e ≤ 1 / (4 * N) := by
    refine le_of_eq ?_
    rw [he]
    field_simp
  have hv0' : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) ρ → |S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x| ≤ N :=
    fun x hx => le_trans (hMω x hx) hLM
  have hpole : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ ≤ 3 * floorRadius ρ (S.c₀ / 6) t N →
      N + 4 ≤ S.c₀ / 6 * t * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x :=
    fun x h0 hx => pole_of_floorRadius hρ hα ht hN0 h0 hx
  have hEg0 : ∀ x : ℂ, floorRadius ρ (S.c₀ / 6) t N ≤ ‖x‖ → ‖x‖ ≤ ρ →
      |rescale (S.mε ε) ε (S.η ω)
          (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a) x -
        S.c₀ / 6 * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x| ≤ e := by
    intro x h1 h2
    have := hEg x h1 h2
    rw [hv0 ε hε] at this
    exact this
  intro k hk
  have hbound := floor_cell_bound (m := S.mult ε ω) (ε := ε) (ρ := ρ) (t := t) (mε := S.mε ε)
    (α := S.c₀ / 6) (δ := δ) (d := min (δ / 8) (floorRadius ρ (S.c₀ / 6) t N / 4))
    (r := floorRadius ρ (S.c₀ / 6) t N) (e := e) (n := N) (s := s ω) (η := S.η ω)
    (W := fun x => _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x)
    (G := fun x => _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x)
    (Λt := Λ ω t) (k := k) hsymm hlf hcons hcont hε ht hmεpos hδ hδρ hr hr3 hfin
    (fun j l h => hadjω ε hε j l h) hexcl (min_le_left _ _) (min_le_right _ _) hsmall hΛ hEw hEg0
    (fun x hx => hv0' x hx) hpole hsω' hL hs1 (by linarith) hen hk
  -- the floor `s/2 ≤ m_ε⁻¹ u` gives `c/ε ≤ u` with `m_ε ≥ C⁻¹ ε⁻¹` (eq:meps-scaling)
  have hu : S.mε ε * (s ω / 2) ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k := by
    have h1 := mul_le_mul_of_nonneg_left hbound hmεpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hmεpos.ne', one_mul] at h1
  calc C⁻¹ * s ω / 2 / ε = (C⁻¹ * ε⁻¹) * (s ω / 2) := by ring
    _ ≤ S.mε ε * (s ω / 2) := mul_le_mul_of_nonneg_right hmε (by linarith)
    _ ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k := hu

/-- The annulus `{x : r ≤ |x| ≤ ρ}` of the good event `E_g` (floor note Section 7). -/
def floorAnnulus (ρ α t N : ℝ) : Set ℂ := {x : ℂ | floorRadius ρ α t N ≤ ‖x‖ ∧ ‖x‖ ≤ ρ}

/-- The bad event of `E_w` (the event of `ConvergenceDivisibleStmt` at tolerance `e`, floor note (19)). -/
def floorBadW {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t e ε : ℝ) : Set Ω :=
  {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
    e < |rescaledMatedLeastSupersolution S ρ t ε ω x -
      S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x|}

/-- The bad event of `E_g` (the event of `UniformConvergenceGreenKernelStmt` on the annulus, floor note (19)). -/
def floorBadG {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ t e N ε : ℝ) : Set Ω :=
  {ω | ¬ ∀ x ∈ floorAnnulus ρ (S.c₀ / 6) t N,
    |rescale (S.mε ε) ε (S.η ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ))
          (vertexOf ε (S.η ω) 0) a) x -
      S.c₀ / 6 * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x| ≤ e}

/-- The localization failure `L_N^c` of floor note (16), `L_N = {s ≥ 1/N, M ≤ N}`. -/
def floorBadLoc {Ω : Type} (s M : Ω → ℝ) (N : ℝ) : Set Ω := {ω | ¬ (1 / N ≤ s ω ∧ M ω ≤ N)}

/-- **Proposition 5.1 floor, the single floor input (floor note Part I; corrected tex 2362 [C21]).** Given the named inputs
`h41` (Theorem `convergence-divisible`), `h33` (Lemma `uniform-convergence-of-greens-function`), `h28` (Lemma
`cell-size-estimate`), `hm` (`eq:meps-scaling`), `hcell` (cell adjacency) and the floor constant `hconst`, the cell floor
`StoppedFloorCellStep 𝒮` holds (Sections 6-9: the epsilon-n limit of Limit.lean over the good events). -/
theorem stoppedFloorCell_proved {𝒮 : SpaceFillingSLEModel}
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hconst : FloorConstantStep 𝒮) : StoppedFloorCellStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨C, hC1, hCm⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmeps⟩ := hCm Ω S hS
  obtain ⟨s, M, hsm, hMm, hsbd, hfl⟩ := hconst γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hc0 : 0 < S.c₀ := div_pos two_pos hm0
  have hα : 0 < S.c₀ / 6 := div_pos hc0 (by norm_num)
  have hCpos : 0 < C⁻¹ := inv_pos.2 (by linarith)
  have hsfield : Measurable s := hsm.mono (MatedCRTEnv.fieldSigma_le S hS) le_rfl
  have hMfield : Measurable M := hMm.mono (MatedCRTEnv.fieldSigma_le S hS) le_rfl
  have hfe : S.fieldSigma ≤ S.envSigma := by
    unfold MatedCRTEnv.envSigma
    exact le_sup_left
  have hsenv : Measurable[S.envSigma] s := hsm.mono hfe le_rfl
  -- the almost sure facts
  have hmono : ∀ᵐ ω ∂S.P, MonotoneOn (Λ ω) (Ioi 0) := hΛ.mono fun ω h => h.2.1.monotoneOn
  have hcont : ∀ᵐ ω ∂S.P, Continuous (S.η ω) := hS.isAreaParametrized.mono fun _ hω => hω.1
  have hprop : ∀ᵐ ω ∂S.P, Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    MatedCRTEnv.IsValid.ae_tendsto_cocompact hS
  have harea : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) := hS.isAreaParametrized
  have hv0 : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0 :=
    MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero hS
  have hadj : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    hcell γ hγ hγ2 Ω S hS
  have hgood := ((((hmono.and hcont).and hprop).and harea).and hv0).and (hadj.and hfl)
  -- the good events of Section 7, each with probability tending to one
  have hθ := tendsto_cellExponent_rpow hγ
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ := nhdsWithin_le_nhds (gt_mem_nhds hε₀)
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hLb : Tendsto (fun n : ℕ => S.P (floorBadLoc s M ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_Lbad S.P hsfield hMfield (fun ω => (hsbd ω).1)
  have hBw : ∀ n : ℕ, Tendsto (fun ε => S.P (floorBadW S Λ ρ t (floorTol t n) ε)) (𝓝[>] 0) (𝓝 0) :=
    fun n => h41 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht (floorTol t n) (floorTol_pos ht n)
  have hBg : ∀ n : ℕ, Tendsto (fun ε => S.P (floorBadG S ρ t (floorTol t n) ((n : ℝ) + 1) ε)) (𝓝[>] 0) (𝓝 0) := by
    intro n
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hr := floorRadius_pos (α := S.c₀ / 6) (t := t) (N := (n : ℝ) + 1) hρ
    have hO : floorAnnulus ρ (S.c₀ / 6) t ((n : ℝ) + 1) ⊆ closedBall (0 : ℂ) ρ \ {0} := by
      intro x hx
      refine ⟨mem_closedBall_zero_iff.2 hx.2, fun h0 => ?_⟩
      have h0' : x = 0 := h0
      have h1 := hx.1
      rw [h0', norm_zero] at h1
      linarith
    have hinf : 0 < Metric.infDist (0 : ℂ) (floorAnnulus ρ (S.c₀ / 6) t ((n : ℝ) + 1)) := by
      have hne : (floorAnnulus ρ (S.c₀ / 6) t ((n : ℝ) + 1)).Nonempty := by
        have hnorm : ‖((ρ / 2 : ℝ) : ℂ)‖ = ρ / 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have hrle := floorRadius_le (α := S.c₀ / 6) (t := t) (N := (n : ℝ) + 1) hρ hα ht hN.le
        refine ⟨((ρ / 2 : ℝ) : ℂ), ?_⟩
        show floorRadius ρ (S.c₀ / 6) t ((n : ℝ) + 1) ≤ ‖((ρ / 2 : ℝ) : ℂ)‖ ∧
          ‖((ρ / 2 : ℝ) : ℂ)‖ ≤ ρ
        rw [hnorm]
        constructor <;> linarith
      refine lt_of_lt_of_le hr ((Metric.le_infDist hne).2 fun y hy => ?_)
      rw [dist_zero_left]
      exact hy.1
    exact h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS ρ 0 0 hρ Subset.rfl (mem_ball_self hρ) (floorTol t n)
      (floorTol_pos ht n) (floorAnnulus ρ (S.c₀ / 6) t ((n : ℝ) + 1)) hO hinf
  have hBc := tendsto_cellSizeEvent_compl hγ hγ2 hρ hρ1 h28 S hS
  refine ⟨fun ω => C⁻¹ * s ω / 2, (hsenv.const_mul C⁻¹).div_const 2,
    fun ω => div_pos (mul_pos hCpos (hsbd ω).1) two_pos, ?_⟩
  unfold TendsToOneOn
  refine tendsto_zero_of_le_add (h := fun n : ℕ => S.P (floorBadLoc s M ((n : ℝ) + 1)))
    (q := fun n ε => S.P (floorBadW S Λ ρ t (floorTol t n) ε) +
      (S.P (floorBadG S ρ t (floorTol t n) ((n : ℝ) + 1) ε) +
        S.P (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ)) hLb ?_ ?_
  · intro n
    simpa using (hBw n).add ((hBg n).add hBc)
  · intro n
    have hθn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) <
        min (δ / 8) (floorRadius ρ (S.c₀ / 6) t ((n : ℝ) + 1) / 4) :=
      hθ.eventually (gt_mem_nhds (lt_min (div_pos hδ (by norm_num))
        (div_pos (floorRadius_pos (α := S.c₀ / 6) (t := t) (N := (n : ℝ) + 1) hρ) (by norm_num))))
    dsimp only
    filter_upwards [hev1, hev2, hθn] with ε hε1 hε2 hε3
    refine le_trans (measure_mono_ae ?_) (measure_le_four S.P _ _ _ _)
    filter_upwards [hgood] with ω hω hωF
    obtain ⟨⟨⟨⟨⟨hmo, hco⟩, hpo⟩, hao⟩, hvo⟩, hadjo, hflo⟩ := hω
    obtain ⟨hF, hnotE⟩ := hωF
    by_contra hcon
    have hLs : 1 / ((n : ℝ) + 1) ≤ s ω ∧ M ω ≤ (n : ℝ) + 1 := by
      by_contra h
      exact hcon (Or.inl (Or.inl (Or.inl h)))
    have hGall : ∀ x ∈ floorAnnulus ρ (S.c₀ / 6) t ((n : ℝ) + 1), |rescale (S.mε ε) ε (S.η ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ))
          (vertexOf ε (S.η ω) 0) a) x - S.c₀ / 6 * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x|
        ≤ floorTol t n := by
      by_contra h
      exact hcon (Or.inl (Or.inr h))
    have hEw : ∀ x ∈ ball (0 : ℂ) ρ, |rescale (S.mε ε) ε (S.η ω)
        (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) x -
          S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x| ≤ floorTol t n := by
      intro x hx
      by_contra h
      exact hcon (Or.inl (Or.inl (Or.inr ⟨hF, x, hx, lt_of_not_ge h⟩)))
    have hCell : ω ∈ cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε := by
      by_contra h
      exact hcon (Or.inr h)
    have hCell' : ∀ j : ℤ, (cell ε (S.η ω) j ∩ ball (0 : ℂ) ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) ≤ diam (cell ε (S.η ω) j) ∧
          diam (cell ε (S.η ω) j) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) := hCell
    have hEg0 : ∀ x : ℂ, floorRadius ρ (S.c₀ / 6) t ((n : ℝ) + 1) ≤ ‖x‖ → ‖x‖ ≤ ρ →
        |rescale (S.mε ε) ε (S.η ω)
            (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) ρ))
              (vertexOf ε (S.η ω) 0) a) x -
          S.c₀ / 6 * _root_.HarmonicBalls.greenFunction (ball (0 : ℂ) ρ) 0 x| ≤ floorTol t n :=
      fun x h1 h2 => hGall x ⟨h1, h2⟩
    have hmεC : C⁻¹ * ε⁻¹ ≤ S.mε ε := (hmeps ε hε2 hε1).1
    have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    have hE := floor_point S hρ ht hδ hδρ hε2 hmεC hCpos hα hN1 rfl hco hpo hao hvo hadjo hmo hF
      (hsbd ω).1 (hsbd ω).2 (hflo hF).1 (hflo hF).2 hLs.1 hLs.2 hEw hEg0
      (fun j hj => (hCell' j hj).2) hε3
    exact hnotE hE

end FloorProof

end MatedCRT
