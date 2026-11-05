import MatedCRT.Steps.Sec3.UniformConvergenceGreenKernel
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PoleLocation
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.HarmonicTranslation
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite

/-! # Boundary control for Lemma 3.3 -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- Interior convergence and the discrete maximum principle give convergence in
a sufficiently thin boundary layer. -/
theorem greenKernelBoundaryStep (𝒮 : SpaceFillingSLEModel) : GreenKernelBoundaryStep 𝒮 := by
  intro h210 h34 h214 h28 h31 hinterior h213 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
    r z y hr hball hy δ hδ O hO hdist
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨r₀, hr₀0, hr₀r, hgreen⟩ :=
    greenFunction_ball_boundary_small hy (S.c₀ / 6) hδ4
  let L : ℝ := max r₀ (dist y z)
  have hLr : L < r := max_lt hr₀r (show dist y z < r from hy)
  have hL0 : 0 ≤ L := le_trans dist_nonneg (le_max_right _ _)
  let q : ℝ := (L + r) / 2
  let d : ℝ := (r - L) / 8
  have hd : 0 < d := by dsimp [d]; linarith
  have hq0 : 0 < q + d := by dsimp [q, d]; linarith
  have hqr : q + d < r := by dsimp [q, d]; linarith
  have hyq : dist y z + d < q := by
    dsimp [q, d]
    linarith [le_max_right r₀ (dist y z)]
  have hr₀q : r₀ < q - d := by
    dsimp [q, d]
    linarith [le_max_left r₀ (dist y z)]
  let K : Set ℂ := closedBall z (q + d) \ ball z (q - d)
  have hKsub : K ⊆ closedBall z (q + d) := sdiff_subset
  have hKdist : 0 < q - d - dist y z := by linarith
  have hKaway : ∀ x ∈ K, q - d - dist y z ≤ dist y x := by
    intro x hx
    have hxlo : q - d ≤ dist x z := le_of_not_gt hx.2
    have ht := dist_triangle x y z
    rw [dist_comm x y] at ht
    linarith
  have hKgreen : ∀ x ∈ K, |S.c₀ / 6 * greenFunction (ball z r) y x| < δ / 4 := by
    intro x hx
    apply hgreen x
    constructor
    · change dist x z ≤ r
      have hxhi : dist x z ≤ q + d := hx.1
      linarith
    · change ¬ dist x z ≤ r₀
      have hxlo : q - d ≤ dist x z := le_of_not_gt hx.2
      linarith
  have hcv := hinterior h210 h34 h214 h28 h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z y hr hball hy (q + d) hq0 hqr K hKsub (q - d - dist y z) hKdist hKaway (δ / 4) hδ4
  have hcvprob : ProbTendsToOne S.P fun ε =>
      {ω | ∀ x ∈ K, |rescaledBallGreenKernel S r z y ε ω x -
        S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ / 4} := by
    unfold ProbTendsToOne
    change Tendsto (fun ε => S.P {ω | ¬ ∀ x ∈ K,
      |rescaledBallGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ / 4})
      (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa only [not_forall, not_imp, not_le, exists_prop] using hcv
  let G : Set Ω := {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    (∀ ε : ℝ, 0 < ε → ∀ a b, S.mult ε ω a b ≠ 0 →
      (cell ε (S.η ω) a ∩ cell ε (S.η ω) b).Nonempty) ∧
    (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))}
  have hcell := adjacentCellsMeetAeStep 𝒮
  have hG : ∀ᵐ ω ∂S.P, ω ∈ G := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      hcell γ hγ hγ2 Ω S hS, hS.ae_isLocallyFiniteMult hγ hγ2 hcell] with ω hη hp ha hl
    exact ⟨hη, hp, ha, hl⟩
  have hpG : ProbTendsToOne S.P fun _ => G := probTendsToOne_of_ae hG
  have hpdiam := hS.probTendsToOne_small_cells ρ d hd
  refine ⟨q + d, hq0, hqr, ((hpG.inter hpdiam).inter hcvprob).mono_pos ?_⟩
  intro ε hε ω hω
  rcases hω with ⟨⟨⟨hη, hp, ha, hlf⟩, hdiam⟩, hcvω⟩
  have hsmall : ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ x ∈ cell ε (S.η ω) b, ∀ w ∈ cell ε (S.η ω) b, dist x w ≤ d := by
    intro b hb x hx w hw
    exact (dist_le_diam_of_mem (isCompact_Icc.image hη.1).isBounded hx hw).trans (hdiam b hb)
  have hKbound : ∀ x : ℂ, q - d ≤ dist x z → dist x z < q + d →
      |rescaledBallGreenKernel S r z y ε ω x| ≤ δ / 2 := by
    intro x hlo hhi
    have hx : x ∈ K := ⟨le_of_lt hhi, by change ¬ dist x z < q - d; linarith⟩
    have hdiff := abs_le.mp (hcvω x hx)
    have hg := abs_lt.mp (hKgreen x hx)
    apply abs_le.mpr
    constructor <;> linarith
  let c : ℝ := (S.mε ε)⁻¹ * ε⁻¹
  let A := interiorCellVertices ε (S.η ω) (ball z r)
  have hscale (x : ℂ) : rescaledBallGreenKernel S r z y ε ω x =
      c * greenKernel (S.mult ε ω) A (vertexOf ε (S.η ω) y) (vertexOf ε (S.η ω) x) := by
    simp [rescaledBallGreenKernel, rescale, c, A, mul_assoc]
  have hpos : ∀ x : ℂ, q + d ≤ dist x z →
      c * greenKernel (S.mult ε ω) A (vertexOf ε (S.η ω) y) (vertexOf ε (S.η ω) x) ≤ δ / 2 := by
    apply scaled_greenKernel_vertexOf_le_of_small_cells hη hp hε (S.mult_symm ε ω)
      (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) (ha ε hε) hball hd.le hyq hqr (by positivity) hsmall
    intro x hlo hhi
    rw [← hscale]
    exact (abs_le.mp (hKbound x hlo hhi)).2
  have hneg : ∀ x : ℂ, q + d ≤ dist x z →
      -c * greenKernel (S.mult ε ω) A (vertexOf ε (S.η ω) y) (vertexOf ε (S.η ω) x) ≤ δ / 2 := by
    apply scaled_greenKernel_vertexOf_le_of_small_cells hη hp hε (S.mult_symm ε ω)
      (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) (ha ε hε) hball hd.le hyq hqr (by positivity) hsmall
    intro x hlo hhi
    rw [neg_mul, ← hscale]
    have hh := (abs_le.mp (hKbound x hlo hhi)).1
    linarith
  intro x hx
  have hxout : q + d ≤ dist x z := le_of_lt (lt_of_not_ge hx.2)
  have hxgreen : |S.c₀ / 6 * greenFunction (ball z r) y x| < δ / 4 := by
    apply hgreen x
    exact ⟨(hO hx.1).1, by change ¬ dist x z ≤ r₀; linarith⟩
  have hkernel : |rescaledBallGreenKernel S r z y ε ω x| ≤ δ / 2 := by
    rw [hscale]
    apply abs_le.mpr
    constructor
    · have hn := hneg x hxout
      rw [neg_mul] at hn
      linarith
    · exact hpos x hxout
  calc
    |rescaledBallGreenKernel S r z y ε ω x - S.c₀ / 6 * greenFunction (ball z r) y x| ≤
        |rescaledBallGreenKernel S r z y ε ω x| + |S.c₀ / 6 * greenFunction (ball z r) y x| := abs_sub _ _
    _ ≤ δ := by linarith

/-- Lemma 3.3 follows from its interior identification step. -/
theorem uniformConvergenceGreenKernel_of_interiorStep (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessAeStep 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hinterior : GreenKernelInteriorStep 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_steps 𝒮 h210 h34 h214 h28 h31 h213 hinterior
    (greenKernelBoundaryStep 𝒮)

end MatedCRT
