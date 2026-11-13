import MatedCRT.FirstPass.Derived.ExitCouplingGoodEnv
import MatedCRT.FirstPass.Derived.ExitFiniteData

/-!
# Proposition 6.12 of Berestycki-Gwynne: the good-environment theorem with the scales of the proof

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Proposition 6.12.  The deterministic good-environment theorem
`ExitCouplingGoodEnv.levyProkhorovEDist_stoppedWalk_le_of_goodEnv` has free scale parameters; here they are
chosen as in the proof, in terms of one master scale `δ`:

* `δ' = δ^a` is the radius of the balls of Lemma 6.11 and of the successive exits (6.36);
* the cells meeting `B_{ρ₁}` have diameter at most `d = √δ / 4`;
* `ρ_t = δ^(a χ) / 2` is the time scale in units of `ε⁻¹`, and `T = ε⁻¹ (δ')^χ` the lower exit time of Lemma 6.11;
* the expected exit time from the interior vertices of `B_{√δ}(z)` is at most `Q = ε⁻¹ (√δ)^q` (Lemma 2.19);
* `K = ⌊(2 δ')^{-3}⌋` successive exits (Lemma 6.10).

The estimates enter as hypotheses on one environment; the arithmetic condition on the parameters is the one
produced by `ExitCouplingNumerics.exists_small_parameters`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingParams

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingQuenched MatedCRT.ExitCouplingCells
  MatedCRT.ExitCouplingGlue MatedCRT.ExitCouplingNoShortTravel MatedCRT.ExitCouplingMarkov
  MatedCRT.ExitCouplingHq
  MatedCRT.SuccessiveExitGaps MatedCRT.FirstPass.Derived MatedCRT.InteriorCellGeometry

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Equicontinuity of the laws of the stopped walks in a good environment, with the scales of the proof of
Proposition 6.12.**  The hypotheses `hdiam`, `hTV`, `hQ`, `h611`, `h0` are the estimates of the proof (cell
diameters, total variation of the first exit vertex, Lemma 2.19, Lemma 6.11, (6.36)) in one environment. -/
theorem stoppedWalk_le_of_numerics {mult : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hlf : IsLocallyFiniteMult mult) (hcons : ∀ k : ℤ, mult k (k + 1) ≠ 0)
    (hadj : ∀ j k, mult k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {ρ ρ0 ρ1 δ a χ q e ξ A r : ℝ} {T₀ : ℝ≥0} {ψ ψ₀ : ℝ → ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (he : e = q / 2 - a * χ)
    (hρ0 : ρ + Real.sqrt δ ≤ ρ0) (hρ1 : ρ0 + δ ^ a ≤ ρ1)
    (hd : Real.sqrt δ / 4 < δ ^ a) (hr0 : 2 * (Real.sqrt δ / 4) + δ < Real.sqrt δ)
    (hA : 0 ≤ A) (hψ : 0 ≤ ψ (δ ^ a)) (hψ₀ : 0 ≤ ψ₀ (2 * δ ^ a))
    (hT0 : (T₀ : ℝ) * (2 * (3 * (2 * δ ^ a) + 2 * (Real.sqrt δ / 4)) +
        (2 * δ + 2 * (Real.sqrt δ / 4))) + Real.exp (-(T₀ : ℝ)) < r)
    (hfin : A * δ ^ ξ + 2 * (2 * δ ^ e + ψ₀ (2 * δ ^ a) +
        (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a)) ≤ r)
    (hεδ : ε ≤ δ ^ (a * χ) / 6)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ1).Nonempty → ∀ x ∈ cell ε η k,
      ∀ y ∈ cell ε η k, dist x y ≤ Real.sqrt δ / 4)
    (hTV : ∀ z ∈ ball (0 : ℂ) ρ, ∀ x ∈ cellVertices ε η (ball z δ), ∀ y ∈ cellVertices ε η (ball z δ),
      ∀ T : Set ℤ,
      |(srwLaw mult x).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T} -
        (srwLaw mult y).real
          {X | vExitPosition (interiorCellVertices ε η (ball z (Real.sqrt δ))) X ∈ T}| ≤
        A * δ ^ ξ)
    (hQ : ∀ y : ℂ, ball y (Real.sqrt δ) ⊆ ball (0 : ℂ) ρ0 → ∀ b : ℤ,
      expectedExitTime mult (interiorCellVertices ε η (ball y (Real.sqrt δ))) b ≤
        ENNReal.ofReal (ε⁻¹ * Real.sqrt δ ^ q))
    (h611 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) (ρ1 - δ ^ a)),
      srwLaw mult x {X | (vExitTime (cellVertices ε η (ball (vertexPoint ε η x) (δ ^ a))) X : ℝ≥0∞) <
        ENNReal.ofReal (ε⁻¹ * (δ ^ a) ^ χ)} ≤ ENNReal.ofReal (ψ (δ ^ a)))
    (h0 : ∀ x ∈ cellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult x {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
        succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) (2 * δ ^ a)))
          ⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ (2 * δ ^ a))) :
    ∀ z ∈ ball (0 : ℂ) ρ, ∀ x ∈ cellVertices ε η (ball z δ), ∀ y ∈ cellVertices ε η (ball z δ),
      levyProkhorovEDist
        ((srwLaw mult x).map
          (stoppedInterp (vertexPoint ε η) (ε⁻¹).toNNReal
            (interiorCellVertices ε η (ball (0 : ℂ) ρ0))))
        ((srwLaw mult y).map
          (stoppedInterp (vertexPoint ε η) (ε⁻¹).toNNReal
            (interiorCellVertices ε η (ball (0 : ℂ) ρ0)))) ≤ ENNReal.ofReal r := by
  have hδa : 0 < δ ^ a := Real.rpow_pos_of_pos hδ a
  have hP : 0 < δ ^ (a * χ) := Real.rpow_pos_of_pos hδ _
  have hεi : 0 ≤ ε⁻¹ := inv_nonneg.2 hε.le
  have hrpos : 0 < r := by
    have := Real.exp_pos (-(T₀ : ℝ))
    have h2 : 0 ≤ (T₀ : ℝ) * (2 * (3 * (2 * δ ^ a) + 2 * (Real.sqrt δ / 4)) +
        (2 * δ + 2 * (Real.sqrt δ / 4))) :=
      mul_nonneg T₀.coe_nonneg (by positivity)
    linarith
  have hT : (δ ^ a) ^ χ = δ ^ (a * χ) := (Real.rpow_mul hδ.le a χ).symm
  have hm : 0 < (ε⁻¹).toNNReal := by simpa using inv_pos.2 hε
  have hρt : 0 < (δ ^ (a * χ) / 2).toNNReal := by simpa using hP
  have hmR : (((ε⁻¹).toNNReal : ℝ≥0) : ℝ) = ε⁻¹ := Real.coe_toNNReal _ hεi
  have hρtR : ((((δ ^ (a * χ) / 2).toNNReal : ℝ≥0)) : ℝ) = δ ^ (a * χ) / 2 :=
    Real.coe_toNNReal _ (by positivity)
  have hT6 : 6 ≤ ε⁻¹ * (δ ^ a) ^ χ := by
    rw [hT, inv_mul_eq_div, le_div_iff₀ hε]; linarith
  have hQratio : ENNReal.ofReal (ε⁻¹ * Real.sqrt δ ^ q) /
      ((((ε⁻¹).toNNReal * (δ ^ (a * χ) / 2).toNNReal : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (2 * δ ^ e) := by
    have hmρ : ((((ε⁻¹).toNNReal * (δ ^ (a * χ) / 2).toNNReal : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (ε⁻¹ * (δ ^ (a * χ) / 2)) := by
      rw [ENNReal.ofReal_mul hεi, ENNReal.coe_mul]; rfl
    rw [hmρ, ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    have hsq : Real.sqrt δ ^ q = δ ^ (q / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]; congr 1; ring
    rw [hsq, he, Real.rpow_sub hδ]
    field_simp
  have hap : ENNReal.ofReal (A * δ ^ ξ) + (ENNReal.ofReal (2 * δ ^ e) +
        (ENNReal.ofReal (ψ₀ (2 * δ ^ a)) +
          ((⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ψ (δ ^ a)))) +
      (ENNReal.ofReal (2 * δ ^ e) + (ENNReal.ofReal (ψ₀ (2 * δ ^ a)) +
          ((⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ψ (δ ^ a)))) ≤
        ENNReal.ofReal r := by
    have hKψ : ((⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ψ (δ ^ a)) =
        ENNReal.ofReal ((⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have h2δ : 0 ≤ 2 * δ ^ e := by positivity
    have hKn : 0 ≤ (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a) :=
      mul_nonneg (Nat.cast_nonneg _) hψ
    rw [hKψ, ← ENNReal.ofReal_add hψ₀ hKn, ← ENNReal.ofReal_add h2δ (add_nonneg hψ₀ hKn),
      ← ENNReal.ofReal_add (by positivity) (add_nonneg h2δ (add_nonneg hψ₀ hKn)),
      ← ENNReal.ofReal_add (add_nonneg (by positivity) (add_nonneg h2δ (add_nonneg hψ₀ hKn)))
        (add_nonneg h2δ (add_nonneg hψ₀ hKn))]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hrnn : (((r.toNNReal : ℝ≥0)) : ℝ) = r := Real.coe_toNNReal _ hrpos.le
  have hgood := ExitCouplingGoodEnv.levyProkhorovEDist_stoppedWalk_le_of_goodEnv (mult := mult) hε.le hη hadj
    (ρ := ρ) (ρ0 := ρ0) (ρ1 := ρ1) (δ := δ) (d := Real.sqrt δ / 4) (δ' := δ ^ a)
    hδ hδ1 (by positivity) hδa hρ0 hρ1 hd hr0 hdiam (c := A * δ ^ ξ) hTV
    (fun z _ => ExitFiniteData.finiteExitData_interiorCellVertices hlf hcons hε hη hp isBounded_ball)
    (fun x _ => ExitFiniteData.srwLaw_vExitTime_eq_top_null_cellVertices hlf hcons hε hη hp isBounded_ball x)
    (m := (ε⁻¹).toNNReal) hm (ρt := (δ ^ (a * χ) / 2).toNNReal) hρt
    (Q := ENNReal.ofReal (ε⁻¹ * Real.sqrt δ ^ q))
    (fun z hz b => hQ z (Metric.ball_subset_ball' (by
      rw [mem_ball] at hz; linarith [dist_comm z (0 : ℂ)])) b)
    (g := ⌊ε⁻¹ * (δ ^ a) ^ χ⌋₊) (K := ⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊)
    (by rw [hmR, hρtR, hT]; rw [hT] at hT6
        have := Nat.lt_floor_add_one (ε⁻¹ * δ ^ (a * χ))
        have h3 : ε⁻¹ * (δ ^ (a * χ) / 2) = (ε⁻¹ * δ ^ (a * χ)) / 2 := by ring
        rw [h3]; linarith)
    (T := ε⁻¹ * (δ ^ a) ^ χ) (ψ := ψ (δ ^ a)) (Nat.floor_le (by positivity))
    (R₁ := ρ1 - δ ^ a) (by linarith) h611 (ψ₀ := ENNReal.ofReal (ψ₀ (2 * δ ^ a))) h0
    T₀ r.toNNReal (by rw [hrnn]; exact hT0) (by rw [hQratio]; exact hap)
  exact fun z hz x hx y hy => (hgood z hz x hx y hy)

end ExitCouplingParams
end MatedCRT

#print axioms MatedCRT.ExitCouplingParams.stoppedWalk_le_of_numerics
