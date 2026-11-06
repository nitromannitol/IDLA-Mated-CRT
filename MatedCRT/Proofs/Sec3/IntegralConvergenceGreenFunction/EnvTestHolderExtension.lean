import MatedCRT.Defs.Notation
import Mathlib.Topology.ExtendFrom

/-!
# Hölder extension to the closed ball (E-c2-9)

A function that is Hölder on the open ball `ball z r` extends to a continuous function on the closed
ball, with the same Hölder constant and exponent. The extension is the continuous extension
`extendFrom` of `f`; the limits at the boundary exist because a Hölder function is uniformly continuous,
hence Cauchy along the ball. This is the extension step that places an environment-dependent Hölder
test in the countable family of `EnvTestHolderFamily.lean`.
-/

namespace MatedCRT

open Metric Set Filter Topology
open scoped NNReal ENNReal

/-- A real distance bound `dist (g x) (g y) ≤ C dist x y ^ χ` gives the edistance form `HolderWith C χ g`. -/
theorem holderWith_of_dist_le {α β : Type*} [MetricSpace α] [MetricSpace β] {g : α → β}
    {C χ : ℝ≥0} (h : ∀ x y, dist (g x) (g y) ≤ C * dist x y ^ (χ : ℝ)) : HolderWith C χ g := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg χ),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- A Hölder function on a set has a limit along the set at every point of the closure of the set. -/
theorem exists_tendsto_nhdsWithin_of_holderOnWith {f : ℂ → ℝ} {C χ : ℝ≥0} {s : Set ℂ}
    (hf : HolderOnWith C χ f s) (hχ : 0 < χ) {x : ℂ} (hx : x ∈ closure s) :
    ∃ y, Tendsto f (𝓝[s] x) (𝓝 y) := by
  have : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 (hf.uniformContinuousOn hχ) ε hε
  refine ⟨f '' (s ∩ ball x (δ / 2)), Filter.image_mem_map ?_, ?_⟩
  · exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (ball_mem_nhds x (by linarith)))
  · rintro _ ⟨a, ⟨has, hax⟩, rfl⟩ _ ⟨b, ⟨hbs, hbx⟩, rfl⟩
    apply hδε a has b hbs
    have h1 : dist a x < δ / 2 := hax
    have h2 : dist b x < δ / 2 := hbx
    have h3 : dist a b ≤ dist a x + dist b x := dist_triangle_right a b x
    linarith

/-- **Hölder extension to the closed ball.** A function that is Hölder on the open ball `ball z r`
extends to a continuous function on `closedBall z r`, which is Hölder with the same constant and exponent
and agrees with `f` on the ball. -/
theorem exists_holderWith_closedBall_extension {z : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    {C χ : ℝ≥0} (hχ : 0 < χ) (hf : HolderOnWith C χ f (ball z r)) :
    ∃ F : C(closedBall z r, ℝ), HolderWith C χ F ∧
      ∀ x (hx : x ∈ ball z r), F ⟨x, ball_subset_closedBall hx⟩ = f x := by
  set E : ℂ → ℝ := extendFrom (ball z r) f with hE
  have hcl : closedBall z r ⊆ closure (ball z r) := subset_of_eq (closure_ball z hr.ne').symm
  have hlim : ∀ x ∈ closedBall z r, ∃ y, Tendsto f (𝓝[ball z r] x) (𝓝 y) :=
    fun x hx => exists_tendsto_nhdsWithin_of_holderOnWith hf hχ (hcl hx)
  have hcont : ContinuousOn E (closedBall z r) := continuousOn_extendFrom hcl hlim
  have hEq : EqOn E f (ball z r) := extendFrom_extends (hf.continuousOn hχ)
  have hdist : ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
      dist (E x) (E y) ≤ C * dist x y ^ (χ : ℝ) := by
    intro x hx y hy
    obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 (hcl hx)
    obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.1 (hcl hy)
    have hu' : Tendsto u atTop (𝓝[closedBall z r] x) :=
      tendsto_nhdsWithin_iff.2 ⟨hux, Eventually.of_forall fun n => ball_subset_closedBall (hu n)⟩
    have hv' : Tendsto v atTop (𝓝[closedBall z r] y) :=
      tendsto_nhdsWithin_iff.2 ⟨hvy, Eventually.of_forall fun n => ball_subset_closedBall (hv n)⟩
    have hEu : Tendsto (fun n => E (u n)) atTop (𝓝 (E x)) := (hcont x hx).tendsto.comp hu'
    have hEv : Tendsto (fun n => E (v n)) atTop (𝓝 (E y)) := (hcont y hy).tendsto.comp hv'
    have hd : ∀ n, dist (E (u n)) (E (v n)) ≤ C * dist (u n) (v n) ^ (χ : ℝ) := by
      intro n
      rw [hEq (hu n), hEq (hv n)]
      exact hf.dist_le (hu n) (hv n)
    have hdu : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 (dist x y)) := hux.dist hvy
    have hR : Tendsto (fun n => C * dist (u n) (v n) ^ (χ : ℝ)) atTop
        (𝓝 (C * dist x y ^ (χ : ℝ))) :=
      (hdu.rpow_const (Or.inr (NNReal.coe_nonneg χ))).const_mul (C : ℝ)
    exact le_of_tendsto_of_tendsto (hEu.dist hEv) hR (Eventually.of_forall hd)
  refine ⟨⟨fun x => E x, continuousOn_iff_continuous_domRestrict.1 hcont⟩, ?_, fun x hx => hEq hx⟩
  exact holderWith_of_dist_le fun x y => hdist x x.2 y y.2

end MatedCRT
