import MatedCRT.FirstPass.Derived.SrwRingAssembly
import MatedCRT.FirstPass.Derived.SrwRingGeometry

/-!
# The per-pair ring estimate on a sphere

Berestycki–Gwynne (2020), Lemma 3.10 in the form (3.21), specialised to the data that the Harnack inequality for the
Green function needs.  Fix a sphere `∂B_s(z)`, a grid centre `z'` with `|z - z'| ≤ h` and the grid circles of radii
`a = s - 3h`, `b = s + 3h` around `z'`, where `δ ≤ h` bounds the diameter of the cells near the sphere and `300 h ≤ s`.
For a barrier `I = P ∪ O` consisting of cells inside `B_{a/4}(z')` and cells having a point farther than `T` from `z'`,
the per-pair estimate (`srwLaw_ringPair_lower`) gives, for every pair of vertices `x, y` whose cells meet the sphere,
the lower bound `p₀ p₁` for the probability that the trace of simple random walk from `x` before the first visit to
`I` separates `y` from `I`, provided the edge-end walk follows a polar template itinerary from the vertices meeting the
two grid circles with probability at least `p₀`, and satisfies the event of Lemma 3.11 from the vertices meeting
`B_{s/5}(w)`, `w ∈ ∂B_s(z)`, with probability at least `p₁`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

section Sphere

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- **The per-pair ring estimate for two vertices of a sphere** (see the module documentation). -/
theorem srwLaw_ringPair_lower_sphere (hε : 0 ≤ ε) {o : ℤ}
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω h) o)
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {z z' : ℂ} {s h₀ δ T : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀) (hhs : 300 * h₀ ≤ s)
    (hzz : dist z z' ≤ h₀)
    (hdiam : ∀ k, (H.cell k ∩ ball z' (6 * (s + 3 * h₀) / 5)).Nonempty →
      ∀ x ∈ H.cell k, ∀ x' ∈ H.cell k, dist x x' ≤ δ)
    {P O : Set ℤ} (hP : ∀ k ∈ P, ∀ q ∈ H.cell k, dist q z' ≤ (s - 3 * h₀) / 4)
    (hO : ∀ k ∈ O, ∃ q ∈ H.cell k, T < dist q z') (hT : 6 * (s + 3 * h₀) / 5 + δ ≤ T)
    (hT2 : 7 * s / 5 + h₀ ≤ T) {p₀ p₁ : ℝ≥0∞}
    (hItin : ∀ c, (c = s - 3 * h₀ ∨ c = s + 3 * h₀) → ∀ y ∈ verticesMeeting H.cell (sphere z' c),
      p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
        {ξ | PolarTemplateItinerary H z' c ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    (h311 : ∀ w ∈ sphere z s, ∀ y ∈ verticesMeeting H.cell (ball w (s / 5)),
      p₁ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
        {ξ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w (s / 5)
          ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    {x y : ℤ} (hx : ∃ q ∈ H.cell x, dist q z = s) (hy : ∃ q ∈ H.cell y, dist q z = s) :
    p₀ * p₁ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
      {ξ | GraphSeparates (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
        (traceBefore (id : ℤ → ℤ) (P ∪ O) ξ) {y} (P ∪ O)} := by
  obtain ⟨w, hwy, hwz⟩ := hy
  obtain ⟨q0, hq0x, hq0z⟩ := hx
  have hwz' : w ∈ sphere z s := mem_sphere.2 hwz
  have ha : 0 < s - 3 * h₀ := by linarith
  have hab : s - 3 * h₀ ≤ s + 3 * h₀ := by linarith
  have hw1 : dist w z' ≤ s + h₀ := by
    have := dist_triangle w z z'
    linarith
  have hw2 : s - h₀ ≤ dist w z' := by
    have := dist_triangle w z' z
    rw [dist_comm z' z] at this
    linarith
  have hwn : ‖w - z'‖ = dist w z' := (dist_eq_norm w z').symm
  obtain ⟨hIcirc, hIann, hIfar⟩ := ringPair_barrier_geometry H (z' := z') (w := w) (a := s - 3 * h₀)
    (b := s + 3 * h₀) (r := s / 5) (δ := δ) (T := T) ha hab hδ hdiam hP hO hT (by rw [hwn]; linarith)
    (by rw [hwn]; linarith)
  have hxA : x ∈ LatticeProb.LQG.annulusCells H.cell z' (s - 3 * h₀) (s + 3 * h₀) := by
    have hq0' : dist q0 z' ≤ s + h₀ := by
      have := dist_triangle q0 z z'
      linarith
    have hq0'' : s - h₀ ≤ dist q0 z' := by
      have := dist_triangle q0 z' z
      rw [dist_comm z' z] at this
      linarith
    intro q hq
    have hd : dist q q0 ≤ δ := hdiam x ⟨q0, hq0x, mem_ball.2 (by linarith)⟩ q hq q0 hq0x
    have h1 := dist_triangle q q0 z'
    have h2 := dist_triangle q0 q z'
    rw [dist_comm q0 q] at h2
    constructor <;> linarith
  exact srwLaw_ringPair_lower h hε H hlf hcons (z' := z') (w := w) (a := s - 3 * h₀) (b := s + 3 * h₀)
    (r := s / 5) ha (by linarith) (by linarith) (by linarith) (by linarith) (by rw [hwn, abs_le]; constructor <;> linarith)
    (by rw [hwn, abs_le]; constructor <;> linarith) (finite_annulusCells H z' _ _) hIcirc hIann hIfar hItin
    (h311 w hwz') hxA hwy

end Sphere

end MatedCRT

#print axioms MatedCRT.srwLaw_ringPair_lower_sphere
