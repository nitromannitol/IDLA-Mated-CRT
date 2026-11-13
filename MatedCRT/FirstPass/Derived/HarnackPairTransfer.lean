import MatedCRT.FirstPass.Derived.PairEventsMultInvariance
import MatedCRT.FirstPass.Derived.CurveMultOuterTransfer

/-!
# Transfer of the failure of the pair events to every valid environment

Berestycki–Gwynne (2020), Lemmas 3.9–3.11.  The itinerary event `PairItinGood` and the disconnection event
`PairL311Good` of the mesh-`ε` mated-CRT map of a path `ω` and a curve `η` depend on `ω` only through the edge count
of Definition 1.1 (`pairItinGood_iff_of_multEq`, `pairL311Good_iff_of_multEq`). Hence the failure event of a valid
environment `S` is the preimage of a set of pairs (curve, edge multiplicities), and the outer-measure transfer
`measure_eta_mult_preimage_le_of_valid` (a one-sided mating-rigid set `G`, full for every `γ`-correlated two-sided
Brownian law) bounds its probability by the probability of the same event in any valid environment on a standard
Borel carrier, for any two models with the same normalized space-filling SLE law:

* `measure_not_of_multEq_le_of_valid`: for any property `Q ω η` of a path and a curve that depends on `ω` only
  through the edge count at mesh `ε`, `S.P {¬ Q (S.bm ·) (S.η ·)} ≤ S'.P {¬ Q (S'.bm ·) (S'.η ·)}`;
* `pairItin_failure_le_of_valid`, `pairL311_failure_le_of_valid`: the two pair events.
-/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- The pairs (curve, edge multiplicities) at mesh `ε` for which the property `Q` fails for every path with that
edge count. -/
def failSetOfMult (ε : ℝ) (Q : MatedCRTHarmonic.MatedCRT.Path2 → (ℝ → ℂ) → Prop) :
    Set ((ℝ → ℂ) × (ℤ → ℤ → ℕ)) :=
  {x | ∀ ω : MatedCRTHarmonic.MatedCRT.Path2,
    bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) = x.2 → ¬ Q ω x.1}

/-- If `Q ω η` depends on `ω` only through the edge count at mesh `ε`, the failure event of a valid environment is
the preimage of `failSetOfMult ε Q` under (curve, edge multiplicities). -/
theorem setOf_not_eq_preimage_failSetOfMult {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    {Q : MatedCRTHarmonic.MatedCRT.Path2 → (ℝ → ℂ) → Prop}
    (hQ : ∀ (ω ω' : MatedCRTHarmonic.MatedCRT.Path2) (η : ℝ → ℂ),
      bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
        bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2) → (Q ω η ↔ Q ω' η)) :
    {w | ¬ Q (S.bm w) (S.η w)} = {w | (S.η w, S.mult ε w) ∈ failSetOfMult ε Q} := by
  ext w
  constructor
  · intro hw ω hω hQω
    exact hw ((hQ ω (S.bm w) (S.η w) hω).1 hQω)
  · intro hw
    exact hw (S.bm w) rfl

/-- **Transfer of the failure of a multiplicity-determined event.** Let `S, S'` be valid environments of models
with the same normalized space-filling SLE law `ν` and the same `0 < γ < 2`, the carrier of `S'` a standard Borel
space, and `G` a one-sided mating-rigid set, full for every `γ`-correlated two-sided Brownian law. If `Q ω η`
depends on the path `ω` only through its edge count at mesh `ε`, then
`S.P {¬ Q (S.bm ·) (S.η ·)} ≤ S'.P {¬ Q (S'.bm ·) (S'.η ·)}` (outer measures). -/
theorem measure_not_of_multEq_le_of_valid {𝒮 𝒮' : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (ε : ℝ) {Q : MatedCRTHarmonic.MatedCRT.Path2 → (ℝ → ℂ) → Prop}
    (hQ : ∀ (ω ω' : MatedCRTHarmonic.MatedCRT.Path2) (η : ℝ → ℂ),
      bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) =
        bmEdgeCount ε (fun t => (ω' t).1) (fun t => (ω' t).2) → (Q ω η ↔ Q ω' η)) :
    S.P {w | ¬ Q (S.bm w) (S.η w)} ≤ S'.P {w | ¬ Q (S'.bm w) (S'.η w)} := by
  rw [setOf_not_eq_preimage_failSetOfMult S ε hQ, setOf_not_eq_preimage_failSetOfMult S' ε hQ]
  exact measure_eta_mult_preimage_le_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG ε (failSetOfMult ε Q)

/-- **Transfer of the failure of the itinerary event** `PairItinGood` (Berestycki–Gwynne (3.21)) at mesh
`ε ≥ 0`, with the hypotheses of `measure_not_of_multEq_le_of_valid`. -/
theorem pairItin_failure_le_of_valid {𝒮 𝒮' : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ) (z : ℂ) (r : ℝ) :
    S.P {w | ¬ PairItinGood ε (S.bm w) (S.η w) p z r} ≤
      S'.P {w | ¬ PairItinGood ε (S'.bm w) (S'.η w) p z r} :=
  measure_not_of_multEq_le_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG ε
    (Q := fun ω η => PairItinGood ε ω η p z r)
    fun _ _ η hm => pairItinGood_iff_of_multEq hε hm η p z r

/-- **Transfer of the failure of the disconnection event** `PairL311Good` (Berestycki–Gwynne, Lemma 3.11) at mesh
`ε ≥ 0`, with the hypotheses of `measure_not_of_multEq_le_of_valid`. -/
theorem pairL311_failure_le_of_valid {𝒮 𝒮' : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) {ε : ℝ} (hε : 0 ≤ ε) (ρ'' f p : ℝ) :
    S.P {w | ¬ PairL311Good ε (S.bm w) (S.η w) ρ'' f p} ≤
      S'.P {w | ¬ PairL311Good ε (S'.bm w) (S'.η w) ρ'' f p} :=
  measure_not_of_multEq_le_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG ε
    (Q := fun ω η => PairL311Good ε ω η ρ'' f p)
    fun _ _ η hm => pairL311Good_iff_of_multEq hε hm η ρ'' f p

end MatedCRT.FirstPass.Derived

/-! ## Audit -/
#print axioms MatedCRT.FirstPass.Derived.measure_not_of_multEq_le_of_valid
#print axioms MatedCRT.FirstPass.Derived.pairItin_failure_le_of_valid
#print axioms MatedCRT.FirstPass.Derived.pairL311_failure_le_of_valid
