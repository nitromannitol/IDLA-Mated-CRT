# Lemma 3.2: audit of uses after [C6]

| Use in corrected paper | Assessment and smallest repair |
| --- | --- |
| Lemma 3.1, Borel–Cantelli | BREAKS independently of [C6]: polynomial probability at deterministic ε does not justify a random scale sequence. Thin a deterministic sequence to summable failure probabilities first and use its random subsequences (N3, review-L32). |
| Lemma 3.1, interior estimate | OK after [C6]: cell-size control puts a in the interior of the larger ball, and ε^β ≤ 2δ for sufficiently small ε. Replace ε by ε^β in the displayed estimate; the distance numerator bound is 2δ + 2δ², and the supremum is over the larger ball. |
| Lemma 3.1, boundary estimate | OK for unscaled data with the χ-dependent ξ′; apply the estimate to εu for the scaled-data repair below. |
| Lemma 3.3 via 3.1 | OK with respect to [C6]: uses interior compactness; maximum principle handles the boundary. N3 applies to the subsequence argument. |
| Lemma 3.5 via 3.1 | BREAKS independently of [C6]: the data mεφ have order ε⁻¹ and do not satisfy the unscaled Hölder hypothesis with a uniform constant for nonconstant boundary φ (N1). Strengthen 3.1's hypothesis to C′ε⁻¹ times the Hölder modulus and apply [C6] to εu. Handle N3 as above. |
| Lemma 3.7, Step 1 via 3.1 | OK with respect to [C6]: only interior compactness is used; N3 applies to random subsequences. |
| Lemma 3.7, Step 3 via 3.5 | OK with respect to N1: the boundary data are zero; N3 applies to the subsequence argument. |
| Lemma 3.7, Step 2 direct use | BREAKS independently of [C6]: the annulus is not simply connected and its inner boundary data are not shown Hölder (N2). Use the already established uniform Green-function convergence away from the pole and integrate directly; cell boundary errors vanish as their μh mass tends to the mass of the two circles, zero a.s. |
| Lemma 4.6 via 3.1 | OK with respect to [C6]: uses interior compactness and a boundary barrier; N3 applies. |
| Lemma 4.8, barrier via 3.5 | BREAKS through N1 for its nonconstant boundary data φδ + δ; the scaled-data repair applies. |
| Lemma 4.8 via 3.5 | BREAKS through N1: polynomial nonconstant φ requires the scaled-data repair to 3.1 and hence the 3.5 proof. |

N1 needs its own correction to Lemma 3.1, beyond the authorized [C6] correction. See `review-L32.md`, N1–N3. The Draft now chooses ξ′ after χ and before C′, with ξ′ ≤ χ, as in the corrected paper. The existing proof step retains the weaker quantifier order; `discreteHolderContinuityCorrected_of_draft` supplies it from the Draft.
