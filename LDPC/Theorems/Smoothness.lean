module

public import LDPC.PaperLemmas.Expansion
public import LDPC.Probability.Instances
public import LDPC.PaperLemmas.Folding

/-!
# The smoothness-to-proximity-gap theorem

The headline is the smoothness-to-proximity-gap theorem. Its probability is
over one uniform field seed, for a fixed far interleaved input satisfying the
bad-check bound. It is not a conditional-on-acceptance or MCA statement.
-/

@[expose] public section

namespace SmoothLDPC

open scoped ProbabilityTheory
attribute [local instance] Classical.propDecidable

variable {L R F : Type} [Fintype L] [Fintype R] [Fintype F]
    [DecidableEq L] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R}

/-- Under smoothness, the strict-good-fold probability is at most `1/|F|`. -/
theorem theorem_8 (H : G.WeightedSystem F) {α d : ℚ}
    (hsmooth : IsSmooth H α (d / 2) (d / 2)) (u v : L → F)
    (hfar : PairFar H.code (d / 2) u v)
    (hbad : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R) :
    Pr_{let r ← $ᵖ F}[GoodFold H.code (d / 2) u v r] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  classical
  exact LegacyProbability.prob_uniform_le_inv_of_card_le_one _
    (theorem_8_card H hsmooth u v hfar hbad)

/-- The integer-cutoff expander variant of the few-check lemma. Smoothness is
proved from the graph assumptions; here `d = 2(1−γ)K`.
Choosing `K = δn` requires integrality; any integer `K ≤ δn` is valid. -/
theorem expander_theorem_8 [Nonempty L] [Nonempty R]
    {c k K : ℕ} {γ δ τ α : ℚ}
    (hG : G.IsExpander c k γ δ) (hc : 0 < c)
    (hγ0 : 0 ≤ γ) (hτlo : γ < τ) (hτhi : τ < 1 - 2 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (hα : α < (τ - γ) * k * ((1 - γ) * K) / Fintype.card L)
    (H : G.WeightedSystem F) (u v : L → F)
    (hfar : PairFar H.code ((1 - γ) * K) u v)
    (hbad : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R) :
    Pr_{let r ← $ᵖ F}[GoodFold H.code ((1 - γ) * K) u v r] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  apply LegacyProbability.prob_uniform_le_inv_of_card_le_one
  exact theorem_8_card H (proposition_7 hG hc hγ0 hτlo hτhi hK hα H) u v hfar hbad

end SmoothLDPC
