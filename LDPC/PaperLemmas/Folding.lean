module

public import LDPC.PaperLemmas.Expansion
public import LDPC.Probability.Instances

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

/-- The few-check folding lemma, with separate absolute puncturing budget `P` and distance `D`:
two good seeds would force a common agreement set whose complement has size
at most `P`. The note specializes to `P = D = d/2`. -/
theorem theorem_8_card (H : G.WeightedSystem F) {α P D : ℚ}
    (hsmooth : IsSmooth H α P D) (u v : L → F)
    (hfar : PairFar H.code P u v)
    (hbad : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R) :
    (Finset.univ.filter (GoodFold H.code D u v)).card ≤ 1 := by
  classical
  obtain ⟨L₀, hL₀, hD⟩ := hsmooth (H.badChecks u v) hbad
  have huv := inputs_mem_relaxed_badChecks H u v
  apply Finset.card_le_one.mpr
  intro r₁ hr₁ r₂ hr₂
  by_contra hne
  obtain ⟨c₁, hc₁, he₁⟩ := (Finset.mem_filter.mp hr₁).2
  obtain ⟨c₂, hc₂, he₂⟩ := (Finset.mem_filter.mp hr₂).2
  have hag₁ := agreement_of_close (code_le_relaxed H (H.badChecks u v))
    (Finset.univ \ L₀) hD
    ((H.relaxedCode _).add_mem huv.1 ((H.relaxedCode _).smul_mem r₁ huv.2)) hc₁ he₁
  have hag₂ := agreement_of_close (code_le_relaxed H (H.badChecks u v))
    (Finset.univ \ L₀) hD
    ((H.relaxedCode _).add_mem huv.1 ((H.relaxedCode _).smul_mem r₂ huv.2)) hc₂ he₂
  obtain ⟨cu, hcu, cv, hcv, hag⟩ :=
    interpolate_agreement H.code (Finset.univ \ L₀) u v c₁ c₂ hne hc₁ hc₂ hag₁ hag₂
  have hbound : (pairDistance u v cu cv : ℚ) ≤ P := calc
    _ ≤ (L₀.card : ℚ) := by exact_mod_cast pairDistance_le_deleted L₀ u v cu cv hag
    _ ≤ P := hL₀
  exact (not_lt_of_ge hbound) (hfar cu hcu cv hcv)

end SmoothLDPC
