module

public import LDPC.PaperLemmas.Protocol

/-! Acceptance soundness for the parity-augmented folding verifier.
This is an information-theoretic theorem for fixed committed inputs and exact
response-code membership, with independent check and coordinate samples. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {L R F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [DecidableEq F] [Fintype F] {G : TannerGraph L R}

/-- The full acceptance bound, without an assumption that the inputs fail few checks. -/
theorem soundness_of_smooth (H : G.WeightedSystem F) {P : ℚ} {s t : ℕ}
    (hs : IsSmooth H ((t : ℚ) / Fintype.card R) P s) :
    Soundness H P s t := by
  let _ := SampleableType.ofFintype F; let _ := SampleableType.ofFintype R
  let _ := SampleableType.ofFintype L
  intro u v hfar response Qp Qs
  by_cases hb : (H.badChecks u v).card ≤ t
  · have hbad : ((H.badChecks u v).card : ℚ) ≤
        (t : ℚ) / Fintype.card R * Fintype.card R := by
      rw [div_mul_cancel₀ _ (by positivity)]
      exact_mod_cast hb
    exact (acceptance_le_of_few H hs u v hfar hbad response Qp Qs).trans
      (le_max_left _ _)
  · exact (acceptance_le_of_many H u v response Qp Qs t (by omega)).trans
      (le_max_right _ _)

end SmoothLDPC.Protocol
