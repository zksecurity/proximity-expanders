module

public import LDPC.Theorems.All

/-! Start with these five public entry points.
The remaining checks are the complete reference. No assumptions are introduced. -/

-- 1. Original distance from expansion
-- Distance
#check @SmoothLDPC.Main.expansion_distance

-- 2. Smoothness from expansion
-- Smoothness
#check @SmoothLDPC.Main.expansion_smoothness

-- 3. Main technical lemma: few failed checks, radius d/2, error 1/|F|
#check @SmoothLDPC.Main.smoothness_proximity_gap

-- 4. Main folding theorem
#check @SmoothLDPC.Main.folding

-- 5. Shared-query verifier soundness
-- Shared queries
#check @SmoothLDPC.Main.shared_query_soundness

-- Complete reference: remaining headline statements.
#check @SmoothLDPC.smoothness_from_expansion
#check @SmoothLDPC.proposition_7
#check @SmoothLDPC.Protocol.fold_only_response_probability_le
#check @SmoothLDPC.Protocol.fold_only_soundness_of_smooth
#check @SmoothLDPC.Protocol.combined_folding_paper_parameters
#check @SmoothLDPC.MCA.card_bad_le_of_smooth
#check @SmoothLDPC.MCA.probability_le_of_smooth
#check @SmoothLDPC.MCA.queried_soundness
#check @SmoothLDPC.MCA.queried_soundness_of_budgets
#check @SmoothLDPC.MCA.guarantees_of_smooth
#check @SmoothLDPC.Protocol.soundness_of_smooth
#check @SmoothLDPC.Protocol.shared_soundness_of_smooth
#check @SmoothLDPC.Protocol.shared_soundness_of_expansion
#check @SmoothLDPC.Protocol.shared_query_paper_parameters
#check @SmoothLDPC.theorem_8
#check @SmoothLDPC.expander_theorem_8

-- Paper statements and the closed-budget smoothness boundary.
#check @SmoothLDPC.half_distance_smoothness
#check @SmoothLDPC.Paper.main_technical_lemma
#check @SmoothLDPC.Paper.folding
#check @SmoothLDPC.Paper.ligero
#check @SmoothLDPC.Paper.check_sampling
#check @SmoothLDPC.Paper.hybrid_sampling
#check @SmoothLDPC.IsSmooth.mono
#check @SmoothLDPC.smoothness_from_expansion_le
