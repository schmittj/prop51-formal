import Prop51.PositiveSaddle

namespace Prop51

/-!
# Default finite-window chunks for the positive-saddle certificate

Generated finite-window §6 certificates can use these 100-row chunks for
`401 ≤ a ≤ 2000`.  The Boolean checks for each chunk remain separate; this
file only proves that the chosen half-open intervals cover the whole finite
window.
-/

/-- Default 100-row chunks covering the finite positive-saddle window
`401 ≤ a ≤ 2000`. -/
def positiveSaddleDefaultChunks : List (Nat × Nat) :=
  [(401, 100), (501, 100), (601, 100), (701, 100),
   (801, 100), (901, 100), (1001, 100), (1101, 100),
   (1201, 100), (1301, 100), (1401, 100), (1501, 100),
   (1601, 100), (1701, 100), (1801, 100), (1901, 100)]

theorem positiveSaddleDefaultChunks_cover :
    PositiveSaddleFiniteWindowChunkCover positiveSaddleDefaultChunks := by
  intro a ha h2000
  by_cases h501 : a < 501
  · refine ⟨(401, 100), ?_, ?_, ?_⟩
    · norm_num [positiveSaddleDefaultChunks]
    · omega
    · omega
  · by_cases h601 : a < 601
    · refine ⟨(501, 100), ?_, ?_, ?_⟩
      · norm_num [positiveSaddleDefaultChunks]
      · omega
      · omega
    · by_cases h701 : a < 701
      · refine ⟨(601, 100), ?_, ?_, ?_⟩
        · norm_num [positiveSaddleDefaultChunks]
        · omega
        · omega
      · by_cases h801 : a < 801
        · refine ⟨(701, 100), ?_, ?_, ?_⟩
          · norm_num [positiveSaddleDefaultChunks]
          · omega
          · omega
        · by_cases h901 : a < 901
          · refine ⟨(801, 100), ?_, ?_, ?_⟩
            · norm_num [positiveSaddleDefaultChunks]
            · omega
            · omega
          · by_cases h1001 : a < 1001
            · refine ⟨(901, 100), ?_, ?_, ?_⟩
              · norm_num [positiveSaddleDefaultChunks]
              · omega
              · omega
            · by_cases h1101 : a < 1101
              · refine ⟨(1001, 100), ?_, ?_, ?_⟩
                · norm_num [positiveSaddleDefaultChunks]
                · omega
                · omega
              · by_cases h1201 : a < 1201
                · refine ⟨(1101, 100), ?_, ?_, ?_⟩
                  · norm_num [positiveSaddleDefaultChunks]
                  · omega
                  · omega
                · by_cases h1301 : a < 1301
                  · refine ⟨(1201, 100), ?_, ?_, ?_⟩
                    · norm_num [positiveSaddleDefaultChunks]
                    · omega
                    · omega
                  · by_cases h1401 : a < 1401
                    · refine ⟨(1301, 100), ?_, ?_, ?_⟩
                      · norm_num [positiveSaddleDefaultChunks]
                      · omega
                      · omega
                    · by_cases h1501 : a < 1501
                      · refine ⟨(1401, 100), ?_, ?_, ?_⟩
                        · norm_num [positiveSaddleDefaultChunks]
                        · omega
                        · omega
                      · by_cases h1601 : a < 1601
                        · refine ⟨(1501, 100), ?_, ?_, ?_⟩
                          · norm_num [positiveSaddleDefaultChunks]
                          · omega
                          · omega
                        · by_cases h1701 : a < 1701
                          · refine ⟨(1601, 100), ?_, ?_, ?_⟩
                            · norm_num [positiveSaddleDefaultChunks]
                            · omega
                            · omega
                          · by_cases h1801 : a < 1801
                            · refine ⟨(1701, 100), ?_, ?_, ?_⟩
                              · norm_num [positiveSaddleDefaultChunks]
                              · omega
                              · omega
                            · by_cases h1901 : a < 1901
                              · refine ⟨(1801, 100), ?_, ?_, ?_⟩
                                · norm_num [positiveSaddleDefaultChunks]
                                · omega
                                · omega
                              · refine ⟨(1901, 100), ?_, ?_, ?_⟩
                                · norm_num [positiveSaddleDefaultChunks]
                                · omega
                                · omega

/-- Constructor for the default chunk cover, leaving only the five families of
Boolean chunk checks to generated certificates. -/
theorem positiveSaddleDefaultFiniteWindowChunks
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true) :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks
      positiveSaddleDefaultChunks where
  cover := positiveSaddleDefaultChunks_cover
  smallXplusGcompChunks := hsmall
  temperedXplusGcompChunks := htempered
  smallTangentEdgeChunks := htangent
  soloGcompChunks := hsolo
  edgeBudgetChunks := hedge

end Prop51
