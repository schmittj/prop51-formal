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

/-- Fixed-width row chunks covering the finite positive-saddle window
`401 ≤ a ≤ 2000`.

The final chunk may overrun `2000`; row-range checkers only need the cover
property for rows inside the finite window. -/
def positiveSaddleFixedRowChunks (rowLen : Nat) : List (Nat × Nat) :=
  if rowLen = 0 then []
  else
    (List.range ((1600 + rowLen - 1) / rowLen)).map fun i =>
      (401 + rowLen * i, rowLen)

/-- Membership in the fixed row cover, exposed by row-index.

This is mainly for generated finite-window certificates: after rewriting a
row chunk to `(401 + rowLen * i, rowLen)`, `interval_cases i` can dispatch to
the individual `native_decide` branch for that chunk. -/
theorem mem_positiveSaddleFixedRowChunks_iff
    {rowLen : Nat} (hrowLen : 0 < rowLen) {chunk : Nat × Nat} :
    chunk ∈ positiveSaddleFixedRowChunks rowLen ↔
      ∃ i, i < (1600 + rowLen - 1) / rowLen ∧
        chunk = (401 + rowLen * i, rowLen) := by
  unfold positiveSaddleFixedRowChunks
  rw [if_neg hrowLen.ne']
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem positiveSaddleFixedRowChunks_cover {rowLen : Nat}
    (hrowLen : 0 < rowLen) :
    PositiveSaddleFiniteWindowChunkCover
      (positiveSaddleFixedRowChunks rowLen) := by
  intro a ha h2000
  let off := a - 401
  let i := off / rowLen
  have hoff_add : 401 + off = a := by
    dsimp [off]
    exact Nat.add_sub_of_le ha
  have hoff_lt : off < 1600 := by
    omega
  have hceil_mul :
      1600 ≤ ((1600 + rowLen - 1) / rowLen) * rowLen := by
    have hmod := Nat.mod_lt (1600 + rowLen - 1) hrowLen
    have hdiv := Nat.div_add_mod (1600 + rowLen - 1) rowLen
    have hdiv' :
        ((1600 + rowLen - 1) / rowLen) * rowLen +
            (1600 + rowLen - 1) % rowLen =
          1600 + rowLen - 1 := by
      simpa [Nat.mul_comm] using hdiv
    omega
  have hi_lt : i < (1600 + rowLen - 1) / rowLen := by
    rw [Nat.div_lt_iff_lt_mul hrowLen]
    exact hoff_lt.trans_le hceil_mul
  refine ⟨(401 + rowLen * i, rowLen), ?_, ?_, ?_⟩
  · unfold positiveSaddleFixedRowChunks
    rw [if_neg hrowLen.ne']
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi_lt, rfl⟩
  · have hdiv_le : rowLen * i ≤ off := by
      simpa [i] using Nat.mul_div_le off rowLen
    omega
  · have hmod_lt : off % rowLen < rowLen := Nat.mod_lt off hrowLen
    have hdiv_add : rowLen * i + off % rowLen = off := by
      simpa [i] using Nat.div_add_mod off rowLen
    omega

/-- Every default finite-window chunk starts inside the proved finite window. -/
theorem positiveSaddleDefaultChunks_lo_ge_401
    {chunk : Nat × Nat} (hchunk : chunk ∈ positiveSaddleDefaultChunks) :
    401 ≤ chunk.1 := by
  simp [positiveSaddleDefaultChunks] at hchunk
  rcases hchunk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## Row-dependent product `N`-chunks -/

/-- Canonical singleton `N`-chunks for the positive rectangle at a fixed row
`a`.

This is not necessarily the most efficient generated-certificate shape, but
it gives a simple built-in cover for the fine-grained table-backed raw product
interface.  Larger generated `N` chunks can still use the parameterized
certificate directly. -/
def positiveProductSingletonNChunks (a : Nat) : List (Nat × Nat) :=
  (positiveNRangeList a).map fun N => (N, 1)

theorem positiveProductSingletonNChunks_cover
    {a N : Nat} (hrect : positiveRectangle a N) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveProductSingletonNChunks a ∧
        N ∈ List.range' chunk.1 chunk.2 := by
  refine ⟨(N, 1), ?_, ?_⟩
  · unfold positiveProductSingletonNChunks
    exact List.mem_map.mpr
      ⟨N, mem_positiveNRangeList_of_rectangle hrect, rfl⟩
  · exact (List.mem_range'_1).mpr ⟨le_rfl, by omega⟩

/-- Fixed-width `N`-chunks for the positive rectangle at a fixed row `a`.

The final chunk is allowed to overrun `posNhi a`; the table-backed product
range checker ignores values outside `positiveRectangle a`, which keeps this
cover simple for generated certificates.  Use a positive `nLen`; for
`nLen = 0` the list is empty. -/
def positiveProductFixedNChunks (nLen a : Nat) : List (Nat × Nat) :=
  if nLen = 0 then []
  else
    let len := posNhi a + 1 - posNlo a
    (List.range ((len + nLen - 1) / nLen)).map fun i =>
      (posNlo a + nLen * i, nLen)

theorem positiveProductFixedNChunks_cover
    {nLen a N : Nat} (hnLen : 0 < nLen)
    (hrect : positiveRectangle a N) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveProductFixedNChunks nLen a ∧
        N ∈ List.range' chunk.1 chunk.2 := by
  let len := posNhi a + 1 - posNlo a
  let off := N - posNlo a
  let i := off / nLen
  have hNlt : N < posNhi a + 1 := Nat.lt_succ_of_le hrect.2
  have hlo_le_hi_succ : posNlo a ≤ posNhi a + 1 :=
    hrect.1.trans hNlt.le
  have hlen_add : posNlo a + len = posNhi a + 1 := by
    dsimp [len]
    exact Nat.add_sub_of_le hlo_le_hi_succ
  have hoff_add : posNlo a + off = N := by
    dsimp [off]
    exact Nat.add_sub_of_le hrect.1
  have hoff_lt : off < len := by
    omega
  have hlen_pos : 0 < len := lt_of_le_of_lt (Nat.zero_le off) hoff_lt
  have hceil_mul : len ≤ ((len + nLen - 1) / nLen) * nLen := by
    have hmod := Nat.mod_lt (len + nLen - 1) hnLen
    have hdiv := Nat.div_add_mod (len + nLen - 1) nLen
    have hdiv' :
        ((len + nLen - 1) / nLen) * nLen +
            (len + nLen - 1) % nLen =
          len + nLen - 1 := by
      simpa [Nat.mul_comm] using hdiv
    omega
  have hi_lt : i < (len + nLen - 1) / nLen := by
    rw [Nat.div_lt_iff_lt_mul hnLen]
    exact hoff_lt.trans_le hceil_mul
  refine ⟨(posNlo a + nLen * i, nLen), ?_, ?_⟩
  · unfold positiveProductFixedNChunks
    simp [hnLen.ne', len, i, hi_lt]
  · have hdiv_le : nLen * i ≤ off := by
      simpa [i] using Nat.mul_div_le off nLen
    have hmod_lt : off % nLen < nLen := Nat.mod_lt off hnLen
    have hdiv_add : nLen * i + off % nLen = off := by
      simpa [i] using Nat.div_add_mod off nLen
    exact (List.mem_range'_1).mpr ⟨by
      omega, by
      omega⟩

/-- Membership in the fixed-width product `N`-chunk cover for one row,
exposed by chunk index. -/
theorem mem_positiveProductFixedNChunks_iff
    {nLen a : Nat} (hnLen : 0 < nLen) {chunk : Nat × Nat} :
    chunk ∈ positiveProductFixedNChunks nLen a ↔
      ∃ i, i < ((posNhi a + 1 - posNlo a + nLen - 1) / nLen) ∧
        chunk = (posNlo a + nLen * i, nLen) := by
  unfold positiveProductFixedNChunks
  rw [if_neg hnLen.ne']
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- Uniform product `N`-chunk indices for all rows evaluated by a fixed row
cover.  The bound allows the final row chunk to overrun `a = 2000`, matching
the existing row-range checkers. -/
def positiveProductFixedNChunkIndices (rowLen nLen : Nat) : List Nat :=
  if nLen = 0 then []
  else List.range ((6 * (2000 + rowLen) + nLen - 1) / nLen)

theorem mem_positiveProductFixedNChunkIndices_iff
    {rowLen nLen i : Nat} (hnLen : 0 < nLen) :
    i ∈ positiveProductFixedNChunkIndices rowLen nLen ↔
      i < (6 * (2000 + rowLen) + nLen - 1) / nLen := by
  unfold positiveProductFixedNChunkIndices
  rw [if_neg hnLen.ne']
  exact List.mem_range

theorem positiveSaddleFixedRowChunks_row_le_bound
    {rowLen a : Nat} {rowChunk : Nat × Nat} (hrowLen : 0 < rowLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (ha_mem : a ∈ List.range' rowChunk.1 rowChunk.2) :
    a ≤ 2000 + rowLen := by
  rcases (mem_positiveSaddleFixedRowChunks_iff hrowLen).1 hrowChunk with
    ⟨i, hi, rfl⟩
  rcases (List.mem_range'_1.mp ha_mem) with ⟨_ha_lo, ha_hi⟩
  let count := (1600 + rowLen - 1) / rowLen
  have hi_succ : i + 1 ≤ count := Nat.succ_le_of_lt hi
  have hmul : rowLen * (i + 1) ≤ rowLen * count :=
    Nat.mul_le_mul_left rowLen hi_succ
  have hcount : rowLen * count ≤ 1600 + rowLen - 1 := by
    dsimp [count]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (1600 + rowLen - 1) rowLen
  have hend : rowLen * (i + 1) ≤ 1600 + rowLen - 1 := hmul.trans hcount
  rw [Nat.mul_succ] at hend
  omega

theorem positiveProductFixedNChunkIndices_cover_chunk
    {rowLen nLen a : Nat} {rowChunk nChunk : Nat × Nat}
    (hrowLen : 0 < rowLen) (hnLen : 0 < nLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (ha_mem : a ∈ List.range' rowChunk.1 rowChunk.2)
    (hnChunk : nChunk ∈ positiveProductFixedNChunks nLen a) :
    ∃ i, i ∈ positiveProductFixedNChunkIndices rowLen nLen ∧
      nChunk = (posNlo a + nLen * i, nLen) := by
  rcases (mem_positiveProductFixedNChunks_iff hnLen).1 hnChunk with
    ⟨i, hi, rfl⟩
  refine ⟨i, ?_, rfl⟩
  rw [mem_positiveProductFixedNChunkIndices_iff hnLen]
  have ha_bound : a ≤ 2000 + rowLen :=
    positiveSaddleFixedRowChunks_row_le_bound hrowLen hrowChunk ha_mem
  have ha_lo : 401 ≤ a := by
    rcases (mem_positiveSaddleFixedRowChunks_iff hrowLen).1 hrowChunk with
      ⟨j, _hj, hrow⟩
    subst rowChunk
    rcases (List.mem_range'_1.mp ha_mem) with ⟨ha_lo, _ha_hi⟩
    omega
  have hlen_le :
      posNhi a + 1 - posNlo a ≤ 6 * (2000 + rowLen) := by
    unfold posNhi posNlo
    omega
  have hnum_le :
      posNhi a + 1 - posNlo a + nLen - 1
        ≤ 6 * (2000 + rowLen) + nLen - 1 := by
    omega
  exact hi.trans_le (Nat.div_le_div_right hnum_le)

/-! ## Product retained-`k` chunks -/

/-- Fixed-width retained-`k` chunks covering `1 ≤ k ≤ 1800`.

This is the product analogue of `positiveTangentFixedKChunks`, but it covers
the whole finite-window retained-`k` range rather than only the small tangent
range.  It lets proof-producing generated certificates choose product
`k`-atoms finer than the default 20-wide edge chunks while still assembling
back to the existing finite-window target. -/
def positiveProductFixedKChunks (kLen : Nat) : List (Nat × Nat) :=
  if kLen = 0 then []
  else
    (List.range ((1800 + kLen - 1) / kLen)).map fun i =>
      (1 + kLen * i, kLen)

theorem mem_positiveProductFixedKChunks_iff
    {kLen : Nat} (hkLen : 0 < kLen) {chunk : Nat × Nat} :
    chunk ∈ positiveProductFixedKChunks kLen ↔
      ∃ i, i < (1800 + kLen - 1) / kLen ∧
        chunk = (1 + kLen * i, kLen) := by
  unfold positiveProductFixedKChunks
  rw [if_neg hkLen.ne']
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem positiveProductFixedKChunks_cover_of_le_1800
    {kLen k : Nat} (hkLen : 0 < kLen) (hk1 : 1 ≤ k)
    (hk1800 : k ≤ 1800) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveProductFixedKChunks kLen ∧
        k ∈ List.range' chunk.1 chunk.2 := by
  let off := k - 1
  let i := off / kLen
  have hoff_add : 1 + off = k := by
    dsimp [off]
    exact Nat.add_sub_of_le hk1
  have hoff_lt : off < 1800 := by
    omega
  have hceil_mul :
      1800 ≤ ((1800 + kLen - 1) / kLen) * kLen := by
    have hmod := Nat.mod_lt (1800 + kLen - 1) hkLen
    have hdiv := Nat.div_add_mod (1800 + kLen - 1) kLen
    have hdiv' :
        ((1800 + kLen - 1) / kLen) * kLen +
            (1800 + kLen - 1) % kLen =
          1800 + kLen - 1 := by
      simpa [Nat.mul_comm] using hdiv
    omega
  have hi_lt : i < (1800 + kLen - 1) / kLen := by
    rw [Nat.div_lt_iff_lt_mul hkLen]
    exact hoff_lt.trans_le hceil_mul
  refine ⟨(1 + kLen * i, kLen), ?_, ?_⟩
  · unfold positiveProductFixedKChunks
    rw [if_neg hkLen.ne']
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi_lt, rfl⟩
  · have hdiv_le : kLen * i ≤ off := by
      simpa [i] using Nat.mul_div_le off kLen
    have hmod_lt : off % kLen < kLen := Nat.mod_lt off hkLen
    have hdiv_add : kLen * i + off % kLen = off := by
      simpa [i] using Nat.div_add_mod off kLen
    exact (List.mem_range'_1).mpr ⟨by
      omega, by
      omega⟩

/-- Product table check over one fixed `N`-chunk index across a row range and
one retained-`k` chunk, for the small regime. -/
def checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
    (nLen lo len nIndex kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen

/-- Product table check over one fixed `N`-chunk index across a row range and
one retained-`k` chunk, for the tempered regime. -/
def checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
    (nLen lo len nIndex kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen

/-- Combined product table check over one fixed `N`-chunk index across a row
range and one retained-`k` chunk.  It chooses the small or tempered product
cell according to the same `k ≤ ceilSqrt N` split as the separate checkers,
but shares the table-backed `(a,N)` pass. -/
def checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
    (nLen lo len nIndex kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveXYProductRawClearedTableNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen

theorem checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
    {nLen lo len nIndex kLo kLen a : Nat}
    (h :
      checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
        nLen lo len nIndex kLo kLen = true)
    (ha_mem : a ∈ List.range' lo len) :
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          x (posNlo x + nLen * nIndex) nLen kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk]
        using h)
  exact hall a ha_mem

theorem checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
    {nLen lo len nIndex kLo kLen a : Nat}
    (h :
      checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
        nLen lo len nIndex kLo kLen = true)
    (ha_mem : a ∈ List.range' lo len) :
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          x (posNlo x + nLen * nIndex) nLen kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk]
        using h)
  exact hall a ha_mem

theorem checkPositiveXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
    {nLen lo len nIndex kLo kLen a : Nat}
    (h :
      checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
        nLen lo len nIndex kLo kLen = true)
    (ha_mem : a ∈ List.range' lo len) :
    checkPositiveXYProductRawClearedTableNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveXYProductRawClearedTableNRangeKChunk
          x (posNlo x + nLen * nIndex) nLen kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk]
        using h)
  exact hall a ha_mem

theorem checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_combined
    {nLen lo len nIndex kLo kLen : Nat}
    (h :
      checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
        nLen lo len nIndex kLo kLen = true) :
    checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
      nLen lo len nIndex kLo kLen = true := by
  unfold checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  exact checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_combined
    (checkPositiveXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
      h ha_mem)

theorem checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_combined
    {nLen lo len nIndex kLo kLen : Nat}
    (h :
      checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
        nLen lo len nIndex kLo kLen = true) :
    checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
      nLen lo len nIndex kLo kLen = true := by
  unfold checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  exact checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_combined
    (checkPositiveXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
      h ha_mem)

/-- A checked table-backed small product `N`/`k` chunk gives the executable
cell check for every covered active cell. -/
theorem checkPositiveSmallXYProductRawClearedTableCell_of_NRangeKChunk
    {a N k nLo nLen kLo kLen : Nat}
    (h :
      checkPositiveSmallXYProductRawClearedTableNRangeKChunk
        a nLo nLen kLo kLen = true)
    (hNmem : N ∈ List.range' nLo nLen)
    (hkmem : k ∈ List.range' kLo kLen)
    (hrect : positiveRectangle a N)
    (hk : k ∈ positiveKRange a) (hsmall : k ≤ ceilSqrt N) :
    checkPositiveSmallXYProductRawClearedTableCell
      (cList a) (BListQ (cList a) N a) (QListQ (cList a) N a)
      a N k = true := by
  have hNs :
      ∀ x ∈ List.range' nLo nLen,
        (if positiveRectangle a x then
            checkPositiveSmallXYProductRawClearedTableKChunkAtN
              a x kLo kLen
          else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXYProductRawClearedTableNRangeKChunk] using h)
  have hAtN :
      checkPositiveSmallXYProductRawClearedTableKChunkAtN
        a N kLo kLen = true := by
    simpa [hrect] using hNs N hNmem
  have hks :
      ∀ y ∈ List.range' kLo kLen,
        (if y ∈ positiveKRange a ∧ y ≤ ceilSqrt N then
            checkPositiveSmallXYProductRawClearedTableCell
              (cList a) (BListQ (cList a) N a)
              (QListQ (cList a) N a) a N y
          else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXYProductRawClearedTableKChunkAtN] using hAtN)
  simpa [hk, hsmall] using hks k hkmem

/-- A checked table-backed tempered product `N`/`k` chunk gives the
executable cell check for every covered active cell. -/
theorem checkPositiveTemperedXYProductRawClearedTableCell_of_NRangeKChunk
    {a N k nLo nLen kLo kLen : Nat}
    (h :
      checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
        a nLo nLen kLo kLen = true)
    (hNmem : N ∈ List.range' nLo nLen)
    (hkmem : k ∈ List.range' kLo kLen)
    (hrect : positiveRectangle a N)
    (hk : k ∈ positiveKRange a) (htempered : ceilSqrt N < k) :
    checkPositiveTemperedXYProductRawClearedTableCell
      (cList a) (BListQ (cList a) N a) (QListQ (cList a) N a)
      a N k = true := by
  have hNs :
      ∀ x ∈ List.range' nLo nLen,
        (if positiveRectangle a x then
            checkPositiveTemperedXYProductRawClearedTableKChunkAtN
              a x kLo kLen
          else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXYProductRawClearedTableNRangeKChunk] using h)
  have hAtN :
      checkPositiveTemperedXYProductRawClearedTableKChunkAtN
        a N kLo kLen = true := by
    simpa [hrect] using hNs N hNmem
  have hks :
      ∀ y ∈ List.range' kLo kLen,
        (if y ∈ positiveKRange a ∧ ceilSqrt N < y then
            checkPositiveTemperedXYProductRawClearedTableCell
              (cList a) (BListQ (cList a) N a)
              (QListQ (cList a) N a) a N y
          else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXYProductRawClearedTableKChunkAtN] using hAtN)
  simpa [hk, htempered] using hks k hkmem

/-- Product table check over all fixed-width `N`-chunks in one row and one
retained-`k` chunk, for the small regime. -/
def checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow
    (nLen a kLo kLen : Nat) : Bool :=
  (positiveProductFixedNChunks nLen a).all fun nChunk =>
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk
      a nChunk.1 nChunk.2 kLo kLen

/-- Product table check over all fixed-width `N`-chunks in one row and one
retained-`k` chunk, for the tempered regime. -/
def checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow
    (nLen a kLo kLen : Nat) : Bool :=
  (positiveProductFixedNChunks nLen a).all fun nChunk =>
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
      a nChunk.1 nChunk.2 kLo kLen

/-- Row-range version of
`checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow`. -/
def checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
    (nLen lo len kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow
      nLen a kLo kLen

/-- Row-range version of
`checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow`. -/
def checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
    (nLen lo len kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow
      nLen a kLo kLen

theorem checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk_of_fixedNIndexRowRangeKChunks
    {rowLen nLen kLo kLen : Nat} {rowChunk : Nat × Nat}
    (hrowLen : 0 < rowLen) (hnLen : 0 < nLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hchunks :
      ∀ {nIndex : Nat}, nIndex ∈ positiveProductFixedNChunkIndices rowLen nLen →
        checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 nIndex kLo kLen = true) :
    checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
      nLen rowChunk.1 rowChunk.2 kLo kLen = true := by
  unfold checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  unfold checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow
  apply List.all_eq_true.mpr
  intro nChunk hnChunk
  rcases positiveProductFixedNChunkIndices_cover_chunk
      hrowLen hnLen hrowChunk ha_mem hnChunk with
    ⟨nIndex, hnIndex, rfl⟩
  exact checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
    (hchunks hnIndex) ha_mem

theorem checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk_of_fixedNIndexRowRangeKChunks
    {rowLen nLen kLo kLen : Nat} {rowChunk : Nat × Nat}
    (hrowLen : 0 < rowLen) (hnLen : 0 < nLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hchunks :
      ∀ {nIndex : Nat}, nIndex ∈ positiveProductFixedNChunkIndices rowLen nLen →
        checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 nIndex kLo kLen = true) :
    checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
      nLen rowChunk.1 rowChunk.2 kLo kLen = true := by
  unfold checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  unfold checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow
  apply List.all_eq_true.mpr
  intro nChunk hnChunk
  rcases positiveProductFixedNChunkIndices_cover_chunk
      hrowLen hnLen hrowChunk ha_mem hnChunk with
    ⟨nIndex, hnIndex, rfl⟩
  exact checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
    (hchunks hnIndex) ha_mem

theorem checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
    {nLen lo len a kLo kLen : Nat} {nChunk : Nat × Nat}
    (h :
      checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
        nLen lo len kLo kLen = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hnChunk : nChunk ∈ positiveProductFixedNChunks nLen a) :
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk
      a nChunk.1 nChunk.2 kLo kLen = true := by
  have hrows :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow
          nLen x kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk]
        using h)
  have hrow :
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow
        nLen a kLo kLen = true :=
    hrows a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)
  have hchunks :
      ∀ chunk ∈ positiveProductFixedNChunks nLen a,
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a chunk.1 chunk.2 kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunkRow]
        using hrow)
  exact hchunks nChunk hnChunk

theorem checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
    {nLen lo len a kLo kLen : Nat} {nChunk : Nat × Nat}
    (h :
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
        nLen lo len kLo kLen = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hnChunk : nChunk ∈ positiveProductFixedNChunks nLen a) :
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
      a nChunk.1 nChunk.2 kLo kLen = true := by
  have hrows :
      ∀ x ∈ List.range' lo len,
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow
          nLen x kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk]
        using h)
  have hrow :
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow
        nLen a kLo kLen = true :=
    hrows a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)
  have hchunks :
      ∀ chunk ∈ positiveProductFixedNChunks nLen a,
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a chunk.1 chunk.2 kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunkRow]
        using hrow)
  exact hchunks nChunk hnChunk

/-! ## Tangent-edge `N`/`k` chunks -/

/-- Fixed-width `k` chunks covering every possible small-regime tangent
`k` in the finite window.

For `401 ≤ a ≤ 2000` and `positiveRectangle a N`, any `k ≤ ceilSqrt N`
satisfies `k ≤ 155`, so this compact cover is enough for tangent-cell
generation. -/
def positiveTangentFixedKChunks (kLen : Nat) : List (Nat × Nat) :=
  if kLen = 0 then []
  else
    (List.range ((155 + kLen - 1) / kLen)).map fun i =>
      (1 + kLen * i, kLen)

theorem mem_positiveTangentFixedKChunks_iff
    {kLen : Nat} (hkLen : 0 < kLen) {chunk : Nat × Nat} :
    chunk ∈ positiveTangentFixedKChunks kLen ↔
      ∃ i, i < (155 + kLen - 1) / kLen ∧
        chunk = (1 + kLen * i, kLen) := by
  unfold positiveTangentFixedKChunks
  rw [if_neg hkLen.ne']
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem positiveTangentFixedKChunks_cover
    {kLen a N k : Nat} (hkLen : 0 < kLen) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (_hk : k ∈ positiveKRange a)
    (hsmall : k ≤ ceilSqrt N) (hk1 : 1 ≤ k) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveTangentFixedKChunks kLen ∧
        k ∈ List.range' chunk.1 chunk.2 := by
  let off := k - 1
  let i := off / kLen
  have hceil_le : ceilSqrt N ≤ posSmallCutoff a := by
    exact ceilSqrt_mono hrect.2
  have hk155 : k ≤ 155 :=
    hsmall.trans (hceil_le.trans (posSmallCutoff_le_155 ha2000))
  have hoff_add : 1 + off = k := by
    dsimp [off]
    exact Nat.add_sub_of_le hk1
  have hoff_lt : off < 155 := by
    omega
  have hceil_mul :
      155 ≤ ((155 + kLen - 1) / kLen) * kLen := by
    have hmod := Nat.mod_lt (155 + kLen - 1) hkLen
    have hdiv := Nat.div_add_mod (155 + kLen - 1) kLen
    have hdiv' :
        ((155 + kLen - 1) / kLen) * kLen +
            (155 + kLen - 1) % kLen =
          155 + kLen - 1 := by
      simpa [Nat.mul_comm] using hdiv
    omega
  have hi_lt : i < (155 + kLen - 1) / kLen := by
    rw [Nat.div_lt_iff_lt_mul hkLen]
    exact hoff_lt.trans_le hceil_mul
  refine ⟨(1 + kLen * i, kLen), ?_, ?_⟩
  · unfold positiveTangentFixedKChunks
    rw [if_neg hkLen.ne']
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi_lt, rfl⟩
  · have hdiv_le : kLen * i ≤ off := by
      simpa [i] using Nat.mul_div_le off kLen
    have hmod_lt : off % kLen < kLen := Nat.mod_lt off hkLen
    have hdiv_add : kLen * i + off % kLen = off := by
      simpa [i] using Nat.div_add_mod off kLen
    exact (List.mem_range'_1).mpr ⟨by
      omega, by
      omega⟩

/-- Tangent-cell check over one `N` chunk and one `k` chunk.  Values outside
the positive rectangle or outside the active small-regime cells are ignored. -/
def checkPositiveSmallTangentExpEdgeNRangeKChunk
    (a nLo nLen kLo kLen : Nat) : Bool :=
  (List.range' nLo nLen).all fun N =>
    if _hrect : positiveRectangle a N then
      (List.range' kLo kLen).all fun k =>
        if _hcell : k ∈ positiveKRange a ∧ k ≤ ceilSqrt N then
          checkPositiveSmallTangentExpEdgeCell a N k
        else true
    else true

/-- Row-range tangent check using fixed-width `N` chunks and one fixed
`k` chunk. -/
def checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk
    (nLen lo len kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    (positiveProductFixedNChunks nLen a).all fun nChunk =>
      checkPositiveSmallTangentExpEdgeNRangeKChunk
        a nChunk.1 nChunk.2 kLo kLen

/-- Tangent check over one fixed `N`-chunk index across a row range and one
small-regime `k` chunk.  This is the tangent analogue of the product
fixed-`N`-index checks above and is useful when all-`N` row-range tangent
atoms are too large for `native_decide`. -/
def checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
    (nLen lo len nIndex kLo kLen : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveSmallTangentExpEdgeNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen

theorem checkPositiveSmallTangentExpEdgeCell_of_NRangeKChunk
    {a N k nLo nLen kLo kLen : Nat}
    (h :
      checkPositiveSmallTangentExpEdgeNRangeKChunk
        a nLo nLen kLo kLen = true)
    (hNmem : N ∈ List.range' nLo nLen)
    (hkmem : k ∈ List.range' kLo kLen)
    (hrect : positiveRectangle a N)
    (hk : k ∈ positiveKRange a) (hsmall : k ≤ ceilSqrt N) :
    checkPositiveSmallTangentExpEdgeCell a N k = true := by
  have hNs :
      ∀ x ∈ List.range' nLo nLen,
        (if hrect : positiveRectangle a x then
          (List.range' kLo kLen).all fun y =>
            if _hcell : y ∈ positiveKRange a ∧ y ≤ ceilSqrt x then
              checkPositiveSmallTangentExpEdgeCell a x y
            else true
        else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeNRangeKChunk] using h)
  have hN := hNs N hNmem
  have hks :
      ∀ y ∈ List.range' kLo kLen,
        (if _hcell : y ∈ positiveKRange a ∧ y ≤ ceilSqrt N then
          checkPositiveSmallTangentExpEdgeCell a N y
        else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [hrect] using hN)
  have hkcheck := hks k hkmem
  simpa [hk, hsmall] using hkcheck

theorem checkPositiveSmallTangentExpEdgeCell_of_fixedNChunksRowRangeKChunk
    {nLen lo len a N k kLo kLen : Nat} {nChunk : Nat × Nat}
    (h :
      checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk
        nLen lo len kLo kLen = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hnChunk : nChunk ∈ positiveProductFixedNChunks nLen a)
    (hNmem : N ∈ List.range' nChunk.1 nChunk.2)
    (hkmem : k ∈ List.range' kLo kLen)
    (hrect : positiveRectangle a N)
    (hk : k ∈ positiveKRange a) (hsmall : k ≤ ceilSqrt N) :
    checkPositiveSmallTangentExpEdgeCell a N k = true := by
  have hrows :
      ∀ x ∈ List.range' lo len,
        ((positiveProductFixedNChunks nLen x).all fun nChunk =>
          checkPositiveSmallTangentExpEdgeNRangeKChunk
            x nChunk.1 nChunk.2 kLo kLen) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk]
        using h)
  have hrow := hrows a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)
  have hnChunks :
      ∀ chunk ∈ positiveProductFixedNChunks nLen a,
        checkPositiveSmallTangentExpEdgeNRangeKChunk
          a chunk.1 chunk.2 kLo kLen = true := by
    exact List.all_eq_true.mp hrow
  exact checkPositiveSmallTangentExpEdgeCell_of_NRangeKChunk
    (hnChunks nChunk hnChunk) hNmem hkmem hrect hk hsmall

theorem checkPositiveSmallTangentExpEdgeNRangeKChunk_of_fixedNIndexRowRangeKChunk
    {nLen lo len nIndex kLo kLen a : Nat}
    (h :
      checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
        nLen lo len nIndex kLo kLen = true)
    (ha_mem : a ∈ List.range' lo len) :
    checkPositiveSmallTangentExpEdgeNRangeKChunk
      a (posNlo a + nLen * nIndex) nLen kLo kLen = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallTangentExpEdgeNRangeKChunk
          x (posNlo x + nLen * nIndex) nLen kLo kLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk]
        using h)
  exact hall a ha_mem

theorem checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk_of_fixedNIndexRowRangeKChunks
    {rowLen nLen kLo kLen : Nat} {rowChunk : Nat × Nat}
    (hrowLen : 0 < rowLen) (hnLen : 0 < nLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hchunks :
      ∀ {nIndex : Nat}, nIndex ∈ positiveProductFixedNChunkIndices rowLen nLen →
        checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 nIndex kLo kLen = true) :
    checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk
      nLen rowChunk.1 rowChunk.2 kLo kLen = true := by
  unfold checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  apply List.all_eq_true.mpr
  intro nChunk hnChunk
  rcases positiveProductFixedNChunkIndices_cover_chunk
      hrowLen hnLen hrowChunk ha_mem hnChunk with
    ⟨nIndex, hnIndex, rfl⟩
  exact
    checkPositiveSmallTangentExpEdgeNRangeKChunk_of_fixedNIndexRowRangeKChunk
      (hchunks hnIndex) ha_mem

/-! ## Fixed-`N` chunks for displayed solo checks -/

/-- Displayed-solo saddle check over one `N` chunk.  Values outside the
positive rectangle are ignored, matching the product/tangent table checkers. -/
def checkPositiveSoloDisplayedYSaddleClearedNRange
    (a nLo nLen : Nat) : Bool :=
  (List.range' nLo nLen).all fun N =>
    if _hrect : positiveRectangle a N then
      checkPositiveSoloDisplayedYSaddleClearedCell a N
    else true

/-- Displayed-solo unit-budget check over one `N` chunk. -/
def checkPositiveSoloDisplayedYBoundUnitNRange
    (a nLo nLen : Nat) : Bool :=
  (List.range' nLo nLen).all fun N =>
    if _hrect : positiveRectangle a N then
      checkPositiveSoloDisplayedYBoundUnitCell a N
    else true

/-- Displayed-solo saddle check over one fixed `N`-chunk index across a row
range. -/
def checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
    (nLen lo len nIndex : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveSoloDisplayedYSaddleClearedNRange
      a (posNlo a + nLen * nIndex) nLen

/-- Displayed-solo unit-budget check over one fixed `N`-chunk index across a
row range. -/
def checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
    (nLen lo len nIndex : Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveSoloDisplayedYBoundUnitNRange
      a (posNlo a + nLen * nIndex) nLen

theorem checkPositiveSoloDisplayedYSaddleClearedCell_of_NRange
    {a N nLo nLen : Nat}
    (h : checkPositiveSoloDisplayedYSaddleClearedNRange a nLo nLen = true)
    (hNmem : N ∈ List.range' nLo nLen) (hrect : positiveRectangle a N) :
    checkPositiveSoloDisplayedYSaddleClearedCell a N = true := by
  have hNs :
      ∀ x ∈ List.range' nLo nLen,
        (if _hrect : positiveRectangle a x then
          checkPositiveSoloDisplayedYSaddleClearedCell a x
        else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloDisplayedYSaddleClearedNRange] using h)
  simpa [hrect] using hNs N hNmem

theorem checkPositiveSoloDisplayedYBoundUnitCell_of_NRange
    {a N nLo nLen : Nat}
    (h : checkPositiveSoloDisplayedYBoundUnitNRange a nLo nLen = true)
    (hNmem : N ∈ List.range' nLo nLen) (hrect : positiveRectangle a N) :
    checkPositiveSoloDisplayedYBoundUnitCell a N = true := by
  have hNs :
      ∀ x ∈ List.range' nLo nLen,
        (if _hrect : positiveRectangle a x then
          checkPositiveSoloDisplayedYBoundUnitCell a x
        else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloDisplayedYBoundUnitNRange] using h)
  simpa [hrect] using hNs N hNmem

theorem checkPositiveSoloDisplayedYSaddleClearedNRange_of_fixedNIndexRowRange
    {nLen lo len nIndex a : Nat}
    (h :
      checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
        nLen lo len nIndex = true)
    (ha_mem : a ∈ List.range' lo len) :
    checkPositiveSoloDisplayedYSaddleClearedNRange
      a (posNlo a + nLen * nIndex) nLen = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSoloDisplayedYSaddleClearedNRange
          x (posNlo x + nLen * nIndex) nLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange]
        using h)
  exact hall a ha_mem

theorem checkPositiveSoloDisplayedYBoundUnitNRange_of_fixedNIndexRowRange
    {nLen lo len nIndex a : Nat}
    (h :
      checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
        nLen lo len nIndex = true)
    (ha_mem : a ∈ List.range' lo len) :
    checkPositiveSoloDisplayedYBoundUnitNRange
      a (posNlo a + nLen * nIndex) nLen = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSoloDisplayedYBoundUnitNRange
          x (posNlo x + nLen * nIndex) nLen = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange]
        using h)
  exact hall a ha_mem

theorem checkPositiveSoloDisplayedYSaddleClearedRange_of_fixedNIndexRowRangeChunks
    {rowLen nLen : Nat} {rowChunk : Nat × Nat}
    (hrowLen : 0 < rowLen) (hnLen : 0 < nLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hchunks :
      ∀ {nIndex : Nat}, nIndex ∈ positiveProductFixedNChunkIndices rowLen nLen →
        checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
          nLen rowChunk.1 rowChunk.2 nIndex = true) :
    checkPositiveSoloDisplayedYSaddleClearedRange
      rowChunk.1 rowChunk.2 = true := by
  unfold checkPositiveSoloDisplayedYSaddleClearedRange
  apply List.all_eq_true.mpr
  intro a ha_mem
  unfold checkPositiveSoloDisplayedYSaddleClearedRow
  apply List.all_eq_true.mpr
  intro N hNmem
  have ha401 : 401 ≤ a := by
    rcases (mem_positiveSaddleFixedRowChunks_iff hrowLen).1 hrowChunk with
      ⟨i, _hi, hrow⟩
    subst rowChunk
    rcases (List.mem_range'_1.mp ha_mem) with ⟨ha_lo, _ha_hi⟩
    omega
  have hrect : positiveRectangle a N :=
    positiveRectangle_of_mem_positiveNRangeList (by omega : 1 ≤ a) hNmem
  rcases positiveProductFixedNChunks_cover hnLen hrect with
    ⟨nChunk, hnChunk, hNChunkMem⟩
  rcases positiveProductFixedNChunkIndices_cover_chunk
      hrowLen hnLen hrowChunk ha_mem hnChunk with
    ⟨nIndex, hnIndex, rfl⟩
  exact checkPositiveSoloDisplayedYSaddleClearedCell_of_NRange
    (checkPositiveSoloDisplayedYSaddleClearedNRange_of_fixedNIndexRowRange
      (hchunks hnIndex) ha_mem)
    hNChunkMem hrect

theorem checkPositiveSoloDisplayedYBoundUnitRange_of_fixedNIndexRowRangeChunks
    {rowLen nLen : Nat} {rowChunk : Nat × Nat}
    (hrowLen : 0 < rowLen) (hnLen : 0 < nLen)
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hchunks :
      ∀ {nIndex : Nat}, nIndex ∈ positiveProductFixedNChunkIndices rowLen nLen →
        checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
          nLen rowChunk.1 rowChunk.2 nIndex = true) :
    checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true := by
  unfold checkPositiveSoloDisplayedYBoundUnitRange
  apply List.all_eq_true.mpr
  intro a ha_mem
  unfold checkPositiveSoloDisplayedYBoundUnitRow
  apply List.all_eq_true.mpr
  intro N hNmem
  have ha401 : 401 ≤ a := by
    rcases (mem_positiveSaddleFixedRowChunks_iff hrowLen).1 hrowChunk with
      ⟨i, _hi, hrow⟩
    subst rowChunk
    rcases (List.mem_range'_1.mp ha_mem) with ⟨ha_lo, _ha_hi⟩
    omega
  have hrect : positiveRectangle a N :=
    positiveRectangle_of_mem_positiveNRangeList (by omega : 1 ≤ a) hNmem
  rcases positiveProductFixedNChunks_cover hnLen hrect with
    ⟨nChunk, hnChunk, hNChunkMem⟩
  rcases positiveProductFixedNChunkIndices_cover_chunk
      hrowLen hnLen hrowChunk ha_mem hnChunk with
    ⟨nIndex, hnIndex, rfl⟩
  exact checkPositiveSoloDisplayedYBoundUnitCell_of_NRange
    (checkPositiveSoloDisplayedYBoundUnitNRange_of_fixedNIndexRowRange
      (hchunks hnIndex) ha_mem)
    hNChunkMem hrect

/-! ## Default edge `k`-chunks

The corrected finite edge budget is expensive as a single row check.  These
fixed 20-wide chunks cover every retained `k` for all `a ≤ 2000`; generated
audits can prove each chunk separately and then combine them through the
reducers in `PositiveSaddle.lean`. -/

/-- Default 20-wide `k`-chunks covering `1 ≤ k ≤ 1800`, hence all retained
`k ∈ positiveKRange a` for `a ≤ 2000`. -/
def positiveEdgeDefaultKChunks : Finset (Nat × Nat) :=
  (Finset.range 90).image fun i => (1 + 20 * i, 20)

/-- Membership in the default edge `k`-chunk cover, exposed by chunk-index. -/
theorem mem_positiveEdgeDefaultKChunks_iff {chunk : Nat × Nat} :
    chunk ∈ positiveEdgeDefaultKChunks ↔
      ∃ i, i < 90 ∧ chunk = (1 + 20 * i, 20) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- List version of `positiveEdgeDefaultKChunks`, convenient for generated
certificates that use `List.all` reducers. -/
def positiveEdgeDefaultKChunkList : List (Nat × Nat) :=
  (List.range 90).map fun i => (1 + 20 * i, 20)

theorem mem_positiveEdgeDefaultKChunkList_iff {chunk : Nat × Nat} :
    chunk ∈ positiveEdgeDefaultKChunkList ↔
      chunk ∈ positiveEdgeDefaultKChunks := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_range.mpr (by simpa using List.mem_range.mp hi), rfl⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩
    exact List.mem_map.mpr
      ⟨i, List.mem_range.mpr (by simpa using Finset.mem_range.mp hi), rfl⟩

/-- Common edge scale threshold sufficient for the 90 default reciprocal
`k`-chunk budgets to fit inside `positiveEdgeBudget = 1 / 200000000`. -/
def positiveEdgeUniformScaleMin : Nat := 18000000000

theorem positiveEdgeUniformScaleMin_pos : 0 < positiveEdgeUniformScaleMin := by
  norm_num [positiveEdgeUniformScaleMin]

/-- Row-range check for one default edge `k`-chunk using a row-dependent unit
scale. -/
def checkPositiveEdgeMajorantKChunkUnitRowRange
    (lo len kLo kLen : Nat) (edgeScale : Nat → Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveEdgeMajorantKChunkUnit a kLo kLen (edgeScale a)

theorem checkPositiveEdgeMajorantKChunkUnit_of_rowRange
    {lo len a kLo kLen : Nat} {edgeScale : Nat → Nat}
    (h :
      checkPositiveEdgeMajorantKChunkUnitRowRange
        lo len kLo kLen edgeScale = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len) :
    checkPositiveEdgeMajorantKChunkUnit a kLo kLen (edgeScale a) = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveEdgeMajorantKChunkUnit x kLo kLen (edgeScale x) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveEdgeMajorantKChunkUnitRowRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)

theorem positiveEdgeUniformScale_pos_of_scale_ge
    {scale : Nat} (hscale : positiveEdgeUniformScaleMin ≤ scale) :
    0 < scale := by
  exact positiveEdgeUniformScaleMin_pos.trans_le hscale

theorem positiveEdgeDefaultKChunks_card :
    positiveEdgeDefaultKChunks.card = 90 := by
  unfold positiveEdgeDefaultKChunks
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    simp at h
    omega

theorem positiveEdgeDefaultKChunks_disjoint :
    (positiveEdgeDefaultKChunks : Set (Nat × Nat)).PairwiseDisjoint
      fun chunk => Finset.Ico chunk.1 (chunk.1 + chunk.2) := by
  intro chunk hchunk chunk' hchunk' hne
  have hchunkFin : chunk ∈ positiveEdgeDefaultKChunks := by simpa using hchunk
  have hchunkFin' : chunk' ∈ positiveEdgeDefaultKChunks := by simpa using hchunk'
  rcases Finset.mem_image.mp hchunkFin with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hchunkFin' with ⟨j, _hj, rfl⟩
  have hij : i ≠ j := by
    intro h
    apply hne
    simp [h]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · simp [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    omega
  · simp [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    omega

theorem positiveEdgeDefaultKChunks_cover
    {a k : Nat} (ha2000 : a ≤ 2000) (hk : k ∈ positiveKRange a) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveEdgeDefaultKChunks ∧
        k ∈ Finset.Ico chunk.1 (chunk.1 + chunk.2) := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hkhi : k ≤ 1800 := by
    unfold posKmax at hkmax
    omega
  let i := (k - 1) / 20
  have hi : i < 90 := by
    dsimp [i]
    omega
  refine ⟨(1 + 20 * i, 20), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  · simp [Finset.mem_Ico]
    dsimp [i]
    constructor <;> omega

/-- Finer edge `k`-chunks covering `1 ≤ k ≤ 1800`.

These are used only for proof production.  The semantic edge-budget reducer in
`PositiveSaddle.lean` accepts any disjoint chunk cover, so generated edge atoms
can be much narrower than the default 20-wide chunks. -/
def positiveEdgeFixedKChunks (kLen : Nat) : Finset (Nat × Nat) :=
  if kLen = 0 then ∅
  else
    (Finset.range ((1800 + kLen - 1) / kLen)).image fun i =>
      (1 + kLen * i, kLen)

theorem mem_positiveEdgeFixedKChunks_iff
    {kLen : Nat} (hkLen : 0 < kLen) {chunk : Nat × Nat} :
    chunk ∈ positiveEdgeFixedKChunks kLen ↔
      ∃ i, i < (1800 + kLen - 1) / kLen ∧
        chunk = (1 + kLen * i, kLen) := by
  unfold positiveEdgeFixedKChunks
  rw [if_neg hkLen.ne']
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem positiveEdgeFixedKChunks_card
    {kLen : Nat} (hkLen : 0 < kLen) :
    (positiveEdgeFixedKChunks kLen).card =
      (1800 + kLen - 1) / kLen := by
  unfold positiveEdgeFixedKChunks
  rw [if_neg hkLen.ne']
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    simp at h
    omega

theorem positiveEdgeFixedKChunks_disjoint
    {kLen : Nat} (hkLen : 0 < kLen) :
    (positiveEdgeFixedKChunks kLen : Set (Nat × Nat)).PairwiseDisjoint
      fun chunk => Finset.Ico chunk.1 (chunk.1 + chunk.2) := by
  intro chunk hchunk chunk' hchunk' hne
  have hchunkFin : chunk ∈ positiveEdgeFixedKChunks kLen := by
    simpa using hchunk
  have hchunkFin' : chunk' ∈ positiveEdgeFixedKChunks kLen := by
    simpa using hchunk'
  rcases (mem_positiveEdgeFixedKChunks_iff hkLen).1 hchunkFin with
    ⟨i, _hi, rfl⟩
  rcases (mem_positiveEdgeFixedKChunks_iff hkLen).1 hchunkFin' with
    ⟨j, _hj, rfl⟩
  have hij : i ≠ j := by
    intro h
    apply hne
    simp [h]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hsep : 1 + kLen * i + kLen ≤ 1 + kLen * j := by
      have hij_succ : i + 1 ≤ j := Nat.succ_le_of_lt hijlt
      calc
        1 + kLen * i + kLen = 1 + kLen * (i + 1) := by ring
        _ ≤ 1 + kLen * j :=
          Nat.add_le_add_left (Nat.mul_le_mul_left kLen hij_succ) 1
    simp [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    omega
  · have hsep : 1 + kLen * j + kLen ≤ 1 + kLen * i := by
      have hji_succ : j + 1 ≤ i := Nat.succ_le_of_lt hjilt
      calc
        1 + kLen * j + kLen = 1 + kLen * (j + 1) := by ring
        _ ≤ 1 + kLen * i :=
          Nat.add_le_add_left (Nat.mul_le_mul_left kLen hji_succ) 1
    simp [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    omega

theorem positiveEdgeFixedKChunks_cover_of_le_1800
    {kLen k : Nat} (hkLen : 0 < kLen) (hk1 : 1 ≤ k)
    (hk1800 : k ≤ 1800) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveEdgeFixedKChunks kLen ∧
        k ∈ Finset.Ico chunk.1 (chunk.1 + chunk.2) := by
  rcases positiveProductFixedKChunks_cover_of_le_1800
      hkLen hk1 hk1800 with
    ⟨chunk, hchunk, hkChunk⟩
  rcases (mem_positiveProductFixedKChunks_iff hkLen).1 hchunk with
    ⟨i, hi, rfl⟩
  refine ⟨(1 + kLen * i, kLen), ?_, ?_⟩
  · exact (mem_positiveEdgeFixedKChunks_iff hkLen).2 ⟨i, hi, rfl⟩
  · exact Finset.mem_Ico.mpr ((List.mem_range'_1).mp hkChunk)

/-- Uniform scale for the finer edge chunks.

For `c = ceil(1800 / kLen)` chunks, each generated atom proves a bound by
`1 / (c * 200000000)`, so summing over all chunks fits exactly into
`positiveEdgeBudget = 1 / 200000000`. -/
def positiveEdgeFixedKScale (kLen : Nat) : Nat :=
  ((1800 + kLen - 1) / kLen) * 200000000

theorem positiveEdgeFixedKScale_pos
    {kLen : Nat} (hkLen : 0 < kLen) :
    0 < positiveEdgeFixedKScale kLen := by
  unfold positiveEdgeFixedKScale
  have hcount : 0 < (1800 + kLen - 1) / kLen := by
    exact Nat.div_pos (by omega) hkLen
  omega

theorem positiveEdgeFixedKChunks_uniformBudget
    {kLen : Nat} (hkLen : 0 < kLen) :
    ∑ _chunk ∈ positiveEdgeFixedKChunks kLen,
      (1 : ℚ) / (positiveEdgeFixedKScale kLen : ℚ) ≤
        positiveEdgeBudget := by
  rw [Finset.sum_const, positiveEdgeFixedKChunks_card hkLen, nsmul_eq_mul]
  rw [positiveEdgeBudget_eq_inv_200000000]
  let count := (1800 + kLen - 1) / kLen
  have hcount_pos : 0 < count := by
    exact Nat.div_pos (by omega) hkLen
  have hcount_ne : (count : ℚ) ≠ 0 := by
    exact_mod_cast hcount_pos.ne'
  have hcast :
      (((count * 200000000 : Nat) : ℚ)) =
        (count : ℚ) * 200000000 := by
    norm_num
  change (count : ℚ) *
      (1 / (((count * 200000000 : Nat) : ℚ))) ≤
        (1 : ℚ) / 200000000
  rw [hcast]
  apply le_of_eq
  field_simp [hcount_ne]

set_option maxHeartbeats 800000 in
theorem positiveEdgeBudget_of_fixedKChunksUniformUnitChecks
    {a kLen : Nat} (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hkLen : 0 < kLen)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeFixedKChunks kLen →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (positiveEdgeFixedKScale kLen) = true) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  exact positiveEdgeBudget_of_KChunksUnitChecks
    (a := a) (chunks := positiveEdgeFixedKChunks kLen)
    (scale := fun _ => positiveEdgeFixedKScale kLen)
    ha401 ha2000
    (positiveEdgeFixedKChunks_disjoint hkLen)
    (by
      intro k hk
      rcases mem_positiveKRange.mp hk with ⟨hk1, hkmax⟩
      have hk1800 : k ≤ 1800 := by
        unfold posKmax at hkmax
        omega
      exact positiveEdgeFixedKChunks_cover_of_le_1800 hkLen hk1 hk1800)
    (fun {_chunk} _hchunk => positiveEdgeFixedKScale_pos hkLen)
    (fun {chunk} hchunk => hchunks (chunk := chunk) hchunk)
    (positiveEdgeFixedKChunks_uniformBudget hkLen)

set_option maxHeartbeats 4000000 in
theorem checkPositiveEdgeMajorantKChunkUnit_of_fixedKRowRangeChunks
    {rowLen kLen a : Nat} (hrowLen : 0 < rowLen)
    (hchunks :
      ∀ (rowChunk : Nat × Nat),
        rowChunk ∈ positiveSaddleFixedRowChunks rowLen →
      ∀ (edgeChunk : Nat × Nat), edgeChunk ∈ positiveEdgeFixedKChunks kLen →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeFixedKScale kLen) = true)
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    {edgeChunk : Nat × Nat}
    (hedgeChunk : edgeChunk ∈ positiveEdgeFixedKChunks kLen) :
    checkPositiveEdgeMajorantKChunkUnit
      a edgeChunk.1 edgeChunk.2 (positiveEdgeFixedKScale kLen) = true := by
  rcases positiveSaddleFixedRowChunks_cover hrowLen ha401 ha2000 with
    ⟨rowChunk, hrowChunk, hlo, hhi⟩
  have hall :
      ∀ x ∈ List.range' rowChunk.1 rowChunk.2,
        checkPositiveEdgeMajorantKChunkUnit
          x edgeChunk.1 edgeChunk.2 (positiveEdgeFixedKScale kLen) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveEdgeMajorantKChunkUnitRowRange]
        using hchunks rowChunk hrowChunk edgeChunk hedgeChunk)
  exact hall a ((List.mem_range'_1).mpr ⟨hlo, hhi⟩)

theorem positiveEdgeBudget_of_fixedKChunksUniformUnitRowRangeChecks
    {rowLen kLen a : Nat} (hrowLen : 0 < rowLen) (hkLen : 0 < kLen)
    (hchunks :
      ∀ (rowChunk : Nat × Nat),
        rowChunk ∈ positiveSaddleFixedRowChunks rowLen →
      ∀ (edgeChunk : Nat × Nat), edgeChunk ∈ positiveEdgeFixedKChunks kLen →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeFixedKScale kLen) = true)
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  exact positiveEdgeBudget_of_fixedKChunksUniformUnitChecks
    ha401 ha2000 hkLen
    (fun {chunk} hchunk =>
      checkPositiveEdgeMajorantKChunkUnit_of_fixedKRowRangeChunks
        hrowLen hchunks ha401 ha2000 hchunk)

theorem checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_productKChunks
    {productKLen a nLo nLen : Nat} {edgeChunk : Nat × Nat}
    (hproductKLen : 0 < productKLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks)
    (hchunks :
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nLo nLen productKChunk.1 productKChunk.2 = true) :
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk
      a nLo nLen edgeChunk.1 edgeChunk.2 = true := by
  unfold checkPositiveSmallXYProductRawClearedTableNRangeKChunk
  apply List.all_eq_true.mpr
  intro N hNmem
  by_cases hrect : positiveRectangle a N
  · have hAtN :
        checkPositiveSmallXYProductRawClearedTableKChunkAtN
          a N edgeChunk.1 edgeChunk.2 = true := by
      unfold checkPositiveSmallXYProductRawClearedTableKChunkAtN
      apply List.all_eq_true.mpr
      intro k hkmem
      by_cases hcell : k ∈ positiveKRange a ∧ k ≤ ceilSqrt N
      · rcases (mem_positiveEdgeDefaultKChunks_iff).1 hedgeChunk with
          ⟨i, hi, hedgeEq⟩
        have hkmem' : k ∈ List.range' (1 + 20 * i) 20 := by
          simpa [hedgeEq] using hkmem
        rcases (List.mem_range'_1.mp hkmem') with ⟨hklo, hkhi⟩
        have hk1 : 1 ≤ k := by omega
        have hk1800 : k ≤ 1800 := by omega
        rcases positiveProductFixedKChunks_cover_of_le_1800
            hproductKLen hk1 hk1800 with
          ⟨productKChunk, hproductKChunk, hkProductMem⟩
        have hcellCheck :
            checkPositiveSmallXYProductRawClearedTableCell
              (cList a) (BListQ (cList a) N a)
              (QListQ (cList a) N a) a N k = true :=
          checkPositiveSmallXYProductRawClearedTableCell_of_NRangeKChunk
            (hchunks hproductKChunk) hNmem hkProductMem hrect
            hcell.1 hcell.2
        simpa [hcell] using hcellCheck
      · simp [hcell]
    simpa [hrect] using hAtN
  · simp [hrect]

theorem checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_productKChunks
    {productKLen a nLo nLen : Nat} {edgeChunk : Nat × Nat}
    (hproductKLen : 0 < productKLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks)
    (hchunks :
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nLo nLen productKChunk.1 productKChunk.2 = true) :
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
      a nLo nLen edgeChunk.1 edgeChunk.2 = true := by
  unfold checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
  apply List.all_eq_true.mpr
  intro N hNmem
  by_cases hrect : positiveRectangle a N
  · have hAtN :
        checkPositiveTemperedXYProductRawClearedTableKChunkAtN
          a N edgeChunk.1 edgeChunk.2 = true := by
      unfold checkPositiveTemperedXYProductRawClearedTableKChunkAtN
      apply List.all_eq_true.mpr
      intro k hkmem
      by_cases hcell : k ∈ positiveKRange a ∧ ceilSqrt N < k
      · rcases (mem_positiveEdgeDefaultKChunks_iff).1 hedgeChunk with
          ⟨i, hi, hedgeEq⟩
        have hkmem' : k ∈ List.range' (1 + 20 * i) 20 := by
          simpa [hedgeEq] using hkmem
        rcases (List.mem_range'_1.mp hkmem') with ⟨hklo, hkhi⟩
        have hk1 : 1 ≤ k := by omega
        have hk1800 : k ≤ 1800 := by omega
        rcases positiveProductFixedKChunks_cover_of_le_1800
            hproductKLen hk1 hk1800 with
          ⟨productKChunk, hproductKChunk, hkProductMem⟩
        have hcellCheck :
            checkPositiveTemperedXYProductRawClearedTableCell
              (cList a) (BListQ (cList a) N a)
              (QListQ (cList a) N a) a N k = true :=
          checkPositiveTemperedXYProductRawClearedTableCell_of_NRangeKChunk
            (hchunks hproductKChunk) hNmem hkProductMem hrect
            hcell.1 hcell.2
        simpa [hcell] using hcellCheck
      · simp [hcell]
    simpa [hrect] using hAtN
  · simp [hrect]

theorem checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_productKChunks
    {productKLen nLen lo len nIndex : Nat} {edgeChunk : Nat × Nat}
    (hproductKLen : 0 < productKLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks)
    (hchunks :
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
          nLen lo len nIndex productKChunk.1 productKChunk.2 = true) :
    checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
      nLen lo len nIndex edgeChunk.1 edgeChunk.2 = true := by
  unfold checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  exact
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_productKChunks
      hproductKLen hedgeChunk
      (fun {productKChunk} hproductKChunk =>
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
          (hchunks hproductKChunk) ha_mem)

theorem checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_productKChunks
    {productKLen nLen lo len nIndex : Nat} {edgeChunk : Nat × Nat}
    (hproductKLen : 0 < productKLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks)
    (hchunks :
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
          nLen lo len nIndex productKChunk.1 productKChunk.2 = true) :
    checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
      nLen lo len nIndex edgeChunk.1 edgeChunk.2 = true := by
  unfold checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
  apply List.all_eq_true.mpr
  intro a ha_mem
  exact
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_productKChunks
      hproductKLen hedgeChunk
      (fun {productKChunk} hproductKChunk =>
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
          (hchunks hproductKChunk) ha_mem)

theorem checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
    {edgeScale : Nat → Nat}
    (hchunks :
      ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
        ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnitRowRange
            rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 edgeScale = true)
    {a : Nat} (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    {edgeChunk : Nat × Nat} (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks) :
    checkPositiveEdgeMajorantKChunkUnit
      a edgeChunk.1 edgeChunk.2 (edgeScale a) = true := by
  rcases positiveSaddleDefaultChunks_cover (a := a) ha401 ha2000 with
    ⟨rowChunk, hrowChunk, hlo, hhi⟩
  exact checkPositiveEdgeMajorantKChunkUnit_of_rowRange
      (hchunks (rowChunk := rowChunk) hrowChunk
        (edgeChunk := edgeChunk) hedgeChunk)
    hlo hhi

theorem checkPositiveEdgeMajorantKChunkUnit_of_rowChunks
    {rowChunks : List (Nat × Nat)} {edgeScale : Nat → Nat}
    (hcover : PositiveSaddleFiniteWindowChunkCover rowChunks)
    (hchunks :
      ∀ {rowChunk : Nat × Nat}, rowChunk ∈ rowChunks →
        ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnitRowRange
            rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 edgeScale = true)
    {a : Nat} (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    {edgeChunk : Nat × Nat} (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks) :
    checkPositiveEdgeMajorantKChunkUnit
      a edgeChunk.1 edgeChunk.2 (edgeScale a) = true := by
  rcases hcover ha401 ha2000 with ⟨rowChunk, hrowChunk, hlo, hhi⟩
  exact checkPositiveEdgeMajorantKChunkUnit_of_rowRange
    (hchunks (rowChunk := rowChunk) hrowChunk
      (edgeChunk := edgeChunk) hedgeChunk)
    hlo hhi

/-- Single Boolean over all fixed product row chunks and default edge
`k`-chunks, for the small table-product finite family. -/
def checkPositiveSmallXYProductRawClearedTableFixedNChunksFixedRowKChunks
    (rowLen nLen : Nat) : Bool :=
  (positiveSaddleFixedRowChunks rowLen).all fun rowChunk =>
    positiveEdgeDefaultKChunkList.all fun edgeChunk =>
      checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
        nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2

/-- Single Boolean over all fixed product row chunks and default edge
`k`-chunks, for the tempered table-product finite family. -/
def checkPositiveTemperedXYProductRawClearedTableFixedNChunksFixedRowKChunks
    (rowLen nLen : Nat) : Bool :=
  (positiveSaddleFixedRowChunks rowLen).all fun rowChunk =>
    positiveEdgeDefaultKChunkList.all fun edgeChunk =>
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
        nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2

/-- Single Boolean over all fixed tangent row chunks. -/
def checkPositiveSmallTangentExpEdgeFixedRows (rowLen : Nat) : Bool :=
  (positiveSaddleFixedRowChunks rowLen).all fun rowChunk =>
    checkPositiveSmallTangentExpEdgeRange rowChunk.1 rowChunk.2

/-- Single Boolean over all fixed displayed-solo saddle row chunks. -/
def checkPositiveSoloDisplayedYSaddleClearedFixedRows
    (rowLen : Nat) : Bool :=
  (positiveSaddleFixedRowChunks rowLen).all fun rowChunk =>
    checkPositiveSoloDisplayedYSaddleClearedRange rowChunk.1 rowChunk.2

/-- Single Boolean over all fixed displayed-solo budget row chunks. -/
def checkPositiveSoloDisplayedYBoundUnitFixedRows
    (rowLen : Nat) : Bool :=
  (positiveSaddleFixedRowChunks rowLen).all fun rowChunk =>
    checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2

/-- Single Boolean over all fixed edge row chunks and default edge
`k`-chunks. -/
def checkPositiveEdgeMajorantKChunkUnitFixedRowKChunks
    (rowLen : Nat) : Bool :=
  (positiveSaddleFixedRowChunks rowLen).all fun rowChunk =>
    positiveEdgeDefaultKChunkList.all fun edgeChunk =>
      checkPositiveEdgeMajorantKChunkUnitRowRange
        rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
        (fun _ => positiveEdgeUniformScaleMin)

theorem checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_fixedRowKChunks
    {rowLen nLen : Nat}
    (h :
      checkPositiveSmallXYProductRawClearedTableFixedNChunksFixedRowKChunks
        rowLen nLen = true)
    {rowChunk edgeChunk : Nat × Nat}
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks) :
    checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
      nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true := by
  have hrows :
      ∀ chunk ∈ positiveSaddleFixedRowChunks rowLen,
        positiveEdgeDefaultKChunkList.all
          (fun edge =>
            checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
              nLen chunk.1 chunk.2 edge.1 edge.2) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXYProductRawClearedTableFixedNChunksFixedRowKChunks]
        using h)
  have hedges :
      ∀ edge ∈ positiveEdgeDefaultKChunkList,
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edge.1 edge.2 = true := by
    exact List.all_eq_true.mp (hrows rowChunk hrowChunk)
  exact hedges edgeChunk
    ((mem_positiveEdgeDefaultKChunkList_iff).2 hedgeChunk)

theorem checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_fixedRowKChunks
    {rowLen nLen : Nat}
    (h :
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksFixedRowKChunks
        rowLen nLen = true)
    {rowChunk edgeChunk : Nat × Nat}
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks) :
    checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
      nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true := by
  have hrows :
      ∀ chunk ∈ positiveSaddleFixedRowChunks rowLen,
        positiveEdgeDefaultKChunkList.all
          (fun edge =>
            checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
              nLen chunk.1 chunk.2 edge.1 edge.2) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXYProductRawClearedTableFixedNChunksFixedRowKChunks]
        using h)
  have hedges :
      ∀ edge ∈ positiveEdgeDefaultKChunkList,
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edge.1 edge.2 = true := by
    exact List.all_eq_true.mp (hrows rowChunk hrowChunk)
  exact hedges edgeChunk
    ((mem_positiveEdgeDefaultKChunkList_iff).2 hedgeChunk)

theorem checkPositiveSmallTangentExpEdgeRange_of_fixedRows
    {rowLen : Nat}
    (h : checkPositiveSmallTangentExpEdgeFixedRows rowLen = true)
    {rowChunk : Nat × Nat}
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen) :
    checkPositiveSmallTangentExpEdgeRange
      rowChunk.1 rowChunk.2 = true := by
  have hall :
      ∀ chunk ∈ positiveSaddleFixedRowChunks rowLen,
        checkPositiveSmallTangentExpEdgeRange
          chunk.1 chunk.2 = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeFixedRows] using h)
  exact hall rowChunk hrowChunk

theorem checkPositiveSoloDisplayedYSaddleClearedRange_of_fixedRows
    {rowLen : Nat}
    (h : checkPositiveSoloDisplayedYSaddleClearedFixedRows rowLen = true)
    {rowChunk : Nat × Nat}
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen) :
    checkPositiveSoloDisplayedYSaddleClearedRange
      rowChunk.1 rowChunk.2 = true := by
  have hall :
      ∀ chunk ∈ positiveSaddleFixedRowChunks rowLen,
        checkPositiveSoloDisplayedYSaddleClearedRange
          chunk.1 chunk.2 = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloDisplayedYSaddleClearedFixedRows] using h)
  exact hall rowChunk hrowChunk

theorem checkPositiveSoloDisplayedYBoundUnitRange_of_fixedRows
    {rowLen : Nat}
    (h : checkPositiveSoloDisplayedYBoundUnitFixedRows rowLen = true)
    {rowChunk : Nat × Nat}
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen) :
    checkPositiveSoloDisplayedYBoundUnitRange
      rowChunk.1 rowChunk.2 = true := by
  have hall :
      ∀ chunk ∈ positiveSaddleFixedRowChunks rowLen,
        checkPositiveSoloDisplayedYBoundUnitRange
          chunk.1 chunk.2 = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloDisplayedYBoundUnitFixedRows] using h)
  exact hall rowChunk hrowChunk

theorem checkPositiveEdgeMajorantKChunkUnit_of_fixedRowKChunks
    {rowLen : Nat}
    (h : checkPositiveEdgeMajorantKChunkUnitFixedRowKChunks rowLen = true)
    {rowChunk edgeChunk : Nat × Nat}
    (hrowChunk : rowChunk ∈ positiveSaddleFixedRowChunks rowLen)
    (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks) :
    checkPositiveEdgeMajorantKChunkUnitRowRange
      rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
        (fun _ => positiveEdgeUniformScaleMin) = true := by
  have hrows :
      ∀ chunk ∈ positiveSaddleFixedRowChunks rowLen,
        positiveEdgeDefaultKChunkList.all
          (fun edge =>
            checkPositiveEdgeMajorantKChunkUnitRowRange
              chunk.1 chunk.2 edge.1 edge.2
                (fun _ => positiveEdgeUniformScaleMin)) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveEdgeMajorantKChunkUnitFixedRowKChunks] using h)
  have hedges :
      ∀ edge ∈ positiveEdgeDefaultKChunkList,
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edge.1 edge.2
            (fun _ => positiveEdgeUniformScaleMin) = true := by
    exact List.all_eq_true.mp (hrows rowChunk hrowChunk)
  exact hedges edgeChunk
    ((mem_positiveEdgeDefaultKChunkList_iff).2 hedgeChunk)

theorem positiveEdgeBudget_of_defaultKChunksBounds
    {a : Nat} {budget : Nat × Nat → ℚ}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        positiveEdgeMajorantKChunkSum a chunk.1 chunk.2 ≤ budget chunk)
    (hbudget :
      ∑ chunk ∈ positiveEdgeDefaultKChunks, budget chunk ≤ positiveEdgeBudget) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_KChunksBounds
    (a := a) (chunks := positiveEdgeDefaultKChunks)
    (budget := budget) ha401 ha2000
    positiveEdgeDefaultKChunks_disjoint
    (fun hk => positiveEdgeDefaultKChunks_cover ha2000 hk)
    hchunks hbudget

theorem positiveEdgeBudget_of_defaultKChunksUnitChecks
    {a : Nat} {scale : Nat × Nat → Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hscale :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        0 < scale chunk)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (scale chunk) = true)
    (hbudget :
      ∑ chunk ∈ positiveEdgeDefaultKChunks,
        (1 : ℚ) / (scale chunk : ℚ) ≤ positiveEdgeBudget) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_KChunksUnitChecks
    (a := a) (chunks := positiveEdgeDefaultKChunks)
    (scale := scale) ha401 ha2000
    positiveEdgeDefaultKChunks_disjoint
    (fun hk => positiveEdgeDefaultKChunks_cover ha2000 hk)
    hscale hchunks hbudget

theorem positiveEdgeDefaultKChunks_uniformBudget
    {scale : Nat} (hbudget : (90 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget) :
    ∑ _chunk ∈ positiveEdgeDefaultKChunks,
      (1 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget := by
  rw [Finset.sum_const, positiveEdgeDefaultKChunks_card, nsmul_eq_mul]
  change (90 : ℚ) * (1 / (scale : ℚ)) ≤ positiveEdgeBudget
  rw [show (90 : ℚ) * (1 / (scale : ℚ)) = (90 : ℚ) / (scale : ℚ) by ring]
  exact hbudget

theorem positiveEdgeUniformBudget_of_scale_ge
    {scale : Nat} (hscale : positiveEdgeUniformScaleMin ≤ scale) :
    (90 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget := by
  rw [positiveEdgeBudget_eq_inv_200000000]
  have hscalePosQ : (0 : ℚ) < (scale : ℚ) := by
    exact_mod_cast positiveEdgeUniformScale_pos_of_scale_ge hscale
  rw [div_le_iff₀ hscalePosQ]
  have hscaleQ : (positiveEdgeUniformScaleMin : ℚ) ≤ (scale : ℚ) := by
    exact_mod_cast hscale
  have hmul :=
    mul_le_mul_of_nonneg_left hscaleQ
      (by norm_num : (0 : ℚ) ≤ 1 / 200000000)
  norm_num [positiveEdgeUniformScaleMin] at hmul
  simpa [mul_comm] using hmul

theorem positiveEdgeDefaultKChunks_uniformBudget_of_scale_ge
    {scale : Nat} (hscale : positiveEdgeUniformScaleMin ≤ scale) :
    ∑ _chunk ∈ positiveEdgeDefaultKChunks,
      (1 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget :=
  positiveEdgeDefaultKChunks_uniformBudget
    (positiveEdgeUniformBudget_of_scale_ge hscale)

theorem positiveEdgeBudget_of_defaultKChunksUniformUnitChecks
    {a scale : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000) (hscale : 0 < scale)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 scale = true)
    (hbudget : (90 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_defaultKChunksUnitChecks
    (a := a) (scale := fun _ => scale) ha401 ha2000
    (fun {_chunk} _hchunk => hscale)
    hchunks
    (positiveEdgeDefaultKChunks_uniformBudget hbudget)

theorem positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
    {a scale : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hscale : positiveEdgeUniformScaleMin ≤ scale)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 scale = true) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_defaultKChunksUniformUnitChecks
    ha401 ha2000
    (positiveEdgeUniformScale_pos_of_scale_ge hscale)
    hchunks
    (positiveEdgeUniformBudget_of_scale_ge hscale)

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

/-- Direct-tail certificate specialized to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeCertificate : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeCertificate
    positiveSaddleDefaultChunks

/-- Geometric entropy-tail certificate specialized to the default
finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Geometric reserve entropy-tail certificate specialized to the default
finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Quotient reserve entropy-tail certificate specialized to the default
finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Raw-base quotient reserve entropy-tail certificate specialized to the
default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Mixed-direction geometric reserve entropy-tail certificate specialized to
the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedReverseRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyMixedGeometricReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedReverseRatio

/-- Mixed-direction raw-quotient reserve entropy-tail certificate specialized
to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedReverseRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyMixedRawQuotientReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedReverseRatio

/-- Concrete variable-cutoff mixed raw-quotient reserve entropy-tail
certificate specialized to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    (smallRatio temperedReverseRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    positiveSaddleDefaultChunks smallRatio temperedReverseRatio

/-- Concrete split-tempered large-exp raw-quotient reserve entropy-tail
certificate specialized to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (temperedSplit : Nat → Nat)
    (smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ) :
    Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    positiveSaddleDefaultChunks temperedSplit smallRatio temperedLowerRatio
    temperedUpperReverseRatio

theorem positiveSaddleDefaultChunkedRangeCertificate
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyTail :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeCertificate where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyTail := entropyTail

theorem positiveSaddleDefaultChunkedRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyGeometric :
      PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyGeometric := entropyGeometric

theorem positiveSaddleDefaultChunkedRangeEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyGeometricReserve :
      PositiveSaddleEntropyShadowExpGeometricReserveCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyGeometricReserve := entropyGeometricReserve

theorem positiveSaddleDefaultChunkedRangeEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyQuotientReserve :
      PositiveSaddleEntropyShadowExpQuotientReserveCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyQuotientReserve := entropyQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyRawQuotientReserve :
      PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyRawQuotientReserve := entropyRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyMixedGeometricReserve :
      PositiveSaddleEntropyShadowExpMixedGeometricReserveCertificate
        smallExp temperedExp smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyMixedGeometricReserve := entropyMixedGeometricReserve

theorem positiveSaddleDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyMixedRawQuotientReserve :
      PositiveSaddleEntropyShadowExpMixedRawQuotientReserveCertificate
        smallExp temperedExp smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyMixedRawQuotientReserve := entropyMixedRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyLargeMixedRawQuotientReserve :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyLargeMixedRawQuotientReserve := entropyLargeMixedRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    hsmall htempered htangent hsolo hedge
    (pointwise.toLargeExpMixedRawQuotientReserveCertificate bounds)

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpGcompPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toGcompPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpGcompPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_productY_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_productY_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_crossmul_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyLargeSplitTemperedRawQuotientReserve :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyLargeSplitTemperedRawQuotientReserve :=
    entropyLargeSplitTemperedRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    hsmall htempered htangent hsolo hedge
    (pointwise.toLargeExpSplitTemperedRawQuotientReserveCertificate bounds)

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_crossmul_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedCrossmulBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_productY_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_productY_crossmul_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedCrossmulBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_productY_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedCrossmulBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_crossmul_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toSplitTemperedCrossmulBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_productY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedCrossmulBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toCandidateSplitTemperedCrossmulBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_productY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    hsmall htempered htangent hsolo hedge
    (pointwise.toLargeExpCandidateSplitTemperedLinearReserveCertificate bounds)

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProductY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseLinearCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProduct_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseLinearCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProductY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseRawCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toLinearBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_productY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_linearProduct_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toLinearBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_linearProductY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseLinearCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProduct_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProduct_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toLinearBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProductY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseRawCertificate bounds

/-- Current most concrete generated-audit target for the default finite-window
positive-saddle path.

This packages exactly the artifacts still expected from computation or
rational audits: the five finite-window chunk families, the raw `X+Y`/`Gcomp`
large-exp product estimates with the `Y_a(N)` solo form, and the raw-cleared
candidate split-tempered entropy-tail bounds. -/
structure PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRaw :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate
  candidateSplitTemperedRawCleared :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate

theorem PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProductY_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeChunks
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRaw
    cert.candidateSplitTemperedRawCleared

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductY_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProductY_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toRawClearedBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductYUnitSolo_parts
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
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductY_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseYRawCertificate bounds

/-- Unit-scaled version of the current concrete generated-audit target.

Compared with
`PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate`,
the candidate tail certificate clears the fixed reserve denominator
`positiveEdgeBudget / 4 = 1 / 800000000`. -/
structure PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRaw :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductY_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeChunks
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRaw
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Unit-scaled solo and reserve version of the current concrete
generated-audit target.

In addition to the candidate tail reserve scaling, the large-exp product
pointwise solo field is stated as `200000000 * solo ≤ 1`. -/
structure PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductYUnitSolo_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeChunks
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using cell-level tangent-edge checks and
chunked row checks for the other finite predicates. -/
theorem positiveSaddleDefaultCellEdgeRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeRowsCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      hsmall (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      htempered (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloGcompRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompRow_of_checkRangeChunks
      hsolo (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  edgeBudgetRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRangeChunks
      hedge (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Unit-budget final audit target with cell-level tangent-edge finite checks.

This variant is intended for generated certificates when the tangent-edge cell
predicate is fast but full tangent rows or ranges are not. -/
structure PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeRowsCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeRowsCertificate :=
  positiveSaddleDefaultCellEdgeRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using cell-level tangent-edge checks and
unit-scaled solo/edge chunk checks. -/
theorem positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompUnitRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetUnitRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      hsmall (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      htempered (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloGcompUnitRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompUnitRow_of_checkUnitRangeChunks
      hsolo (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  edgeBudgetUnitRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetUnitRow_of_checkPositiveEdgeBudgetUnitRangeChunks
      hedge (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Unit-cleared finite budget audit target with cell-level tangent-edge
checks.

Compared with
`PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
the finite solo and edge chunk predicates clear the common denominator
`positiveSoloBudget = positiveEdgeBudget = 1 / 200000000`. -/
structure PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloGcompUnitChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompUnitRange chunk.1 chunk.2 = true
  edgeBudgetUnitChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetUnitRange chunk.1 chunk.2 = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeUnitBudgetRowsCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate :=
  positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloGcompUnitChunks
    cert.edgeBudgetUnitChunks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using cell-level tangent-edge checks and
semantic finite solo/edge budget fields.

This is the practical audit endpoint while the corresponding executable
solo/edge row checks are too expensive to run directly.  It is mathematically
the same budget interface consumed by `PositiveSaddleTangentProductBudgetCertificate`;
the divergence from the TeX-style fully finite audit is only where these two
finite inequalities are supplied to Lean. -/
theorem positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (hedge :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeMajorantSum a ≤ positiveEdgeBudget)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      hsmall (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      htempered (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloY := hsolo
  edgeBudget := hedge
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Unit-budget large-tail audit target with cell-level tangent-edge checks
and semantic finite solo/edge budget fields.

The finite product predicates remain default chunk booleans; the tangent edge
predicate is supplied cell-by-cell; the finite solo and edge budgets are
ordinary inequalities. -/
structure PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloY
    cert.edgeBudget
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using default `k`-chunk edge checks.

This sits between the fully semantic edge-budget endpoint and the currently
too-expensive whole-row edge boolean: each generated row may prove 90 smaller
unit-scaled `k`-chunk checks, together with a rational sum of their declared
budgets. -/
theorem positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (edgeScale : Nat → Nat × Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks → 0 < edgeScale a chunk)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a chunk) = true)
    (hedgeBudget :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        ∑ chunk ∈ positiveEdgeDefaultKChunks,
          (1 : ℚ) / (edgeScale a chunk : ℚ) ≤ positiveEdgeBudget)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent hsolo
    (by
      intro a ha h2000
      exact positiveEdgeBudget_of_defaultKChunksUnitChecks
        ha h2000
        (fun {chunk} hchunk => hedgeScale ha h2000 hchunk)
        (fun {chunk} hchunk => hedgeChunks ha h2000 hchunk)
        (hedgeBudget ha h2000))
    pointwise bounds

/-- Audit target using default edge `k`-chunk checks instead of one whole-row
edge-budget boolean. -/
structure PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat × Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeScalePos :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks → 0 < edgeScale a chunk
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a chunk) = true
  edgeKChunkBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      ∑ chunk ∈ positiveEdgeDefaultKChunks,
        (1 : ℚ) / (edgeScale a chunk : ℚ) ≤ positiveEdgeBudget
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloY
    edgeScale
    cert.edgeScalePos
    cert.edgeKChunkUnitChecks
    cert.edgeKChunkBudget
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 → 0 < edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (hedgeBudget :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        (90 : ℚ) / (edgeScale a : ℚ) ≤ positiveEdgeBudget)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent hsolo
    (fun a _chunk => edgeScale a)
    (fun {_a} {_chunk} ha h2000 _hchunk => hedgeScale ha h2000)
    (fun {_a} {_chunk} ha h2000 hchunk => hedgeChunks ha h2000 hchunk)
    (fun {_a} ha h2000 =>
      positiveEdgeDefaultKChunks_uniformBudget (hedgeBudget ha h2000))
    pointwise bounds

theorem positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent hsolo
    edgeScale
    (fun {_a} ha h2000 =>
      positiveEdgeUniformScale_pos_of_scale_ge (hedgeScale ha h2000))
    hedgeChunks
    (fun {_a} ha h2000 =>
      positiveEdgeUniformBudget_of_scale_ge (hedgeScale ha h2000))
    pointwise bounds

theorem positiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        Ynorm N a ≤ positiveYBound a N a)
    (hsoloBudget : checkPositiveSoloDisplayedYBoundUnitRange 401 1600 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent
    (dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_checkUnitRange
      hsoloY hsoloBudget)
    edgeScale hedgeScale hedgeChunks pointwise bounds

theorem positiveSoloDisplayedYBound_of_defaultUnitChunks
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    {a N : Nat} (ha : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) :
    positiveSoloDisplayedYBound a N ≤ positiveSoloBudget := by
  have hrow : checkPositiveSoloDisplayedYBoundUnitRow a = true := by
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveSoloDisplayedYBoundUnitRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveSoloDisplayedYBoundUnitRange]
          using hchunks (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha ha2000)
  exact positiveSoloDisplayedYBound_of_checkUnitRow hrow hrect

theorem dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
    (hY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        Ynorm N a ≤ positiveYBound a N a)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget := by
  intro a N ha ha2000 hrect
  exact (dyadic_Ynorm_le_positiveSoloDisplayedYBound
      (hY ha ha2000 hrect)).trans
    (positiveSoloDisplayedYBound_of_defaultUnitChunks
      hchunks ha ha2000 hrect)

theorem Ynorm_le_positiveYBound_of_defaultClearedChunks
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a := by
  intro a N ha ha2000 hrect
  have hrow : checkPositiveSoloDisplayedYSaddleClearedRow a = true := by
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveSoloDisplayedYSaddleClearedRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveSoloDisplayedYSaddleClearedRange]
          using hchunks (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha ha2000)
  exact Ynorm_le_positiveYBound_of_positiveSoloDisplayedYSaddleCleared
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a)
    (positiveSoloDisplayedYSaddleCleared_of_checkRow hrow hrect)

/-- Arbitrary-row-cover version of the displayed-solo budget extractor. -/
theorem positiveSoloDisplayedYBound_of_unitRowChunks
    {chunks : List (Nat × Nat)}
    (hcover : PositiveSaddleFiniteWindowChunkCover chunks)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    {a N : Nat} (ha : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) :
    positiveSoloDisplayedYBound a N ≤ positiveSoloBudget := by
  rcases hcover ha ha2000 with ⟨rowChunk, hrowChunk, hlo, hhi⟩
  exact positiveSoloDisplayedYBound_of_checkUnitRange
    (hchunks (chunk := rowChunk) hrowChunk) hlo hhi hrect

/-- Arbitrary-row-cover version of the cleared displayed-solo saddle
extractor. -/
theorem Ynorm_le_positiveYBound_of_clearedRowChunks
    {chunks : List (Nat × Nat)}
    (hcover : PositiveSaddleFiniteWindowChunkCover chunks)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a := by
  intro a N ha ha2000 hrect
  rcases hcover ha ha2000 with ⟨rowChunk, hrowChunk, hlo, hhi⟩
  exact Ynorm_le_positiveYBound_of_positiveSoloDisplayedYSaddleCleared
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a)
    (positiveSoloDisplayedYSaddleCleared_of_checkRange
      (hchunks (chunk := rowChunk) hrowChunk) hlo hhi hrect)

theorem dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_rowChunks
    {saddleChunks budgetChunks : List (Nat × Nat)}
    (hsaddleCover : PositiveSaddleFiniteWindowChunkCover saddleChunks)
    (hbudgetCover : PositiveSaddleFiniteWindowChunkCover budgetChunks)
    (hsaddleChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ saddleChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hbudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ budgetChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget := by
  intro a N ha ha2000 hrect
  exact (dyadic_Ynorm_le_positiveSoloDisplayedYBound
      (Ynorm_le_positiveYBound_of_clearedRowChunks
        hsaddleCover hsaddleChunks ha ha2000 hrect)).trans
    (positiveSoloDisplayedYBound_of_unitRowChunks
      hbudgetCover hbudgetChunks ha ha2000 hrect)

theorem positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        Ynorm N a ≤ positiveYBound a N a)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent
    (dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      hsoloY hsoloBudgetChunks)
    edgeScale hedgeScale hedgeChunks pointwise bounds

theorem positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent
    (Ynorm_le_positiveYBound_of_defaultClearedChunks hsoloClearedChunks)
    hsoloBudgetChunks edgeScale hedgeScale hedgeChunks pointwise bounds

theorem positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmallCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true)
    (htemperedCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (fun {chunk} hchunk =>
      checkPositiveSmallXplusYProductGcompRange_of_checkClearedRange
        (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
        (hsmallCleared (chunk := chunk) hchunk))
    (fun {chunk} hchunk =>
      checkPositiveTemperedXplusYProductGcompRange_of_checkClearedRange
        (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
        (htemperedCleared (chunk := chunk) hchunk))
    htangent hsoloClearedChunks hsoloBudgetChunks
    edgeScale hedgeScale hedgeChunks pointwise bounds

/-- Exact-product variant of
`positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunks...`.

The finite product chunks here check the actual denominator-cleared
`Bq * Qq` inequalities, not the independent `Xplus`/`Gcomp` product
majorants.  This is the preferred generated-certificate target for the
finite product fields. -/
theorem positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmallRawCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXYProductRawClearedRange chunk.1 chunk.2 = true)
    (htemperedRawCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXYProductRawClearedRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleRawProductTangentCellEdgeBudgetCertificate where
  smallXYRawClearedRows := by
    intro a ha h2000
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveSmallXYProductRawClearedRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveSmallXYProductRawClearedRange]
          using hsmallRawCleared (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXYRawClearedRows := by
    intro a ha h2000
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveTemperedXYProductRawClearedRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveTemperedXYProductRawClearedRange]
          using htemperedRawCleared (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      (Ynorm_le_positiveYBound_of_defaultClearedChunks hsoloClearedChunks)
      hsoloBudgetChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 (hedgeScale ha h2000)
      (fun {chunk} hchunk => hedgeChunks (a := a) (chunk := chunk)
        ha h2000 hchunk)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Fine-grained table-backed product certificate.

The exact raw product checks are too expensive as whole-row booleans.  This
interface lets generated certificates provide, for each finite-window row
`a`, a cover of the positive `N`-rectangle by half-open chunks and then check
each `N`-chunk against the default 20-wide retained-`k` chunks.  The checker
itself uses shared `c`, `B`, and `Q` tables at each `(a,N)`. -/
structure PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
    (productNChunks : Nat → List (Nat × Nat)) : Prop where
  productNChunksCover :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      ∃ chunk : Nat × Nat,
        chunk ∈ productNChunks a ∧ N ∈ List.range' chunk.1 chunk.2
  smallXYTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

theorem positiveSaddleRawProductTableSingletonNChunkedTangentCellEdgeBudgetCertificate_of_parts
    (hsmall :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveSmallXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htempered :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (hedge :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeMajorantSum a ≤ positiveEdgeBudget)
    (hentropy :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks where
  productNChunksCover := by
    intro _a _N _ha _ha2000 hrect
    exact positiveProductSingletonNChunks_cover hrect
  smallXYTableChunks := hsmall
  temperedXYTableChunks := htempered
  smallTangentEdgeCells := htangent
  soloY := hsolo
  edgeBudget := hedge
  entropyTail := hentropy

theorem PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate.toTangentProductBudgetCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
        productNChunks) :
    PositiveSaddleTangentProductBudgetCertificate where
  smallXYTangent := by
    intro a N k ha ha2000 hrect hk hsmall _hB
    rcases cert.productNChunksCover ha ha2000 hrect with
      ⟨nChunk, hnChunk, hNmem⟩
    rcases positiveEdgeDefaultKChunks_cover ha2000 hk with
      ⟨kChunk, hkChunk, hkMem⟩
    have hraw : positiveSmallXYProductRawCleared a N k :=
      positiveSmallXYProductRawCleared_of_checkTableNRangeKChunk
        (by omega : 1 ≤ a)
        (cert.smallXYTableChunks ha ha2000 hnChunk hkChunk)
        hNmem hrect hkMem hk hsmall
    exact positiveSmallXYProductTangentBound_of_rawCleared
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
      (by omega : 1 ≤ a) hk hraw
  smallTangentEdge := by
    intro a N k ha ha2000 hrect hk hsmall
    exact positiveSmallTangentExpEdgeGap_of_checkCell
      (cert.smallTangentEdgeCells ha ha2000 hrect hk hsmall)
  temperedXY := by
    intro a N k ha ha2000 hrect hk htempered _hB
    rcases cert.productNChunksCover ha ha2000 hrect with
      ⟨nChunk, hnChunk, hNmem⟩
    rcases positiveEdgeDefaultKChunks_cover ha2000 hk with
      ⟨kChunk, hkChunk, hkMem⟩
    have hraw : positiveTemperedXYProductRawCleared a N k :=
      positiveTemperedXYProductRawCleared_of_checkTableNRangeKChunk
        (by omega : 1 ≤ a)
        (cert.temperedXYTableChunks ha ha2000 hnChunk hkChunk)
        hNmem hrect hkMem hk htempered
    exact positiveTemperedXYProductBound_of_rawCleared
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
      (by omega : 1 ≤ a) hk hraw
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

/-- Table-backed exact-product constructor with the current finite solo,
edge, and entropy-tail audit inputs.

The finite product side uses the corrected raw `Bq * Qq` table checks.  This
is the practical generated-certificate route replacing the older independent
`Xplus`/`Gcomp` product route, whose product inequalities are intentionally
stronger than the combined-exponent target. -/
theorem positiveSaddleRawProductTableChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    {productNChunks : Nat → List (Nat × Nat)}
    (hcover :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        ∃ chunk : Nat × Nat,
          chunk ∈ productNChunks a ∧ N ∈ List.range' chunk.1 chunk.2)
    (hsmall :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveSmallXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htempered :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      productNChunks where
  productNChunksCover := hcover
  smallXYTableChunks := hsmall
  temperedXYTableChunks := htempered
  smallTangentEdgeCells := htangent
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      (Ynorm_le_positiveYBound_of_defaultClearedChunks hsoloClearedChunks)
      hsoloBudgetChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 (hedgeScale ha h2000)
      (fun {chunk} hchunk => hedgeChunks (a := a) (chunk := chunk)
        ha h2000 hchunk)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Singleton-`N` specialization of the table-backed exact-product
constructor.  Generated certificates can still use larger row-dependent
`N`-chunks through the parameterized constructor above. -/
theorem positiveSaddleRawProductTableSingletonNChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveSmallXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htempered :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks :=
  positiveSaddleRawProductTableChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (productNChunks := positiveProductSingletonNChunks)
    (fun {_a _N} _ha _h2000 hrect =>
      positiveProductSingletonNChunks_cover hrect)
    hsmall htempered htangent
    hsoloClearedChunks hsoloBudgetChunks
    edgeScale hedgeScale hedgeChunks pointwise bounds

/-- Audit target using the same edge unit scale for every default `k`-chunk
in a fixed row `a`.

This is a generated-certificate convenience wrapper around
`PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`:
instead of providing a scale and reciprocal budget for each of the 90 chunks,
it is enough to provide one positive scale per row and the single budget check
`90 / scale ≤ positiveEdgeBudget`. -/
structure PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeScalePos :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 → 0 < edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  edgeKChunkBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      (90 : ℚ) / (edgeScale a : ℚ) ≤ positiveEdgeBudget
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Same uniform edge-scale audit target, with the reciprocal-budget field
replaced by the natural lower bound
`positiveEdgeUniformScaleMin ≤ edgeScale a`.

This is a Lean-side generated-certificate convenience: the definition of
`positiveEdgeUniformScaleMin` proves exactly the rational inequality required
by the sibling uniform-budget endpoint. -/
structure PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Preferred generated-audit wrapper with the finite solo input split in the
same shape as the TeX proof: prove the displayed tempered `Y_a(N)` saddle
bound, and discharge the remaining rational budget by the unit-scaled
displayed-solo range check. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYDisplayed :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a
  soloYBudget :
    checkPositiveSoloDisplayedYBoundUnitRange 401 1600 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper using the default finite-window chunks for
the rational solo-budget check.  This is the practical variant of the
displayed-solo endpoint: the `Y_a(N)` saddle estimate remains a semantic
field, while the budget side is split into the same 100-row chunks used by
the product checks. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYDisplayed :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with both finite solo sub-obligations
chunked over the default 100-row cover.

The saddle field is the denominator-cleared displayed `Y_a(N)` inequality,
and the budget field is the unit-scaled displayed-solo budget.  This is the
lowest-level current Lean target for the finite solo side; it is still a
finite certificate route, not a proof of the analytic saddle estimate from
first principles. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with denominator-cleared finite product
chunks.

This is a lower-level variant of
`PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`:
the small and tempered product fields clear the `X`/`Y` `Gcomp`
normalization denominators before evaluation, while converting back to the
same normalized product row checks used by the established proof chain. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with exact raw-product cleared chunks.

This is the corrected finite product endpoint after the independent
`Xplus`/`Gcomp` product check was found to be too strong.  The product chunks
check the actual denominator-cleared `Bq * Qq` inequalities, and the wrapper
converts to `PositiveSaddleRawProductTangentCellEdgeBudgetCertificate`. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXYProductRawClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXYProductRawClearedRange chunk.1 chunk.2 = true
  temperedXYProductRawClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXYProductRawClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with table-backed exact raw-product chunks.

This is the concrete generated-certificate target for the corrected finite
product route.  The product fields are checked against the shared
`c`/`B`/`Q` tables on singleton `N` chunks and the default 20-wide retained
`k` chunks; the rest of the finite and large-tail inputs are the same as in
the displayed-solo raw-product endpoint. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Table-backed exact raw-product wrapper for arbitrary generated `N` chunks,
with tangent and edge checks chunked and the edge scale fixed.

Generated certificates can instantiate `productNChunks` with coarser
row-dependent `N` chunks than the built-in singleton cover, while retaining
the same default row chunks for tangent/solo and the same fixed-scale edge
row chunks. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (productNChunks : Nat → List (Nat × Nat)) :
    Prop where
  productNChunksCover :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      ∃ chunk : Nat × Nat,
        chunk ∈ productNChunks a ∧ N ∈ List.range' chunk.1 chunk.2
  smallXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ productNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ productNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fixed-width `N`-chunk version of the table-backed exact raw-product
wrapper.

This is the preferred generated-certificate shape when all rows use the same
positive `N`-chunk length: product checks are stated over the default row
chunks and default retained-`k` chunks, and the fixed-width `N`-chunk cover is
proved once by `positiveProductFixedNChunks_cover`. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (nLen : Nat) :
    Prop where
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fixed-width `N`-chunk table-product wrapper with an independent product
row cover.

Product table checks are often much heavier than the other finite checks, so
generated certificates may need product row chunks smaller than the default
100-row cover used for tangent, solo, and edge checks. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (productRowChunks : List (Nat × Nat)) (nLen : Nat) :
    Prop where
  productRowChunksCover : PositiveSaddleFiniteWindowChunkCover productRowChunks
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ productRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ productRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fully fixed-width product-chunk wrapper.

The generated product side is controlled by two positive lengths: `rowLen`
for the product row chunks and `nLen` for each row's `N` chunks.  The product
row cover is supplied by `positiveSaddleFixedRowChunks_cover`. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (rowLen nLen : Nat) :
    Prop where
  rowLenPos : 0 < rowLen
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleFixedRowChunks rowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleFixedRowChunks rowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fixed-width `N`-chunk table-product wrapper with independent product and
tangent row covers.

This is the most flexible generated finite-window endpoint on the corrected
exact-product route when range checks need different row granularities.  The
product table checks are grouped by `productRowChunks`, while the corrected
tangent-edge range checks are grouped by `tangentRowChunks`; displayed-solo
and edge checks keep the default finite-window chunks. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (productRowChunks tangentRowChunks : List (Nat × Nat)) (nLen : Nat) :
    Prop where
  productRowChunksCover : PositiveSaddleFiniteWindowChunkCover productRowChunks
  tangentRowChunksCover : PositiveSaddleFiniteWindowChunkCover tangentRowChunks
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ productRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ productRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ tangentRowChunks →
      checkPositiveSmallTangentExpEdgeRange rowChunk.1 rowChunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fully fixed-width version with independent product and tangent row
lengths.

This is a convenience wrapper over
`PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunks...`:
`positiveSaddleFixedRowChunks` supplies both finite row covers. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (productRowLen tangentRowLen nLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      checkPositiveSmallTangentExpEdgeRange rowChunk.1 rowChunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fixed-width `N`-chunk table-product wrapper with independent row covers
for every finite range-check family.

This endpoint is intended for generated certificates that need to tune each
finite Boolean family separately.  It keeps the corrected exact-product route
and fixed edge scale, but lets product, tangent, displayed-solo saddle,
displayed-solo budget, and edge `k`-chunk checks each use their own finite
row cover. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (productRowChunks tangentRowChunks soloSaddleRowChunks
      soloBudgetRowChunks edgeRowChunks : List (Nat × Nat)) (nLen : Nat) :
    Prop where
  productRowChunksCover : PositiveSaddleFiniteWindowChunkCover productRowChunks
  tangentRowChunksCover : PositiveSaddleFiniteWindowChunkCover tangentRowChunks
  soloSaddleRowChunksCover :
    PositiveSaddleFiniteWindowChunkCover soloSaddleRowChunks
  soloBudgetRowChunksCover :
    PositiveSaddleFiniteWindowChunkCover soloBudgetRowChunks
  edgeRowChunksCover : PositiveSaddleFiniteWindowChunkCover edgeRowChunks
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ productRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ productRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ tangentRowChunks →
      checkPositiveSmallTangentExpEdgeRange rowChunk.1 rowChunk.2 = true
  soloYSaddleClearedRowRangeChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ soloSaddleRowChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange
        rowChunk.1 rowChunk.2 = true
  soloYBudgetRowRangeChunks :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ soloBudgetRowChunks →
      checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ edgeRowChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Fully fixed-width version of the independent finite-row-cover endpoint.

Each finite Boolean family gets its own positive row length, and
`positiveSaddleFixedRowChunks` supplies all five covers. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      checkPositiveSmallTangentExpEdgeRange rowChunk.1 rowChunk.2 = true
  soloYSaddleClearedRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      checkPositiveSoloDisplayedYSaddleClearedRange
        rowChunk.1 rowChunk.2 = true
  soloYBudgetRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Short alias for the fully fixed-width final positive-saddle audit target. -/
abbrev PositiveSaddleFixedFiniteAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat) : Prop :=
  PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
    edgeRowLen nLen

/-- Finite-window part of `PositiveSaddleFixedFiniteAuditCertificate`.

This is the target generated files should usually prove with `native_decide`.
The two non-finite large-`a` certificates are supplied separately by
`PositiveSaddleLargeTailAuditCertificate`. -/
structure PositiveSaddleFixedFiniteWindowAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      checkPositiveSmallTangentExpEdgeRange rowChunk.1 rowChunk.2 = true
  soloYSaddleClearedRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      checkPositiveSoloDisplayedYSaddleClearedRange
        rowChunk.1 rowChunk.2 = true
  soloYBudgetRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Fully executable fixed finite-window target.

This version asks for one `Bool` proof per finite family.  It is convenient
when the chosen row lengths make each whole-family `native_decide` check fast
enough.  If a family is too large, use
`PositiveSaddleFixedFiniteWindowAuditCertificate` directly and split that
field into smaller generated lemmas. -/
structure PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableFixedRowKChunks :
    checkPositiveSmallXYProductRawClearedTableFixedNChunksFixedRowKChunks
      productRowLen nLen = true
  temperedXYProductRawClearedTableFixedRowKChunks :
    checkPositiveTemperedXYProductRawClearedTableFixedNChunksFixedRowKChunks
      productRowLen nLen = true
  smallTangentExpEdgeFixedRows :
    checkPositiveSmallTangentExpEdgeFixedRows tangentRowLen = true
  soloYSaddleClearedFixedRows :
    checkPositiveSoloDisplayedYSaddleClearedFixedRows soloSaddleRowLen = true
  soloYBudgetFixedRows :
    checkPositiveSoloDisplayedYBoundUnitFixedRows soloBudgetRowLen = true
  edgeKChunkUnitFixedRowKChunks :
    checkPositiveEdgeMajorantKChunkUnitFixedRowKChunks edgeRowLen = true

/-- Fixed finite-window target with tangent checks kept at cell granularity.

This is the practical split target when tangent row-range booleans are still
too large for `native_decide`: product, displayed-solo, and edge obligations
use fixed row chunks, while the tangent finite obligation is supplied as the
already-supported cell predicate `checkPositiveSmallTangentExpEdgeCell`. -/
structure PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
    (productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  nLenPos : 0 < nLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          nLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      checkPositiveSoloDisplayedYSaddleClearedRange
        rowChunk.1 rowChunk.2 = true
  soloYBudgetRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Fixed finite-window target with tangent checks chunked in row, `N`, and
small-regime `k`.

This is the fully generated variant of
`PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate`: the tangent
cell field is discharged by fixed row chunks, fixed `N` chunks inside each
row, and fixed `k` chunks covering `1 ≤ k ≤ 155`. -/
structure PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  productNLenPos : 0 < productNLen
  tangentNLenPos : 0 < tangentNLen
  tangentKLenPos : 0 < tangentKLen
  smallXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeNChunksKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
        checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk
          tangentNLen rowChunk.1 rowChunk.2 kChunk.1 kChunk.2 = true
  soloYSaddleClearedRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      checkPositiveSoloDisplayedYSaddleClearedRange
        rowChunk.1 rowChunk.2 = true
  soloYBudgetRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Fixed finite-window target with both product and tangent checks split by
row and `N` chunks.

This is the lowest-granularity fixed-width finite target currently exposed for
generated certificates.  Product checks are supplied by row chunk, by a
uniform product `N`-chunk index, and by default retained-`k` chunk; tangent
checks are supplied by row, `N`, and small-`k` chunks. -/
structure PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  productNLenPos : 0 < productNLen
  tangentNLenPos : 0 < tangentNLen
  tangentKLenPos : 0 < tangentKLen
  smallXYProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeNChunksKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
        checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk
          tangentNLen rowChunk.1 rowChunk.2 kChunk.1 kChunk.2 = true
  soloYSaddleClearedRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      checkPositiveSoloDisplayedYSaddleClearedRange
        rowChunk.1 rowChunk.2 = true
  soloYBudgetRowRangeChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      checkPositiveSoloDisplayedYBoundUnitRange rowChunk.1 rowChunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Fixed finite-window target with product, tangent, and displayed-solo checks
split by uniform fixed `N`-chunk indices.

This is a proof-production refinement of
`PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate`.
The mathematical endpoint is the same, but the tangent and solo generated
atoms no longer have to prove a full row's worth of `N` chunks at once. -/
structure PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  productNLenPos : 0 < productNLen
  tangentNLenPos : 0 < tangentNLen
  soloSaddleNLenPos : 0 < soloSaddleNLen
  soloBudgetNLenPos : 0 < soloBudgetNLen
  tangentKLenPos : 0 < tangentKLen
  smallXYProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex edgeChunk.1 edgeChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex edgeChunk.1 edgeChunk.2 = true
  smallTangentExpEdgeRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices tangentRowLen tangentNLen →
      ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
        checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
          tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true
  soloYSaddleClearedRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloSaddleRowLen soloSaddleNLen →
        checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
          soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true
  soloYBudgetRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloBudgetRowLen soloBudgetNLen →
        checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
          soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Fixed finite-window target with product checks split by row, `N`, and
retained-`k` chunk, while tangent and displayed-solo checks use the same
fixed `N`-index split as
`PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate`.

This is a proof-production refinement only: the product `k` atoms can be
finer than the default 20-wide edge chunks, and the conversion below assembles
them back to the older default-`k` product obligations. -/
structure PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  productNLenPos : 0 < productNLen
  productKLenPos : 0 < productKLen
  tangentNLenPos : 0 < tangentNLen
  soloSaddleNLenPos : 0 < soloSaddleNLen
  soloBudgetNLenPos : 0 < soloBudgetNLen
  tangentKLenPos : 0 < tangentKLen
  smallXYProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex
            productKChunk.1 productKChunk.2 = true
  temperedXYProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex
            productKChunk.1 productKChunk.2 = true
  smallTangentExpEdgeRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices tangentRowLen tangentNLen →
      ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
        checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
          tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true
  soloYSaddleClearedRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloSaddleRowLen soloSaddleNLen →
        checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
          soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true
  soloYBudgetRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloBudgetRowLen soloBudgetNLen →
        checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
          soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Fixed finite-window target with combined small/tempered product atoms.

This is a proof-production refinement of
`PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate`.
The product field runs one table-backed pass per row/`N`/retained-`k` atom and
checks the small or tempered product inequality according to the usual
`k ≤ ceilSqrt N` split.  The conversion below extracts the two older product
fields, so the mathematical endpoint is unchanged. -/
structure PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  productNLenPos : 0 < productNLen
  productKLenPos : 0 < productKLen
  tangentNLenPos : 0 < tangentNLen
  soloSaddleNLenPos : 0 < soloSaddleNLen
  soloBudgetNLenPos : 0 < soloBudgetNLen
  tangentKLenPos : 0 < tangentKLen
  xyProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex
            productKChunk.1 productKChunk.2 = true
  smallTangentExpEdgeRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices tangentRowLen tangentNLen →
      ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
        checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
          tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true
  soloYSaddleClearedRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloSaddleRowLen soloSaddleNLen →
        checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
          soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true
  soloYBudgetRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloBudgetRowLen soloBudgetNLen →
        checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
          soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true

/-- Combined-product proof-production target with a separate fixed-width edge
`k`-chunk cover.

This is mathematically the same finite-window route as
`PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate`,
but its edge field ranges over `positiveEdgeFixedKChunks edgeKLen` and uses the
matching reciprocal scale `positiveEdgeFixedKScale edgeKLen`.  This is a Lean
proof-production refinement of the TeX edge-budget decomposition: the analytic
edge majorant and final budget are unchanged, while the executable atoms may be
much narrower than the default 20-wide chunks. -/
structure PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
    (productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat) :
    Prop where
  productRowLenPos : 0 < productRowLen
  tangentRowLenPos : 0 < tangentRowLen
  soloSaddleRowLenPos : 0 < soloSaddleRowLen
  soloBudgetRowLenPos : 0 < soloBudgetRowLen
  edgeRowLenPos : 0 < edgeRowLen
  productNLenPos : 0 < productNLen
  productKLenPos : 0 < productKLen
  tangentNLenPos : 0 < tangentNLen
  soloSaddleNLenPos : 0 < soloSaddleNLen
  soloBudgetNLenPos : 0 < soloBudgetNLen
  tangentKLenPos : 0 < tangentKLen
  edgeKLenPos : 0 < edgeKLen
  xyProductRawClearedTableProductRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks productRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices productRowLen productNLen →
      ∀ {productKChunk : Nat × Nat},
        productKChunk ∈ positiveProductFixedKChunks productKLen →
        checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
          productNLen rowChunk.1 rowChunk.2 nIndex
            productKChunk.1 productKChunk.2 = true
  smallTangentExpEdgeRowRangeNIndexKChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices tangentRowLen tangentNLen →
      ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
        checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
          tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true
  soloYSaddleClearedRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloSaddleRowLen soloSaddleNLen →
        checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
          soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true
  soloYBudgetRowRangeNIndexChunks :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
      ∀ {nIndex : Nat},
        nIndex ∈ positiveProductFixedNChunkIndices soloBudgetRowLen soloBudgetNLen →
        checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
          soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat},
      rowChunk ∈ positiveSaddleFixedRowChunks edgeRowLen →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeFixedKChunks edgeKLen →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeFixedKScale edgeKLen) = true

/-- Large-`a` part shared by the generated fixed finite-window targets. -/
structure PositiveSaddleLargeTailAuditCertificate : Prop where
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Large-tail audit certificate with the two remaining analytic inputs split
into natural subtargets.  The conversion below rebuilds
`PositiveSaddleLargeTailAuditCertificate`, so this is a proof-production
interface rather than a different mathematical endpoint. -/
structure PositiveSaddleLargeTailPartsAuditCertificate : Prop where
  smallProductRaw : PositiveSaddleLargeTailSmallProductRawCertificate
  temperedProductRaw : PositiveSaddleLargeTailTemperedProductRawCertificate
  soloYUnit : PositiveSaddleLargeTailSoloYUnitCertificate
  candidateRawClearedSteps :
    PositiveSaddleLargeTailCandidateRawClearedStepCertificate
  candidateUnitReserves :
    PositiveSaddleLargeTailCandidateUnitReserveCertificate

theorem positiveSaddleLargeTailPartsAuditCertificate_of_productBounds
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product : PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound)
    (solo : PositiveSaddleLargeTailSoloYUnitCertificate)
    (steps : PositiveSaddleLargeTailCandidateRawClearedStepCertificate)
    (reserves : PositiveSaddleLargeTailCandidateUnitReserveCertificate) :
    PositiveSaddleLargeTailPartsAuditCertificate where
  smallProductRaw := product.toSmallProductRawCertificate
  temperedProductRaw := product.toTemperedProductRawCertificate
  soloYUnit := solo
  candidateRawClearedSteps := steps
  candidateUnitReserves := reserves

theorem positiveSaddleLargeTailPartsAuditCertificate_of_productAndSoloBounds
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (product : PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound)
    (solo : PositiveSaddleLargeTailSoloYBoundCertificate soloYBound)
    (steps : PositiveSaddleLargeTailCandidateRawClearedStepCertificate)
    (reserves : PositiveSaddleLargeTailCandidateUnitReserveCertificate) :
    PositiveSaddleLargeTailPartsAuditCertificate :=
  positiveSaddleLargeTailPartsAuditCertificate_of_productBounds
    product solo.toSoloYUnitCertificate steps reserves

/-- Large-tail audit certificate with product and solo saddle bounds split
before reassembling to the grouped candidate step/reserve interface. -/
structure PositiveSaddleLargeTailBoundsPartsAuditCertificate
    (smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ)
    (soloYBound : Nat → Nat → ℚ) : Prop where
  productBounds :
    PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound
  soloY : PositiveSaddleLargeTailSoloYBoundCertificate soloYBound
  candidateRawClearedSteps :
    PositiveSaddleLargeTailCandidateRawClearedStepCertificate
  candidateUnitReserves :
    PositiveSaddleLargeTailCandidateUnitReserveCertificate

theorem PositiveSaddleLargeTailBoundsPartsAuditCertificate.toLargeTailPartsAuditCertificate
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailBoundsPartsAuditCertificate
      smallXBound smallYBound temperedXBound temperedYBound soloYBound) :
  PositiveSaddleLargeTailPartsAuditCertificate :=
  positiveSaddleLargeTailPartsAuditCertificate_of_productAndSoloBounds
    cert.productBounds cert.soloY
    cert.candidateRawClearedSteps cert.candidateUnitReserves

theorem PositiveSaddleLargeTailBoundsPartsAuditCertificate.toLargeTailAuditCertificate
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailBoundsPartsAuditCertificate
      smallXBound smallYBound temperedXBound temperedYBound soloYBound) :
    PositiveSaddleLargeTailAuditCertificate where
  productPointwiseYRawUnitSolo :=
    positiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate_of_parts
      cert.productBounds.toSmallProductRawCertificate
      cert.productBounds.toTemperedProductRawCertificate
      cert.soloY.toSoloYUnitCertificate
  candidateSplitTemperedRawClearedUnitReserve :=
    positiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate_of_parts
      cert.candidateRawClearedSteps cert.candidateUnitReserves

theorem PositiveSaddleLargeTailPartsAuditCertificate.toProductPointwiseYRawUnitSoloCertificate
    (cert : PositiveSaddleLargeTailPartsAuditCertificate) :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate :=
  positiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate_of_parts
    cert.smallProductRaw cert.temperedProductRaw cert.soloYUnit

theorem PositiveSaddleLargeTailPartsAuditCertificate.toCandidateRawClearedUnitReserveBoundsCertificate
    (cert : PositiveSaddleLargeTailPartsAuditCertificate) :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate :=
  positiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate_of_parts
    cert.candidateRawClearedSteps cert.candidateUnitReserves

theorem PositiveSaddleLargeTailPartsAuditCertificate.toCandidateBoundsCertificate
    (cert : PositiveSaddleLargeTailPartsAuditCertificate) :
    PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveBoundsCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  cert.toCandidateRawClearedUnitReserveBoundsCertificate.toBoundsCertificate

theorem PositiveSaddleLargeTailPartsAuditCertificate.toLargeTailAuditCertificate
    (cert : PositiveSaddleLargeTailPartsAuditCertificate) :
    PositiveSaddleLargeTailAuditCertificate where
  productPointwiseYRawUnitSolo :=
    cert.toProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.toCandidateRawClearedUnitReserveBoundsCertificate

/-- Large-tail audit certificate with the six candidate entropy-reserve
families split into atomic one-dimensional targets.  This refines
`PositiveSaddleLargeTailPartsAuditCertificate` only as a proof-production
interface; the reassembled mathematical certificate is unchanged. -/
structure PositiveSaddleLargeTailAtomicPartsAuditCertificate : Prop where
  smallProductRaw : PositiveSaddleLargeTailSmallProductRawCertificate
  temperedProductRaw : PositiveSaddleLargeTailTemperedProductRawCertificate
  soloYUnit : PositiveSaddleLargeTailSoloYUnitCertificate
  candidateSmallRawStep :
    PositiveSaddleLargeTailCandidateSmallRawStepCertificate
  candidateTemperedLowerRawStep :
    PositiveSaddleLargeTailCandidateTemperedLowerRawStepCertificate
  candidateTemperedUpperReverseRawStep :
    PositiveSaddleLargeTailCandidateTemperedUpperReverseRawStepCertificate
  candidateSmallFirstReserve :
    PositiveSaddleLargeTailCandidateSmallFirstReserveCertificate
  candidateTemperedLowerFirstReserve :
    PositiveSaddleLargeTailCandidateTemperedLowerFirstReserveCertificate
  candidateTemperedUpperLastReserve :
    PositiveSaddleLargeTailCandidateTemperedUpperLastReserveCertificate

theorem positiveSaddleLargeTailAtomicPartsAuditCertificate_of_productBounds
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product : PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound)
    (solo : PositiveSaddleLargeTailSoloYUnitCertificate)
    (smallStep : PositiveSaddleLargeTailCandidateSmallRawStepCertificate)
    (temperedLowerStep :
      PositiveSaddleLargeTailCandidateTemperedLowerRawStepCertificate)
    (temperedUpperStep :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseRawStepCertificate)
    (smallReserve : PositiveSaddleLargeTailCandidateSmallFirstReserveCertificate)
    (temperedLowerReserve :
      PositiveSaddleLargeTailCandidateTemperedLowerFirstReserveCertificate)
    (temperedUpperReserve :
      PositiveSaddleLargeTailCandidateTemperedUpperLastReserveCertificate) :
    PositiveSaddleLargeTailAtomicPartsAuditCertificate where
  smallProductRaw := product.toSmallProductRawCertificate
  temperedProductRaw := product.toTemperedProductRawCertificate
  soloYUnit := solo
  candidateSmallRawStep := smallStep
  candidateTemperedLowerRawStep := temperedLowerStep
  candidateTemperedUpperReverseRawStep := temperedUpperStep
  candidateSmallFirstReserve := smallReserve
  candidateTemperedLowerFirstReserve := temperedLowerReserve
  candidateTemperedUpperLastReserve := temperedUpperReserve

theorem positiveSaddleLargeTailAtomicPartsAuditCertificate_of_productAndSoloBounds
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (product : PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound)
    (solo : PositiveSaddleLargeTailSoloYBoundCertificate soloYBound)
    (smallStep : PositiveSaddleLargeTailCandidateSmallRawStepCertificate)
    (temperedLowerStep :
      PositiveSaddleLargeTailCandidateTemperedLowerRawStepCertificate)
    (temperedUpperStep :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseRawStepCertificate)
    (smallReserve : PositiveSaddleLargeTailCandidateSmallFirstReserveCertificate)
    (temperedLowerReserve :
      PositiveSaddleLargeTailCandidateTemperedLowerFirstReserveCertificate)
    (temperedUpperReserve :
      PositiveSaddleLargeTailCandidateTemperedUpperLastReserveCertificate) :
    PositiveSaddleLargeTailAtomicPartsAuditCertificate :=
  positiveSaddleLargeTailAtomicPartsAuditCertificate_of_productBounds
    product solo.toSoloYUnitCertificate smallStep temperedLowerStep
    temperedUpperStep smallReserve temperedLowerReserve temperedUpperReserve

/-- Large-tail audit certificate with product, solo, and candidate
entropy-reserve fields all split into the current atomic proof-production
targets. -/
structure PositiveSaddleLargeTailAtomicBoundsAuditCertificate
    (smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ)
    (soloYBound : Nat → Nat → ℚ) : Prop where
  productBounds :
    PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound
  soloY : PositiveSaddleLargeTailSoloYBoundCertificate soloYBound
  candidateSmallRawStep :
    PositiveSaddleLargeTailCandidateSmallRawStepCertificate
  candidateTemperedLowerRawStep :
    PositiveSaddleLargeTailCandidateTemperedLowerRawStepCertificate
  candidateTemperedUpperReverseRawStep :
    PositiveSaddleLargeTailCandidateTemperedUpperReverseRawStepCertificate
  candidateSmallFirstReserve :
    PositiveSaddleLargeTailCandidateSmallFirstReserveCertificate
  candidateTemperedLowerFirstReserve :
    PositiveSaddleLargeTailCandidateTemperedLowerFirstReserveCertificate
  candidateTemperedUpperLastReserve :
    PositiveSaddleLargeTailCandidateTemperedUpperLastReserveCertificate

theorem PositiveSaddleLargeTailAtomicBoundsAuditCertificate.toAtomicPartsAuditCertificate
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailAtomicBoundsAuditCertificate
      smallXBound smallYBound temperedXBound temperedYBound soloYBound) :
  PositiveSaddleLargeTailAtomicPartsAuditCertificate :=
  positiveSaddleLargeTailAtomicPartsAuditCertificate_of_productAndSoloBounds
    cert.productBounds cert.soloY cert.candidateSmallRawStep
    cert.candidateTemperedLowerRawStep
    cert.candidateTemperedUpperReverseRawStep
    cert.candidateSmallFirstReserve
    cert.candidateTemperedLowerFirstReserve
    cert.candidateTemperedUpperLastReserve

theorem PositiveSaddleLargeTailAtomicBoundsAuditCertificate.toLargeTailPartsAuditCertificate
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailAtomicBoundsAuditCertificate
      smallXBound smallYBound temperedXBound temperedYBound soloYBound) :
    PositiveSaddleLargeTailPartsAuditCertificate where
  smallProductRaw := cert.productBounds.toSmallProductRawCertificate
  temperedProductRaw := cert.productBounds.toTemperedProductRawCertificate
  soloYUnit := cert.soloY.toSoloYUnitCertificate
  candidateRawClearedSteps :=
    positiveSaddleLargeTailCandidateRawClearedStepCertificate_of_atomic
      cert.candidateSmallRawStep
      cert.candidateTemperedLowerRawStep
      cert.candidateTemperedUpperReverseRawStep
  candidateUnitReserves :=
    positiveSaddleLargeTailCandidateUnitReserveCertificate_of_atomic
      cert.candidateSmallFirstReserve
      cert.candidateTemperedLowerFirstReserve
      cert.candidateTemperedUpperLastReserve

theorem PositiveSaddleLargeTailAtomicBoundsAuditCertificate.toLargeTailAuditCertificate
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    {soloYBound : Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailAtomicBoundsAuditCertificate
      smallXBound smallYBound temperedXBound temperedYBound soloYBound) :
    PositiveSaddleLargeTailAuditCertificate where
  productPointwiseYRawUnitSolo :=
    positiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate_of_parts
      cert.productBounds.toSmallProductRawCertificate
      cert.productBounds.toTemperedProductRawCertificate
      cert.soloY.toSoloYUnitCertificate
  candidateSplitTemperedRawClearedUnitReserve :=
    positiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate_of_parts
      (positiveSaddleLargeTailCandidateRawClearedStepCertificate_of_atomic
        cert.candidateSmallRawStep
        cert.candidateTemperedLowerRawStep
        cert.candidateTemperedUpperReverseRawStep)
      (positiveSaddleLargeTailCandidateUnitReserveCertificate_of_atomic
        cert.candidateSmallFirstReserve
        cert.candidateTemperedLowerFirstReserve
        cert.candidateTemperedUpperLastReserve)

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toCandidateAtomicCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleLargeTailCandidateAtomicCertificate where
  smallRawStep := cert.candidateSmallRawStep
  temperedLowerRawStep := cert.candidateTemperedLowerRawStep
  temperedUpperReverseRawStep := cert.candidateTemperedUpperReverseRawStep
  smallFirstReserve := cert.candidateSmallFirstReserve
  temperedLowerFirstReserve := cert.candidateTemperedLowerFirstReserve
  temperedUpperLastReserve := cert.candidateTemperedUpperLastReserve

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toProductPointwiseYRawUnitSoloCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate :=
  positiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate_of_parts
    cert.smallProductRaw cert.temperedProductRaw cert.soloYUnit

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toCandidateRawClearedStepCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleLargeTailCandidateRawClearedStepCertificate :=
  cert.toCandidateAtomicCertificate.toRawClearedStepCertificate

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toCandidateUnitReserveCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleLargeTailCandidateUnitReserveCertificate :=
  cert.toCandidateAtomicCertificate.toUnitReserveCertificate

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toCandidateRawClearedUnitReserveBoundsCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate :=
  cert.toCandidateAtomicCertificate.toRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toCandidateBoundsCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveBoundsCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  cert.toCandidateAtomicCertificate.toBoundsCertificate

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toLargeTailPartsAuditCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleLargeTailPartsAuditCertificate where
  smallProductRaw := cert.smallProductRaw
  temperedProductRaw := cert.temperedProductRaw
  soloYUnit := cert.soloYUnit
  candidateRawClearedSteps :=
    cert.toCandidateRawClearedStepCertificate
  candidateUnitReserves :=
    cert.toCandidateUnitReserveCertificate

theorem PositiveSaddleLargeTailAtomicPartsAuditCertificate.toLargeTailAuditCertificate
    (cert : PositiveSaddleLargeTailAtomicPartsAuditCertificate) :
    PositiveSaddleLargeTailAuditCertificate :=
  cert.toLargeTailPartsAuditCertificate.toLargeTailAuditCertificate

/-- Table-backed exact raw-product wrapper with the remaining finite
tangent and edge checks also chunked.

This is the most compact corrected finite-window target: product checks use
singleton `N` table chunks and default retained-`k` chunks, tangent and solo
checks use the default 100-row chunks, and every edge row-chunk check uses the
fixed scale `positiveEdgeUniformScaleMin`.  It stays on the actual
`Bq * Qq` product route rather than the stronger independent `Gcomp` product
audit route. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Latest default-chunk finite-window audit wrapper.

Compared with
`PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
this also chunks the tangent-edge finite check over the default 100-row cover.
The wrapper converts those range checks back into the cell booleans expected
by the established cell-edge certificate. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Default-chunk finite-window audit wrapper with row-chunked edge
`k`-chunk checks.

This replaces the row-indexed edge `k`-chunk family by executable checks over
each default row chunk and each default edge `k`-chunk.  The scale lower bound
is still kept as a simple row-wise semantic field, which is typically
immediate for a generated or constant `edgeScale`. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 edgeScale = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Constant-scale version of the latest default-chunk audit wrapper.

All edge `k`-chunk checks use `positiveEdgeUniformScaleMin`, whose reciprocal
budget has already been proved to fit inside `positiveEdgeBudget`.  This is
the most compact current generated-certificate target for the finite window:
it has no semantic finite-budget fields and no row-dependent edge-scale data. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloY
    edgeScale
    cert.edgeScalePos
    cert.edgeKChunkUnitChecks
    cert.edgeKChunkBudget
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloY := cert.soloY
  edgeScalePos := by
    intro a ha h2000
    exact positiveEdgeUniformScale_pos_of_scale_ge (cert.edgeScaleLarge ha h2000)
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  edgeKChunkBudget := by
    intro a ha h2000
    exact positiveEdgeUniformBudget_of_scale_ge (cert.edgeScaleLarge ha h2000)
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_checkUnitRange
      cert.soloYDisplayed cert.soloYBudget
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      cert.soloYDisplayed cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toDisplayedSoloChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloYDisplayed :=
    Ynorm_le_positiveYBound_of_defaultClearedChunks
      cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toDisplayedSoloClearedChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := by
    intro chunk hchunk
    exact checkPositiveSmallXplusYProductGcompRange_of_checkClearedRange
      (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
      (cert.smallXplusYProductGcompClearedChunks hchunk)
  temperedXplusYProductGcompChunks := by
    intro chunk hchunk
    exact checkPositiveTemperedXplusYProductGcompRange_of_checkClearedRange
      (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
      (cert.temperedXplusYProductGcompClearedChunks hchunk)
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleRawProductTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXYProductRawClearedChunks
    cert.temperedXYProductRawClearedChunks
    cert.smallTangentExpEdgeCells
    cert.soloYSaddleClearedChunks
    cert.soloYBudgetChunks
    edgeScale
    cert.edgeScaleLarge
    cert.edgeKChunkUnitChecks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks :=
  positiveSaddleRawProductTableSingletonNChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXYProductRawClearedTableChunks
    cert.temperedXYProductRawClearedTableChunks
    cert.smallTangentExpEdgeCells
    cert.soloYSaddleClearedChunks
    cert.soloYBudgetChunks
    edgeScale
    cert.edgeScaleLarge
    cert.edgeKChunkUnitChecks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productNChunks) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      productNChunks :=
  positiveSaddleRawProductTableChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.productNChunksCover
    cert.smallXYProductRawClearedTableChunks
    cert.temperedXYProductRawClearedTableChunks
    (by
      intro a N k ha h2000 hrect hk hsmall
      have hrow : checkPositiveSmallTangentExpEdgeRow a = true := by
        exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
          cert.smallTangentExpEdgeChunks
          (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
      exact decide_eq_true
        (positiveSmallTangentExpEdgeGap_of_checkRow hrow hrect hk hsmall))
    cert.soloYSaddleClearedChunks
    cert.soloYBudgetChunks
    (fun _ => positiveEdgeUniformScaleMin)
    (fun {_a} _ha _h2000 => le_rfl)
    (fun {_a} {chunk} ha h2000 hchunk =>
      checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
        cert.edgeKChunkUnitRowRanges ha h2000 hchunk)
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productNChunks) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productNChunks) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productNChunks) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableNChunksAuditCertificate
    {productRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks nLen) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (positiveProductFixedNChunks nLen) where
  productNChunksCover := by
    intro _a _N _ha _h2000 hrect
    exact positiveProductFixedNChunks_cover cert.nLenPos hrect
  smallXYProductRawClearedTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases cert.productRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.smallXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  temperedXYProductRawClearedTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases cert.productRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.temperedXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) :=
  cert.toRawProductTableNChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {productRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {productRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toProductRowChunksAuditCertificate
    {rowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        rowLen nLen) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (positiveSaddleFixedRowChunks rowLen) nLen where
  productRowChunksCover := positiveSaddleFixedRowChunks_cover cert.rowLenPos
  nLenPos := cert.nLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks :=
    cert.smallXYProductRawClearedTableProductRowRangeKChunks
  temperedXYProductRawClearedTableProductRowRangeKChunks :=
    cert.temperedXYProductRawClearedTableProductRowRangeKChunks
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {rowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        rowLen nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) :=
  cert.toProductRowChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {rowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        rowLen nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {rowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        rowLen nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {rowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        rowLen nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowChunks tangentRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) where
  productNChunksCover := by
    intro _a _N _ha _h2000 hrect
    exact positiveProductFixedNChunks_cover cert.nLenPos hrect
  smallXYTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases cert.productRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.smallXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  temperedXYTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases cert.productRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.temperedXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  smallTangentEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    rcases cert.tangentRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact decide_eq_true
      (positiveSmallTangentExpEdgeGap_of_checkRange
        (cert.smallTangentExpEdgeRowRangeChunks
          (rowChunk := rowChunk) hrowChunk)
        hlo hhi hrect hk hsmall)
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      (Ynorm_le_positiveYBound_of_defaultClearedChunks
        cert.soloYSaddleClearedChunks)
      cert.soloYBudgetChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 le_rfl
      (fun {chunk} hchunk =>
        checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
          cert.edgeKChunkUnitRowRanges ha h2000 hchunk)
  entropyTail :=
    (cert.productPointwiseYRawUnitSolo.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        cert.candidateSplitTemperedRawClearedUnitReserve.toRawClearedBoundsCertificate).entropyTail

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {productRowChunks tangentRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {productRowChunks tangentRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowChunks tangentRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toProductTangentRowChunksAuditCertificate
    {productRowLen tangentRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen nLen) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (positiveSaddleFixedRowChunks productRowLen)
      (positiveSaddleFixedRowChunks tangentRowLen) nLen where
  productRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.productRowLenPos
  tangentRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.tangentRowLenPos
  nLenPos := cert.nLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks :=
    cert.smallXYProductRawClearedTableProductRowRangeKChunks
  temperedXYProductRawClearedTableProductRowRangeKChunks :=
    cert.temperedXYProductRawClearedTableProductRowRangeKChunks
  smallTangentExpEdgeRowRangeChunks :=
    cert.smallTangentExpEdgeRowRangeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowLen tangentRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) :=
  cert.toProductTangentRowChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {productRowLen tangentRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowLen tangentRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowChunks tangentRowChunks soloSaddleRowChunks
      soloBudgetRowChunks edgeRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks soloSaddleRowChunks
        soloBudgetRowChunks edgeRowChunks nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) where
  productNChunksCover := by
    intro _a _N _ha _h2000 hrect
    exact positiveProductFixedNChunks_cover cert.nLenPos hrect
  smallXYTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases cert.productRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.smallXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  temperedXYTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases cert.productRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.temperedXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  smallTangentEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    rcases cert.tangentRowChunksCover ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact decide_eq_true
      (positiveSmallTangentExpEdgeGap_of_checkRange
        (cert.smallTangentExpEdgeRowRangeChunks
          (rowChunk := rowChunk) hrowChunk)
        hlo hhi hrect hk hsmall)
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_rowChunks
      cert.soloSaddleRowChunksCover
      cert.soloBudgetRowChunksCover
      cert.soloYSaddleClearedRowRangeChunks
      cert.soloYBudgetRowRangeChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 le_rfl
      (fun {chunk} hchunk =>
        checkPositiveEdgeMajorantKChunkUnit_of_rowChunks
          cert.edgeRowChunksCover
          cert.edgeKChunkUnitRowRanges
          ha h2000 hchunk)
  entropyTail :=
    (cert.productPointwiseYRawUnitSolo.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        cert.candidateSplitTemperedRawClearedUnitReserve.toRawClearedBoundsCertificate).entropyTail

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {productRowChunks tangentRowChunks soloSaddleRowChunks
      soloBudgetRowChunks edgeRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks soloSaddleRowChunks
        soloBudgetRowChunks edgeRowChunks nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {productRowChunks tangentRowChunks soloSaddleRowChunks
      soloBudgetRowChunks edgeRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks soloSaddleRowChunks
        soloBudgetRowChunks edgeRowChunks nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowChunks tangentRowChunks soloSaddleRowChunks
      soloBudgetRowChunks edgeRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks soloSaddleRowChunks
        soloBudgetRowChunks edgeRowChunks nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toIndependentRowChunksAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (positiveSaddleFixedRowChunks productRowLen)
      (positiveSaddleFixedRowChunks tangentRowLen)
      (positiveSaddleFixedRowChunks soloSaddleRowLen)
      (positiveSaddleFixedRowChunks soloBudgetRowLen)
      (positiveSaddleFixedRowChunks edgeRowLen) nLen where
  productRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.productRowLenPos
  tangentRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.tangentRowLenPos
  soloSaddleRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.soloSaddleRowLenPos
  soloBudgetRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.soloBudgetRowLenPos
  edgeRowChunksCover :=
    positiveSaddleFixedRowChunks_cover cert.edgeRowLenPos
  nLenPos := cert.nLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks :=
    cert.smallXYProductRawClearedTableProductRowRangeKChunks
  temperedXYProductRawClearedTableProductRowRangeKChunks :=
    cert.temperedXYProductRawClearedTableProductRowRangeKChunks
  smallTangentExpEdgeRowRangeChunks :=
    cert.smallTangentExpEdgeRowRangeChunks
  soloYSaddleClearedRowRangeChunks :=
    cert.soloYSaddleClearedRowRangeChunks
  soloYBudgetRowRangeChunks := cert.soloYBudgetRowRangeChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleFixedFiniteWindowAuditCertificate.toAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleFixedFiniteAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen where
  productRowLenPos := finite.productRowLenPos
  tangentRowLenPos := finite.tangentRowLenPos
  soloSaddleRowLenPos := finite.soloSaddleRowLenPos
  soloBudgetRowLenPos := finite.soloBudgetRowLenPos
  edgeRowLenPos := finite.edgeRowLenPos
  nLenPos := finite.nLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks :=
    finite.smallXYProductRawClearedTableProductRowRangeKChunks
  temperedXYProductRawClearedTableProductRowRangeKChunks :=
    finite.temperedXYProductRawClearedTableProductRowRangeKChunks
  smallTangentExpEdgeRowRangeChunks :=
    finite.smallTangentExpEdgeRowRangeChunks
  soloYSaddleClearedRowRangeChunks :=
    finite.soloYSaddleClearedRowRangeChunks
  soloYBudgetRowRangeChunks := finite.soloYBudgetRowRangeChunks
  edgeKChunkUnitRowRanges := finite.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := tail.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    tail.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate.toFiniteWindowAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen) :
    PositiveSaddleFixedFiniteWindowAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen where
  productRowLenPos := cert.productRowLenPos
  tangentRowLenPos := cert.tangentRowLenPos
  soloSaddleRowLenPos := cert.soloSaddleRowLenPos
  soloBudgetRowLenPos := cert.soloBudgetRowLenPos
  edgeRowLenPos := cert.edgeRowLenPos
  nLenPos := cert.nLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks := by
    intro rowChunk hrowChunk edgeChunk hedgeChunk
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_fixedRowKChunks
        cert.smallXYProductRawClearedTableFixedRowKChunks
        hrowChunk hedgeChunk
  temperedXYProductRawClearedTableProductRowRangeKChunks := by
    intro rowChunk hrowChunk edgeChunk hedgeChunk
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_fixedRowKChunks
        cert.temperedXYProductRawClearedTableFixedRowKChunks
        hrowChunk hedgeChunk
  smallTangentExpEdgeRowRangeChunks := by
    intro rowChunk hrowChunk
    exact checkPositiveSmallTangentExpEdgeRange_of_fixedRows
      cert.smallTangentExpEdgeFixedRows hrowChunk
  soloYSaddleClearedRowRangeChunks := by
    intro rowChunk hrowChunk
    exact checkPositiveSoloDisplayedYSaddleClearedRange_of_fixedRows
      cert.soloYSaddleClearedFixedRows hrowChunk
  soloYBudgetRowRangeChunks := by
    intro rowChunk hrowChunk
    exact checkPositiveSoloDisplayedYBoundUnitRange_of_fixedRows
      cert.soloYBudgetFixedRows hrowChunk
  edgeKChunkUnitRowRanges := by
    intro rowChunk hrowChunk edgeChunk hedgeChunk
    exact checkPositiveEdgeMajorantKChunkUnit_of_fixedRowKChunks
      cert.edgeKChunkUnitFixedRowKChunks hrowChunk hedgeChunk

theorem PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate.toAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleFixedFiniteAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen :=
  cert.toFiniteWindowAuditCertificate.toAuditCertificate tail

theorem PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
        productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) where
  productNChunksCover := by
    intro _a _N _ha _h2000 hrect
    exact positiveProductFixedNChunks_cover finite.nLenPos hrect
  smallXYTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases positiveSaddleFixedRowChunks_cover
        finite.productRowLenPos ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (finite.smallXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  temperedXYTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases positiveSaddleFixedRowChunks_cover
        finite.productRowLenPos ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (finite.temperedXYProductRawClearedTableProductRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  smallTangentEdgeCells := finite.smallTangentExpEdgeCells
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_rowChunks
      (positiveSaddleFixedRowChunks_cover finite.soloSaddleRowLenPos)
      (positiveSaddleFixedRowChunks_cover finite.soloBudgetRowLenPos)
      finite.soloYSaddleClearedRowRangeChunks
      finite.soloYBudgetRowRangeChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 le_rfl
      (fun {chunk} hchunk =>
        checkPositiveEdgeMajorantKChunkUnit_of_rowChunks
          (positiveSaddleFixedRowChunks_cover finite.edgeRowLenPos)
          finite.edgeKChunkUnitRowRanges
          ha h2000 hchunk)
  entropyTail :=
    (tail.productPointwiseYRawUnitSolo.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        tail.candidateSplitTemperedRawClearedUnitReserve.toRawClearedBoundsCertificate).entropyTail

theorem PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate.toCellTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen) :
    PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
      productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen productNLen where
  productRowLenPos := cert.productRowLenPos
  soloSaddleRowLenPos := cert.soloSaddleRowLenPos
  soloBudgetRowLenPos := cert.soloBudgetRowLenPos
  edgeRowLenPos := cert.edgeRowLenPos
  nLenPos := cert.productNLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks :=
    cert.smallXYProductRawClearedTableProductRowRangeKChunks
  temperedXYProductRawClearedTableProductRowRangeKChunks :=
    cert.temperedXYProductRawClearedTableProductRowRangeKChunks
  smallTangentExpEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    rcases positiveSaddleFixedRowChunks_cover
        cert.tangentRowLenPos ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    rcases positiveProductFixedNChunks_cover
        cert.tangentNLenPos hrect with
      ⟨nChunk, hnChunk, hNmem⟩
    rcases mem_positiveKRange.mp hk with ⟨hk1, _hkmax⟩
    rcases positiveTangentFixedKChunks_cover
        cert.tangentKLenPos h2000 hrect hk hsmall hk1 with
      ⟨kChunk, hkChunk, hKmem⟩
    exact
      checkPositiveSmallTangentExpEdgeCell_of_fixedNChunksRowRangeKChunk
        (cert.smallTangentExpEdgeRowRangeNChunksKChunks
          (rowChunk := rowChunk) hrowChunk (kChunk := kChunk) hkChunk)
        hlo hhi hnChunk hNmem hKmem hrect hk hsmall
  soloYSaddleClearedRowRangeChunks :=
    cert.soloYSaddleClearedRowRangeChunks
  soloYBudgetRowRangeChunks := cert.soloYBudgetRowRangeChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges

theorem PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks productNLen) :=
  cert.toCellTangentAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate tail

theorem PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
        productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  finite.toRawProductTableChunkedTangentCellEdgeBudgetCertificate tail
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate.toCertificate
    {productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
        productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  (finite.toTangentProductBudgetCertificate tail).toCertificate

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowCellTangentAuditCertificate
    {productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
        productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    (finite.toTangentProductBudgetCertificate tail)

theorem PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toCellTangentAuditCertificate.toTangentProductBudgetCertificate tail

theorem PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate.toCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toCellTangentAuditCertificate.toCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleFixedFiniteWindowCellTangentAuditCertificate
    cert.toCellTangentAuditCertificate tail

theorem PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate.toChunkedTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen) :
    PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen where
  productRowLenPos := cert.productRowLenPos
  tangentRowLenPos := cert.tangentRowLenPos
  soloSaddleRowLenPos := cert.soloSaddleRowLenPos
  soloBudgetRowLenPos := cert.soloBudgetRowLenPos
  edgeRowLenPos := cert.edgeRowLenPos
  productNLenPos := cert.productNLenPos
  tangentNLenPos := cert.tangentNLenPos
  tangentKLenPos := cert.tangentKLenPos
  smallXYProductRawClearedTableProductRowRangeKChunks := by
    intro rowChunk hrowChunk edgeChunk hedgeChunk
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksRowRangeKChunk_of_fixedNIndexRowRangeKChunks
        cert.productRowLenPos cert.productNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.smallXYProductRawClearedTableProductRowRangeNIndexKChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
            (edgeChunk := edgeChunk) hedgeChunk)
  temperedXYProductRawClearedTableProductRowRangeKChunks := by
    intro rowChunk hrowChunk edgeChunk hedgeChunk
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksRowRangeKChunk_of_fixedNIndexRowRangeKChunks
        cert.productRowLenPos cert.productNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.temperedXYProductRawClearedTableProductRowRangeNIndexKChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
            (edgeChunk := edgeChunk) hedgeChunk)
  smallTangentExpEdgeRowRangeNChunksKChunks :=
    cert.smallTangentExpEdgeRowRangeNChunksKChunks
  soloYSaddleClearedRowRangeChunks :=
    cert.soloYSaddleClearedRowRangeChunks
  soloYBudgetRowRangeChunks := cert.soloYBudgetRowRangeChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges

theorem PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate.toProductTangentSoloNChunkedAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen) :
    PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen where
  productRowLenPos := cert.productRowLenPos
  tangentRowLenPos := cert.tangentRowLenPos
  soloSaddleRowLenPos := cert.soloSaddleRowLenPos
  soloBudgetRowLenPos := cert.soloBudgetRowLenPos
  edgeRowLenPos := cert.edgeRowLenPos
  productNLenPos := cert.productNLenPos
  tangentNLenPos := cert.tangentNLenPos
  soloSaddleNLenPos := cert.soloSaddleNLenPos
  soloBudgetNLenPos := cert.soloBudgetNLenPos
  tangentKLenPos := cert.tangentKLenPos
  smallXYProductRawClearedTableProductRowRangeNIndexKChunks := by
    intro rowChunk hrowChunk nIndex hnIndex edgeChunk hedgeChunk
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_productKChunks
        cert.productKLenPos hedgeChunk
        (fun {productKChunk} hproductKChunk =>
          cert.smallXYProductRawClearedTableProductRowRangeNIndexKChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
            (productKChunk := productKChunk) hproductKChunk)
  temperedXYProductRawClearedTableProductRowRangeNIndexKChunks := by
    intro rowChunk hrowChunk nIndex hnIndex edgeChunk hedgeChunk
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_productKChunks
        cert.productKLenPos hedgeChunk
        (fun {productKChunk} hproductKChunk =>
          cert.temperedXYProductRawClearedTableProductRowRangeNIndexKChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
            (productKChunk := productKChunk) hproductKChunk)
  smallTangentExpEdgeRowRangeNIndexKChunks :=
    cert.smallTangentExpEdgeRowRangeNIndexKChunks
  soloYSaddleClearedRowRangeNIndexChunks :=
    cert.soloYSaddleClearedRowRangeNIndexChunks
  soloYBudgetRowRangeNIndexChunks :=
    cert.soloYBudgetRowRangeNIndexChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges

theorem PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate.toProductNKChunkedTangentSoloNChunkedAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen) :
    PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen where
  productRowLenPos := cert.productRowLenPos
  tangentRowLenPos := cert.tangentRowLenPos
  soloSaddleRowLenPos := cert.soloSaddleRowLenPos
  soloBudgetRowLenPos := cert.soloBudgetRowLenPos
  edgeRowLenPos := cert.edgeRowLenPos
  productNLenPos := cert.productNLenPos
  productKLenPos := cert.productKLenPos
  tangentNLenPos := cert.tangentNLenPos
  soloSaddleNLenPos := cert.soloSaddleNLenPos
  soloBudgetNLenPos := cert.soloBudgetNLenPos
  tangentKLenPos := cert.tangentKLenPos
  smallXYProductRawClearedTableProductRowRangeNIndexKChunks := by
    intro rowChunk hrowChunk nIndex hnIndex productKChunk hproductKChunk
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_combined
        (cert.xyProductRawClearedTableProductRowRangeNIndexKChunks
          (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
          (productKChunk := productKChunk) hproductKChunk)
  temperedXYProductRawClearedTableProductRowRangeNIndexKChunks := by
    intro rowChunk hrowChunk nIndex hnIndex productKChunk hproductKChunk
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_combined
        (cert.xyProductRawClearedTableProductRowRangeNIndexKChunks
          (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
          (productKChunk := productKChunk) hproductKChunk)
  smallTangentExpEdgeRowRangeNIndexKChunks :=
    cert.smallTangentExpEdgeRowRangeNIndexKChunks
  soloYSaddleClearedRowRangeNIndexChunks :=
    cert.soloYSaddleClearedRowRangeNIndexChunks
  soloYBudgetRowRangeNIndexChunks :=
    cert.soloYBudgetRowRangeNIndexChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges

theorem positiveSaddleFixedEdgeCombinedProduct_smallXYTangent
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen) :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤
          positiveSmallXYProductTangentBound a N k := by
  intro a N k ha h2000 hrect hk hsmall _hB
  rcases positiveSaddleFixedRowChunks_cover
      cert.productRowLenPos ha h2000 with
    ⟨rowChunk, hrowChunk, hlo, hhi⟩
  have haMem : a ∈ List.range' rowChunk.1 rowChunk.2 :=
    (List.mem_range'_1).mpr ⟨hlo, hhi⟩
  rcases positiveProductFixedNChunks_cover cert.productNLenPos hrect with
    ⟨nChunk, hnChunk, hNmem⟩
  rcases positiveProductFixedNChunkIndices_cover_chunk
      cert.productRowLenPos cert.productNLenPos hrowChunk haMem hnChunk with
    ⟨nIndex, hnIndex, hnChunkEq⟩
  rcases mem_positiveKRange.mp hk with ⟨hk1, hkmax⟩
  have hk1800 : k ≤ 1800 := by
    unfold posKmax at hkmax
    omega
  rcases positiveProductFixedKChunks_cover_of_le_1800
      cert.productKLenPos hk1 hk1800 with
    ⟨productKChunk, hproductKChunk, hKmem⟩
  have hfixedSmall :
      checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk
        productNLen rowChunk.1 rowChunk.2 nIndex
        productKChunk.1 productKChunk.2 = true :=
    checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_combined
      (cert.xyProductRawClearedTableProductRowRangeNIndexKChunks
        (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
        (productKChunk := productKChunk) hproductKChunk)
  have hNRange :
      checkPositiveSmallXYProductRawClearedTableNRangeKChunk
        a (posNlo a + productNLen * nIndex) productNLen
        productKChunk.1 productKChunk.2 = true :=
    checkPositiveSmallXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
      hfixedSmall haMem
  have hNmem' :
      N ∈ List.range' (posNlo a + productNLen * nIndex) productNLen := by
    simpa [hnChunkEq] using hNmem
  have hKmemIco :
      k ∈ Finset.Ico productKChunk.1
        (productKChunk.1 + productKChunk.2) :=
    Finset.mem_Ico.mpr ((List.mem_range'_1).mp hKmem)
  have hraw : positiveSmallXYProductRawCleared a N k :=
    positiveSmallXYProductRawCleared_of_checkTableNRangeKChunk
      (by omega : 1 ≤ a) hNRange hNmem' hrect hKmemIco hk hsmall
  exact positiveSmallXYProductTangentBound_of_rawCleared
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a) hk hraw

theorem positiveSaddleFixedEdgeCombinedProduct_smallTangentEdge
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen) :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        positiveSmallTangentExpEdgeGap a N k := by
  intro a N k ha h2000 hrect hk hsmall
  rcases positiveSaddleFixedRowChunks_cover
      cert.tangentRowLenPos ha h2000 with
    ⟨rowChunk, hrowChunk, hlo, hhi⟩
  have haMem : a ∈ List.range' rowChunk.1 rowChunk.2 :=
    (List.mem_range'_1).mpr ⟨hlo, hhi⟩
  rcases positiveProductFixedNChunks_cover cert.tangentNLenPos hrect with
    ⟨nChunk, hnChunk, hNmem⟩
  rcases positiveProductFixedNChunkIndices_cover_chunk
      cert.tangentRowLenPos cert.tangentNLenPos hrowChunk haMem hnChunk with
    ⟨nIndex, hnIndex, hnChunkEq⟩
  rcases mem_positiveKRange.mp hk with ⟨hk1, _hkmax⟩
  rcases positiveTangentFixedKChunks_cover
      cert.tangentKLenPos h2000 hrect hk hsmall hk1 with
    ⟨kChunk, hkChunk, hKmem⟩
  have hNRange :
      checkPositiveSmallTangentExpEdgeNRangeKChunk
        a (posNlo a + tangentNLen * nIndex) tangentNLen
        kChunk.1 kChunk.2 = true :=
    checkPositiveSmallTangentExpEdgeNRangeKChunk_of_fixedNIndexRowRangeKChunk
      (cert.smallTangentExpEdgeRowRangeNIndexKChunks
        (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
        (kChunk := kChunk) hkChunk)
      haMem
  have hNmem' :
      N ∈ List.range' (posNlo a + tangentNLen * nIndex) tangentNLen := by
    simpa [hnChunkEq] using hNmem
  exact positiveSmallTangentExpEdgeGap_of_checkCell
    (checkPositiveSmallTangentExpEdgeCell_of_NRangeKChunk
      hNRange hNmem' hKmem hrect hk hsmall)

theorem positiveSaddleFixedEdgeCombinedProduct_temperedXY
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen) :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤
          positiveTemperedXYProductBound a N k := by
  intro a N k ha h2000 hrect hk htempered _hB
  rcases positiveSaddleFixedRowChunks_cover
      cert.productRowLenPos ha h2000 with
    ⟨rowChunk, hrowChunk, hlo, hhi⟩
  have haMem : a ∈ List.range' rowChunk.1 rowChunk.2 :=
    (List.mem_range'_1).mpr ⟨hlo, hhi⟩
  rcases positiveProductFixedNChunks_cover cert.productNLenPos hrect with
    ⟨nChunk, hnChunk, hNmem⟩
  rcases positiveProductFixedNChunkIndices_cover_chunk
      cert.productRowLenPos cert.productNLenPos hrowChunk haMem hnChunk with
    ⟨nIndex, hnIndex, hnChunkEq⟩
  rcases mem_positiveKRange.mp hk with ⟨hk1, hkmax⟩
  have hk1800 : k ≤ 1800 := by
    unfold posKmax at hkmax
    omega
  rcases positiveProductFixedKChunks_cover_of_le_1800
      cert.productKLenPos hk1 hk1800 with
    ⟨productKChunk, hproductKChunk, hKmem⟩
  have hfixedTempered :
      checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk
        productNLen rowChunk.1 rowChunk.2 nIndex
        productKChunk.1 productKChunk.2 = true :=
    checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk_of_combined
      (cert.xyProductRawClearedTableProductRowRangeNIndexKChunks
        (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
        (productKChunk := productKChunk) hproductKChunk)
  have hNRange :
      checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
        a (posNlo a + productNLen * nIndex) productNLen
        productKChunk.1 productKChunk.2 = true :=
    checkPositiveTemperedXYProductRawClearedTableNRangeKChunk_of_fixedNIndexRowRangeKChunk
      hfixedTempered haMem
  have hNmem' :
      N ∈ List.range' (posNlo a + productNLen * nIndex) productNLen := by
    simpa [hnChunkEq] using hNmem
  have hKmemIco :
      k ∈ Finset.Ico productKChunk.1
        (productKChunk.1 + productKChunk.2) :=
    Finset.mem_Ico.mpr ((List.mem_range'_1).mp hKmem)
  have hraw : positiveTemperedXYProductRawCleared a N k :=
    positiveTemperedXYProductRawCleared_of_checkTableNRangeKChunk
      (by omega : 1 ≤ a) hNRange hNmem' hrect hKmemIco hk
      htempered
  exact positiveTemperedXYProductBound_of_rawCleared
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a) hk hraw

theorem positiveSaddleFixedEdgeCombinedProduct_soloY
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget :=
  dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_rowChunks
    (positiveSaddleFixedRowChunks_cover cert.soloSaddleRowLenPos)
    (positiveSaddleFixedRowChunks_cover cert.soloBudgetRowLenPos)
    (by
      intro rowChunk hrowChunk
      exact checkPositiveSoloDisplayedYSaddleClearedRange_of_fixedNIndexRowRangeChunks
        cert.soloSaddleRowLenPos cert.soloSaddleNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.soloYSaddleClearedRowRangeNIndexChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex))
    (by
      intro rowChunk hrowChunk
      exact checkPositiveSoloDisplayedYBoundUnitRange_of_fixedNIndexRowRangeChunks
        cert.soloBudgetRowLenPos cert.soloBudgetNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.soloYBudgetRowRangeNIndexChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex))

theorem positiveSaddleFixedEdgeCombinedProduct_edgeBudget
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen) :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  intro a ha h2000
  exact positiveEdgeBudget_of_fixedKChunksUniformUnitRowRangeChecks
    cert.edgeRowLenPos cert.edgeKLenPos
    (fun rowChunk hrowChunk edgeChunk hedgeChunk =>
      cert.edgeKChunkUnitRowRanges
        (rowChunk := rowChunk) hrowChunk (edgeChunk := edgeChunk) hedgeChunk)
    ha h2000

theorem PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate where
  smallXYTangent :=
    positiveSaddleFixedEdgeCombinedProduct_smallXYTangent cert
  smallTangentEdge :=
    positiveSaddleFixedEdgeCombinedProduct_smallTangentEdge cert
  temperedXY :=
    positiveSaddleFixedEdgeCombinedProduct_temperedXY cert
  soloY :=
    positiveSaddleFixedEdgeCombinedProduct_soloY cert
  edgeBudget :=
    positiveSaddleFixedEdgeCombinedProduct_edgeBudget cert
  entropyTail :=
    (tail.productPointwiseYRawUnitSolo.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        tail.candidateSplitTemperedRawClearedUnitReserve.toRawClearedBoundsCertificate).entropyTail

theorem PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate.toProductNChunkedTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen) :
    PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen where
  productRowLenPos := cert.productRowLenPos
  tangentRowLenPos := cert.tangentRowLenPos
  soloSaddleRowLenPos := cert.soloSaddleRowLenPos
  soloBudgetRowLenPos := cert.soloBudgetRowLenPos
  edgeRowLenPos := cert.edgeRowLenPos
  productNLenPos := cert.productNLenPos
  tangentNLenPos := cert.tangentNLenPos
  tangentKLenPos := cert.tangentKLenPos
  smallXYProductRawClearedTableProductRowRangeNIndexKChunks :=
    cert.smallXYProductRawClearedTableProductRowRangeNIndexKChunks
  temperedXYProductRawClearedTableProductRowRangeNIndexKChunks :=
    cert.temperedXYProductRawClearedTableProductRowRangeNIndexKChunks
  smallTangentExpEdgeRowRangeNChunksKChunks := by
    intro rowChunk hrowChunk kChunk hkChunk
    exact
      checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk_of_fixedNIndexRowRangeKChunks
        cert.tangentRowLenPos cert.tangentNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.smallTangentExpEdgeRowRangeNIndexKChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex
            (kChunk := kChunk) hkChunk)
  soloYSaddleClearedRowRangeChunks := by
    intro rowChunk hrowChunk
    exact
      checkPositiveSoloDisplayedYSaddleClearedRange_of_fixedNIndexRowRangeChunks
        cert.soloSaddleRowLenPos cert.soloSaddleNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.soloYSaddleClearedRowRangeNIndexChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex)
  soloYBudgetRowRangeChunks := by
    intro rowChunk hrowChunk
    exact
      checkPositiveSoloDisplayedYBoundUnitRange_of_fixedNIndexRowRangeChunks
        cert.soloBudgetRowLenPos cert.soloBudgetNLenPos hrowChunk
        (fun {nIndex} hnIndex =>
          cert.soloYBudgetRowRangeNIndexChunks
            (rowChunk := rowChunk) hrowChunk (nIndex := nIndex) hnIndex)
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges

theorem PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate.toChunkedTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen) :
    PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
      productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen :=
  cert.toProductNChunkedTangentAuditCertificate.toChunkedTangentAuditCertificate

theorem PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate.toCellTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen) :
    PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate
      productRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen productNLen :=
  cert.toChunkedTangentAuditCertificate.toCellTangentAuditCertificate

theorem PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks productNLen) :=
  cert.toChunkedTangentAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate tail

theorem PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toChunkedTangentAuditCertificate.toTangentProductBudgetCertificate tail

theorem PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate.toCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toChunkedTangentAuditCertificate.toCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate
    cert.toChunkedTangentAuditCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate
    cert.toProductNChunkedTangentAuditCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate
    cert.toProductTangentSoloNChunkedAuditCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate
    cert.toProductNKChunkedTangentSoloNChunkedAuditCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
      tangentKLen edgeKLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        productNLen productKLen tangentNLen soloSaddleNLen soloBudgetNLen
        tangentKLen edgeKLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    (cert.toTangentProductBudgetCertificate tail)

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) :=
  cert.toIndependentRowChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleFixedFiniteWindowAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  (finite.toAuditCertificate tail).toTangentProductBudgetCertificate

theorem PositiveSaddleFixedFiniteWindowAuditCertificate.toCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  (finite.toAuditCertificate tail).toCertificate

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (finite :
      PositiveSaddleFixedFiniteWindowAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    (finite.toTangentProductBudgetCertificate tail)

theorem PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate.toTangentProductBudgetCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toFiniteWindowAuditCertificate.toTangentProductBudgetCertificate tail

theorem PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate.toCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toFiniteWindowAuditCertificate.toCertificate tail

theorem unorm_tail_of_positiveSaddleFixedFiniteWindowAllChunksAuditCertificate
    {productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
      edgeRowLen nLen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate
        productRowLen tangentRowLen soloSaddleRowLen soloBudgetRowLen
        edgeRowLen nLen)
    (tail : PositiveSaddleLargeTailAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleFixedFiniteWindowAuditCertificate
    cert.toFiniteWindowAuditCertificate tail

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableNChunksAuditCertificate
    {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        nLen) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (positiveProductFixedNChunks nLen) where
  productNChunksCover := by
    intro _a _N _ha _h2000 hrect
    exact positiveProductFixedNChunks_cover cert.nLenPos hrect
  smallXYProductRawClearedTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases positiveSaddleDefaultChunks_cover (a := a) ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveSmallXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.smallXYProductRawClearedTableRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  temperedXYProductRawClearedTableChunks := by
    intro a nChunk kChunk ha h2000 hnChunk hkChunk
    rcases positiveSaddleDefaultChunks_cover (a := a) ha h2000 with
      ⟨rowChunk, hrowChunk, hlo, hhi⟩
    exact
      checkPositiveTemperedXYProductRawClearedTableFixedNChunksKChunk_of_rowRange
        (cert.temperedXYProductRawClearedTableRowRangeKChunks
          (rowChunk := rowChunk) hrowChunk (edgeChunk := kChunk) hkChunk)
        hlo hhi hnChunk
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        nLen) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      (positiveProductFixedNChunks nLen) :=
  cert.toRawProductTableNChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        nLen) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        nLen) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        nLen) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableNChunksAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      positiveProductSingletonNChunks where
  productNChunksCover := by
    intro _a _N _ha _h2000 hrect
    exact positiveProductSingletonNChunks_cover hrect
  smallXYProductRawClearedTableChunks :=
    cert.smallXYProductRawClearedTableChunks
  temperedXYProductRawClearedTableChunks :=
    cert.temperedXYProductRawClearedTableChunks
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableSingletonNChunksAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (fun _ => positiveEdgeUniformScaleMin) where
  smallXYProductRawClearedTableChunks :=
    cert.smallXYProductRawClearedTableChunks
  temperedXYProductRawClearedTableChunks :=
    cert.temperedXYProductRawClearedTableChunks
  smallTangentExpEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    have hrow : checkPositiveSmallTangentExpEdgeRow a = true := by
      exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
        cert.smallTangentExpEdgeChunks
        (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
    exact decide_eq_true
      (positiveSmallTangentExpEdgeGap_of_checkRow hrow hrect hk hsmall)
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := by
    intro _a _ha _h2000
    exact le_rfl
  edgeKChunkUnitChecks := by
    intro a edgeChunk ha h2000 hedgeChunk
    exact checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
      cert.edgeKChunkUnitRowRanges ha h2000 hedgeChunk
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks :=
  cert.toRawProductTableSingletonNChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toProductClearedChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompClearedChunks :=
    cert.smallXplusYProductGcompClearedChunks
  temperedXplusYProductGcompClearedChunks :=
    cert.temperedXplusYProductGcompClearedChunks
  smallTangentExpEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    have hrow : checkPositiveSmallTangentExpEdgeRow a = true := by
      exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
        cert.smallTangentExpEdgeChunks
        (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
    exact decide_eq_true
      (positiveSmallTangentExpEdgeGap_of_checkRow hrow hrect hk hsmall)
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompClearedChunks :=
    cert.smallXplusYProductGcompClearedChunks
  temperedXplusYProductGcompClearedChunks :=
    cert.temperedXplusYProductGcompClearedChunks
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := by
    intro a edgeChunk ha h2000 hedgeChunk
    exact checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
      cert.edgeKChunkUnitRowRanges ha h2000 hedgeChunk
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentEdgeChunksAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (fun _ => positiveEdgeUniformScaleMin) where
  smallXplusYProductGcompClearedChunks :=
    cert.smallXplusYProductGcompClearedChunks
  temperedXplusYProductGcompClearedChunks :=
    cert.temperedXplusYProductGcompClearedChunks
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := by
    intro a ha h2000
    exact le_rfl
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    edgeScale :=
  cert.toDisplayedSoloChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale :=
  cert.toDisplayedSoloClearedChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale :=
  cert.toProductClearedChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale :=
  cert.toTangentChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        (fun _ => positiveEdgeUniformScaleMin) :=
  cert.toTangentEdgeChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

end Prop51
