/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Eduardo Gomes
-/

import CompPoly.Fields.KoalaBear
import CompPoly.Fields.BN254
import CompPoly.Data.Vector.Basic

/-!
  # Poseidon2 Reference Implementation (field-generic)

  This is the Lean translation of the reference Python implementation of Poseidon2 in
  `leanEthereum/leanSpec`, generalized to an arbitrary field `F`. The S-box degree, the
  width, the round constants, and the external linear layer are all fields of `Params F`,
  so a single `permute` serves the KoalaBear reference instantiations (`params16` /
  `params24`, `x^3` S-box) as well as other fields: `Poseidon2.BN254.paramsBN254T4`
  instantiates the BN254 scalar field at width 4 with the `x^5` S-box and the TACEO/Noir
  round constants, validated against four Noir/TACEO reference vectors by `native_decide`.

  Per-round constant windows are read by direct indexing at offset `round * width`
  (`Vector.ofFn`, bounds discharged by `omega`), preserving the corrected round-constant
  schedule.

  The original KoalaBear translation was done on Sep 12, 2025.

  ## References

  * [Grassi, L., Khovratovich, D., Rechberger, C., Roy, A., and Schofnegger, M.,
      *Poseidon2: A Faster Version of the Poseidon Hash Function*][Poseidon2]
  * See also the Lean Ethereum spec
    <https://github.com/leanEthereum/leanSpec/blob/main/src/lean_spec/subspecs/poseidon2/>
-/

set_option linter.style.nativeDecide false

open Vector

namespace Poseidon2

/-! First, we give the KoalaBear round constants (the BN254 constants live in
`Poseidon2.BN254` below) -/

/-- The constants for Poseidon2 with 16 rounds
(total of 8 * 16 + 20 = 148 constants) -/
def rawConstants16 : Vector KoalaBear.Field 148 := #v[
    -- External initial (4 rounds × 16 = 64 constants)
    2128964168,
    288780357,
    316938561,
    2126233899,
    426817493,
    1714118888,
    1045008582,
    1738510837,
    889721787,
    8866516,
    681576474,
    419059826,
    1596305521,
    1583176088,
    1584387047,
    1529751136,
    1863858111,
    1072044075,
    517831365,
    1464274176,
    1138001621,
    428001039,
    245709561,
    1641420379,
    1365482496,
    770454828,
    693167409,
    757905735,
    136670447,
    436275702,
    525466355,
    1559174242,
    1030087950,
    869864998,
    322787870,
    267688717,
    948964561,
    740478015,
    679816114,
    113662466,
    2066544572,
    1744924186,
    367094720,
    1380455578,
    1842483872,
    416711434,
    1342291586,
    1692058446,
    1493348999,
    1113949088,
    210900530,
    1071655077,
    610242121,
    1136339326,
    2020858841,
    1019840479,
    678147278,
    1678413261,
    1361743414,
    61132629,
    1209546658,
    64412292,
    1936878279,
    1980661727,
    -- Internal (20 constants)
    2102596038,
    1533193853,
    1436311464,
    2012303432,
    839997195,
    1225781098,
    2011967775,
    575084315,
    1309329169,
    786393545,
    995788880,
    1702925345,
    1444525226,
    908073383,
    1811535085,
    1531002367,
    1635653662,
    1585100155,
    867006515,
    879151050,
    -- External final (4 rounds × 16 = 64 constants)
    1423960925,
    2101391318,
    1915532054,
    275400051,
    1168624859,
    1141248885,
    356546469,
    1165250474,
    1320543726,
    932505663,
    1204226364,
    1452576828,
    1774936729,
    926808140,
    1184948056,
    1186493834,
    843181003,
    185193011,
    452207447,
    510054082,
    1139268644,
    630873441,
    669538875,
    462500858,
    876500520,
    1214043330,
    383937013,
    375087302,
    636912601,
    307200505,
    390279673,
    1999916485,
    1518476730,
    1606686591,
    1410677749,
    1581191572,
    1004269969,
    143426723,
    1747283099,
    1016118214,
    1749423722,
    66331533,
    1177761275,
    1581069649,
    1851371119,
    852520128,
    1499632627,
    1820847538,
    150757557,
    884787840,
    619710451,
    1651711087,
    505263814,
    212076987,
    1482432120,
    1458130652,
    382871348,
    417404007,
    2066495280,
    1996518884,
    902934924,
    582892981,
    1337064375,
    1199354861,
]

/-- The constants for Poseidon2 with width 24
(total of 8 * 24 + 23 = 215 constants) -/
def RAW_CONSTANTS_24 : Vector KoalaBear.Field 215 := #v[
    -- External initial (4 rounds × 24 = 96 constants)
    487143900,
    1829048205,
    1652578477,
    646002781,
    1044144830,
    53279448,
    1519499836,
    22697702,
    1768655004,
    230479744,
    1484895689,
    705130286,
    1429811285,
    1695785093,
    1417332623,
    1115801016,
    1048199020,
    878062617,
    738518649,
    249004596,
    1601837737,
    24601614,
    245692625,
    364803730,
    1857019234,
    1906668230,
    1916890890,
    835590867,
    557228239,
    352829675,
    515301498,
    973918075,
    954515249,
    1142063750,
    1795549558,
    608869266,
    1850421928,
    2028872854,
    1197543771,
    1027240055,
    1976813168,
    963257461,
    652017844,
    2113212249,
    213459679,
    90747280,
    1540619478,
    324138382,
    1377377119,
    294744504,
    512472871,
    668081958,
    907306515,
    518526882,
    1907091534,
    1152942192,
    1572881424,
    720020214,
    729527057,
    1762035789,
    86171731,
    205890068,
    453077400,
    1201344594,
    986483134,
    125174298,
    2050269685,
    1895332113,
    749706654,
    40566555,
    742540942,
    1735551813,
    162985276,
    1943496073,
    1469312688,
    703013107,
    1979485151,
    1278193166,
    548674995,
    2118718736,
    749596440,
    1476142294,
    1293606474,
    918523452,
    890353212,
    1691895663,
    1932240646,
    1180911992,
    86098300,
    1592168978,
    895077289,
    724819849,
    1697986774,
    1608418116,
    1083269213,
    691256798,
    -- Internal (23 constants)
    893435011,
    403879071,
    1363789863,
    1662900517,
    2043370,
    2109755796,
    931751726,
    2091644718,
    606977583,
    185050397,
    946157136,
    1350065230,
    1625860064,
    122045240,
    880989921,
    145137438,
    1059782436,
    1477755661,
    335465138,
    1640704282,
    1757946479,
    1551204074,
    681266718,
    -- External final (4 rounds × 24 = 96 constants)
    328586442,
    1572520009,
    1375479591,
    322991001,
    967600467,
    1172861548,
    1973891356,
    1503625929,
    1881993531,
    40601941,
    1155570620,
    571547775,
    1361622243,
    1495024047,
    1733254248,
    964808915,
    763558040,
    1887228519,
    994888261,
    718330940,
    213359415,
    603124968,
    1038411577,
    2099454809,
    949846777,
    630926956,
    1168723439,
    222917504,
    1527025973,
    1009157017,
    2029957881,
    805977836,
    1347511739,
    540019059,
    589807745,
    440771316,
    1530063406,
    761076336,
    87974206,
    1412686751,
    1230318064,
    514464425,
    1469011754,
    1770970737,
    1510972858,
    965357206,
    209398053,
    778802532,
    40567006,
    1984217577,
    1545851069,
    879801839,
    1611910970,
    1215591048,
    330802499,
    1051639108,
    321036,
    511927202,
    591603098,
    1775897642,
    115598532,
    278200718,
    233743176,
    525096211,
    1335507608,
    830017835,
    1380629279,
    560028578,
    598425701,
    302162385,
    567434115,
    1859222575,
    958294793,
    1582225556,
    1781487858,
    1570246000,
    1067748446,
    526608119,
    1666453343,
    1786918381,
    348203640,
    1860035017,
    1489902626,
    1904576699,
    860033965,
    1954077639,
    1685771567,
    971513929,
    1877873770,
    137113380,
    520695829,
    806829080,
    1408699405,
    1613277964,
    793223662,
    648443918,
]

/-! ## Field-generic parameters -/

/-- The parameters determining a Poseidon2 permutation over a field `F`. -/
structure Params (F : Type) where
  -- First, the parameters
  /-- The S-box exponent (3 for KoalaBear, 5 for BN254-Fr). -/
  sBoxDegree : Nat
  /-- The state width. -/
  width : Nat
  /-- The number of full rounds (split half/half around the partial rounds). -/
  numFullRounds : Nat
  /-- The number of partial rounds. -/
  numPartialRounds : Nat
  /-- The diagonal of the internal linear layer `M_I = J + D`. -/
  internalDiagVectors : Vector F width
  /-- The external linear layer `M_E`. This is a parameter because the dedicated
      width-4 external matrix (e.g. the Noir/TACEO BN254 instantiation) differs from
      the `M4`-block plus cross-chunk-diffusion construction used for widths 16/24. -/
  externalLayer : Vector F width → Vector F width
  /-- All round constants, laid out `[full-first | partial | full-second]`,
      of length `numFullRounds * width + numPartialRounds`. -/
  roundConstants : Vector F (numFullRounds * width + numPartialRounds)

  -- Conditions on the parameters
  /-- The width must be non-zero (i.e. positive) -/
  [width_ne_zero : NeZero width]
  /-- The number of full rounds must be non-zero (i.e. positive) -/
  [numFullRounds_ne_zero : NeZero numFullRounds]
  /-- The number of partial rounds must be non-zero (i.e. positive) -/
  [numPartialRounds_ne_zero : NeZero numPartialRounds]
  /-- The width must be a multiple of 4 -/
  width_dvd_by_4 : 4 ∣ width
  /-- The number of full rounds must be even -/
  numFullRounds_even : Even numFullRounds

namespace Params

variable {F : Type} (params : Params F)

instance : NeZero params.width := params.width_ne_zero
instance : NeZero params.numFullRounds := params.numFullRounds_ne_zero
instance : NeZero params.numPartialRounds := params.numPartialRounds_ne_zero

@[simp]
lemma width_pos : 0 < params.width := Nat.zero_lt_of_ne_zero params.width_ne_zero.out

def widthDiv4 : Nat := params.width / 4

@[simp]
lemma widthDiv4_mul_4_eq_width : params.widthDiv4 * 4 = params.width :=
  Nat.div_mul_cancel params.width_dvd_by_4

def halfNumFullRounds : Nat := params.numFullRounds / 2

@[simp]
lemma numFullRounds_dvd_by_2 : 2 ∣ params.numFullRounds :=
  even_iff_two_dvd.mp params.numFullRounds_even

@[simp]
lemma halfNumFullRounds_mul_2_eq_numFullRounds :
    params.halfNumFullRounds * 2 = params.numFullRounds :=
  Nat.div_mul_cancel params.numFullRounds_dvd_by_2

/-- The first half of full rounds consumes `halfNumFullRounds * width` round constants,
which fit within the constant table. -/
lemma half_full_le : params.halfNumFullRounds * params.width
    ≤ params.numFullRounds * params.width + params.numPartialRounds := by
  have h : params.halfNumFullRounds ≤ params.numFullRounds := by
    have := params.halfNumFullRounds_mul_2_eq_numFullRounds; omega
  have := Nat.mul_le_mul_right params.width h
  omega

end Params

/-! ## M4 matrix and linear layers -/

variable {F : Type} [Field F]

/-- The M4 matrix -/
def m4Matrix : Vector (Vector F 4) 4 :=
  #v[
    #v[2, 3, 1, 1],
    #v[1, 2, 3, 1],
    #v[1, 1, 2, 3],
    #v[3, 1, 1, 2]
  ]

/-- Multiply the m4 block with an input vector of length 4
TODO: define matrix-vector multiplication with `Vector` representation generally -/
def applyM4 (chunk : Vector F 4) : Vector F 4 :=
  Vector.Matrix.mulVec m4Matrix chunk

/-- The dedicated width-4 external matrix (the cheap `t0..t7` evaluation from the
Poseidon2 paper), as used by the Noir/TACEO BN254 instantiation. This is the genuine
width-4 external `M_E`; it is *not* `applyM4` followed by diffusion — `m4Matrix` is the
4×4 building block of the wider block-diagonal construction. -/
def cheapExternalLayer4 (s : Vector F 4) : Vector F 4 :=
  let a := s.get ⟨0, by decide⟩
  let b := s.get ⟨1, by decide⟩
  let cc := s.get ⟨2, by decide⟩
  let d := s.get ⟨3, by decide⟩
  let t0 := a + b
  let t1 := cc + d
  let t2 := b + b + t1
  let t3 := d + d + t0
  let t4 := t1 + t1 + t1 + t1 + t3
  let t5 := t0 + t0 + t0 + t0 + t2
  let t6 := t3 + t5
  let t7 := t2 + t4
  #v[t6, t5, t7, t4]

/--
The generic external linear layer (`M_E`) for `width = 4k`, standalone in `width` so
that it can populate the `externalLayer` field of `Params`.

The matrix `M_E` is applied in two steps:
1.  **Block-Diagonal Matrix Multiplication**: The `width`-element state vector is treated
    as a `width/4 × 4` matrix. Each 4-element row is multiplied by the `m4Matrix`.
    This is equivalent to multiplying the state vector by a block-diagonal matrix where
    each block is `m4Matrix`.

2.  **Diffusion Layer**: A diffusion effect is achieved by adding the sum of all elements
    in each column to every element in that same column. This mixes the state across the
    4-element chunks. If `s'` is the state after the M4 multiplication, the output is
    `s''` where `s''_{i,j} = s'_{i,j} + ∑_k s'_{k,j}`.

This is the construction the reference spec uses for widths 16 and 24. For width 4 use
`cheapExternalLayer4` instead (here the diffusion step would double-count the single
chunk). -/
def m4DiffusionExternalLayer {width : Nat} (hdvd : 4 ∣ width)
    (state : Vector F width) : Vector F width :=
  have hw : width / 4 * 4 = width := Nat.div_mul_cancel hdvd
  -- First step: convert `state` into chunks of length 4, then apply M4 to each chunk
  let chunks := Vector.Matrix.ofFlatten (state.cast hw.symm)
  let chunksAfterM4 := chunks.map (fun chunk => applyM4 chunk)
  -- Diffusion step: add column sums to each row
  -- This is equivalent to multiplication by circ(2*I, I, ..., I)
  let transposedMatrix := Vector.Matrix.transpose chunksAfterM4
  let columnSums := transposedMatrix.map (fun col => col.foldl (· + ·) 0)
  let chunksAfterDiffusion := chunksAfterM4.map (fun row => row.zipWith (· + ·) columnSums)
  (Vector.flatten chunksAfterDiffusion).cast hw

variable (params : Params F)

/--
Applies the internal linear layer (M_I), optimized for partial rounds.

This layer's matrix is `M_I = J + D`, where `J` is the all-ones matrix and `D` is a
diagonal matrix defined by `internalDiagVectors`. This structure allows the matrix-vector
product `M_I * s` to be computed in `O(width)` time instead of `O(width^2)`.

The computation is performed as `M_I * s = J*s + D*s`:
- `J*s` is a vector where each element is the sum of all elements in `s`.
- `D*s` is the element-wise product of the state `s` and the diagonal vector `d`.
-/
def internalLinearLayer (state : Vector F params.width) : Vector F params.width :=
  let sumAll := state.foldl (fun acc x => acc + x) 0
  state.zipWith (fun s d => sumAll + d * s) params.internalDiagVectors

/-- A single full round of the Poseidon2 permutation: add the round-constant chunk,
apply the S-box `x ^ sBoxDegree` to the full state, then the external linear layer. -/
def fullRound (state : Vector F params.width)
    (roundConstants : Vector F params.width) : Vector F params.width :=
  let stateWithConstants := state.zipWith (·+·) roundConstants
  let stateAfterSbox := stateWithConstants.map (fun x => x ^ params.sBoxDegree)
  params.externalLayer stateAfterSbox

/-- A single partial round of the Poseidon2 permutation: add the round constant to
slot 0, apply the S-box to slot 0 only, then the internal linear layer. -/
def partialRound (state : Vector F params.width) (roundConstant : F) :
    Vector F params.width :=
  let stateWithConstant := state.set 0 (state[0] + roundConstant)
  let stateAfterSbox := stateWithConstant.set 0 (stateWithConstant[0] ^ params.sBoxDegree)
  internalLinearLayer params stateAfterSbox

/-! ## Round-constant slicing

The two halves of the full rounds each consume `halfNumFullRounds` width-sized chunks of
`roundConstants`; the partial rounds consume `numPartialRounds` single constants in
between. Chunks are read by direct indexing (`Vector.ofFn`) at offset `r * width`, with
the bounds discharged by `omega`. -/

/-- The `r`-th width-chunk of full-round constants starting at element `base`. -/
def fullRoundChunk (base : Nat)
    (hr : base + params.width ≤ params.numFullRounds * params.width + params.numPartialRounds)
    (state : Vector F params.width) : Vector F params.width :=
  let rc : Vector F params.width :=
    Vector.ofFn (fun j => params.roundConstants.get
      ⟨base + j.val, by have := j.isLt; omega⟩)
  fullRound params state rc

/-- Full Poseidon2 permutation. -/
@[inline]
def permute (state : Vector F params.width) : Vector F params.width :=
  -- Initial external linear layer
  let st0 := params.externalLayer state
  -- First half of full rounds: chunks at base = r * width, for r < halfNumFullRounds
  let st1 : Vector F params.width :=
    Fin.foldl params.halfNumFullRounds (fun st_acc r =>
      fullRoundChunk params (r.val * params.width)
        (by
          have hr := r.isLt
          have hle := params.half_full_le
          have hmul : (r.val + 1) * params.width ≤ params.halfNumFullRounds * params.width := by
            apply Nat.mul_le_mul_right; omega
          have hexp : (r.val + 1) * params.width = r.val * params.width + params.width := by ring
          omega)
        st_acc) st0
  -- Partial rounds: single constants at offset halfNumFullRounds*width + i
  let baseP := params.halfNumFullRounds * params.width
  let st2 := Fin.foldl params.numPartialRounds (fun st_acc i =>
    let rc := params.roundConstants.get
      ⟨baseP + i.val, by
        have hi := i.isLt
        have hHalf := params.halfNumFullRounds_mul_2_eq_numFullRounds
        have : params.halfNumFullRounds * params.width
            ≤ params.numFullRounds * params.width := by
          apply Nat.mul_le_mul_right; omega
        omega⟩
    partialRound params st_acc rc) st1
  -- Second half of full rounds: base = halfFull*width + numPartial + r*width
  let baseS := params.halfNumFullRounds * params.width + params.numPartialRounds
  let st3 := Fin.foldl params.halfNumFullRounds (fun st_acc r =>
    fullRoundChunk params (baseS + r.val * params.width)
      (by
        have hr := r.isLt
        have hHalf := params.halfNumFullRounds_mul_2_eq_numFullRounds
        have hb : (r.val + 1) * params.width ≤ params.halfNumFullRounds * params.width := by
          apply Nat.mul_le_mul_right; omega
        have hexp : (r.val + 1) * params.width = r.val * params.width + params.width := by ring
        have htwo : 2 * params.halfNumFullRounds = params.numFullRounds := by omega
        have hsum : 2 * (params.halfNumFullRounds * params.width)
            = params.numFullRounds * params.width := by
          rw [← htwo]; ring
        omega)
      st_acc) st2
  st3

/-! ## Parameter sets for KoalaBear (widths 16 and 24, `x^3` S-box) -/

/-- Parameters for width = 16, following the Python spec. -/
def params16 : Params KoalaBear.Field where
  sBoxDegree := 3
  width := 16
  numFullRounds := 8
  numPartialRounds := 20
  internalDiagVectors := #v[
       -2,
        1,
        2,
        1 / 2,
        3,
        4,
        -1 / 2,
        -3,
        -4,
        1 / (2 ^ 8),
        1 / 8,
        1 / (2 ^ 24),
        -1 / (2 ^ 8),
        -1 / 8,
        -1 / 16,
        -1 / (2 ^ 24),
    ]
  externalLayer := m4DiffusionExternalLayer (by decide)
  roundConstants := rawConstants16
  width_dvd_by_4 := by decide
  numFullRounds_even := by decide

/-- Parameters for width = 24, following the Python spec. -/
def params24 : Params KoalaBear.Field where
  sBoxDegree := 3
  width := 24
  numFullRounds := 8
  numPartialRounds := 23
  internalDiagVectors := #v[
        -2,
        1,
        2,
        1 / 2,
        3,
        4,
        -1 / 2,
        -3,
        -4,
        1 / (2 ^ 8),
        1 / 4,
        1 / 8,
        1 / 16,
        1 / 32,
        1 / 64,
        1 / (2 ^ 24),
        -1 / (2 ^ 8),
        -1 / 8,
        -1 / 16,
        -1 / 32,
        -1 / 64,
        -1 / (2 ^ 7),
        -1 / (2 ^ 9),
        -1 / (2 ^ 24)
    ]
  externalLayer := m4DiffusionExternalLayer (by decide)
  roundConstants := RAW_CONSTANTS_24
  width_dvd_by_4 := by decide
  numFullRounds_even := by decide

/-! ## Known-answer tests

Permutation vectors from the reference Python implementation's test suite
(`leanEthereum/leanSpec`, `tests/lean_spec/subspecs/poseidon2/test_permutation.py`
at commit `7d16d183`, the last revision carrying the Poseidon2 subspec; the vectors
agree with Plonky3's KoalaBear Poseidon2). They pin the full round-constant
schedule: any drift in the constant table order or the per-round constant windows
perturbs the output. -/

example :
    permute params16 #v[
      894848333, 1437655012, 1200606629, 1690012884,
      71131202, 1749206695, 1717947831, 120589055,
      19776022, 42382981, 1831865506, 724844064,
      171220207, 1299207443, 227047920, 1783754913] = #v[
      190453639, 458899855, 383789123, 1958965770,
      1470307143, 135446903, 1980271247, 26609194,
      337889870, 543343594, 900082402, 1267415354,
      1018710090, 902823573, 1161524658, 1483653556] := by
  native_decide

example :
    permute params24 #v[
      886409618, 1327899896, 1902407911, 591953491,
      648428576, 1844789031, 1198336108, 355597330,
      1799586834, 59617783, 790334801, 1968791836,
      559272107, 31054313, 1042221543, 474748436,
      135686258, 263665994, 1962340735, 1741539604,
      2026927696, 449439011, 1131357108, 50869465] = #v[
      556605495, 885256863, 899046610, 1365261647,
      799824470, 1363091631, 588658632, 173515151,
      783308499, 1346358755, 1865380489, 1166148328,
      1402826941, 434428806, 928050984, 1402941053,
      201160368, 1850628943, 651578331, 12196116,
      759351756, 948448587, 1529251366, 456048743] := by
  native_decide

/-! ## Cached additive sponge (Noir/TACEO construction) -/

/-- Sponge parameters: a permutation on `Vector F width` plus a `rate < width`. -/
structure SpongeParams (F : Type) where
  rate : Nat
  width : Nat
  rate_pos : 0 < rate
  rate_lt_width : rate < width
  permute : Vector F width → Vector F width

/-- A sponge run-state for `sp`. -/
structure SpongeState {F : Type} (sp : SpongeParams F) where
  cache : Vector F sp.rate
  st : Vector F sp.width
  cacheSize : Nat
  squeezeMode : Bool

def zeroVector {F : Type} [Zero F] (n : Nat) : Vector F n := Vector.replicate n 0

namespace SpongeParams

variable (sp : SpongeParams F)

def init [Zero F] (iv : F) : SpongeState sp where
  cache := zeroVector sp.rate
  st := (zeroVector sp.width).set sp.rate iv sp.rate_lt_width
  cacheSize := 0
  squeezeMode := false

def addCacheToState [Add F] (s : SpongeState sp) : Vector F sp.width :=
  Vector.ofFn fun i =>
    if hRate : i.val < sp.rate then
      if i.val < s.cacheSize then s.st.get i + s.cache.get ⟨i.val, hRate⟩
      else s.st.get i
    else s.st.get i

def performDuplex [Add F] (s : SpongeState sp) : SpongeState sp :=
  { s with st := sp.permute (addCacheToState sp s) }

def absorb? [Add F] (s : SpongeState sp) (input : F) : Option (SpongeState sp) :=
  if s.squeezeMode then none
  else if s.cacheSize = sp.rate then
    let s' := performDuplex sp s
    some { s' with cache := s'.cache.set 0 input sp.rate_pos, cacheSize := 1 }
  else if hSpace : s.cacheSize < sp.rate then
    some { s with cache := s.cache.set s.cacheSize input hSpace, cacheSize := s.cacheSize + 1 }
  else none

def squeeze? [Add F] (s : SpongeState sp) : Option (F × SpongeState sp) :=
  if s.squeezeMode then none
  else
    let s' := performDuplex sp s
    have wpos : 0 < sp.width := Nat.lt_trans sp.rate_pos sp.rate_lt_width
    some (s'.st.get ⟨0, wpos⟩, { s' with squeezeMode := true })

def absorbPrefix? [Add F] : SpongeState sp → List F → Nat → Option (SpongeState sp)
  | s, [], _ => some s
  | s, _ :: _, 0 => some s
  | s, x :: xs, n + 1 => do
      let s' ← absorb? sp s x
      absorbPrefix? s' xs n

def hashWithIV? [Zero F] [Add F]
    (input : List F) (inLen : Nat) (isVariableLength : Bool) (iv : F) : Option F := do
  let s ← absorbPrefix? sp (init sp iv) input inLen
  let s ← if isVariableLength then absorb? sp s 1 else some s
  let (out, _) ← squeeze? sp s
  pure out

end SpongeParams

/-! ### Toy-sponge structural checks (permute = id), from lampe `Tests/Poseidon2.lean`.
These pin the cached-additive-sponge plumbing independently of the permutation. -/

namespace SpongeToyTest

-- Over `KoalaBear.Field` (a `Field`; the sponge plumbing is field-generic and the
-- `permute := id` toy outputs match lampe's `Nat` toy vectors).
def testParams : SpongeParams KoalaBear.Field where
  rate := 3
  width := 4
  rate_pos := by decide
  rate_lt_width := by decide
  permute := id

example : testParams.hashWithIV? [1, 2, 3] 3 false 0 = some 1 := by native_decide
example : testParams.hashWithIV? [1, 2, 0] 2 true 0 = some 1 := by native_decide
example : testParams.hashWithIV? [1, 2, 3, 4] 4 false 0 = some 5 := by native_decide

end SpongeToyTest

end Poseidon2

/-! ## BN254-Fr instantiation (width 4, `x^5` S-box, TACEO/Noir constants)

Round constants and reference test vectors are carried from the lampe project
(Reilabs, `Lampe/Crypto/Poseidon2/BN254T4.lean` and `Tests/Poseidon2.lean`), which
validates them against the Noir/TACEO Poseidon2 implementation for BN254. -/

namespace Poseidon2.BN254

open Poseidon2

/-- The BN254 scalar field `Fr` (from `CompPoly.Fields.BN254`). -/
abbrev Fr := _root_.BN254.ScalarField

/-- Cast a `Nat` literal through `NatCast`, avoiding per-literal `OfNat` blowup. -/
def c {F : Type} [NatCast F] (n : Nat) : F := n

/-- Internal-layer diagonal `matDiagM1` (4 entries). -/
def matDiagM1 : Vector Fr 4 := #v[
  c 7626475329478847982857743246276194948757851985510858890691733676098590062311,
  c 5498568565063849786384470689962419967523752476452646391422913716315471115275,
  c 148936322117705719734052984176402258788283488576388928671173547788498414613,
  c 15456385653678559339152734484033356164266089951521103188900320352052358038155]

/-- Round constants in `[external-first(16) | internal(56) | external-second(16)]` order,
matching `permute`'s expected `[full-first | partial | full-second]` layout. -/
def roundConstants88 : Vector Fr 88 := #v[
  -- external-first: 4 rounds × 4
  c 11633431549750490989983886834189948010834808234699737327785600195936805266405,
  c 17353750182810071758476407404624088842693631054828301270920107619055744005334,
  c 11575173631114898451293296430061690731976535592475236587664058405912382527658,
  c 9724643380371653925020965751082872123058642683375812487991079305063678725624,
  c 20936725237749945635418633443468987188819556232926135747685274666391889856770,
  c 6427758822462294912934022562310355233516927282963039741999349770315205779230,
  c 16782979953202249973699352594809882974187694538612412531558950864304931387798,
  c 8979171037234948998646722737761679613767384188475887657669871981433930833742,
  c 5428827536651017352121626533783677797977876323745420084354839999137145767736,
  c 507241738797493565802569310165979445570507129759637903167193063764556368390,
  c 6711578168107599474498163409443059675558516582274824463959700553865920673097,
  c 2197359304646916921018958991647650011119043556688567376178243393652789311643,
  c 4634703622846121403803831560584049007806112989824652272428991253572845447400,
  c 17008376818199175111793852447685303011746023680921106348278379453039148937791,
  c 18430784755956196942937899353653692286521408688385681805132578732731487278753,
  c 4573768376486344895797915946239137669624900197544620153250805961657870918727,
  -- internal: 56
  c 5624865188680173294191042415227598609140934495743721047183803859030618890703,
  c 8228252753786907198149068514193371173033070694924002912950645971088002709521,
  c 17586714789554691446538331362711502394998837215506284064347036653995353304693,
  c 12985198716830497423350597750558817467658937953000235442251074063454897365701,
  c 13480076116139680784838493959937969792577589073830107110893279354229821035984,
  c 480609231761423388761863647137314056373740727639536352979673303078459561332,
  c 19503345496799249258956440299354839375920540225688429628121751361906635419276,
  c 16837818502122887883669221005435922946567532037624537243846974433811447595173,
  c 5492108497278641078569490709794391352213168666744080628008171695469579703581,
  c 11365311159988448419785032079155356000691294261495515880484003277443744617083,
  c 13876891705632851072613751905778242936713392247975808888614530203269491723653,
  c 10660388389107698747692475159023710744797290186015856503629656779989214850043,
  c 18876318870401623474401728758498150977988613254023317877612912724282285739292,
  c 15543349138237018307536452195922365893694804703361435879256942490123776892424,
  c 2839988449157209999638903652853828318645773519300826410959678570041742458201,
  c 7566039810305694135184226097163626060317478635973510706368412858136696413063,
  c 6344830340705033582410486810600848473125256338903726340728639711688240744220,
  c 12475357769019880256619207099578191648078162511547701737481203260317463892731,
  c 13337401254840718303633782478677852514218549070508887338718446132574012311307,
  c 21161869193849404954234950798647336336709035097706159414187214758702055364571,
  c 20671052961616073313397254362345395594858011165315285344464242404604146448678,
  c 2772189387845778213446441819361180378678387127454165972767013098872140927416,
  c 3339032002224218054945450150550795352855387702520990006196627537441898997147,
  c 14919705931281848425960108279746818433850049439186607267862213649460469542157,
  c 17056699976793486403099510941807022658662936611123286147276760381688934087770,
  c 16144580075268719403964467603213740327573316872987042261854346306108421013323,
  c 15582343953927413680541644067712456296539774919658221087452235772880573393376,
  c 17528510080741946423534916423363640132610906812668323263058626230135522155749,
  c 3190600034239022251529646836642735752388641846393941612827022280601486805721,
  c 8463814172152682468446984305780323150741498069701538916468821815030498611418,
  c 16533435971270903741871235576178437313873873358463959658178441562520661055273,
  c 11845696835505436397913764735273748291716405946246049903478361223369666046634,
  c 18391057370973634202531308463652130631065370546571735004701144829951670507215,
  c 262537877325812689820791215463881982531707709719292538608229687240243203710,
  c 2187234489894387585309965540987639130975753519805550941279098789852422770021,
  c 19189656350920455659006418422409390013967064310525314160026356916172976152967,
  c 15839474183930359560478122372067744245080413846070743460407578046890458719219,
  c 1805019124769763805045852541831585930225376844141668951787801647576910524592,
  c 323592203814803486950280155834638828455175703393817797003361354810251742052,
  c 9780393509796825017346015868945480913627956475147371732521398519483580624282,
  c 14009429785059642386335012561867511048847749030947687313594053997432177705759,
  c 13749550162460745037234826077137388777330401847577727796245150843898019635981,
  c 19497187499283431845443758879472819384797584633472792651343926414232528405311,
  c 3708428802547661961864524194762556064568867603968214870300574294082023305587,
  c 1339414413482882567499652761996854155383863472782829777976929310155400981782,
  c 6396261245879814100794661157306877072718690153118140891315137894471052482309,
  c 2069661495404347929962833138824526893650803079024564477269192079629046031674,
  c 15793521554502133342917616035884588152451122589545915605459159078589855944361,
  c 17053424498357819626596285492499512504457128907932827007302385782133229252374,
  c 13658536470391360399708067455536748955260723760813498481671323619545320978896,
  c 21546095668130239633971575351786704948662094117932406102037724221634677838565,
  c 21411726238386979516934941789127061362496195649331822900487557574597304399109,
  c 1944776378988765673004063363506638781964264107780425928778257145151172817981,
  c 15590719714223718537172639598316570285163081746016049278954513732528516468773,
  c 1351266421179051765004709939353170430290500926943038391678843253157009556309,
  c 6772476224477167317130064764757502335545080109882028900432703947986275397548,
  -- external-second: 4 rounds × 4
  c 10670120969725161535937685539136065944959698664551200616467222887025111751992,
  c 4731853626374224678749618809759140702342195350742653173378450474772131006181,
  c 14473527495914528513885847341981310373531349450901830749157165104135412062812,
  c 16937191362061486658876740597821783333355021670608822932942683228741190786143,
  c 5656559696428674390125424316117443507583679061659043998559560535270557939546,
  c 8897648276515725841133578021896617755369443750194849587616503841335248902806,
  c 14938684446722672719637788054570691068799510611164812175626676768545923371470,
  c 15284149043690546115252102390417391226617211133644099356880071475803043461465,
  c 2623479025068612775740107497276979457946709347831661908218182874823658838107,
  c 6809791961761836061129379546794905411734858375517368211894790874813684813988,
  c 2417620338751920563196799065781703780495622795713803712576790485412779971775,
  c 4445143310792944321746901285176579692343442786777464604312772017806735512661,
  c 1429019233589939118995503267516676481141938536269008901607126781291273208629,
  c 19874283200702583165110559932895904979843482162236139561356679724680604144459,
  c 13426632171723830006915194799390005513190035492503509233177687891041405113055,
  c 10582332261829184460912611488470654685922576576939233092337240630493625631748]

/-- BN254-Fr width-4 Poseidon2, x^5 S-box. -/
def paramsBN254T4 : Params Fr where
  sBoxDegree := 5
  width := 4
  numFullRounds := 8
  numPartialRounds := 56
  internalDiagVectors := matDiagM1
  externalLayer := Poseidon2.cheapExternalLayer4
  roundConstants := roundConstants88
  width_dvd_by_4 := by decide
  numFullRounds_even := by decide

/-- BN254 sponge params (rate 3, width 4), as the Noir/TACEO construction. -/
def bn254Sponge : Poseidon2.SpongeParams Fr where
  rate := 3
  width := 4
  rate_pos := by decide
  rate_lt_width := by decide
  permute := Poseidon2.permute paramsBN254T4

/-- Noir IV: `inLen * 2^64`. -/
def noirIV (inLen : Nat) : Fr := (inLen : Fr) * (((2 : Nat) ^ 64 : Nat) : Fr)

/-- Noir/TACEO hash with the BN254 IV. -/
def noirHash? (input : List Fr) (inLen : Nat) (isVariableLength : Bool) : Option Fr :=
  bn254Sponge.hashWithIV? input inLen isVariableLength (noirIV inLen)

def vals (state : Vector Fr 4) : List Nat := state.toList.map ZMod.val
def val? : Option Fr → Option Nat := Option.map ZMod.val

/-! ### Reference vectors (from lampe `Tests/Poseidon2.lean`, validated vs Noir/TACEO) -/

-- permutation of [0,1,2,3]
example :
    vals (Poseidon2.permute paramsBN254T4 #v[c 0, c 1, c 2, c 3]) =
      [ 786823568102245344938517132468097745676732687098822989626730198331658606391
      , 16105493617470833344375945651585194737369509580406730765188791202038211593826
      , 2169165722086073256768101917994796590773204847633762971322389403847680713675
      , 20837792685223053096472825292260687493226094382304778455120670180090619921530
      ] := by native_decide

-- permutation of [1,2,3,4]
example :
    vals (Poseidon2.permute paramsBN254T4 #v[c 1, c 2, c 3, c 4]) =
      [ 15505005361706012551741834895355031099510014664842462842053262257331543442865
      , 15540689879131394802373076737172779194862932999849486641952351767738780953784
      , 7917159902307905727813080625122777309809151624119093977983495514817909259553
      , 10305078288915035001787281422329641624507094761680960003698404035062931519465
      ] := by native_decide

-- fixed-length hash of [1,2,3]
example :
    val? (noirHash? [c 1, c 2, c 3] 3 false) =
      some 16068223842875184682212183064520144190817798559788034419026031423767658184152 := by
  native_decide

-- variable-length hash of [1,2]
example :
    val? (noirHash? [c 1, c 2, c 0] 2 true) =
      some 2304388032127604510543726135849368789537863614140798013660173624597943578110 := by
  native_decide

end Poseidon2.BN254
