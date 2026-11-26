/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BabyBear
import WideTrail.Hades.Krylov
import Mathlib.Tactic.IntervalCases

/-!
# Checks for the SP1 `5.2.4` BabyBear certificate

`WideTrail.Poseidon2.BabyBear` instantiates the generic Plonky3 model at the SP1 `5.2.4`
parameters. The checks below test that instance from the outside: they show why the exponent
is `7`, that `28` is the largest per-S-box exponent the margin `6 * 2^dd ≤ p` allows, that the
zero partial-round contribution comes from the round count and not from the field or the
scale, and that the model with the pinned constants computes the reference output of an
outside model. All finite checks are kernel `decide`.

* **Why `D = 7`.** No even power permutes `F` (`even_power_not_injective`: `1` and `-1`
  collide). `gcd(3, p - 1) = 3` and `gcd(5, p - 1) = 5` (`gcd_three`, `gcd_five`), and explicit
  nontrivial cube and fifth roots of unity make `x ↦ x^3` and `x ↦ x^5` non-injective
  (`cube_not_injective`, `fifth_not_injective`). So `7` is the least exponent above `1` that
  permutes `F` (`least_permutation_exponent`), and `gcd(7, p - 1) = 1` (`gcd_seven`); the
  source asserts this gcd condition before choosing round numbers (`p3-poseidon2`
  `0.2.3-succinct` `src/round_numbers.rs:33`). The inverse exponent satisfies
  `7 * 1725656503 ≡ 1 mod (p - 1)` with `1725656503 < p - 1` (`inverseExponent_mod`).
* **The uniformity bound `6` is attained.** For input difference `1`, the output difference
  `1346933384` has six solutions of `(x + 1)^7 - x^7 = 1346933384`, listed in `diffWitnesses`
  and found outside Lean by exact root finding mod `p`; only their membership in the difference
  set and their distinctness are checked here (`sbox_not_uniform_five`). With `sbox_uniform`,
  the differential uniformity of `x ↦ x^7` on `F` is exactly `6`.
* **The trail exponent is the largest the margin allows.** `6 * 2^28 ≤ p < 6 * 2^29`
  (`probability_margin_sharp`), so with `u = 6` the generic bound gives at most `dd = 28` per
  charged S-box.
* **The external branch number is exactly `8`.** `external_isBranchBound` gives at least `8`.
  The difference `branchWitness`, equal to `-1` at coordinates `0`, `4`, `8` and to `4` at
  coordinate `12`, has block sum `e_0`, so the external layer cancels it in the first three
  blocks and sends it to `5 M4 e_0` in the last: four active coordinates in, four out
  (`external_branchWitness`, `external_not_branch_nine`).
* **The window is exactly sixteen over BabyBear.** A Krylov certificate
  (`inactive_sixteen`) shows that no nonzero difference stays inactive through sixteen
  consecutive partial rounds with `diag d + J`, while some does through fifteen
  (`inactive_fifteen_ne_bot`). So the hypothesis of `Plonky3.activity_with_middle` holds over
  this field with `w = 16`, unlike over `ZMod 23` (`Checks/Plonky3.lean`), and it yields
  `32 + 13 / 16 = 32` (`activity_with_window`): the partial rounds add nothing because
  `13 < 16`.
* **An explicit inactive difference.** `witness` is a nonzero difference that stays inactive
  through thirteen consecutive partial rounds (`witness_mem`) and not through fourteen
  (`witness_not_mem_fourteen`). Membership is orthogonality to the first thirteen Krylov
  vectors, which `decide` checks directly.
* **The Montgomery factor.** Dropping the scale `R^{-1}` does not change the inactive space
  (`scale_invisible`, from `Plonky3.inactiveSpace_internal`), although the scaled and unscaled
  layers differ as maps (`scale_visible`). So the partial-round statements do not depend on
  the scale, while the layer's values do.
* **An execution with the pinned constants.** `permutation 0` is checked round by round
  against a trace computed outside Lean by a field-level model of the code's loops, with the
  constants parsed from `sp1-primitives` `5.2.4` `src/lib.rs` and the code's `drain`
  selection emulated (`permutation_zero`). The output also agrees with that of a separate
  bit-exact emulation of the Montgomery code, which reproduces the upstream width-sixteen
  known-answer test of `p3-baby-bear` `0.2.3-succinct` (`src/poseidon2.rs:164-181`, with that
  test's own constants). No SP1 binary was run; the value is a regression check of the model,
  not a statement about the deployed code.

## What is not claimed

`permutation_zero` is a regression value from outside models, which reproduce the test vector of
`p3-baby-bear` `0.2.3-succinct` with that test's own constants; it is not an output of SP1 and is
not compared with SP1's AIR, the gnark circuit or a built binary. The exponent checks
(`least_permutation_exponent`, `gcd_seven`) are facts about the field; they say nothing about
which exponent SP1 uses beyond the citations in `WideTrail.Poseidon2.BabyBear`.
`sbox_not_uniform_five` and `external_not_branch_nine` show that the uniformity `u = 6` and the
branch number `8` used by the bounds cannot be improved, not that the count `32` is attained.
Nothing here strengthens the security claims of `WideTrail.Poseidon2.BabyBear`.

The axiom footprints of the main results are pinned at the end of the file.
-/

set_option autoImplicit false

namespace Poseidon2.BabyBear.Checks

open Plonky3

/-! ### Why `D = 7` -/

/-- **No even power permutes `F`**: `1` and `-1` have the same image, and `1 ≠ -1`. -/
theorem even_power_not_injective (k : ℕ) : ¬ Function.Injective (fun x : F => x ^ (2 * k)) := by
  intro h
  have heq : (1 : F) = -1 := h (by simp [pow_mul])
  have htwo : (2 : F) = 0 := by linear_combination heq
  exact (by decide : (2 : F) ≠ 0) htwo

theorem gcd_three : Nat.gcd 3 (modulus - 1) = 3 := by decide

theorem gcd_five : Nat.gcd 5 (modulus - 1) = 5 := by decide

theorem gcd_seven : Nat.gcd 7 (modulus - 1) = 1 := by decide

/-- A nontrivial cube root of unity, `31^((p - 1) / 3)`; only its two displayed properties are
checked. -/
def cubeRoot : F := 1314723123

theorem cubeRoot_spec : cubeRoot ^ 3 = 1 ∧ cubeRoot ≠ 1 := by decide

/-- **`x ↦ x^3` does not permute `F`.** -/
theorem cube_not_injective : ¬ Function.Injective (fun x : F => x ^ 3) := by
  intro h
  exact cubeRoot_spec.2 (h (show cubeRoot ^ 3 = (1 : F) ^ 3 by rw [cubeRoot_spec.1, one_pow]))

/-- A nontrivial fifth root of unity, `31^((p - 1) / 5)`; only its two displayed properties
are checked. -/
def fifthRoot : F := 645581151

theorem fifthRoot_spec : fifthRoot ^ 5 = 1 ∧ fifthRoot ≠ 1 := by decide

/-- **`x ↦ x^5` does not permute `F`.** -/
theorem fifth_not_injective : ¬ Function.Injective (fun x : F => x ^ 5) := by
  intro h
  exact fifthRoot_spec.2
    (h (show fifthRoot ^ 5 = (1 : F) ^ 5 by rw [fifthRoot_spec.1, one_pow]))

/-- **`7` is the least exponent above `1` whose power map permutes `F`.** This theorem shows
that the exponents `2` to `6` fail; that `7` itself permutes `F` is `BabyBear.sbox`
(see also `gcd_seven`). -/
theorem least_permutation_exponent (d : ℕ) (h1 : 1 < d) (h7 : d < 7) :
    ¬ Function.Injective (fun x : F => x ^ d) := by
  interval_cases d
  · exact even_power_not_injective 1
  · exact cube_not_injective
  · exact even_power_not_injective 2
  · exact fifth_not_injective
  · exact even_power_not_injective 3

theorem inverseExponent_mod :
    7 * inverseExponent % (modulus - 1) = 1 ∧ inverseExponent < modulus - 1 := by
  decide

/-! ### The uniformity bound -/

/-- Six solutions of `(x + 1)^7 - x^7 = 1346933384`, found outside Lean by exact root finding
mod `p`. -/
def diffWitnesses : Finset F :=
  {216551164, 323534659, 937428934, 1075836986, 1689731261, 1796714756}

/-- **`x ↦ x^7` is not differentially `5`-uniform.** For input difference `1`, the output
difference `1346933384` has the six solutions `diffWitnesses`. With `sbox_uniform`, the
differential uniformity is exactly `6`. -/
theorem sbox_not_uniform_five : ¬ IsDiffUniform sbox 5 := by
  intro h
  have hle := h 1 one_ne_zero 1346933384
  have hsub : diffWitnesses ⊆ diffSet sbox 1 1346933384 := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [sbox_toFun]
    simp only [diffWitnesses, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hcard : diffWitnesses.card = 6 := by decide
  have hge := Finset.card_le_card hsub
  rw [hcard] at hge
  unfold diffCount at hle
  omega

/-! ### The trail exponent -/

/-- `28` is the largest `dd` with `6 * 2^dd ≤ p`. -/
theorem probability_margin_sharp :
    6 * 2 ^ 28 ≤ Fintype.card F ∧ Fintype.card F < 6 * 2 ^ 29 := by
  rw [field_card]
  decide

/-! ### The external branch number -/

/-- A nonzero difference of weight four whose image also has weight four. -/
def branchWitness : State := ![-1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 4, 0, 0, 0]

/-- The first three blocks of `branchWitness` cancel against the block sum `e_0`; the last
becomes `5 M4 e_0 = (10, 5, 5, 15)`. -/
theorem external_branchWitness :
    external branchWitness = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 5, 5, 15] := by
  rw [external_eq_mdsLight]
  decide

/-- **The bound `8` of `external_isBranchBound` is attained.** -/
theorem external_not_branch_nine : ¬ isBranchBound id external 9 := by
  intro h
  have hw := h branchWitness (by decide)
  rw [external_branchWitness] at hw
  revert hw
  decide

/-! ### The window over BabyBear -/

/-- Rows `e_0, A e_0, …, A^15 e_0` for `A = diag d + J` over `F`. -/
def krylov : Fin 16 → State :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2013265920, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![16, 15, 16, 18, 22, 30, 46, 78, 142, 270, 526, 1038, 2062, 4110, 8206, 32782],
    ![49345, 49392, 49409, 49449, 49553, 49857, 50849, 54369, 67553, 118497, 318689, 1112289,
      4272353, 16883937, 67272929, 1074249953],
    ![1164599733, 1164747815, 1164797241, 1164896219, 1165094847, 1165496135, 1166325591,
      1168178039, 1173345207, 1195033655, 1327867191, 290416438, 1861413683, 1870263061,
      629670437, 232529642],
    ![1482614021, 950029460, 101610206, 418334679, 1052976737, 313826516, 868913979, 57837064,
      991789987, 1710743254, 1182668060, 1221623770, 848115976, 1919216017, 58211947,
      1118345637],
    ![1265299663, 1154025323, 407216275, 1877334579, 574746075, 1198688277, 1836786218,
      1892302038, 317361176, 1275564030, 1750266283, 908599402, 1710290809, 1522645911,
      1945508331, 687535037],
    ![1687442733, 1345535540, 1005942767, 1661050770, 762946975, 1251129360, 583957484,
      502885389, 548422325, 586822695, 424512268, 468442363, 1797650430, 1864604336,
      782727133, 893946643],
    ![713538219, 1407427383, 60511456, 666297160, 125669880, 1960568314, 629138042, 34302003,
      1808908129, 1306823609, 1992719512, 589582357, 1399868895, 1163613746, 1923872915,
      1899605038],
    ![149242852, 970480752, 1697342202, 214976088, 568412409, 733157578, 1576077424,
      1758381561, 1590978887, 1921020308, 1122887487, 1328876558, 1617144746, 324521978,
      84343461, 1678458996],
    ![931690215, 187390750, 598328481, 76814350, 1750943349, 881101641, 1333005462,
      1023704247, 1535615434, 1774490043, 354515857, 1032008715, 1320175682, 1716689947,
      1621597528, 562861048],
    ![744690872, 782196131, 1791462343, 902062781, 509490726, 599570190, 972395824,
      1687367717, 1866786596, 1879424164, 912991275, 407121016, 498470214, 1832232161,
      1193207999, 896523964],
    ![1893750782, 138796815, 926259449, 951585887, 1419260571, 896660040, 274278237,
      645040759, 739906294, 1331897470, 1743705733, 1515741342, 1511042930, 737444573,
      1723747958, 1090799725],
    ![1672821475, 1572588012, 1273044174, 1213602903, 708280239, 1687490390, 144365176,
      437815432, 1518298542, 144336947, 321057569, 1324900314, 1659991260, 94614784,
      1329893239, 1236018563],
    ![913880543, 1805579663, 765814078, 1060871421, 1872701721, 1060380918, 826145441,
      67456405, 1301676611, 944463505, 1539927378, 2002948354, 1502217483, 1228090083,
      936507008, 1218731278],
    ![1113503436, 720312343, 446360836, 1144952443, 1816750922, 1787965921, 1192195740,
      1218676679, 441533366, 1118745361, 170575105, 429139598, 1199076497, 33441990,
      236983206, 1171707149]]

/-- A left inverse of the matrix with rows `krylov j`. -/
def krylovInv : Fin 16 → Fin 16 → F :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![248363260, 921605170, 781570089, 1544760390, 234298528, 596388224, 300696935, 862602636,
      383108031, 694537766, 1987775630, 1535387400, 1323126678, 1044378824, 1168555975,
      641048520],
    ![1415051227, 666469455, 77305713, 252542039, 1766228576, 1590449494, 1890755837,
      1907206059, 757169024, 1892635640, 1504249718, 1943322162, 1703179929, 902611735,
      142952836, 772329848],
    ![523544546, 118680116, 157233014, 1830766526, 130660934, 1299209130, 1420915, 1243656702,
      1456995084, 72814296, 954203306, 1921336677, 867931478, 924116508, 1848106788, 71834047],
    ![1690749271, 80195706, 1519372538, 556034342, 959264636, 1136538956, 582663953,
      807707655, 1391342931, 1983833972, 1426645862, 1095087831, 1526219385, 1099179610,
      1278961421, 1849416568],
    ![1010294777, 432523231, 1298267865, 572153804, 724447445, 755007439, 1390723292,
      1567114206, 1644554812, 608405290, 254261762, 981453598, 262351835, 27604768,
      1470649845, 1722852835],
    ![1332187122, 1822403961, 1925799353, 686193743, 669880337, 152049222, 663567743,
      944829635, 1540911061, 1210754105, 702033915, 310182898, 1178903776, 302306935,
      1769545370, 1047716200],
    ![1869349148, 1259364466, 112193409, 537398259, 1968497518, 669471647, 839278181,
      763524858, 53731934, 427332855, 802179327, 2004030791, 1763178062, 1224406032,
      532035707, 1045882061],
    ![1721807967, 141692102, 1571420439, 236581317, 221009653, 647359636, 386218476,
      1806602330, 1461620705, 674372383, 787412100, 590008327, 305783090, 1412089476,
      1663929020, 1486852268],
    ![623585440, 1397358361, 2002241225, 1592966060, 1230230363, 1573299086, 223898044,
      1246459684, 1470159875, 766292206, 764069648, 837935285, 1587980756, 1825681928,
      1588331511, 976283563],
    ![28622156, 270477866, 921472821, 1493871727, 1177959323, 94993716, 1367191010, 535457260,
      102688056, 1058252527, 1186678940, 1466978058, 1170289798, 1661335887, 752352740,
      1116585108],
    ![1531931385, 664415852, 1074469282, 1014519182, 1430272223, 739010477, 1473028062,
      885454930, 574167539, 428886621, 1562436863, 1158039598, 345556287, 755272443,
      1736708108, 1755742916],
    ![1191289172, 562701278, 993023227, 262525798, 90356153, 1512222541, 357764102,
      1032193227, 1445678875, 76880572, 968470824, 215589229, 1433950329, 628461501,
      652664963, 688650682],
    ![950492842, 694087995, 1551253048, 1385714040, 1976757633, 705299280, 800136775,
      1560575390, 1166861915, 885970645, 1926636514, 1613166236, 1278447774, 1582580668,
      1227984847, 1312935365],
    ![886701688, 1196790087, 1082022494, 394171357, 765272982, 635521741, 1184474465,
      1787065474, 1920527869, 1184130856, 565379555, 1673804754, 529228333, 1201323192,
      446703403, 1947903600],
    ![1082157368, 1850829881, 1038482851, 1732662863, 747725143, 1986040858, 617777736,
      1168943243, 736609657, 114495792, 713693404, 773070445, 829999858, 1514777861,
      1839910755, 1683359708]]

theorem krylov_zero : ∀ j : Fin 16, (j : ℕ) = 0 → krylov j = Pi.single 0 1 := by decide

theorem krylov_succ : ∀ j k : Fin 16, (k : ℕ) = j + 1 →
    krylov k = fun i => sp1Diag F i * krylov j i + ∑ m, krylov j m := by
  decide

theorem krylovInv_mul : ∀ i k : Fin 16,
    ∑ j, krylovInv i j * krylov j k = if i = k then 1 else 0 := by
  decide

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds over
BabyBear.** -/
theorem inactive_sixteen :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Hades.inactiveSpace_diagPlusOnes_eq_bot one_ne_zero (sp1Diag F) 0 16 krylov krylov_zero
    krylov_succ krylovInv krylovInv_mul

/-- Some nonzero difference stays inactive through fifteen consecutive partial rounds, so the
window `16` cannot be shortened. -/
theorem inactive_fifteen_ne_bot :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) 15 ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ 15 (by simp)

/-- **The window theorem applies over BabyBear and adds nothing.** With the certificate
`inactive_sixteen`, `Plonky3.activity_with_middle` gives `32 + 13 / 16`, which is `32`, for
every round-constant table. -/
theorem activity_with_window (v : ℕ → Fin 16 → F) {x y : State} (hxy : x ≠ y) :
    32 + 13 / 16 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 13 sbox v)
      (Hades.differenceTrace (Plonky3.rounds conditions 13 sbox v) (external x) (external y))
      0 (8 + 13) :=
  activity_with_middle conditions m4Primes_ne_zero 13 sbox v inactive_sixteen hxy

theorem window_term_eq_zero : 13 / 16 = 0 := partial_window_term_eq_zero inactive_sixteen

/-! ### An explicit inactive difference -/

/-- A nonzero difference orthogonal to `e_0, A e_0, …, A^12 e_0`: zero at coordinate `0`,
and its last three coordinates are `0, 0, 1`. -/
def witness : State :=
  ![0, 29083821, 1854367537, 328832088, 968876904, 1645652314, 418901802, 2005456611,
    1192416822, 191335366, 1821413053, 1355540817, 267718390, 0, 0, 1]

theorem witness_ne_zero : witness ≠ 0 := by decide

theorem witness_orthogonal :
    ∀ j : Fin 13, krylov (Fin.castLE (by norm_num) j) ⬝ᵥ witness = 0 := by
  decide

theorem krylov_eq_pow (j : Fin 16) :
    krylov j = (diagPlusOnes (1 : F) (sp1Diag F) ^ (j : ℕ)) (Pi.single 0 1) :=
  Hades.eq_pow_apply_of_recurrence _ _ krylov krylov_zero
    (fun j k hjk => by
      rw [krylov_succ j k hjk]
      funext i
      rw [diagPlusOnes_apply, one_mul]) j

/-- **The scale is invisible to inactive differences**, for every mask and window. -/
theorem scale_invisible (mask : Finset (Fin 16)) (r : ℕ) :
    Hades.inactiveSpace internal.toLinearMap mask r =
      Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) mask r :=
  inactiveSpace_internal _ _ _ _ mask r

/-- **The scaled and unscaled internal layers differ as maps.** -/
theorem scale_visible :
    internal (Pi.single 0 1) ≠ diagPlusOnes (1 : F) (sp1Diag F) (Pi.single 0 1) := by
  decide

/-- **`witness` stays inactive through thirteen consecutive partial rounds.** -/
theorem witness_mem :
    witness ∈ Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 13 := by
  rw [scale_invisible]
  exact (Hades.mem_inactiveSpace_singleton_iff _ (diagPlusOnes_dotProduct 1 (sp1Diag F)) 0 13
    (fun j => krylov (Fin.castLE (by norm_num) j)) (fun j => krylov_eq_pow _) witness).mpr
    witness_orthogonal

/-- `witness` does not stay inactive through fourteen consecutive partial rounds: with the
unscaled layer `diag d + J`, coordinate `0` of the fourteenth S-box input is
`krylov 13 ⬝ᵥ witness ≠ 0`, and the scale does not change which coordinates vanish
(`scale_invisible`). So thirteen is exactly how far it travels unseen. -/
theorem witness_not_mem_fourteen :
    witness ∉ Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 14 := by
  rw [scale_invisible]
  intro h
  have h13 := (Hades.mem_inactiveSpace_singleton_iff _ (diagPlusOnes_dotProduct 1 (sp1Diag F)) 0
    14 (fun j => krylov (Fin.castLE (by norm_num) j)) (fun j => krylov_eq_pow _) witness).mp h 13
  exact (by decide : krylov 13 ⬝ᵥ witness ≠ 0) h13

/-! ### An execution with the pinned constants -/

/-- The states entering each of the `21` rounds, and the output, for the input `0`. They were
computed outside Lean by a field-level model of the code's loops (initial external layer, four
full rounds, thirteen partial rounds with the constant and the S-box on `state[0]` only and
the internal layer scaled by `R^{-1}`, four full rounds), with the constants parsed from the
crate source. -/
def zeroTrace : Fin 22 → State :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1170476166, 74941348, 915274506, 666211844, 826407734, 1137896222, 1714044489,
      163469768, 112105412, 306380490, 1843385155, 364391011, 1730704381, 1821778723,
      1877910637, 110155944],
    ![1989972102, 347977803, 1453004233, 815115183, 169895892, 912554391, 359171004,
      774382431, 894949941, 1846468065, 219824651, 1533743017, 755751837, 1790902339,
      223848388, 1075091911],
    ![7076772, 380037661, 1950774868, 512375691, 1924246812, 1500264233, 97998824, 1935694534,
      606156337, 602479624, 1450446091, 1520939434, 387709635, 1117001985, 1919294798,
      594741329],
    ![811733401, 318713535, 1533409020, 1480378026, 15286386, 574533908, 987637782, 964916309,
      1926008974, 1070358696, 1055115459, 1725814313, 1924069017, 1463883158, 203555048,
      1936105040],
    ![1908069738, 1151255093, 1310115987, 978611105, 1180413555, 1961897995, 1522665180,
      1482604087, 1439989520, 637079966, 674900428, 1305793754, 1302963700, 94666898,
      1740163491, 1621875154],
    ![1515592247, 1388963510, 637466037, 156633073, 333218705, 615180659, 1549134566,
      43648866, 400984617, 284430292, 1328358095, 1587886646, 1636172076, 1676675865,
      31707573, 380062228],
    ![946768780, 820163529, 1628590485, 296749322, 1102473871, 1261404434, 1764267136,
      1545894515, 942208606, 935980191, 132167292, 1684288553, 464319994, 836641453,
      1894235435, 1557443394],
    ![390480413, 1720553455, 1521919930, 604881730, 46908574, 257133618, 1373053122,
      1592883922, 1503532617, 76605924, 143441924, 525732070, 849177490, 1899218387,
      1730305362, 959744671],
    ![1457533933, 528540547, 600310205, 1647931616, 89595306, 1356899205, 808997799,
      1803999863, 1657144844, 132488223, 1071594316, 578981944, 1434443024, 797415310,
      677084639, 727062421],
    ![465911157, 1405785746, 650346390, 1772309909, 1506300410, 1731868375, 780278388,
      1073833824, 56989336, 1043190455, 1351051895, 755013825, 844236771, 1893620528,
      1970206019, 742927074],
    ![1778059235, 1971276116, 384759883, 1194593906, 1133972609, 1846650018, 111588129,
      1746674360, 343340105, 1389066846, 1632792825, 1730664124, 615034426, 1956273910,
      2011652502, 1580817932],
    ![956678015, 1214980501, 1652474670, 654127327, 654859538, 1627027772, 1723485446,
      1328724606, 916294370, 1797091383, 87352134, 130821392, 837907353, 79076925, 1539772657,
      7613200],
    ![1648336111, 967787373, 554345520, 877051785, 402791976, 1728769519, 158791645,
      242196602, 1232399950, 1620369870, 1020029333, 1468857674, 753925882, 1019130358,
      73623459, 1682553701],
    ![1837688502, 182767768, 1941241415, 564810003, 950470430, 568131513, 79065665,
      1234840043, 994516496, 1290084356, 1259076861, 39063249, 1454559259, 611862271,
      1604086720, 717454936],
    ![1053488781, 1689041547, 583945712, 1470669903, 727032227, 30309992, 85412483, 464982746,
      1998385328, 1482750655, 1082838968, 640431227, 87792071, 229869081, 158844997,
      1781232052],
    ![1792773668, 468966912, 398683232, 453550430, 736343887, 718807397, 1678211013,
      1089511404, 1838967917, 183454785, 776083826, 1568829290, 1222912859, 502733516,
      1000917920, 1505680007],
    ![1489050032, 1766718701, 1612781411, 1639456365, 1741839766, 1628656266, 972572798,
      1513459557, 364831655, 104631951, 946893433, 1909942195, 1724234244, 1092572380,
      1786377330, 1127273948],
    ![693182332, 231317100, 1266654334, 1936435794, 513380184, 1898992457, 1673591921,
      971227904, 7934641, 1061414648, 584707797, 1472610116, 1021477861, 1807618065,
      1975110663, 1045546792],
    ![1154882244, 59547768, 1430680418, 1797692677, 1357056366, 223870244, 114077977,
      1141143493, 1070438029, 989201016, 1950462792, 106208515, 960745360, 1892683484,
      652927589, 1106502784],
    ![746281646, 1555670663, 1348460820, 1040874291, 933262868, 1389914572, 1489965065,
      214317356, 1147705120, 376666888, 875508199, 1081324511, 105165400, 1779913882,
      178486529, 952627746],
    ![348670919, 1568590631, 1535107508, 186917780, 587749971, 1827585060, 1218809104,
      691692291, 1480664293, 1491566329, 366224457, 490018300, 732772134, 560796067,
      484676252, 405025962]]

def zeroTraceAt (n : ℕ) : State := if h : n < 22 then zeroTrace ⟨n, h⟩ else 0

theorem zeroTrace_start : zeroTraceAt 0 = external 0 := by decide

set_option maxHeartbeats 4000000 in
-- Kernel evaluation of twenty-one rounds exceeds the default limit.
/-- Each of the `21` rounds is checked once, on literal states. -/
theorem zeroTrace_step : ∀ n : Fin 21,
    (rounds n.val).apply (zeroTraceAt n.val) = zeroTraceAt (n.val + 1) := by
  decide

theorem zero_execute (n : ℕ) (hn : n ≤ 21) :
    Hades.execute rounds (external 0) n = zeroTraceAt n := by
  induction n with
  | zero => exact zeroTrace_start.symm
  | succ n ih =>
    rw [Hades.execute_succ, ih (by omega)]
    exact zeroTrace_step ⟨n, by omega⟩

/-- **The pinned permutation on the zero input.** A regression value computed outside Lean;
see the module docstring for what it is and is not checked against. -/
theorem permutation_zero :
    permutation 0 =
      ![348670919, 1568590631, 1535107508, 186917780, 587749971, 1827585060, 1218809104,
        691692291, 1480664293, 1491566329, 366224457, 490018300, 732772134, 560796067,
        484676252, 405025962] := by
  rw [permutation_eq, zero_execute 21 le_rfl]
  decide

end Poseidon2.BabyBear.Checks

/-- info: 'Poseidon2.BabyBear.prime_2013265921' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.prime_2013265921

/-- info: 'Poseidon2.BabyBear.sbox_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.sbox_uniform

/-- info: 'Poseidon2.BabyBear.conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.conditions

/-- info: 'Poseidon2.BabyBear.external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.external_isBranchBound

/-- info: 'Poseidon2.BabyBear.partialRowsAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.partialRowsAtZero

/-- info: 'Poseidon2.BabyBear.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.permutation_bijective

/-- info: 'Poseidon2.BabyBear.values_eq_roundValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.values_eq_roundValues

/-- info: 'Poseidon2.BabyBear.rounds_apply_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.rounds_apply_prefix

/-- info: 'Poseidon2.BabyBear.rounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.rounds_apply_partial

/-- info: 'Poseidon2.BabyBear.rounds_apply_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.rounds_apply_suffix

/-- info: 'Poseidon2.BabyBear.activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.activity_general

/-- info: 'Poseidon2.BabyBear.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.activity

/-- info: 'Poseidon2.BabyBear.partial_inactive_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.partial_inactive_ne_bot

/-- info: 'Poseidon2.BabyBear.three_le_finrank_partial_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.three_le_finrank_partial_inactive

/-- info: 'Poseidon2.BabyBear.partial_window_term_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.partial_window_term_eq_zero

/-- info: 'Poseidon2.BabyBear.exists_pair_partial_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.exists_pair_partial_free

/-- info: 'Poseidon2.BabyBear.independent_key_probability_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.independent_key_probability_general

/-- info: 'Poseidon2.BabyBear.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.independent_key_probability

/-- info: 'Poseidon2.BabyBear.probability_exponent' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.probability_exponent

/-- info: 'Poseidon2.BabyBear.Checks.least_permutation_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.least_permutation_exponent

/-- info: 'Poseidon2.BabyBear.Checks.sbox_not_uniform_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.sbox_not_uniform_five

/-- info: 'Poseidon2.BabyBear.Checks.inactive_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.inactive_sixteen

/-- info: 'Poseidon2.BabyBear.Checks.external_not_branch_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.external_not_branch_nine

/-- info: 'Poseidon2.BabyBear.Checks.activity_with_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.activity_with_window

/-- info: 'Poseidon2.BabyBear.Checks.witness_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.witness_mem

/-- info: 'Poseidon2.BabyBear.Checks.witness_not_mem_fourteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.witness_not_mem_fourteen

/-- info: 'Poseidon2.BabyBear.Checks.scale_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.scale_visible

/-- info: 'Poseidon2.BabyBear.Checks.permutation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.permutation_zero

/-! ### The sharp exponent -/

namespace Poseidon2.BabyBear.Checks

set_option exponentiation.threshold 1000 in
/-- **`906` is the largest exponent the exact ratio gives.** `2^907 * 6^32 ≤ p^32` fails; with
`sharp_exponent_bound`, `906` is the largest `E` with `2^E * 6^32 ≤ p^32`. -/
theorem sharp_exponent_succ_fails :
    ¬ 2 ^ 907 * 6 ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) := by
  decide

end Poseidon2.BabyBear.Checks

/-- info: 'Poseidon2.BabyBear.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.independent_key_probability_exact

/-- info: 'Poseidon2.BabyBear.sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.sharp_exponent_bound

/-- info: 'Poseidon2.BabyBear.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.independent_key_probability_sharp

/-- info: 'Poseidon2.BabyBear.Checks.sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Checks.sharp_exponent_succ_fails

/-! ### The exact ratio and the sharp exponent for every round-constant table -/

/--
info: 'Poseidon2.BabyBear.independent_key_probability_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.BabyBear.independent_key_probability_exact_general

/--
info: 'Poseidon2.BabyBear.independent_key_probability_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.BabyBear.independent_key_probability_sharp_general

/-! ### The inactive dimensions through the diagonal criterion -/

/-- info: 'Poseidon2.BabyBear.diag_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.diag_injOn

/-- info: 'Poseidon2.BabyBear.inactive_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.inactive_sixteen

/-- info: 'Poseidon2.BabyBear.finrank_inactive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.finrank_inactive_eq

/-- info: 'Poseidon2.BabyBear.finrank_partial_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.finrank_partial_inactive
