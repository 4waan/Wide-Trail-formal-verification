/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.KoalaBear

/-!
# Checks for the SP1 v6.10.0 KoalaBear certificate

`WideTrail.Poseidon2.KoalaBear` instantiates the generic Plonky3 model with the parameters of
SP1's KoalaBear Poseidon2. The checks below test that instantiation against the code and show
which of its ingredients could not be changed. Every finite check is `decide`.

* **The upstream known-answer test.** `p3-koala-bear` `0.4.3-succinct` tests its width-sixteen,
  degree-three permutation on a fixed input, with round constants drawn from
  `Xoroshiro128Plus::seed_from_u64(1)` (`src/poseidon2.rs:154-167`, test at `:174-191`). Those
  constants were regenerated outside Lean by an emulation of the generator, of KoalaBear's
  sampler (`src/koala_bear.rs:73-84`) and of `Poseidon2::new_from_rng_128` (`p3-poseidon2`
  `0.4.3-succinct` `src/lib.rs:142-166`). Each sample is a Montgomery representative, so the
  field element is the sample times `R^{-1}`. With those constants the model
  `Plonky3.permutation conditions 20 sbox` sends the test's input to the test's expected output
  (`upstream_kat`); input and output are copied from the crate source. The states in between
  were computed outside Lean and are checked round by round (`kat_step`). This exercises the
  external layer, the internal layer with its factor `R^{-1}`, the S-box and the schedule end to
  end. It does not exercise the pinned table `RC16`.
* **The pinned permutation, as a regression value.** `permutation 0`, with the pinned constants,
  is checked round by round against a trace computed outside Lean by a model of the code that
  reproduces the upstream test (`zero_permutation`). This value does not come from an SP1 test.
* **S-box exponents.** Squaring is not injective on `F` (`square_not_injective`). Three is the
  least exponent at least two that is coprime to `p - 1 = 2^24 * 127`, the condition that
  `poseidon2_round_numbers_128` asserts (`p3-poseidon2` `src/round_numbers.rs:33`;
  `three_least_coprime`). The inverse exponent `1420470955` is the least positive one
  (`inverseExponent_least`). `x ↦ x^5` is also a permutation of `F`, since `gcd(5, p - 1) = 1`
  (`pow_five_bijective`, inverse exponent `852282573`). `x ↦ x^127` is not, since `127` divides
  `p - 1` (`pow_127_not_injective`, witness the primitive `127`-th root of unity
  `3^(2^24) = 1828256994`).
* **The trail-bound exponent `29` is the largest possible**: `2 * 2^30 > p`
  (`thirty_too_large`).
* **The bounds `u = 2` and `8` are attained.** For input difference `1`, both `0` and `-1`
  solve `(x + 1)^3 - x^3 = 1`, so the cube S-box is not differentially `1`-uniform
  (`sbox_not_uniform_one`) and `2` is the least `u` with `IsDiffUniform sbox u`. The
  difference `branchWitness`, equal to `-1` at coordinates `0`, `4`, `8` and to `4` at
  coordinate `12`, has weight four and an image of weight four (`external_branchWitness`), so
  the branch number of the external layer is exactly `8` (`external_not_branch_nine`), as over
  BabyBear.
* **The window `16` cannot be shortened.** Some nonzero difference stays inactive through
  fifteen consecutive partial rounds, by a dimension count (`inactive_fifteen_ne_bot`) and
  explicitly: `witness15` is orthogonal to `krylov 0, …, krylov 14`, so it stays inactive through
  fifteen consecutive partial rounds with `diag d + J` (`witness15_mem`), and
  `krylov 15 ⬝ᵥ witness15 ≠ 0`, so it does not stay inactive through sixteen
  (`witness15_not_mem_sixteen`).
* **The Montgomery factor.** Dropping `R^{-1}` changes the internal layer
  (`internal_ne_unscaled`) but none of its inactive spaces (`inactiveSpace_internal_eq`).
* **Cross-checks with other sources.** The diagonal, as elements of `F`, is the gnark chip's
  `matInternalDiagM1` (`sp1-recursion-gnark-ffi` `6.10.0`
  `go/sp1/poseidon2/poseidon2_koalabear.go:117-134`; `sp1Diag_eq_gnark`), and
  `1 + ∑ 1/d_i = 1065548291` in `F` (`one_add_sum_inv_eq`).

## What is not claimed

`upstream_kat` validates the model against the test vector of `p3-koala-bear` `0.4.3-succinct`
only, with round constants regenerated outside Lean; it is not a comparison with SP1's AIR, the
gnark circuit or a built binary. `zero_permutation` is a regression value from an outside model,
not an output of SP1. `pow_five_bijective` and the other exponent checks are facts about the
field; they say nothing about which exponent SP1 uses beyond the citations in
`WideTrail.Poseidon2.KoalaBear`. `sbox_not_uniform_one` and `external_not_branch_nine` show that
the uniformity `u = 2` and the branch number `8` used by the bounds cannot be improved, not that
the count `33` is attained. Nothing here strengthens the security claims of
`WideTrail.Poseidon2.KoalaBear`.

The axiom footprints of the main results are pinned at the end of the file.
-/

set_option autoImplicit false

namespace Poseidon2.KoalaBear.Checks

/-! ### The upstream known-answer test -/

/-- The eight external rows of the upstream test, as field elements. -/
def katExternal : Fin 8 → State :=
  ![![149982203, 704414938, 1392344226, 1491294829, 197688581, 899311491, 1056162890, 764723777,
      449808672, 1084903689, 171434081, 1641662408, 655935650, 1228113479, 1508774146, 1421170583],
    ![1274387589, 403072570, 1601967553, 1752628859, 39886939, 2011156828, 27642459, 208322461,
      2080282783, 836237753, 763905965, 1984915582, 565126060, 1782274063, 2038996442, 1721684758],
    ![544756088, 815114208, 2065774539, 1228994480, 491926639, 1319383600, 1898187379, 180331270,
      1723031861, 1400175095, 397994274, 49971757, 306272827, 1831912802, 468535188, 1544568889],
    ![1114243593, 1410646647, 1032561517, 343087019, 1817069394, 1629401981, 1037947417, 1451211528,
      1719077331, 1008116199, 734732114, 1925215432, 1767196516, 317664581, 1162076651, 714677],
    ![782036973, 428695191, 166795905, 251324149, 1103635030, 783239254, 2122012652, 1204190581,
      1366222545, 1944129258, 1481028382, 1490120284, 927634381, 1304512256, 527518981, 871185958],
    ![1388426043, 651902213, 164257100, 579720568, 1072663191, 495166891, 1948505502, 455511753,
      1491155752, 1540891214, 78341207, 592039221, 1411255569, 1510245508, 501808767, 480067908],
    ![1327703114, 1757388607, 84722148, 2116982772, 1456644483, 395103279, 2099510668, 1579956393,
      1124496440, 344620540, 564154863, 505995716, 1783534630, 1452085293, 478537061, 497166395],
    ![590069616, 941298206, 121360795, 1710918950, 58295855, 1966656716, 823903742, 46772869,
      2008800701, 1933724967, 547645206, 2084431637, 404710466, 690580977, 1142837322, 1086691669]]

/-- The twenty internal constants of the upstream test, as field elements. -/
def katInternal : Fin 20 → F :=
  ![720145094, 266900184, 2102775952, 887192108, 1763870627, 480187560, 324128881, 1537830600,
      1924419105, 589108367, 697206274, 1954012515, 314288859, 1339645712, 1276967891, 2115334499,
      1239850264, 250968678, 1057884600, 161806160]

def katValues : ℕ → State := Plonky3.roundValues 20 katExternal katInternal

def katRounds : ℕ → Hades.RoundSpec (Fin 16) F := Plonky3.rounds conditions 20 sbox katValues

/-- The input of `test_poseidon2_width_16_random` (`p3-koala-bear` `0.4.3-succinct`
`src/poseidon2.rs:175-180`). -/
def katInput : State :=
  ![894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
      19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913]

/-- The expected output of `test_poseidon2_width_16_random` (`src/poseidon2.rs:182-187`). -/
def katOutput : State :=
  ![575479740, 1350824762, 2117880331, 1034350182, 1722317281, 988412135, 1272198010, 2022533539,
      1465703323, 648698653, 439658904, 878238659, 1163940027, 287402877, 685135400, 1397893936]

/-- The states entering each of the `28` rounds, and the output, computed outside Lean. -/
def katTrace : Fin 29 → State :=
  ![![97955010, 174759934, 49005876, 488191487, 463799603, 2087452379, 124664211, 2099204620,
      220203651, 1699164238, 407085694, 1560743059, 1616952237, 608715438, 1782451716, 1654197755],
    ![295486330, 1828292467, 447721097, 1654934794, 461214793, 704874663, 1580095818, 1616046084,
      1671354280, 821124945, 1014752047, 258488767, 1833140061, 705254967, 902495620, 7641159],
    ![148444028, 52737873, 339798639, 252862923, 2008446046, 570435990, 1795586528, 1013093549,
      529433570, 725198227, 321297214, 905473354, 1790232215, 1065137895, 1433538012, 820118396],
    ![1218793784, 1894882661, 122290964, 1056728110, 1234533149, 1131020446, 1141385671, 1993349999,
      1618170431, 1282623030, 1700019965, 1252563671, 609496547, 629589971, 1038578055, 2043121858],
    ![1419839026, 1935372061, 1575789103, 832916973, 1156914320, 1987953273, 247826378, 487562603,
      898790367, 735740111, 1800255236, 318165055, 1488057524, 1403532953, 971225564, 997775310],
    ![1137503716, 1745704160, 1666705429, 861579869, 486401957, 1949596006, 1676338522, 1849355009,
      1272378185, 63228537, 588192733, 56980550, 686262628, 788092873, 889467835, 983774651],
    ![760013096, 1308832232, 2035979967, 1364059379, 1775902637, 549538672, 332453402, 187902398,
      1014003341, 270621951, 1657022979, 661591080, 1406700394, 664340098, 789355779, 619579860],
    ![968265851, 954494856, 465970105, 1260745465, 2013157271, 1303494275, 1985789552, 764909564,
      2001378671, 1126359769, 269375253, 1967392392, 1900460857, 202137571, 175340427, 1363149249],
    ![1817908393, 51848401, 246145204, 1519265793, 658967690, 1564844027, 2093492483, 809197232,
      1346792281, 1366945474, 1418596720, 1523287067, 1209102712, 9395990, 729758420, 1650016582],
    ![1389499311, 816102470, 406171287, 598614057, 365575623, 414421431, 1574087818, 1392458050,
      157587230, 501138845, 1281813267, 1132598113, 354542986, 1599699187, 1721128826, 179014582],
    ![822254908, 2106150899, 177063455, 540770696, 1176658988, 1002681534, 1010079318, 431861630,
      1609665901, 1239482516, 1380437272, 893818347, 836636242, 1832191615, 1404593516, 1446865327],
    ![1548957141, 1732839898, 912424432, 264704889, 396667638, 303807970, 1016747509, 1742120105,
      598905897, 1862131553, 408922967, 1384884996, 1733579938, 934911814, 1498620026, 98986785],
    ![2084111610, 1225622939, 1130039434, 1476769498, 860568318, 1221889613, 1342090484, 1322374562,
      1025835364, 1786704078, 176472412, 1380542168, 415293896, 487623001, 936197096, 1323177201],
    ![1973713579, 1449919397, 994993780, 617308693, 1131161294, 1506250606, 1218690901, 1846049321,
      1063313597, 1226130213, 72802233, 1969661334, 93235186, 80513101, 888650982, 64821467],
    ![1212296695, 277570559, 517353511, 1511416621, 144752590, 268826458, 1933474930, 1819857748,
      901659404, 1127852732, 1989410889, 18179579, 328954250, 1766594283, 1374633261, 136030524],
    ![1561386002, 1698174882, 1730394743, 526242161, 1386235140, 1558110948, 1496204986, 510789805,
      1035901150, 282233660, 429258428, 49799213, 1065591594, 1282956162, 964894235, 1123278923],
    ![833371555, 1430041060, 2053771932, 945248769, 2114286520, 1374182577, 642966239, 1785524784,
      1762302635, 1868460778, 1124513608, 1760603229, 1247934697, 377172612, 659791917, 1622084759],
    ![265886342, 424252411, 527528389, 1122326946, 1565068541, 513429635, 1613422252, 1739302626,
      856511237, 114536084, 788846417, 1410902355, 769316310, 1540209123, 2065689286, 1913613331],
    ![642505270, 1549228929, 1111444745, 1555086862, 1033236577, 439287004, 1673481484, 1893591421,
      597279814, 1021591685, 572144106, 1962400903, 996619273, 955541463, 674817038, 1268342386],
    ![1996968651, 1464181224, 988490206, 819805994, 204531277, 1417609532, 177672506, 1246642984,
      535808257, 341309070, 1804501605, 381312572, 1761441392, 1654374732, 2003803924, 782685977],
    ![655313263, 601054589, 712873285, 233299832, 1581045454, 1061605128, 2035857240, 2030179500,
      129797407, 395548785, 886147440, 1315170842, 1296621463, 1692967865, 1228511805, 232541346],
    ![2072556490, 2100556304, 517878614, 46444030, 1558927602, 1404748325, 2015129323, 1836760378,
      1589103684, 1145318777, 1016492218, 1178092306, 1782935699, 1223247695, 1946963512,
      2054858079],
    ![633361018, 1943772609, 1173613543, 962730386, 2125617625, 1956511190, 159711762, 1265593088,
      223426599, 420860947, 614763203, 1245924407, 626106048, 1883399253, 1972287576, 300126099],
    ![1672894204, 603895496, 1360897532, 1730215758, 531355001, 695311167, 1171794222, 279323869,
      1771191397, 1927509175, 1500904666, 1999400464, 935960885, 1790660191, 319374268, 446348412],
    ![1576228917, 186603725, 867125963, 382024413, 508083779, 1026356537, 1126901705, 1272423190,
      1542240930, 257675044, 186766817, 671633303, 1509616865, 645179926, 1813999452, 1366425800],
    ![1755830576, 1142154172, 1492141038, 247544323, 181431779, 702745791, 2049859887, 462663715,
      1157736624, 1895670737, 1505337646, 970385546, 327609047, 1496085047, 413295918, 95433404],
    ![947930115, 316583780, 733832181, 1951831893, 1984661835, 1156056620, 1161639228, 845972523,
      253882369, 725915610, 1144209163, 1181052613, 253859466, 1079506254, 145977533, 1648202682],
    ![142504470, 409300308, 11476341, 1183273422, 1626649229, 1081260091, 985613781, 361141427,
      1986617591, 1004203593, 902613233, 2081115087, 619846916, 27932889, 1968842614, 1805069680],
    ![575479740, 1350824762, 2117880331, 1034350182, 1722317281, 988412135, 1272198010, 2022533539,
      1465703323, 648698653, 439658904, 878238659, 1163940027, 287402877, 685135400, 1397893936]]

def katTraceAt (n : ℕ) : State := if h : n < 29 then katTrace ⟨n, h⟩ else 0

theorem kat_start : katTraceAt 0 = external katInput := by
  decide

set_option maxHeartbeats 4000000 in
-- Each of the 28 transitions is checked once, avoiding nested execution reduction.
theorem kat_step : ∀ n : Fin 28,
    (katRounds n.val).apply (katTraceAt n.val) = katTraceAt (n.val + 1) := by
  decide

theorem kat_execute (n : ℕ) (hn : n ≤ 28) :
    Hades.execute katRounds (external katInput) n = katTraceAt n := by
  induction n with
  | zero => exact kat_start.symm
  | succ n ih =>
    rw [Hades.execute_succ, ih (by omega)]
    exact kat_step ⟨n, by omega⟩

/-- **The model reproduces the upstream known-answer test.** -/
theorem upstream_kat : Plonky3.permutation conditions 20 sbox katValues katInput = katOutput := by
  unfold Plonky3.permutation
  rw [show Plonky3.rounds conditions 20 sbox katValues = katRounds from rfl]
  apply Eq.trans (kat_execute 28 (by decide))
  decide

/-! ### The pinned permutation on the zero state -/

/-- The states entering each of the `28` pinned rounds on input `0`, and the output, computed
outside Lean. -/
def zeroTrace : Fin 29 → State :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1324785618, 1891905109, 1701446814, 1862965114, 796201983, 525064913, 1513840750, 966677818,
      104568722, 489512458, 2018716943, 454656035, 280337147, 592658923, 513412517, 39611247],
    ![465536426, 1316861644, 1879621717, 401210509, 1160646176, 1238304940, 223966865, 1603370894,
      2123731777, 535614526, 401015953, 1690131985, 1236771091, 1087351242, 1407425535, 159665727],
    ![1826804975, 2069734353, 33496623, 1619158488, 2050503270, 1128385159, 2079700398, 1650061639,
      1653887699, 1681690125, 1127664856, 1627410432, 1283774971, 290717108, 2119063259,
      1697509343],
    ![1742075293, 439040306, 223186417, 1179961564, 476566282, 157856937, 1146817583, 742333699,
      1766384976, 25022019, 1190910647, 774082574, 1102611097, 581599601, 585905847, 724461705],
    ![1319776657, 1831441045, 362942751, 1322435937, 2038888038, 13887991, 1571660435, 736045792,
      1096688337, 1418309817, 403702512, 1281435877, 833402570, 1066374447, 1343123250, 2030378508],
    ![2127316876, 964462378, 1171675621, 455665462, 2079294721, 1005393353, 1867166224, 2116130213,
      1656063019, 901806959, 1781284082, 943849895, 1201256127, 2103379403, 334100259, 857434468],
    ![1758037011, 1431436526, 1546393291, 1688181037, 332803107, 1603462932, 317389131, 591557860,
      438729602, 657426464, 1523076276, 61963640, 547323952, 258920577, 1736014553, 755535753],
    ![1574124586, 777316581, 685561538, 750903659, 1947768373, 861702966, 1892179931, 1732023841,
      1177481901, 942017958, 134118268, 1820695374, 1370871780, 1495504486, 943484270, 740307043],
    ![1490946456, 637203694, 84604771, 1072519464, 1257799769, 616792958, 855974609, 1737389562,
      602727089, 1546735446, 1888718720, 1676797794, 409028133, 1385713770, 684255551, 1662098440],
    ![309841785, 1209630593, 1774722447, 46662168, 1111540132, 1007885133, 305231443, 546823515,
      390120493, 965518261, 1050320612, 1845221915, 1291099374, 268745420, 1133263868, 1791964300],
    ![809076599, 1370773592, 2099343686, 1087576689, 1562836504, 770725353, 596035637, 65161879,
      1709659515, 808634375, 1536055518, 2117284541, 606679152, 1349340249, 851429002, 695171584],
    ![1466936556, 70434656, 365430993, 1954827965, 74479303, 558861645, 1342672111, 2077390587,
      520192868, 1060240363, 1244072871, 1909099041, 871037909, 1842690507, 1542680268, 2040548332],
    ![724476786, 895692692, 18736069, 81121351, 967968031, 1954605812, 1988132669, 226368258,
      657999174, 1313628975, 1079692647, 1378763984, 998303948, 1033742354, 815366531, 1413713749],
    ![1933428531, 1591172476, 2100161049, 742607049, 1623002565, 4213036, 203927100, 1406908570,
      1967809357, 500850195, 1755825765, 1726940831, 1076079186, 1448707856, 735549577, 1605510840],
    ![167703160, 240681119, 1692912060, 288871313, 1680017757, 430641970, 2020829705, 1072247547,
      1752544929, 244624560, 1400012955, 496514583, 1818059921, 793333349, 39050906, 1900995545],
    ![56336580, 1214124888, 1043792127, 452342611, 1515843073, 37688011, 1205127143, 40954005,
      36318827, 354111461, 1816224260, 785491449, 1765138194, 352238699, 560934577, 643358798],
    ![556208484, 310548386, 626307134, 115127650, 1954831018, 2011995664, 1956601297, 1943038657,
      404406193, 1417978037, 556925979, 1057745370, 189003540, 1813623611, 1863060873, 711851367],
    ![248939187, 2089125241, 1938048981, 100423363, 1559561955, 405547034, 2094030187, 1027150175,
      284148310, 356947259, 628243498, 1064190742, 1196799916, 169062691, 381386163, 1471633257],
    ![246503870, 837147180, 608163870, 1516133176, 1818141713, 1525979414, 1864846448, 1696542698,
      817521430, 1227820851, 2044421634, 275118264, 369239805, 1323635252, 885498010, 386185150],
    ![1771366768, 1442438690, 1121160432, 1612425308, 268388925, 2096719429, 318703609, 561034289,
      1448300929, 1832278874, 702525525, 959797375, 2080647670, 1548643724, 192503606, 1459310560],
    ![1666416050, 1651081149, 1803587354, 648516314, 1784235598, 256039219, 1585305185, 1349786596,
      1237564827, 66528182, 1056801005, 873650640, 241692799, 728298356, 153550110, 1251905645],
    ![1960314312, 1265517985, 370019844, 439817367, 971066621, 160497659, 597029063, 220014220,
      1777734706, 535356601, 503165271, 1964729360, 2063672427, 1400321526, 730947812, 1991292879],
    ![1819690673, 1896402300, 234459166, 1160394027, 1275418748, 60068398, 2110206900, 74840620,
      709459924, 860490335, 706579952, 1886975003, 592117046, 1838626462, 301032440, 2033968351],
    ![637878836, 15377940, 1256220423, 384713348, 1454165211, 1777777592, 1514647371, 1742748945,
      1682362116, 1371987735, 1496264761, 92119090, 1256527567, 1027638462, 1617888579, 2101145635],
    ![796549327, 188312064, 935465122, 1872803661, 1202695918, 1107418440, 1435627383, 1456181485,
      1366429232, 541389086, 1422633997, 499557077, 321690297, 1816383066, 350070178, 1497112587],
    ![2036907454, 142367370, 162141797, 132187945, 1421519497, 1710535398, 1081828811, 121595493,
      964065033, 554300055, 577694481, 1135614517, 880935776, 366614472, 1464584320, 103712262],
    ![123788918, 1191756893, 1448047952, 586970863, 2035225862, 950595252, 1196697344, 896850889,
      793934677, 52284365, 653497878, 2115456185, 2075086904, 221346241, 1505280760, 493522439],
    ![145589356, 1876041682, 1734203622, 499355069, 673349476, 595701365, 270340205, 131707822,
      1236787881, 1085405948, 2065733208, 1999012278, 2062318124, 1616707536, 324813015, 749520722]]

def zeroTraceAt (n : ℕ) : State := if h : n < 29 then zeroTrace ⟨n, h⟩ else 0

theorem zero_start : zeroTraceAt 0 = external 0 := by
  decide

set_option maxHeartbeats 4000000 in
-- Each of the 28 transitions is checked once, avoiding nested execution reduction.
theorem zero_step : ∀ n : Fin 28,
    (rounds n.val).apply (zeroTraceAt n.val) = zeroTraceAt (n.val + 1) := by
  decide

theorem zero_execute (n : ℕ) (hn : n ≤ 28) :
    Hades.execute rounds (external 0) n = zeroTraceAt n := by
  induction n with
  | zero => exact zero_start.symm
  | succ n ih =>
    rw [Hades.execute_succ, ih (by omega)]
    exact zero_step ⟨n, by omega⟩

/-- **The pinned permutation on the zero state** (a regression value; see the module
docstring). -/
theorem zero_permutation :
    permutation 0 =
      ![145589356, 1876041682, 1734203622, 499355069, 673349476, 595701365, 270340205,
        131707822, 1236787881, 1085405948, 2065733208, 1999012278, 2062318124, 1616707536,
        324813015, 749520722] := by
  rw [permutation_eq, zero_execute 28 le_rfl]
  decide

/-! ### S-box exponents -/

/-- An even power is rejected as a permutation S-box over this field. -/
theorem square_not_injective : ¬ Function.Injective (fun x : F => x ^ 2) := by
  intro h
  have heq : (1 : F) = -1 := h (by ring)
  have htwo : (2 : F) = 0 := by linear_combination heq
  exact (by decide : (2 : F) ≠ 0) htwo

/-- `p - 1 = 2^24 * 127`, so `2` divides it and `3` is the least exponent at least two that is
coprime to it. -/
theorem three_least_coprime :
    modulus - 1 = 2 ^ 24 * 127 ∧ Nat.gcd 2 (modulus - 1) = 2 ∧ Nat.gcd 3 (modulus - 1) = 1 := by
  decide

/-- The inverse exponent is the least positive solution of `3 e ≡ 1 (mod p - 1)`. -/
theorem inverseExponent_least :
    inverseExponent < modulus - 1 ∧ 3 * inverseExponent % (modulus - 1) = 1 := by
  decide

theorem pow_five_equation : 5 * 852282573 = (modulus - 1) * 2 + 1 := by
  decide

/-- **`x ↦ x^5` is also a permutation of `F`**, with inverse `x ↦ x^852282573`. -/
theorem pow_five_bijective : Function.Bijective (fun x : F => x ^ 5) :=
  (Sbox.powerEquivOfFermat modulus 5 852282573 2 (by decide) (by decide) pow_five_equation
    fermat).bijective

/-- `3^(2^24)`, a primitive `127`-th root of unity in `F`. -/
def zeta127 : F := 1828256994

set_option maxRecDepth 8000 in
-- The power is unfolded one multiplication at a time.
theorem zeta127_pow : zeta127 ^ 127 = 1 ∧ zeta127 ≠ 1 := by
  decide

/-- **`x ↦ x^127` is not a permutation of `F`**: `127` divides `p - 1`. -/
theorem pow_127_not_injective : ¬ Function.Injective (fun x : F => x ^ 127) := by
  intro h
  have h1 : zeta127 = 1 := h (by simp only [zeta127_pow.1, one_pow])
  exact zeta127_pow.2 h1

/-- **`29` is the largest exponent for `u = 2`.** -/
theorem thirty_too_large : ¬ 2 * 2 ^ 30 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-! ### The bounds `u = 2` and `8` are attained -/

/-- **The cube S-box is not differentially `1`-uniform.** For input difference `1`, the output
difference `1` has the two solutions `0` and `-1` of `(x + 1)^3 - x^3 = 1`. With `sbox_uniform`,
the differential uniformity is exactly `2`. -/
theorem sbox_not_uniform_one : ¬ IsDiffUniform sbox 1 := by
  intro h
  have hle := h 1 one_ne_zero 1
  have hsub : ({0, -1} : Finset F) ⊆ diffSet sbox 1 1 := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [sbox_toFun]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · decide
    · rw [Finset.mem_singleton.mp hx]
      decide
  have hcard : ({0, -1} : Finset F).card = 2 := by decide
  have hge := Finset.card_le_card hsub
  rw [hcard] at hge
  unfold diffCount at hle
  omega

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

/-! ### The window length -/

/-- Some nonzero difference stays inactive through fifteen consecutive partial rounds
(dimension count). -/
theorem inactive_fifteen_ne_bot :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 15 ≠ ⊥ :=
  Plonky3.inactiveSpace_internal_ne_bot montyInverse conditions.scale conditions.two
    conditions.shermanMorrison (by norm_num)

/-- A nonzero difference orthogonal to `krylov 0, …, krylov 14`, computed outside Lean: one
that stays inactive through fifteen consecutive partial rounds. -/
def witness15 : State :=
  ![0, 494989731, 578657468, 1162995235, 635910754, 1147037842, 1932065030, 1983974681, 1379422881,
      47766227, 1129244337, 560391998, 580513651, 1330209349, 1951765846, 1]

theorem witness15_orthogonal : ∀ j : Fin 15, krylov j.castSucc ⬝ᵥ witness15 = 0 := by
  decide

theorem witness15_ne_zero : witness15 ≠ 0 := by
  decide

theorem krylov_eq_pow (j : Fin 16) :
    krylov j = (diagPlusOnes (1 : F) (Plonky3.sp1Diag F) ^ (j : ℕ)) (Pi.single 0 1) :=
  Hades.eq_pow_apply_of_recurrence _ _ krylov krylov_zero
    (fun j k hjk => by
      rw [krylov_succ j k hjk]
      funext i
      rw [diagPlusOnes_apply, one_mul]) j

/-- **An explicit difference that stays inactive through fifteen consecutive partial
rounds.** -/
theorem witness15_mem :
    witness15 ∈ Hades.inactiveSpace (diagPlusOnes (1 : F) (Plonky3.sp1Diag F))
      ({0} : Finset (Fin 16)) 15 :=
  (Hades.mem_inactiveSpace_singleton_iff _ (diagPlusOnes_dotProduct 1 _) 0 15
    (fun j : Fin 15 => krylov j.castSucc) (fun j => krylov_eq_pow j.castSucc) witness15).mpr
    witness15_orthogonal

/-- `witness15` does not stay inactive through sixteen consecutive partial rounds: with
`diag d + J`, coordinate `0` of the sixteenth S-box input is `krylov 15 ⬝ᵥ witness15 ≠ 0`. So
fifteen is exactly how far it travels unseen. -/
theorem witness15_not_mem_sixteen :
    witness15 ∉ Hades.inactiveSpace (diagPlusOnes (1 : F) (Plonky3.sp1Diag F))
      ({0} : Finset (Fin 16)) 16 := by
  intro h
  have h15 := (Hades.mem_inactiveSpace_singleton_iff _ (diagPlusOnes_dotProduct 1 _) 0 16 krylov
    krylov_eq_pow witness15).mp h 15
  exact (by decide : krylov 15 ⬝ᵥ witness15 ≠ 0) h15

/-! ### The Montgomery factor -/

/-- Dropping `R^{-1}` changes the internal layer: on `e_0` the first coordinates differ. -/
theorem internal_ne_unscaled :
    internal (Pi.single 0 1) 0 ≠ diagPlusOnes (1 : F) (Plonky3.sp1Diag F) (Pi.single 0 1) 0 := by
  decide

/-- **The scaling lemma.** The inactive spaces of the internal layer are those of
`diag d + J`, for every mask and window. -/
theorem inactiveSpace_internal_eq (mask : Finset (Fin 16)) (r : ℕ) :
    Hades.inactiveSpace internal.toLinearMap mask r =
      Hades.inactiveSpace (diagPlusOnes (1 : F) (Plonky3.sp1Diag F)) mask r :=
  Plonky3.inactiveSpace_internal montyInverse conditions.scale conditions.two
    conditions.shermanMorrison mask r

/-! ### Cross-checks with other sources -/

/-- The diagonal as the gnark chip writes it (`sp1-recursion-gnark-ffi` `6.10.0`
`go/sp1/poseidon2/poseidon2_koalabear.go:117-134`). -/
theorem sp1Diag_eq_gnark :
    Plonky3.sp1Diag F =
      ![2130706431, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 32768] := by
  decide

/-- Explicit inverses of the diagonal entries. -/
def sp1DiagInv : State :=
  ![1065353216, 1, 1065353217, 1598029825, 1864368129, 1997537281, 2064121857, 2097414145,
    2114060289, 2122383361, 2126544897, 2128625665, 2129666049, 2130186241, 2130446337,
    2130641409]

theorem sp1Diag_mul_inv : ∀ i, Plonky3.sp1Diag F i * sp1DiagInv i = 1 := by
  decide

/-- The Sherman–Morrison quantity `1 + ∑ 1/d_i` is `1065548291` in `F`. -/
theorem one_add_sum_inv_eq : 1 + ∑ i, (Plonky3.sp1Diag F i)⁻¹ = 1065548291 := by
  rw [sum_inv_eq_of_mul_eq_one sp1Diag_mul_inv]
  decide

end Poseidon2.KoalaBear.Checks

/-- info: 'Poseidon2.KoalaBear.prime_2130706433' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.prime_2130706433

/-- info: 'Poseidon2.KoalaBear.sbox_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.sbox_uniform

/-- info: 'Poseidon2.KoalaBear.external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.external_isBranchBound

/-- info: 'Poseidon2.KoalaBear.partial_constants_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.partial_constants_zero

/-- info: 'Poseidon2.KoalaBear.values_eq_roundValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.values_eq_roundValues

/-- info: 'Poseidon2.KoalaBear.rounds_apply_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.rounds_apply_prefix

/-- info: 'Poseidon2.KoalaBear.rounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.rounds_apply_partial

/-- info: 'Poseidon2.KoalaBear.rounds_apply_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.rounds_apply_suffix

/-- info: 'Poseidon2.KoalaBear.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.permutation_bijective

/-- info: 'Poseidon2.KoalaBear.permutation_bijective_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.permutation_bijective_general

/-- info: 'Poseidon2.KoalaBear.inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.inactive_trivial

/-- info: 'Poseidon2.KoalaBear.internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.internal_inactive_trivial

/-- info: 'Poseidon2.KoalaBear.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.activity

/-- info: 'Poseidon2.KoalaBear.activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.activity_general

/-- info: 'Poseidon2.KoalaBear.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability

/-- info: 'Poseidon2.KoalaBear.independent_key_probability_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_general

/-- info: 'Poseidon2.KoalaBear.Checks.upstream_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.upstream_kat

/-- info: 'Poseidon2.KoalaBear.Checks.zero_permutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.zero_permutation

/-- info: 'Poseidon2.KoalaBear.Checks.square_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.square_not_injective

/-- info: 'Poseidon2.KoalaBear.Checks.pow_five_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.pow_five_bijective

/-- info: 'Poseidon2.KoalaBear.Checks.pow_127_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.pow_127_not_injective

/-- info: 'Poseidon2.KoalaBear.Checks.thirty_too_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.thirty_too_large

/-- info: 'Poseidon2.KoalaBear.Checks.inactive_fifteen_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.inactive_fifteen_ne_bot

/-- info: 'Poseidon2.KoalaBear.Checks.witness15_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.witness15_mem

/-- info: 'Poseidon2.KoalaBear.Checks.witness15_not_mem_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.witness15_not_mem_sixteen

/-- info: 'Poseidon2.KoalaBear.Checks.sbox_not_uniform_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.sbox_not_uniform_one

/-- info: 'Poseidon2.KoalaBear.Checks.external_not_branch_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.external_not_branch_nine

/-- info: 'Poseidon2.KoalaBear.Checks.internal_ne_unscaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.internal_ne_unscaled

/-- info: 'Poseidon2.KoalaBear.Checks.inactiveSpace_internal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.inactiveSpace_internal_eq

/-- info: 'Poseidon2.KoalaBear.Checks.sp1Diag_eq_gnark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.sp1Diag_eq_gnark

/-- info: 'Poseidon2.KoalaBear.Checks.one_add_sum_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.one_add_sum_inv_eq

/-- info: 'Poseidon2.KoalaBear.probability_exponent' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.probability_exponent

/-! ### The sharp exponent -/

namespace Poseidon2.KoalaBear.Checks

set_option exponentiation.threshold 1000 in
/-- **`989` is the largest exponent the exact ratio gives.** `2^990 * 2^33 ≤ p^33` fails; with
`sharp_exponent_bound`, `989` is the largest `E` with `2^E * 2^33 ≤ p^33`. -/
theorem sharp_exponent_succ_fails :
    ¬ 2 ^ 990 * 2 ^ (32 + 20 / 16) ≤ modulus ^ (32 + 20 / 16) := by
  decide

end Poseidon2.KoalaBear.Checks

/-- info: 'Poseidon2.KoalaBear.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_exact

/-- info: 'Poseidon2.KoalaBear.sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.sharp_exponent_bound

/-- info: 'Poseidon2.KoalaBear.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_sharp

/-- info: 'Poseidon2.KoalaBear.Checks.sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Checks.sharp_exponent_succ_fails

/-! ### The exact ratio and the sharp exponent for every round-constant table -/

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_exact_general

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_sharp_general
