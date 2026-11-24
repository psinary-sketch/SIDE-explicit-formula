import SIDEExplicitFormula.Window.ArithFrame

/-!
# L11d: the prime-power side`s checks and sums, the two constants` numerators

Written by relay tools/b768_arith_data.py from the kernel`s own files; edited by no hand.
-/

namespace SIDEExplicitFormula
namespace Window

set_option maxHeartbeats 0 in
/-- Each `n` whose coefficients are not all `0` has its entry in ktTable. -/
theorem ar_kt_cov : allDC arKtCov 2 1022 10 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- Each prime below 1024 a key of the table of L10a. -/
theorem ar_p_find : ∀ p ∈ primeList, (lpTree.find p).isSome = true := by decide +kernel

/-- The upper end`s numerator at 23. -/
theorem ar_e23 : arHi 23 = 3974711124834728131338879231162 := by decide +kernel

/-- The lower end`s numerator at 2. -/
theorem ar_e2 : arLo 2 = 878668439483319573618263538048 := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 2, 128 places. -/
theorem ar_tq_ok_0 : allDC arTqOK 2 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 130, 128 places. -/
theorem ar_tq_ok_1 : allDC arTqOK 130 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 258, 128 places. -/
theorem ar_tq_ok_2 : allDC arTqOK 258 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 386, 128 places. -/
theorem ar_tq_ok_3 : allDC arTqOK 386 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 514, 128 places. -/
theorem ar_tq_ok_4 : allDC arTqOK 514 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 642, 128 places. -/
theorem ar_tq_ok_5 : allDC arTqOK 642 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 770, 128 places. -/
theorem ar_tq_ok_6 : allDC arTqOK 770 128 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- The table`s entries checked from 898, 126 places. -/
theorem ar_tq_ok_7 : allDC arTqOK 898 126 7 = true := by decide +kernel

/-- The table`s entries summed from 2, 128 places. -/
theorem ar_tq_sum_0 : arSum arTq 2 128 = 671993628258544865335240503146528563370660278408821715264307578929026651 := by decide +kernel

/-- The table`s entries summed from 130, 128 places. -/
theorem ar_tq_sum_1 : arSum arTq 130 128 = 238761550658074224896388564574773380820938456302341268189251244492945 := by decide +kernel

/-- The table`s entries summed from 258, 128 places. -/
theorem ar_tq_sum_2 : arSum arTq 258 128 = 26143250511794992938925609673108757738386536107991222234717307554206 := by decide +kernel

/-- The table`s entries summed from 386, 128 places. -/
theorem ar_tq_sum_3 : arSum arTq 386 128 = 678009652678093554226763402791653153373982439921617424568957147780 := by decide +kernel

/-- The table`s entries summed from 514, 128 places. -/
theorem ar_tq_sum_4 : arSum arTq 514 128 = 32298115356060328879298062294806022355613089362586035895525608680 := by decide +kernel

/-- The table`s entries summed from 642, 128 places. -/
theorem ar_tq_sum_5 : arSum arTq 642 128 = -878587802556657811763145636948025732685061115509762485448479426 := by decide +kernel

/-- The table`s entries summed from 770, 128 places. -/
theorem ar_tq_sum_6 : arSum arTq 770 128 = 36703368957617388913077338878526525907928764062804421376606687 := by decide +kernel

/-- The table`s entries summed from 898, 126 places. -/
theorem ar_tq_sum_7 : arSum arTq 898 126 = 1448773484069485831928056247596554198606361490042667656589 := by decide +kernel

end Window
end SIDEExplicitFormula
