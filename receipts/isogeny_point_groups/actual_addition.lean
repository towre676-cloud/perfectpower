import PerfectPower.DescentRankBridge

example (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P Q : (PerfectPower.TwoIsogenyPointMap.E a b).Point) :
    PerfectPower.TwoIsogenyPointMap.phi a b hb hd (P+Q) =
      PerfectPower.TwoIsogenyPointMap.phi a b hb hd P+
        PerfectPower.TwoIsogenyPointMap.phi a b hb hd Q :=
  PerfectPower.TwoIsogenyPointMap.phi_add a b hb hd P Q
