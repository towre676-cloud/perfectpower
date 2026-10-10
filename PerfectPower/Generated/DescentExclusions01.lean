import PerfectPower.LocalQuarticBridges

namespace PerfectPower.Generated.DescentExclusions01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem cover_0100 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(-8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (-8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0101 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(-8)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (-8) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0102 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(-4)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (-4) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0103 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(0)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (0) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0104 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(4)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (4) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0105 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0106 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(8)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (8) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0107 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(12)*u^2*v^2+(-6)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (12) (-6)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0108 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-14)*u^4+(12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-14) (12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0109 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0110 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-10)*u^2*v^2+(-5)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-10) (-5)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0111 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-10)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-10) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0112 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0113 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0114 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-6)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-13) (-6) (3)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0115 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0116 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (-2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0117 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(-2)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-13) (-2) (3)
    5 1 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0118 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0119 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(2)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-13) (2) (3)
    5 1 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0120 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0121 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0122 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(6)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-13) (6) (3)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0123 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0124 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(10)*u^2*v^2+(-5)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (10) (-5)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0125 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(10)*u^2*v^2+(-1)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-13) (10) (-1)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0126 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-13)*u^4+(12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-13) (12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0127 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0128 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-10)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-10) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0129 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0130 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-6)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-6) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0131 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0132 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-5)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-5) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0133 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0134 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-4)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-4) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0135 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-3)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-3) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0136 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-2)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-2) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0137 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0138 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(-1)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (-1) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0139 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(0)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (0) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0140 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(0)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (0) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0141 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(1)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (1) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0142 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(2)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (2) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0143 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0144 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(3)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (3) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0145 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0146 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(4)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (4) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0147 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(5)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (5) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0148 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(6)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (6) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0149 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0150 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0151 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(10)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (10) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0152 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-11)*u^4+(12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-11) (12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0153 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-12)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-12) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0154 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-12)*u^2*v^2+(-6)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-12) (-6)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0155 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0156 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-12)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-12) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0157 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-8)*u^2*v^2+(-6)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-8) (-6)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0158 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0159 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-8)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-8) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0160 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-8)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-10) (-8) (2)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0161 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0162 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-5)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-5) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0163 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0164 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-4)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-4) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0165 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-4)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-4) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0166 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-4)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-10) (-4) (2)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0167 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-3)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-3) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0168 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0169 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(-1)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (-1) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0170 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(0)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (0) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0171 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(0)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (0) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0172 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(0)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (0) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0173 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(1)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (1) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0174 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0175 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(3)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (3) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0176 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0177 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(4)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (4) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0178 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(4)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (4) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0179 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(4)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-10) (4) (2)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0180 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(5)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (5) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0181 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0182 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(8)*u^2*v^2+(-6)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (8) (-6)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0183 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0184 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(8)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (8) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0185 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(12)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (12) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0186 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(12)*u^2*v^2+(-6)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (12) (-6)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0187 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-10)*u^4+(12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-10) (12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0188 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-12)*u^2*v^2+(-12)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-12) (-12)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0189 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-12)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-12) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0190 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-12)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-12) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0191 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-10)*u^2*v^2+(-7)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-10) (-7)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0192 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-10)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-10) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0193 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-8)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-8) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0194 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-8)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-8) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0195 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-6)*u^2*v^2+(-7)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-6) (-7)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0196 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-6)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-6) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0197 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-6)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-6) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0198 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-5)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-5) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0199 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-7)*u^4+(-4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-7) (-4) (-4)
    u v w (by decide) (by decide) (by decide) hu

end PerfectPower.Generated.DescentExclusions01
