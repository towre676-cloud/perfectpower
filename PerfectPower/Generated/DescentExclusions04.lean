import PerfectPower.LocalQuarticBridges

namespace PerfectPower.Generated.DescentExclusions04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

theorem cover_0400 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-3)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-3) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0401 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-3)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-3) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0402 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-3)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-3) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0403 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-3)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-3) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0404 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-3)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (-3) (2)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0405 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-3)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (-3) (3)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0406 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-15)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-15)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0407 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-11)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-11)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0408 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-7)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-7)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0409 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0410 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0411 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0412 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0413 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (-2) (2)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0414 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (-2) (3)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0415 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-2)*u^2*v^2+(13)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (-2) (13)
    5 1 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0416 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-1)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-1) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0417 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-1)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-1) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0418 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-1)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-1) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0419 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-1)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (-1) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0420 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(-1)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (-1) (3)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0421 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-16)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-16)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0422 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-12)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-12)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0423 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0424 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0425 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0426 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0427 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (0) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0428 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (0) (2)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0429 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(0)*u^2*v^2+(8)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (0) (8)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0430 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(1)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (1) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0431 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(1)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (1) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0432 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(1)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (1) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0433 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(1)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (1) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0434 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-15)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-15)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0435 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-11)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-11)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0436 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-7)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-7)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0437 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0438 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0439 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0440 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (2) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0441 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (2) (3)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0442 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(2)*u^2*v^2+(13)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (2) (13)
    5 1 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0443 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(3)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (3) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0444 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(3)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (3) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0445 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(3)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (3) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0446 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(3)*u^2*v^2+(-1)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (3) (-1)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0447 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(3)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (3) (2)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0448 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(3)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (3) (3)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0449 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(-16)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (4) (-16)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0450 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(-12)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (4) (-12)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0451 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (4) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0452 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (4) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0453 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (4) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0454 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(-2)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (4) (-2)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0455 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(4)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (4) (2)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0456 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(5)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (5) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0457 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(5)*u^2*v^2+(-3)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (5) (-3)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0458 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(5)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (5) (3)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0459 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(-19)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (6) (-19)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0460 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(-15)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (6) (-15)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0461 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(-11)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (6) (-11)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0462 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(-7)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (6) (-7)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0463 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(-4)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (6) (-4)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0464 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(-1)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (6) (-1)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0465 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(2)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (6) (2)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0466 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(3)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (6) (3)
    2 3 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0467 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(6)*u^2*v^2+(5)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (6) (5)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0468 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(8)*u^2*v^2+(-20)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (8) (-20)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0469 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(8)*u^2*v^2+(-16)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (8) (-16)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0470 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(8)*u^2*v^2+(-12)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (8) (-12)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0471 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(8)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (8) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0472 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(8)*u^2*v^2+(8)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (8) (8)
    5 1 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0473 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(10)*u^2*v^2+(-23)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (10) (-23)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0474 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(10)*u^2*v^2+(-19)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (10) (-19)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0475 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(10)*u^2*v^2+(-15)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (10) (-15)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0476 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(10)*u^2*v^2+(-11)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (10) (-11)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0477 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(12)*u^2*v^2+(-28)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (12) (-28)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0478 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(12)*u^2*v^2+(-24)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (12) (-24)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0479 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(12)*u^2*v^2+(-20)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (12) (-20)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0480 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(12)*u^2*v^2+(-16)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-3) (12) (-16)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0481 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-3)*u^4+(12)*u^2*v^2+(-4)*v^4 := by
  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table (-3) (12) (-4)
    3 2 (by decide) (by decide) (by decide) u v w hcop

theorem cover_0482 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-42)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-42)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0483 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-40)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-40)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0484 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-38)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-38)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0485 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-36)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-36)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0486 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-34)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-34)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0487 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-32)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-32)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0488 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-30)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-30)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0489 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-28)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-28)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0490 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-26)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-26)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0491 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-24)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-24)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0492 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-22)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-22)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0493 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-20)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-20)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0494 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-16)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-16)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0495 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-14)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-14)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0496 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-12)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-12)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0497 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-10)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-10)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0498 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-8)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-8)
    u v w (by decide) (by decide) (by decide) hu

theorem cover_0499 (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :
    w^2 ≠ (-2)*u^4+(-12)*u^2*v^2+(-6)*v^4 := by
  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion (-2) (-12) (-6)
    u v w (by decide) (by decide) (by decide) hu

end PerfectPower.Generated.DescentExclusions04
