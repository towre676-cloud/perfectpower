import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_linear_perturbation curve_1000 for 1, 0, 0, -1, -4
theorem curve_1000_packet : curve_1000 = {(-4,-16),(-4,16)} := by decide +kernel
native_linear_perturbation curve_1001 for 1, 0, 0, -1, -3
theorem curve_1001_packet : curve_1001 = {(-3,-9),(-3,9)} := by decide +kernel
native_linear_perturbation curve_1002 for 1, 0, 0, -1, -2
theorem curve_1002_packet : curve_1002 = {(-2,-4),(-2,4),(-1,0)} := by decide +kernel
native_linear_perturbation curve_1003 for 1, 0, 0, -1, -1
theorem curve_1003_packet : curve_1003 = {(-1,-1),(-1,1)} := by decide +kernel
native_linear_perturbation curve_1004 for 1, 0, 0, -1, 0
theorem curve_1004_packet : curve_1004 = {(0,0),(1,0)} := by decide +kernel
native_linear_perturbation curve_1005 for 1, 0, 0, -1, 1
theorem curve_1005_packet : curve_1005 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_linear_perturbation curve_1006 for 1, 0, 0, -1, 2
theorem curve_1006_packet : curve_1006 = {(-1,-2),(-1,2),(2,-4),(2,4)} := by decide +kernel
native_linear_perturbation curve_1007 for 1, 0, 0, -1, 3
theorem curve_1007_packet : curve_1007 = {(3,-9),(3,9)} := by decide +kernel
native_linear_perturbation curve_1008 for 1, 0, 0, -1, 4
theorem curve_1008_packet : curve_1008 = {(0,-2),(0,2),(1,-2),(1,2),(4,-16),(4,16)} := by decide +kernel
native_linear_perturbation curve_1009 for 1, 0, 0, -1, 5
theorem curve_1009_packet : curve_1009 = {(5,-25),(5,25)} := by decide +kernel
native_linear_perturbation curve_1010 for 1, 0, 0, -1, 6
theorem curve_1010_packet : curve_1010 = {(6,-36),(6,36)} := by decide +kernel
native_linear_perturbation curve_1011 for 1, 0, 0, -1, 7
theorem curve_1011_packet : curve_1011 = {(-2,-5),(-2,5),(-1,-3),(-1,3),(7,-49),(7,49)} := by decide +kernel
native_linear_perturbation curve_1012 for 1, 0, 0, -1, 8
theorem curve_1012_packet : curve_1012 = {(8,-64),(8,64)} := by decide +kernel
native_linear_perturbation curve_1013 for 1, 0, 0, -1, 9
theorem curve_1013_packet : curve_1013 = {(0,-3),(0,3),(1,-3),(1,3),(9,-81),(9,81)} := by decide +kernel
native_linear_perturbation curve_1014 for 1, 0, 0, -1, 10
theorem curve_1014_packet : curve_1014 = {(10,-100),(10,100)} := by decide +kernel
native_linear_perturbation curve_1015 for 1, 0, 0, -1, 11
theorem curve_1015_packet : curve_1015 = {(2,-5),(2,5),(11,-121),(11,121)} := by decide +kernel
native_linear_perturbation curve_1016 for 1, 0, 0, -1, 12
theorem curve_1016_packet : curve_1016 = {(12,-144),(12,144)} := by decide +kernel
native_linear_perturbation curve_1017 for 1, 0, 0, -1, 13
theorem curve_1017_packet : curve_1017 = {(13,-169),(13,169)} := by decide +kernel
native_linear_perturbation curve_1018 for 1, 0, 0, -1, 14
theorem curve_1018_packet : curve_1018 = {(-1,-4),(-1,4),(14,-196),(14,196)} := by decide +kernel
native_linear_perturbation curve_1019 for 1, 0, 0, -1, 15
theorem curve_1019_packet : curve_1019 = {(15,-225),(15,225)} := by decide +kernel
native_linear_perturbation curve_1020 for 1, 0, 0, -1, 16
theorem curve_1020_packet : curve_1020 = {(-3,-10),(-3,10),(0,-4),(0,4),(1,-4),(1,4),(16,-256),(16,256)} := by decide +kernel
native_linear_perturbation curve_1021 for 1, 0, 0, -1, 17
theorem curve_1021_packet : curve_1021 = {(17,-289),(17,289)} := by decide +kernel
native_linear_perturbation curve_1022 for 1, 0, 0, -1, 18
theorem curve_1022_packet : curve_1022 = {(-2,-6),(-2,6),(18,-324),(18,324)} := by decide +kernel
native_linear_perturbation curve_1023 for 1, 0, 0, -1, 19
theorem curve_1023_packet : curve_1023 = {(19,-361),(19,361)} := by decide +kernel
native_linear_perturbation curve_1024 for 1, 0, 0, -1, 20
theorem curve_1024_packet : curve_1024 = {(20,-400),(20,400)} := by decide +kernel
native_linear_perturbation curve_1025 for 1, 0, 0, 0, -20
theorem curve_1025_packet : curve_1025 = ∅ := by decide +kernel
native_linear_perturbation curve_1026 for 1, 0, 0, 0, -19
theorem curve_1026_packet : curve_1026 = ∅ := by decide +kernel
native_linear_perturbation curve_1027 for 1, 0, 0, 0, -18
theorem curve_1027_packet : curve_1027 = ∅ := by decide +kernel
native_linear_perturbation curve_1028 for 1, 0, 0, 0, -17
theorem curve_1028_packet : curve_1028 = {(-3,-8),(-3,8),(3,-8),(3,8)} := by decide +kernel
native_linear_perturbation curve_1029 for 1, 0, 0, 0, -16
theorem curve_1029_packet : curve_1029 = {(-2,0),(2,0)} := by decide +kernel
native_linear_perturbation curve_1030 for 1, 0, 0, 0, -15
theorem curve_1030_packet : curve_1030 = {(-2,-1),(-2,1),(2,-1),(2,1)} := by decide +kernel
native_linear_perturbation curve_1031 for 1, 0, 0, 0, -14
theorem curve_1031_packet : curve_1031 = ∅ := by decide +kernel
native_linear_perturbation curve_1032 for 1, 0, 0, 0, -13
theorem curve_1032_packet : curve_1032 = ∅ := by decide +kernel
native_linear_perturbation curve_1033 for 1, 0, 0, 0, -12
theorem curve_1033_packet : curve_1033 = {(-2,-2),(-2,2),(2,-2),(2,2)} := by decide +kernel
native_linear_perturbation curve_1034 for 1, 0, 0, 0, -11
theorem curve_1034_packet : curve_1034 = ∅ := by decide +kernel
native_linear_perturbation curve_1035 for 1, 0, 0, 0, -10
theorem curve_1035_packet : curve_1035 = ∅ := by decide +kernel
native_linear_perturbation curve_1036 for 1, 0, 0, 0, -9
theorem curve_1036_packet : curve_1036 = ∅ := by decide +kernel
native_linear_perturbation curve_1037 for 1, 0, 0, 0, -8
theorem curve_1037_packet : curve_1037 = ∅ := by decide +kernel
native_linear_perturbation curve_1038 for 1, 0, 0, 0, -7
theorem curve_1038_packet : curve_1038 = {(-2,-3),(-2,3),(2,-3),(2,3)} := by decide +kernel
native_linear_perturbation curve_1039 for 1, 0, 0, 0, -6
theorem curve_1039_packet : curve_1039 = ∅ := by decide +kernel
native_linear_perturbation curve_1040 for 1, 0, 0, 0, -5
theorem curve_1040_packet : curve_1040 = ∅ := by decide +kernel
native_linear_perturbation curve_1041 for 1, 0, 0, 0, -4
theorem curve_1041_packet : curve_1041 = ∅ := by decide +kernel
native_linear_perturbation curve_1042 for 1, 0, 0, 0, -3
theorem curve_1042_packet : curve_1042 = ∅ := by decide +kernel
native_linear_perturbation curve_1043 for 1, 0, 0, 0, -2
theorem curve_1043_packet : curve_1043 = ∅ := by decide +kernel
native_linear_perturbation curve_1044 for 1, 0, 0, 0, -1
theorem curve_1044_packet : curve_1044 = {(-1,0),(1,0)} := by decide +kernel
native_linear_perturbation curve_1045 for 1, 0, 0, 0, 1
theorem curve_1045_packet : curve_1045 = {(0,-1),(0,1)} := by decide +kernel
native_linear_perturbation curve_1046 for 1, 0, 0, 0, 2
theorem curve_1046_packet : curve_1046 = ∅ := by decide +kernel
native_linear_perturbation curve_1047 for 1, 0, 0, 0, 3
theorem curve_1047_packet : curve_1047 = {(-1,-2),(-1,2),(1,-2),(1,2)} := by decide +kernel
native_linear_perturbation curve_1048 for 1, 0, 0, 0, 4
theorem curve_1048_packet : curve_1048 = {(0,-2),(0,2)} := by decide +kernel
native_linear_perturbation curve_1049 for 1, 0, 0, 0, 5
theorem curve_1049_packet : curve_1049 = ∅ := by decide +kernel
native_linear_perturbation curve_1050 for 1, 0, 0, 0, 6
theorem curve_1050_packet : curve_1050 = ∅ := by decide +kernel
native_linear_perturbation curve_1051 for 1, 0, 0, 0, 7
theorem curve_1051_packet : curve_1051 = ∅ := by decide +kernel
native_linear_perturbation curve_1052 for 1, 0, 0, 0, 8
theorem curve_1052_packet : curve_1052 = {(-1,-3),(-1,3),(1,-3),(1,3)} := by decide +kernel
native_linear_perturbation curve_1053 for 1, 0, 0, 0, 9
theorem curve_1053_packet : curve_1053 = {(-2,-5),(-2,5),(0,-3),(0,3),(2,-5),(2,5)} := by decide +kernel
native_linear_perturbation curve_1054 for 1, 0, 0, 0, 10
theorem curve_1054_packet : curve_1054 = ∅ := by decide +kernel
native_linear_perturbation curve_1055 for 1, 0, 0, 0, 11
theorem curve_1055_packet : curve_1055 = ∅ := by decide +kernel
native_linear_perturbation curve_1056 for 1, 0, 0, 0, 12
theorem curve_1056_packet : curve_1056 = ∅ := by decide +kernel
native_linear_perturbation curve_1057 for 1, 0, 0, 0, 13
theorem curve_1057_packet : curve_1057 = ∅ := by decide +kernel
native_linear_perturbation curve_1058 for 1, 0, 0, 0, 14
theorem curve_1058_packet : curve_1058 = ∅ := by decide +kernel
native_linear_perturbation curve_1059 for 1, 0, 0, 0, 15
theorem curve_1059_packet : curve_1059 = {(-1,-4),(-1,4),(1,-4),(1,4)} := by decide +kernel
native_linear_perturbation curve_1060 for 1, 0, 0, 0, 16
theorem curve_1060_packet : curve_1060 = {(0,-4),(0,4)} := by decide +kernel
native_linear_perturbation curve_1061 for 1, 0, 0, 0, 17
theorem curve_1061_packet : curve_1061 = ∅ := by decide +kernel
native_linear_perturbation curve_1062 for 1, 0, 0, 0, 18
theorem curve_1062_packet : curve_1062 = ∅ := by decide +kernel
native_linear_perturbation curve_1063 for 1, 0, 0, 0, 19
theorem curve_1063_packet : curve_1063 = {(-3,-10),(-3,10),(3,-10),(3,10)} := by decide +kernel
native_linear_perturbation curve_1064 for 1, 0, 0, 0, 20
theorem curve_1064_packet : curve_1064 = {(-2,-6),(-2,6),(2,-6),(2,6)} := by decide +kernel
native_linear_perturbation curve_1065 for 1, 0, 0, 1, -20
theorem curve_1065_packet : curve_1065 = {(3,-8),(3,8),(20,-400),(20,400)} := by decide +kernel
native_linear_perturbation curve_1066 for 1, 0, 0, 1, -19
theorem curve_1066_packet : curve_1066 = {(19,-361),(19,361)} := by decide +kernel
native_linear_perturbation curve_1067 for 1, 0, 0, 1, -18
theorem curve_1067_packet : curve_1067 = {(2,0),(18,-324),(18,324)} := by decide +kernel
native_linear_perturbation curve_1068 for 1, 0, 0, 1, -17
theorem curve_1068_packet : curve_1068 = {(2,-1),(2,1),(17,-289),(17,289)} := by decide +kernel
native_linear_perturbation curve_1069 for 1, 0, 0, 1, -16
theorem curve_1069_packet : curve_1069 = {(16,-256),(16,256)} := by decide +kernel
native_linear_perturbation curve_1070 for 1, 0, 0, 1, -15
theorem curve_1070_packet : curve_1070 = {(15,-225),(15,225)} := by decide +kernel
native_linear_perturbation curve_1071 for 1, 0, 0, 1, -14
theorem curve_1071_packet : curve_1071 = {(-3,-8),(-3,8),(-2,0),(2,-2),(2,2),(14,-196),(14,196)} := by decide +kernel
native_linear_perturbation curve_1072 for 1, 0, 0, 1, -13
theorem curve_1072_packet : curve_1072 = {(-2,-1),(-2,1),(13,-169),(13,169)} := by decide +kernel
native_linear_perturbation curve_1073 for 1, 0, 0, 1, -12
theorem curve_1073_packet : curve_1073 = {(12,-144),(12,144)} := by decide +kernel
native_linear_perturbation curve_1074 for 1, 0, 0, 1, -11
theorem curve_1074_packet : curve_1074 = {(11,-121),(11,121)} := by decide +kernel
native_linear_perturbation curve_1075 for 1, 0, 0, 1, -10
theorem curve_1075_packet : curve_1075 = {(-2,-2),(-2,2),(10,-100),(10,100)} := by decide +kernel
native_linear_perturbation curve_1076 for 1, 0, 0, 1, -9
theorem curve_1076_packet : curve_1076 = {(2,-3),(2,3),(9,-81),(9,81)} := by decide +kernel
native_linear_perturbation curve_1077 for 1, 0, 0, 1, -8
theorem curve_1077_packet : curve_1077 = {(8,-64),(8,64)} := by decide +kernel
native_linear_perturbation curve_1078 for 1, 0, 0, 1, -7
theorem curve_1078_packet : curve_1078 = {(7,-49),(7,49)} := by decide +kernel
native_linear_perturbation curve_1079 for 1, 0, 0, 1, -6
theorem curve_1079_packet : curve_1079 = {(6,-36),(6,36)} := by decide +kernel
native_linear_perturbation curve_1080 for 1, 0, 0, 1, -5
theorem curve_1080_packet : curve_1080 = {(-2,-3),(-2,3),(5,-25),(5,25)} := by decide +kernel
native_linear_perturbation curve_1081 for 1, 0, 0, 1, -4
theorem curve_1081_packet : curve_1081 = {(4,-16),(4,16)} := by decide +kernel
native_linear_perturbation curve_1082 for 1, 0, 0, 1, -3
theorem curve_1082_packet : curve_1082 = {(3,-9),(3,9)} := by decide +kernel
native_linear_perturbation curve_1083 for 1, 0, 0, 1, -2
theorem curve_1083_packet : curve_1083 = {(1,0),(2,-4),(2,4)} := by decide +kernel
native_linear_perturbation curve_1084 for 1, 0, 0, 1, -1
theorem curve_1084_packet : curve_1084 = {(1,-1),(1,1)} := by decide +kernel
native_linear_perturbation curve_1085 for 1, 0, 0, 1, 0
theorem curve_1085_packet : curve_1085 = {(-1,0),(0,0)} := by decide +kernel
native_linear_perturbation curve_1086 for 1, 0, 0, 1, 1
theorem curve_1086_packet : curve_1086 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_linear_perturbation curve_1087 for 1, 0, 0, 1, 2
theorem curve_1087_packet : curve_1087 = {(-2,-4),(-2,4),(1,-2),(1,2)} := by decide +kernel
native_linear_perturbation curve_1088 for 1, 0, 0, 1, 3
theorem curve_1088_packet : curve_1088 = {(-3,-9),(-3,9)} := by decide +kernel
native_linear_perturbation curve_1089 for 1, 0, 0, 1, 4
theorem curve_1089_packet : curve_1089 = {(-4,-16),(-4,16),(-1,-2),(-1,2),(0,-2),(0,2)} := by decide +kernel
native_linear_perturbation curve_1090 for 1, 0, 0, 1, 5
theorem curve_1090_packet : curve_1090 = {(-5,-25),(-5,25)} := by decide +kernel
native_linear_perturbation curve_1091 for 1, 0, 0, 1, 6
theorem curve_1091_packet : curve_1091 = {(-6,-36),(-6,36)} := by decide +kernel
native_linear_perturbation curve_1092 for 1, 0, 0, 1, 7
theorem curve_1092_packet : curve_1092 = {(-7,-49),(-7,49),(1,-3),(1,3),(2,-5),(2,5)} := by decide +kernel
native_linear_perturbation curve_1093 for 1, 0, 0, 1, 8
theorem curve_1093_packet : curve_1093 = {(-8,-64),(-8,64)} := by decide +kernel
native_linear_perturbation curve_1094 for 1, 0, 0, 1, 9
theorem curve_1094_packet : curve_1094 = {(-9,-81),(-9,81),(-1,-3),(-1,3),(0,-3),(0,3)} := by decide +kernel
native_linear_perturbation curve_1095 for 1, 0, 0, 1, 10
theorem curve_1095_packet : curve_1095 = {(-10,-100),(-10,100)} := by decide +kernel
native_linear_perturbation curve_1096 for 1, 0, 0, 1, 11
theorem curve_1096_packet : curve_1096 = {(-11,-121),(-11,121),(-2,-5),(-2,5)} := by decide +kernel
native_linear_perturbation curve_1097 for 1, 0, 0, 1, 12
theorem curve_1097_packet : curve_1097 = {(-12,-144),(-12,144)} := by decide +kernel
native_linear_perturbation curve_1098 for 1, 0, 0, 1, 13
theorem curve_1098_packet : curve_1098 = {(-13,-169),(-13,169)} := by decide +kernel
native_linear_perturbation curve_1099 for 1, 0, 0, 1, 14
theorem curve_1099_packet : curve_1099 = {(-14,-196),(-14,196),(1,-4),(1,4)} := by decide +kernel
#print axioms curve_1000_complete
#print axioms curve_1000_packet
#print axioms curve_1001_complete
#print axioms curve_1001_packet
#print axioms curve_1002_complete
#print axioms curve_1002_packet
#print axioms curve_1003_complete
#print axioms curve_1003_packet
#print axioms curve_1004_complete
#print axioms curve_1004_packet
#print axioms curve_1005_complete
#print axioms curve_1005_packet
#print axioms curve_1006_complete
#print axioms curve_1006_packet
#print axioms curve_1007_complete
#print axioms curve_1007_packet
#print axioms curve_1008_complete
#print axioms curve_1008_packet
#print axioms curve_1009_complete
#print axioms curve_1009_packet
#print axioms curve_1010_complete
#print axioms curve_1010_packet
#print axioms curve_1011_complete
#print axioms curve_1011_packet
#print axioms curve_1012_complete
#print axioms curve_1012_packet
#print axioms curve_1013_complete
#print axioms curve_1013_packet
#print axioms curve_1014_complete
#print axioms curve_1014_packet
#print axioms curve_1015_complete
#print axioms curve_1015_packet
#print axioms curve_1016_complete
#print axioms curve_1016_packet
#print axioms curve_1017_complete
#print axioms curve_1017_packet
#print axioms curve_1018_complete
#print axioms curve_1018_packet
#print axioms curve_1019_complete
#print axioms curve_1019_packet
#print axioms curve_1020_complete
#print axioms curve_1020_packet
#print axioms curve_1021_complete
#print axioms curve_1021_packet
#print axioms curve_1022_complete
#print axioms curve_1022_packet
#print axioms curve_1023_complete
#print axioms curve_1023_packet
#print axioms curve_1024_complete
#print axioms curve_1024_packet
#print axioms curve_1025_complete
#print axioms curve_1025_packet
#print axioms curve_1026_complete
#print axioms curve_1026_packet
#print axioms curve_1027_complete
#print axioms curve_1027_packet
#print axioms curve_1028_complete
#print axioms curve_1028_packet
#print axioms curve_1029_complete
#print axioms curve_1029_packet
#print axioms curve_1030_complete
#print axioms curve_1030_packet
#print axioms curve_1031_complete
#print axioms curve_1031_packet
#print axioms curve_1032_complete
#print axioms curve_1032_packet
#print axioms curve_1033_complete
#print axioms curve_1033_packet
#print axioms curve_1034_complete
#print axioms curve_1034_packet
#print axioms curve_1035_complete
#print axioms curve_1035_packet
#print axioms curve_1036_complete
#print axioms curve_1036_packet
#print axioms curve_1037_complete
#print axioms curve_1037_packet
#print axioms curve_1038_complete
#print axioms curve_1038_packet
#print axioms curve_1039_complete
#print axioms curve_1039_packet
#print axioms curve_1040_complete
#print axioms curve_1040_packet
#print axioms curve_1041_complete
#print axioms curve_1041_packet
#print axioms curve_1042_complete
#print axioms curve_1042_packet
#print axioms curve_1043_complete
#print axioms curve_1043_packet
#print axioms curve_1044_complete
#print axioms curve_1044_packet
#print axioms curve_1045_complete
#print axioms curve_1045_packet
#print axioms curve_1046_complete
#print axioms curve_1046_packet
#print axioms curve_1047_complete
#print axioms curve_1047_packet
#print axioms curve_1048_complete
#print axioms curve_1048_packet
#print axioms curve_1049_complete
#print axioms curve_1049_packet
#print axioms curve_1050_complete
#print axioms curve_1050_packet
#print axioms curve_1051_complete
#print axioms curve_1051_packet
#print axioms curve_1052_complete
#print axioms curve_1052_packet
#print axioms curve_1053_complete
#print axioms curve_1053_packet
#print axioms curve_1054_complete
#print axioms curve_1054_packet
#print axioms curve_1055_complete
#print axioms curve_1055_packet
#print axioms curve_1056_complete
#print axioms curve_1056_packet
#print axioms curve_1057_complete
#print axioms curve_1057_packet
#print axioms curve_1058_complete
#print axioms curve_1058_packet
#print axioms curve_1059_complete
#print axioms curve_1059_packet
#print axioms curve_1060_complete
#print axioms curve_1060_packet
#print axioms curve_1061_complete
#print axioms curve_1061_packet
#print axioms curve_1062_complete
#print axioms curve_1062_packet
#print axioms curve_1063_complete
#print axioms curve_1063_packet
#print axioms curve_1064_complete
#print axioms curve_1064_packet
#print axioms curve_1065_complete
#print axioms curve_1065_packet
#print axioms curve_1066_complete
#print axioms curve_1066_packet
#print axioms curve_1067_complete
#print axioms curve_1067_packet
#print axioms curve_1068_complete
#print axioms curve_1068_packet
#print axioms curve_1069_complete
#print axioms curve_1069_packet
#print axioms curve_1070_complete
#print axioms curve_1070_packet
#print axioms curve_1071_complete
#print axioms curve_1071_packet
#print axioms curve_1072_complete
#print axioms curve_1072_packet
#print axioms curve_1073_complete
#print axioms curve_1073_packet
#print axioms curve_1074_complete
#print axioms curve_1074_packet
#print axioms curve_1075_complete
#print axioms curve_1075_packet
#print axioms curve_1076_complete
#print axioms curve_1076_packet
#print axioms curve_1077_complete
#print axioms curve_1077_packet
#print axioms curve_1078_complete
#print axioms curve_1078_packet
#print axioms curve_1079_complete
#print axioms curve_1079_packet
#print axioms curve_1080_complete
#print axioms curve_1080_packet
#print axioms curve_1081_complete
#print axioms curve_1081_packet
#print axioms curve_1082_complete
#print axioms curve_1082_packet
#print axioms curve_1083_complete
#print axioms curve_1083_packet
#print axioms curve_1084_complete
#print axioms curve_1084_packet
#print axioms curve_1085_complete
#print axioms curve_1085_packet
#print axioms curve_1086_complete
#print axioms curve_1086_packet
#print axioms curve_1087_complete
#print axioms curve_1087_packet
#print axioms curve_1088_complete
#print axioms curve_1088_packet
#print axioms curve_1089_complete
#print axioms curve_1089_packet
#print axioms curve_1090_complete
#print axioms curve_1090_packet
#print axioms curve_1091_complete
#print axioms curve_1091_packet
#print axioms curve_1092_complete
#print axioms curve_1092_packet
#print axioms curve_1093_complete
#print axioms curve_1093_packet
#print axioms curve_1094_complete
#print axioms curve_1094_packet
#print axioms curve_1095_complete
#print axioms curve_1095_packet
#print axioms curve_1096_complete
#print axioms curve_1096_packet
#print axioms curve_1097_complete
#print axioms curve_1097_packet
#print axioms curve_1098_complete
#print axioms curve_1098_packet
#print axioms curve_1099_complete
#print axioms curve_1099_packet
end PerfectPower.DivisorSumAtlas
