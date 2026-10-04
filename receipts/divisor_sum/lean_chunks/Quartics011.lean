import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_linear_perturbation curve_1100 for 1, 0, 0, 1, 15
theorem curve_1100_packet : curve_1100 = {(-15,-225),(-15,225)} := by decide +kernel
native_linear_perturbation curve_1101 for 1, 0, 0, 1, 16
theorem curve_1101_packet : curve_1101 = {(-16,-256),(-16,256),(-1,-4),(-1,4),(0,-4),(0,4),(3,-10),(3,10)} := by decide +kernel
native_linear_perturbation curve_1102 for 1, 0, 0, 1, 17
theorem curve_1102_packet : curve_1102 = {(-17,-289),(-17,289)} := by decide +kernel
native_linear_perturbation curve_1103 for 1, 0, 0, 1, 18
theorem curve_1103_packet : curve_1103 = {(-18,-324),(-18,324),(2,-6),(2,6)} := by decide +kernel
native_linear_perturbation curve_1104 for 1, 0, 0, 1, 19
theorem curve_1104_packet : curve_1104 = {(-19,-361),(-19,361)} := by decide +kernel
native_linear_perturbation curve_1105 for 1, 0, 0, 1, 20
theorem curve_1105_packet : curve_1105 = {(-20,-400),(-20,400)} := by decide +kernel
native_linear_perturbation curve_1106 for 1, 0, 0, 2, -20
theorem curve_1106_packet : curve_1106 = {(2,0),(10,-100),(10,100)} := by decide +kernel
native_linear_perturbation curve_1107 for 1, 0, 0, 2, -19
theorem curve_1107_packet : curve_1107 = {(2,-1),(2,1)} := by decide +kernel
native_linear_perturbation curve_1108 for 1, 0, 0, 2, -18
theorem curve_1108_packet : curve_1108 = {(9,-81),(9,81)} := by decide +kernel
native_linear_perturbation curve_1109 for 1, 0, 0, 2, -17
theorem curve_1109_packet : curve_1109 = ∅ := by decide +kernel
native_linear_perturbation curve_1110 for 1, 0, 0, 2, -16
theorem curve_1110_packet : curve_1110 = {(2,-2),(2,2),(8,-64),(8,64)} := by decide +kernel
native_linear_perturbation curve_1111 for 1, 0, 0, 2, -15
theorem curve_1111_packet : curve_1111 = ∅ := by decide +kernel
native_linear_perturbation curve_1112 for 1, 0, 0, 2, -14
theorem curve_1112_packet : curve_1112 = {(7,-49),(7,49)} := by decide +kernel
native_linear_perturbation curve_1113 for 1, 0, 0, 2, -13
theorem curve_1113_packet : curve_1113 = ∅ := by decide +kernel
native_linear_perturbation curve_1114 for 1, 0, 0, 2, -12
theorem curve_1114_packet : curve_1114 = {(-2,0),(6,-36),(6,36)} := by decide +kernel
native_linear_perturbation curve_1115 for 1, 0, 0, 2, -11
theorem curve_1115_packet : curve_1115 = {(-3,-8),(-3,8),(-2,-1),(-2,1),(2,-3),(2,3)} := by decide +kernel
native_linear_perturbation curve_1116 for 1, 0, 0, 2, -10
theorem curve_1116_packet : curve_1116 = {(5,-25),(5,25)} := by decide +kernel
native_linear_perturbation curve_1117 for 1, 0, 0, 2, -9
theorem curve_1117_packet : curve_1117 = ∅ := by decide +kernel
native_linear_perturbation curve_1118 for 1, 0, 0, 2, -8
theorem curve_1118_packet : curve_1118 = {(-2,-2),(-2,2),(4,-16),(4,16)} := by decide +kernel
native_linear_perturbation curve_1119 for 1, 0, 0, 2, -7
theorem curve_1119_packet : curve_1119 = ∅ := by decide +kernel
native_linear_perturbation curve_1120 for 1, 0, 0, 2, -6
theorem curve_1120_packet : curve_1120 = {(3,-9),(3,9)} := by decide +kernel
native_linear_perturbation curve_1121 for 1, 0, 0, 2, -5
theorem curve_1121_packet : curve_1121 = ∅ := by decide +kernel
native_linear_perturbation curve_1122 for 1, 0, 0, 2, -4
theorem curve_1122_packet : curve_1122 = {(2,-4),(2,4)} := by decide +kernel
native_linear_perturbation curve_1123 for 1, 0, 0, 2, -3
theorem curve_1123_packet : curve_1123 = {(-2,-3),(-2,3),(1,0)} := by decide +kernel
native_linear_perturbation curve_1124 for 1, 0, 0, 2, -2
theorem curve_1124_packet : curve_1124 = {(1,-1),(1,1)} := by decide +kernel
native_linear_perturbation curve_1125 for 1, 0, 0, 2, -1
theorem curve_1125_packet : curve_1125 = ∅ := by decide +kernel
native_linear_perturbation curve_1126 for 1, 0, 0, 2, 0
theorem curve_1126_packet : curve_1126 = {(0,0)} := by decide +kernel
native_linear_perturbation curve_1127 for 1, 0, 0, 2, 1
theorem curve_1127_packet : curve_1127 = {(-1,0),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_linear_perturbation curve_1128 for 1, 0, 0, 2, 2
theorem curve_1128_packet : curve_1128 = {(-1,-1),(-1,1)} := by decide +kernel
native_linear_perturbation curve_1129 for 1, 0, 0, 2, 3
theorem curve_1129_packet : curve_1129 = ∅ := by decide +kernel
native_linear_perturbation curve_1130 for 1, 0, 0, 2, 4
theorem curve_1130_packet : curve_1130 = {(-2,-4),(-2,4),(0,-2),(0,2)} := by decide +kernel
native_linear_perturbation curve_1131 for 1, 0, 0, 2, 5
theorem curve_1131_packet : curve_1131 = {(-1,-2),(-1,2),(2,-5),(2,5)} := by decide +kernel
native_linear_perturbation curve_1132 for 1, 0, 0, 2, 6
theorem curve_1132_packet : curve_1132 = {(-3,-9),(-3,9),(1,-3),(1,3)} := by decide +kernel
native_linear_perturbation curve_1133 for 1, 0, 0, 2, 7
theorem curve_1133_packet : curve_1133 = ∅ := by decide +kernel
native_linear_perturbation curve_1134 for 1, 0, 0, 2, 8
theorem curve_1134_packet : curve_1134 = {(-4,-16),(-4,16)} := by decide +kernel
native_linear_perturbation curve_1135 for 1, 0, 0, 2, 9
theorem curve_1135_packet : curve_1135 = {(0,-3),(0,3)} := by decide +kernel
native_linear_perturbation curve_1136 for 1, 0, 0, 2, 10
theorem curve_1136_packet : curve_1136 = {(-5,-25),(-5,25),(-1,-3),(-1,3)} := by decide +kernel
native_linear_perturbation curve_1137 for 1, 0, 0, 2, 11
theorem curve_1137_packet : curve_1137 = ∅ := by decide +kernel
native_linear_perturbation curve_1138 for 1, 0, 0, 2, 12
theorem curve_1138_packet : curve_1138 = {(-6,-36),(-6,36)} := by decide +kernel
native_linear_perturbation curve_1139 for 1, 0, 0, 2, 13
theorem curve_1139_packet : curve_1139 = {(-2,-5),(-2,5),(1,-4),(1,4),(3,-10),(3,10)} := by decide +kernel
native_linear_perturbation curve_1140 for 1, 0, 0, 2, 14
theorem curve_1140_packet : curve_1140 = {(-7,-49),(-7,49)} := by decide +kernel
native_linear_perturbation curve_1141 for 1, 0, 0, 2, 15
theorem curve_1141_packet : curve_1141 = ∅ := by decide +kernel
native_linear_perturbation curve_1142 for 1, 0, 0, 2, 16
theorem curve_1142_packet : curve_1142 = {(-8,-64),(-8,64),(0,-4),(0,4),(2,-6),(2,6)} := by decide +kernel
native_linear_perturbation curve_1143 for 1, 0, 0, 2, 17
theorem curve_1143_packet : curve_1143 = {(-1,-4),(-1,4)} := by decide +kernel
native_linear_perturbation curve_1144 for 1, 0, 0, 2, 18
theorem curve_1144_packet : curve_1144 = {(-9,-81),(-9,81)} := by decide +kernel
native_linear_perturbation curve_1145 for 1, 0, 0, 2, 19
theorem curve_1145_packet : curve_1145 = ∅ := by decide +kernel
native_linear_perturbation curve_1146 for 1, 0, 0, 2, 20
theorem curve_1146_packet : curve_1146 = {(-10,-100),(-10,100)} := by decide +kernel
native_linear_perturbation curve_1147 for 1, 0, 0, 3, -20
theorem curve_1147_packet : curve_1147 = ∅ := by decide +kernel
native_linear_perturbation curve_1148 for 1, 0, 0, 3, -19
theorem curve_1148_packet : curve_1148 = {(-4,-15),(-4,15)} := by decide +kernel
native_linear_perturbation curve_1149 for 1, 0, 0, 3, -18
theorem curve_1149_packet : curve_1149 = {(2,-2),(2,2),(6,-36),(6,36)} := by decide +kernel
native_linear_perturbation curve_1150 for 1, 0, 0, 3, -17
theorem curve_1150_packet : curve_1150 = ∅ := by decide +kernel
native_linear_perturbation curve_1151 for 1, 0, 0, 3, -16
theorem curve_1151_packet : curve_1151 = ∅ := by decide +kernel
native_linear_perturbation curve_1152 for 1, 0, 0, 3, -15
theorem curve_1152_packet : curve_1152 = {(5,-25),(5,25)} := by decide +kernel
native_linear_perturbation curve_1153 for 1, 0, 0, 3, -14
theorem curve_1153_packet : curve_1153 = ∅ := by decide +kernel
native_linear_perturbation curve_1154 for 1, 0, 0, 3, -13
theorem curve_1154_packet : curve_1154 = {(2,-3),(2,3)} := by decide +kernel
native_linear_perturbation curve_1155 for 1, 0, 0, 3, -12
theorem curve_1155_packet : curve_1155 = {(4,-16),(4,16)} := by decide +kernel
native_linear_perturbation curve_1156 for 1, 0, 0, 3, -11
theorem curve_1156_packet : curve_1156 = ∅ := by decide +kernel
native_linear_perturbation curve_1157 for 1, 0, 0, 3, -10
theorem curve_1157_packet : curve_1157 = {(-2,0)} := by decide +kernel
native_linear_perturbation curve_1158 for 1, 0, 0, 3, -9
theorem curve_1158_packet : curve_1158 = {(-2,-1),(-2,1),(3,-9),(3,9)} := by decide +kernel
native_linear_perturbation curve_1159 for 1, 0, 0, 3, -8
theorem curve_1159_packet : curve_1159 = {(-3,-8),(-3,8)} := by decide +kernel
native_linear_perturbation curve_1160 for 1, 0, 0, 3, -7
theorem curve_1160_packet : curve_1160 = ∅ := by decide +kernel
native_linear_perturbation curve_1161 for 1, 0, 0, 3, -6
theorem curve_1161_packet : curve_1161 = {(-2,-2),(-2,2),(2,-4),(2,4)} := by decide +kernel
native_linear_perturbation curve_1162 for 1, 0, 0, 3, -5
theorem curve_1162_packet : curve_1162 = ∅ := by decide +kernel
native_linear_perturbation curve_1163 for 1, 0, 0, 3, -4
theorem curve_1163_packet : curve_1163 = {(1,0)} := by decide +kernel
native_linear_perturbation curve_1164 for 1, 0, 0, 3, -3
theorem curve_1164_packet : curve_1164 = {(1,-1),(1,1)} := by decide +kernel
native_linear_perturbation curve_1165 for 1, 0, 0, 3, -2
theorem curve_1165_packet : curve_1165 = ∅ := by decide +kernel
native_linear_perturbation curve_1166 for 1, 0, 0, 3, -1
theorem curve_1166_packet : curve_1166 = {(-2,-3),(-2,3)} := by decide +kernel
native_linear_perturbation curve_1167 for 1, 0, 0, 3, 0
theorem curve_1167_packet : curve_1167 = {(0,0),(1,-2),(1,2)} := by decide +kernel
native_linear_perturbation curve_1168 for 1, 0, 0, 3, 1
theorem curve_1168_packet : curve_1168 = {(0,-1),(0,1)} := by decide +kernel
native_linear_perturbation curve_1169 for 1, 0, 0, 3, 2
theorem curve_1169_packet : curve_1169 = {(-1,0)} := by decide +kernel
native_linear_perturbation curve_1170 for 1, 0, 0, 3, 3
theorem curve_1170_packet : curve_1170 = {(-1,-1),(-1,1),(2,-5),(2,5)} := by decide +kernel
native_linear_perturbation curve_1171 for 1, 0, 0, 3, 4
theorem curve_1171_packet : curve_1171 = {(0,-2),(0,2)} := by decide +kernel
native_linear_perturbation curve_1172 for 1, 0, 0, 3, 5
theorem curve_1172_packet : curve_1172 = {(1,-3),(1,3)} := by decide +kernel
native_linear_perturbation curve_1173 for 1, 0, 0, 3, 6
theorem curve_1173_packet : curve_1173 = {(-2,-4),(-2,4),(-1,-2),(-1,2)} := by decide +kernel
native_linear_perturbation curve_1174 for 1, 0, 0, 3, 7
theorem curve_1174_packet : curve_1174 = ∅ := by decide +kernel
native_linear_perturbation curve_1175 for 1, 0, 0, 3, 8
theorem curve_1175_packet : curve_1175 = ∅ := by decide +kernel
native_linear_perturbation curve_1176 for 1, 0, 0, 3, 9
theorem curve_1176_packet : curve_1176 = {(-3,-9),(-3,9),(0,-3),(0,3)} := by decide +kernel
native_linear_perturbation curve_1177 for 1, 0, 0, 3, 10
theorem curve_1177_packet : curve_1177 = {(3,-10),(3,10)} := by decide +kernel
native_linear_perturbation curve_1178 for 1, 0, 0, 3, 11
theorem curve_1178_packet : curve_1178 = {(-1,-3),(-1,3)} := by decide +kernel
native_linear_perturbation curve_1179 for 1, 0, 0, 3, 12
theorem curve_1179_packet : curve_1179 = {(-4,-16),(-4,16),(1,-4),(1,4)} := by decide +kernel
native_linear_perturbation curve_1180 for 1, 0, 0, 3, 13
theorem curve_1180_packet : curve_1180 = ∅ := by decide +kernel
native_linear_perturbation curve_1181 for 1, 0, 0, 3, 14
theorem curve_1181_packet : curve_1181 = {(2,-6),(2,6)} := by decide +kernel
native_linear_perturbation curve_1182 for 1, 0, 0, 3, 15
theorem curve_1182_packet : curve_1182 = {(-5,-25),(-5,25),(-2,-5),(-2,5)} := by decide +kernel
native_linear_perturbation curve_1183 for 1, 0, 0, 3, 16
theorem curve_1183_packet : curve_1183 = {(0,-4),(0,4)} := by decide +kernel
native_linear_perturbation curve_1184 for 1, 0, 0, 3, 17
theorem curve_1184_packet : curve_1184 = ∅ := by decide +kernel
native_linear_perturbation curve_1185 for 1, 0, 0, 3, 18
theorem curve_1185_packet : curve_1185 = {(-6,-36),(-6,36),(-1,-4),(-1,4)} := by decide +kernel
native_linear_perturbation curve_1186 for 1, 0, 0, 3, 19
theorem curve_1186_packet : curve_1186 = ∅ := by decide +kernel
native_linear_perturbation curve_1187 for 1, 0, 0, 3, 20
theorem curve_1187_packet : curve_1187 = ∅ := by decide +kernel
native_linear_perturbation curve_1188 for 1, 0, 0, 4, -20
theorem curve_1188_packet : curve_1188 = {(-3,-7),(-3,7),(2,-2),(2,2),(5,-25),(5,25)} := by decide +kernel
native_linear_perturbation curve_1189 for 1, 0, 0, 4, -19
theorem curve_1189_packet : curve_1189 = ∅ := by decide +kernel
native_linear_perturbation curve_1190 for 1, 0, 0, 4, -18
theorem curve_1190_packet : curve_1190 = ∅ := by decide +kernel
native_linear_perturbation curve_1191 for 1, 0, 0, 4, -17
theorem curve_1191_packet : curve_1191 = ∅ := by decide +kernel
native_linear_perturbation curve_1192 for 1, 0, 0, 4, -16
theorem curve_1192_packet : curve_1192 = {(4,-16),(4,16)} := by decide +kernel
native_linear_perturbation curve_1193 for 1, 0, 0, 4, -15
theorem curve_1193_packet : curve_1193 = {(-4,-15),(-4,15),(2,-3),(2,3)} := by decide +kernel
native_linear_perturbation curve_1194 for 1, 0, 0, 4, -14
theorem curve_1194_packet : curve_1194 = ∅ := by decide +kernel
native_linear_perturbation curve_1195 for 1, 0, 0, 4, -13
theorem curve_1195_packet : curve_1195 = ∅ := by decide +kernel
native_linear_perturbation curve_1196 for 1, 0, 0, 4, -12
theorem curve_1196_packet : curve_1196 = {(3,-9),(3,9)} := by decide +kernel
native_linear_perturbation curve_1197 for 1, 0, 0, 4, -11
theorem curve_1197_packet : curve_1197 = ∅ := by decide +kernel
native_linear_perturbation curve_1198 for 1, 0, 0, 4, -10
theorem curve_1198_packet : curve_1198 = ∅ := by decide +kernel
native_linear_perturbation curve_1199 for 1, 0, 0, 4, -9
theorem curve_1199_packet : curve_1199 = ∅ := by decide +kernel
#print axioms curve_1100_complete
#print axioms curve_1100_packet
#print axioms curve_1101_complete
#print axioms curve_1101_packet
#print axioms curve_1102_complete
#print axioms curve_1102_packet
#print axioms curve_1103_complete
#print axioms curve_1103_packet
#print axioms curve_1104_complete
#print axioms curve_1104_packet
#print axioms curve_1105_complete
#print axioms curve_1105_packet
#print axioms curve_1106_complete
#print axioms curve_1106_packet
#print axioms curve_1107_complete
#print axioms curve_1107_packet
#print axioms curve_1108_complete
#print axioms curve_1108_packet
#print axioms curve_1109_complete
#print axioms curve_1109_packet
#print axioms curve_1110_complete
#print axioms curve_1110_packet
#print axioms curve_1111_complete
#print axioms curve_1111_packet
#print axioms curve_1112_complete
#print axioms curve_1112_packet
#print axioms curve_1113_complete
#print axioms curve_1113_packet
#print axioms curve_1114_complete
#print axioms curve_1114_packet
#print axioms curve_1115_complete
#print axioms curve_1115_packet
#print axioms curve_1116_complete
#print axioms curve_1116_packet
#print axioms curve_1117_complete
#print axioms curve_1117_packet
#print axioms curve_1118_complete
#print axioms curve_1118_packet
#print axioms curve_1119_complete
#print axioms curve_1119_packet
#print axioms curve_1120_complete
#print axioms curve_1120_packet
#print axioms curve_1121_complete
#print axioms curve_1121_packet
#print axioms curve_1122_complete
#print axioms curve_1122_packet
#print axioms curve_1123_complete
#print axioms curve_1123_packet
#print axioms curve_1124_complete
#print axioms curve_1124_packet
#print axioms curve_1125_complete
#print axioms curve_1125_packet
#print axioms curve_1126_complete
#print axioms curve_1126_packet
#print axioms curve_1127_complete
#print axioms curve_1127_packet
#print axioms curve_1128_complete
#print axioms curve_1128_packet
#print axioms curve_1129_complete
#print axioms curve_1129_packet
#print axioms curve_1130_complete
#print axioms curve_1130_packet
#print axioms curve_1131_complete
#print axioms curve_1131_packet
#print axioms curve_1132_complete
#print axioms curve_1132_packet
#print axioms curve_1133_complete
#print axioms curve_1133_packet
#print axioms curve_1134_complete
#print axioms curve_1134_packet
#print axioms curve_1135_complete
#print axioms curve_1135_packet
#print axioms curve_1136_complete
#print axioms curve_1136_packet
#print axioms curve_1137_complete
#print axioms curve_1137_packet
#print axioms curve_1138_complete
#print axioms curve_1138_packet
#print axioms curve_1139_complete
#print axioms curve_1139_packet
#print axioms curve_1140_complete
#print axioms curve_1140_packet
#print axioms curve_1141_complete
#print axioms curve_1141_packet
#print axioms curve_1142_complete
#print axioms curve_1142_packet
#print axioms curve_1143_complete
#print axioms curve_1143_packet
#print axioms curve_1144_complete
#print axioms curve_1144_packet
#print axioms curve_1145_complete
#print axioms curve_1145_packet
#print axioms curve_1146_complete
#print axioms curve_1146_packet
#print axioms curve_1147_complete
#print axioms curve_1147_packet
#print axioms curve_1148_complete
#print axioms curve_1148_packet
#print axioms curve_1149_complete
#print axioms curve_1149_packet
#print axioms curve_1150_complete
#print axioms curve_1150_packet
#print axioms curve_1151_complete
#print axioms curve_1151_packet
#print axioms curve_1152_complete
#print axioms curve_1152_packet
#print axioms curve_1153_complete
#print axioms curve_1153_packet
#print axioms curve_1154_complete
#print axioms curve_1154_packet
#print axioms curve_1155_complete
#print axioms curve_1155_packet
#print axioms curve_1156_complete
#print axioms curve_1156_packet
#print axioms curve_1157_complete
#print axioms curve_1157_packet
#print axioms curve_1158_complete
#print axioms curve_1158_packet
#print axioms curve_1159_complete
#print axioms curve_1159_packet
#print axioms curve_1160_complete
#print axioms curve_1160_packet
#print axioms curve_1161_complete
#print axioms curve_1161_packet
#print axioms curve_1162_complete
#print axioms curve_1162_packet
#print axioms curve_1163_complete
#print axioms curve_1163_packet
#print axioms curve_1164_complete
#print axioms curve_1164_packet
#print axioms curve_1165_complete
#print axioms curve_1165_packet
#print axioms curve_1166_complete
#print axioms curve_1166_packet
#print axioms curve_1167_complete
#print axioms curve_1167_packet
#print axioms curve_1168_complete
#print axioms curve_1168_packet
#print axioms curve_1169_complete
#print axioms curve_1169_packet
#print axioms curve_1170_complete
#print axioms curve_1170_packet
#print axioms curve_1171_complete
#print axioms curve_1171_packet
#print axioms curve_1172_complete
#print axioms curve_1172_packet
#print axioms curve_1173_complete
#print axioms curve_1173_packet
#print axioms curve_1174_complete
#print axioms curve_1174_packet
#print axioms curve_1175_complete
#print axioms curve_1175_packet
#print axioms curve_1176_complete
#print axioms curve_1176_packet
#print axioms curve_1177_complete
#print axioms curve_1177_packet
#print axioms curve_1178_complete
#print axioms curve_1178_packet
#print axioms curve_1179_complete
#print axioms curve_1179_packet
#print axioms curve_1180_complete
#print axioms curve_1180_packet
#print axioms curve_1181_complete
#print axioms curve_1181_packet
#print axioms curve_1182_complete
#print axioms curve_1182_packet
#print axioms curve_1183_complete
#print axioms curve_1183_packet
#print axioms curve_1184_complete
#print axioms curve_1184_packet
#print axioms curve_1185_complete
#print axioms curve_1185_packet
#print axioms curve_1186_complete
#print axioms curve_1186_packet
#print axioms curve_1187_complete
#print axioms curve_1187_packet
#print axioms curve_1188_complete
#print axioms curve_1188_packet
#print axioms curve_1189_complete
#print axioms curve_1189_packet
#print axioms curve_1190_complete
#print axioms curve_1190_packet
#print axioms curve_1191_complete
#print axioms curve_1191_packet
#print axioms curve_1192_complete
#print axioms curve_1192_packet
#print axioms curve_1193_complete
#print axioms curve_1193_packet
#print axioms curve_1194_complete
#print axioms curve_1194_packet
#print axioms curve_1195_complete
#print axioms curve_1195_packet
#print axioms curve_1196_complete
#print axioms curve_1196_packet
#print axioms curve_1197_complete
#print axioms curve_1197_packet
#print axioms curve_1198_complete
#print axioms curve_1198_packet
#print axioms curve_1199_complete
#print axioms curve_1199_packet
end PerfectPower.DivisorSumAtlas
