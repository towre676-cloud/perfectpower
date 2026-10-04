import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_square_leading_quartic curve_2100 for 1, -2, -2, 0, -2
theorem curve_2100_packet : curve_2100 = ∅ := by decide +kernel
native_square_leading_quartic curve_2101 for 1, -2, -2, 0, -1
theorem curve_2101_packet : curve_2101 = {(-1,0),(5,-18),(5,18)} := by decide +kernel
native_square_leading_quartic curve_2102 for 1, -2, -2, 0, 0
theorem curve_2102_packet : curve_2102 = {(-1,-1),(-1,1),(0,0),(3,-3),(3,3)} := by decide +kernel
native_square_leading_quartic curve_2103 for 1, -2, -2, 0, 1
theorem curve_2103_packet : curve_2103 = {(-2,-5),(-2,5),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2104 for 1, -2, -2, 0, 2
theorem curve_2104_packet : curve_2104 = ∅ := by decide +kernel
native_square_leading_quartic curve_2105 for 1, -2, -2, 1, -2
theorem curve_2105_packet : curve_2105 = ∅ := by decide +kernel
native_square_leading_quartic curve_2106 for 1, -2, -2, 1, -1
theorem curve_2106_packet : curve_2106 = ∅ := by decide +kernel
native_square_leading_quartic curve_2107 for 1, -2, -2, 1, 0
theorem curve_2107_packet : curve_2107 = {(-1,0),(0,0),(4,-10),(4,10)} := by decide +kernel
native_square_leading_quartic curve_2108 for 1, -2, -2, 1, 1
theorem curve_2108_packet : curve_2108 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2109 for 1, -2, -2, 1, 2
theorem curve_2109_packet : curve_2109 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2110 for 1, -2, -2, 2, -2
theorem curve_2110_packet : curve_2110 = ∅ := by decide +kernel
native_square_leading_quartic curve_2111 for 1, -2, -2, 2, -1
theorem curve_2111_packet : curve_2111 = ∅ := by decide +kernel
native_square_leading_quartic curve_2112 for 1, -2, -2, 2, 0
theorem curve_2112_packet : curve_2112 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2113 for 1, -2, -2, 2, 1
theorem curve_2113_packet : curve_2113 = {(-1,0),(0,-1),(0,1),(1,0),(3,-4),(3,4)} := by decide +kernel
native_square_leading_quartic curve_2114 for 1, -2, -2, 2, 2
theorem curve_2114_packet : curve_2114 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2115 for 1, -2, -1, -2, -2
theorem curve_2115_packet : curve_2115 = ∅ := by decide +kernel
native_square_leading_quartic curve_2116 for 1, -2, -1, -2, -1
theorem curve_2116_packet : curve_2116 = ∅ := by decide +kernel
native_square_leading_quartic curve_2117 for 1, -2, -1, -2, 0
theorem curve_2117_packet : curve_2117 = {(-1,-2),(-1,2),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2118 for 1, -2, -1, -2, 1
theorem curve_2118_packet : curve_2118 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2119 for 1, -2, -1, -2, 2
theorem curve_2119_packet : curve_2119 = ∅ := by decide +kernel
native_square_leading_quartic curve_2120 for 1, -2, -1, -1, -2
theorem curve_2120_packet : curve_2120 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2121 for 1, -2, -1, -1, -1
theorem curve_2121_packet : curve_2121 = ∅ := by decide +kernel
native_square_leading_quartic curve_2122 for 1, -2, -1, -1, 0
theorem curve_2122_packet : curve_2122 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2123 for 1, -2, -1, -1, 1
theorem curve_2123_packet : curve_2123 = {(-1,-2),(-1,2),(0,-1),(0,1),(3,-4),(3,4)} := by decide +kernel
native_square_leading_quartic curve_2124 for 1, -2, -1, -1, 2
theorem curve_2124_packet : curve_2124 = ∅ := by decide +kernel
native_square_leading_quartic curve_2125 for 1, -2, -1, 0, -2
theorem curve_2125_packet : curve_2125 = {(-1,0),(3,-4),(3,4)} := by decide +kernel
native_square_leading_quartic curve_2126 for 1, -2, -1, 0, -1
theorem curve_2126_packet : curve_2126 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2127 for 1, -2, -1, 0, 0
theorem curve_2127_packet : curve_2127 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2128 for 1, -2, -1, 0, 1
theorem curve_2128_packet : curve_2128 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2129 for 1, -2, -1, 0, 2
theorem curve_2129_packet : curve_2129 = {(-1,-2),(-1,2),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2130 for 1, -2, -1, 1, -2
theorem curve_2130_packet : curve_2130 = {(-3,-11),(-3,11)} := by decide +kernel
native_square_leading_quartic curve_2131 for 1, -2, -1, 1, -1
theorem curve_2131_packet : curve_2131 = {(-2,-5),(-2,5),(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2132 for 1, -2, -1, 1, 0
theorem curve_2132_packet : curve_2132 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2133 for 1, -2, -1, 1, 1
theorem curve_2133_packet : curve_2133 = {(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2134 for 1, -2, -1, 1, 2
theorem curve_2134_packet : curve_2134 = {(1,-1),(1,1),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2135 for 1, -2, -1, 2, -2
theorem curve_2135_packet : curve_2135 = ∅ := by decide +kernel
native_square_leading_quartic curve_2136 for 1, -2, -1, 2, -1
theorem curve_2136_packet : curve_2136 = ∅ := by decide +kernel
native_square_leading_quartic curve_2137 for 1, -2, -1, 2, 0
theorem curve_2137_packet : curve_2137 = {(-1,0),(0,0),(1,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2138 for 1, -2, -1, 2, 2
theorem curve_2138_packet : curve_2138 = ∅ := by decide +kernel
native_square_leading_quartic curve_2139 for 1, -2, 0, -2, -2
theorem curve_2139_packet : curve_2139 = ∅ := by decide +kernel
native_square_leading_quartic curve_2140 for 1, -2, 0, -2, -1
theorem curve_2140_packet : curve_2140 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2141 for 1, -2, 0, -2, 0
theorem curve_2141_packet : curve_2141 = {(-2,-6),(-2,6),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2142 for 1, -2, 0, -2, 1
theorem curve_2142_packet : curve_2142 = {(0,-1),(0,1),(4,-11),(4,11)} := by decide +kernel
native_square_leading_quartic curve_2143 for 1, -2, 0, -2, 2
theorem curve_2143_packet : curve_2143 = ∅ := by decide +kernel
native_square_leading_quartic curve_2144 for 1, -2, 0, -1, -2
theorem curve_2144_packet : curve_2144 = ∅ := by decide +kernel
native_square_leading_quartic curve_2145 for 1, -2, 0, -1, -1
theorem curve_2145_packet : curve_2145 = ∅ := by decide +kernel
native_square_leading_quartic curve_2146 for 1, -2, 0, -1, 0
theorem curve_2146_packet : curve_2146 = {(-1,-2),(-1,2),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2147 for 1, -2, 0, -1, 1
theorem curve_2147_packet : curve_2147 = {(0,-1),(0,1),(3,-5),(3,5)} := by decide +kernel
native_square_leading_quartic curve_2148 for 1, -2, 0, -1, 2
theorem curve_2148_packet : curve_2148 = {(-2,-6),(-2,6),(1,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2149 for 1, -2, 0, 0, -2
theorem curve_2149_packet : curve_2149 = {(-1,-1),(-1,1),(3,-5),(3,5)} := by decide +kernel
native_square_leading_quartic curve_2150 for 1, -2, 0, 0, -1
theorem curve_2150_packet : curve_2150 = ∅ := by decide +kernel
native_square_leading_quartic curve_2151 for 1, -2, 0, 0, 0
theorem curve_2151_packet : curve_2151 = {(0,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2152 for 1, -2, 0, 0, 1
theorem curve_2152_packet : curve_2152 = {(-1,-2),(-1,2),(0,-1),(0,1),(1,0),(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2153 for 1, -2, 0, 0, 2
theorem curve_2153_packet : curve_2153 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2154 for 1, -2, 0, 1, -2
theorem curve_2154_packet : curve_2154 = {(-1,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2155 for 1, -2, 0, 1, -1
theorem curve_2155_packet : curve_2155 = {(-1,-1),(-1,1),(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2156 for 1, -2, 0, 1, 0
theorem curve_2156_packet : curve_2156 = {(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2157 for 1, -2, 0, 1, 1
theorem curve_2157_packet : curve_2157 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2158 for 1, -2, 0, 1, 2
theorem curve_2158_packet : curve_2158 = {(-1,-2),(-1,2),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2159 for 1, -2, 0, 2, -2
theorem curve_2159_packet : curve_2159 = ∅ := by decide +kernel
native_square_leading_quartic curve_2160 for 1, -2, 0, 2, -1
theorem curve_2160_packet : curve_2160 = {(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2161 for 1, -2, 0, 2, 0
theorem curve_2161_packet : curve_2161 = {(-1,-1),(-1,1),(0,0),(1,-1),(1,1),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2162 for 1, -2, 0, 2, 1
theorem curve_2162_packet : curve_2162 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2163 for 1, -2, 0, 2, 2
theorem curve_2163_packet : curve_2163 = ∅ := by decide +kernel
native_square_leading_quartic curve_2164 for 1, -2, 1, -2, -2
theorem curve_2164_packet : curve_2164 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2165 for 1, -2, 1, -2, -1
theorem curve_2165_packet : curve_2165 = ∅ := by decide +kernel
native_square_leading_quartic curve_2166 for 1, -2, 1, -2, 0
theorem curve_2166_packet : curve_2166 = {(0,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2167 for 1, -2, 1, -2, 1
theorem curve_2167_packet : curve_2167 = {(0,-1),(0,1),(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2168 for 1, -2, 1, -2, 2
theorem curve_2168_packet : curve_2168 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2169 for 1, -2, 1, -1, -2
theorem curve_2169_packet : curve_2169 = {(-2,-6),(-2,6),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2170 for 1, -2, 1, -1, -1
theorem curve_2170_packet : curve_2170 = {(-1,-2),(-1,2),(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2171 for 1, -2, 1, -1, 0
theorem curve_2171_packet : curve_2171 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2172 for 1, -2, 1, -1, 1
theorem curve_2172_packet : curve_2172 = {(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2173 for 1, -2, 1, -1, 2
theorem curve_2173_packet : curve_2173 = {(1,-1),(1,1),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2174 for 1, -2, 1, 0, -2
theorem curve_2174_packet : curve_2174 = ∅ := by decide +kernel
native_square_leading_quartic curve_2175 for 1, -2, 1, 0, -1
theorem curve_2175_packet : curve_2175 = ∅ := by decide +kernel
native_square_leading_quartic curve_2176 for 1, -2, 1, 0, 1
theorem curve_2176_packet : curve_2176 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2177 for 1, -2, 1, 0, 2
theorem curve_2177_packet : curve_2177 = ∅ := by decide +kernel
native_square_leading_quartic curve_2178 for 1, -2, 1, 1, -2
theorem curve_2178_packet : curve_2178 = {(-1,-1),(-1,1),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2179 for 1, -2, 1, 1, -1
theorem curve_2179_packet : curve_2179 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2180 for 1, -2, 1, 1, 0
theorem curve_2180_packet : curve_2180 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2181 for 1, -2, 1, 1, 1
theorem curve_2181_packet : curve_2181 = {(-1,-2),(-1,2),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2182 for 1, -2, 1, 1, 2
theorem curve_2182_packet : curve_2182 = {(-2,-6),(-2,6)} := by decide +kernel
native_square_leading_quartic curve_2183 for 1, -2, 1, 2, -2
theorem curve_2183_packet : curve_2183 = {(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2184 for 1, -2, 1, 2, -1
theorem curve_2184_packet : curve_2184 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2185 for 1, -2, 1, 2, 0
theorem curve_2185_packet : curve_2185 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2186 for 1, -2, 1, 2, 1
theorem curve_2186_packet : curve_2186 = {(0,-1),(0,1),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2187 for 1, -2, 1, 2, 2
theorem curve_2187_packet : curve_2187 = {(-1,-2),(-1,2),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2188 for 1, -2, 2, -2, -2
theorem curve_2188_packet : curve_2188 = ∅ := by decide +kernel
native_square_leading_quartic curve_2189 for 1, -2, 2, -2, -1
theorem curve_2189_packet : curve_2189 = ∅ := by decide +kernel
native_square_leading_quartic curve_2190 for 1, -2, 2, -2, 0
theorem curve_2190_packet : curve_2190 = {(0,0),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2191 for 1, -2, 2, -2, 1
theorem curve_2191_packet : curve_2191 = {(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2192 for 1, -2, 2, -2, 2
theorem curve_2192_packet : curve_2192 = {(-1,-3),(-1,3),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2193 for 1, -2, 2, -1, -2
theorem curve_2193_packet : curve_2193 = {(-1,-2),(-1,2),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2194 for 1, -2, 2, -1, -1
theorem curve_2194_packet : curve_2194 = ∅ := by decide +kernel
native_square_leading_quartic curve_2195 for 1, -2, 2, -1, 0
theorem curve_2195_packet : curve_2195 = {(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2196 for 1, -2, 2, -1, 1
theorem curve_2196_packet : curve_2196 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2197 for 1, -2, 2, -1, 2
theorem curve_2197_packet : curve_2197 = ∅ := by decide +kernel
native_square_leading_quartic curve_2198 for 1, -2, 2, 0, -2
theorem curve_2198_packet : curve_2198 = ∅ := by decide +kernel
native_square_leading_quartic curve_2199 for 1, -2, 2, 0, -1
theorem curve_2199_packet : curve_2199 = {(-1,-2),(-1,2),(1,0)} := by decide +kernel
#print axioms curve_2100_complete
#print axioms curve_2100_packet
#print axioms curve_2101_complete
#print axioms curve_2101_packet
#print axioms curve_2102_complete
#print axioms curve_2102_packet
#print axioms curve_2103_complete
#print axioms curve_2103_packet
#print axioms curve_2104_complete
#print axioms curve_2104_packet
#print axioms curve_2105_complete
#print axioms curve_2105_packet
#print axioms curve_2106_complete
#print axioms curve_2106_packet
#print axioms curve_2107_complete
#print axioms curve_2107_packet
#print axioms curve_2108_complete
#print axioms curve_2108_packet
#print axioms curve_2109_complete
#print axioms curve_2109_packet
#print axioms curve_2110_complete
#print axioms curve_2110_packet
#print axioms curve_2111_complete
#print axioms curve_2111_packet
#print axioms curve_2112_complete
#print axioms curve_2112_packet
#print axioms curve_2113_complete
#print axioms curve_2113_packet
#print axioms curve_2114_complete
#print axioms curve_2114_packet
#print axioms curve_2115_complete
#print axioms curve_2115_packet
#print axioms curve_2116_complete
#print axioms curve_2116_packet
#print axioms curve_2117_complete
#print axioms curve_2117_packet
#print axioms curve_2118_complete
#print axioms curve_2118_packet
#print axioms curve_2119_complete
#print axioms curve_2119_packet
#print axioms curve_2120_complete
#print axioms curve_2120_packet
#print axioms curve_2121_complete
#print axioms curve_2121_packet
#print axioms curve_2122_complete
#print axioms curve_2122_packet
#print axioms curve_2123_complete
#print axioms curve_2123_packet
#print axioms curve_2124_complete
#print axioms curve_2124_packet
#print axioms curve_2125_complete
#print axioms curve_2125_packet
#print axioms curve_2126_complete
#print axioms curve_2126_packet
#print axioms curve_2127_complete
#print axioms curve_2127_packet
#print axioms curve_2128_complete
#print axioms curve_2128_packet
#print axioms curve_2129_complete
#print axioms curve_2129_packet
#print axioms curve_2130_complete
#print axioms curve_2130_packet
#print axioms curve_2131_complete
#print axioms curve_2131_packet
#print axioms curve_2132_complete
#print axioms curve_2132_packet
#print axioms curve_2133_complete
#print axioms curve_2133_packet
#print axioms curve_2134_complete
#print axioms curve_2134_packet
#print axioms curve_2135_complete
#print axioms curve_2135_packet
#print axioms curve_2136_complete
#print axioms curve_2136_packet
#print axioms curve_2137_complete
#print axioms curve_2137_packet
#print axioms curve_2138_complete
#print axioms curve_2138_packet
#print axioms curve_2139_complete
#print axioms curve_2139_packet
#print axioms curve_2140_complete
#print axioms curve_2140_packet
#print axioms curve_2141_complete
#print axioms curve_2141_packet
#print axioms curve_2142_complete
#print axioms curve_2142_packet
#print axioms curve_2143_complete
#print axioms curve_2143_packet
#print axioms curve_2144_complete
#print axioms curve_2144_packet
#print axioms curve_2145_complete
#print axioms curve_2145_packet
#print axioms curve_2146_complete
#print axioms curve_2146_packet
#print axioms curve_2147_complete
#print axioms curve_2147_packet
#print axioms curve_2148_complete
#print axioms curve_2148_packet
#print axioms curve_2149_complete
#print axioms curve_2149_packet
#print axioms curve_2150_complete
#print axioms curve_2150_packet
#print axioms curve_2151_complete
#print axioms curve_2151_packet
#print axioms curve_2152_complete
#print axioms curve_2152_packet
#print axioms curve_2153_complete
#print axioms curve_2153_packet
#print axioms curve_2154_complete
#print axioms curve_2154_packet
#print axioms curve_2155_complete
#print axioms curve_2155_packet
#print axioms curve_2156_complete
#print axioms curve_2156_packet
#print axioms curve_2157_complete
#print axioms curve_2157_packet
#print axioms curve_2158_complete
#print axioms curve_2158_packet
#print axioms curve_2159_complete
#print axioms curve_2159_packet
#print axioms curve_2160_complete
#print axioms curve_2160_packet
#print axioms curve_2161_complete
#print axioms curve_2161_packet
#print axioms curve_2162_complete
#print axioms curve_2162_packet
#print axioms curve_2163_complete
#print axioms curve_2163_packet
#print axioms curve_2164_complete
#print axioms curve_2164_packet
#print axioms curve_2165_complete
#print axioms curve_2165_packet
#print axioms curve_2166_complete
#print axioms curve_2166_packet
#print axioms curve_2167_complete
#print axioms curve_2167_packet
#print axioms curve_2168_complete
#print axioms curve_2168_packet
#print axioms curve_2169_complete
#print axioms curve_2169_packet
#print axioms curve_2170_complete
#print axioms curve_2170_packet
#print axioms curve_2171_complete
#print axioms curve_2171_packet
#print axioms curve_2172_complete
#print axioms curve_2172_packet
#print axioms curve_2173_complete
#print axioms curve_2173_packet
#print axioms curve_2174_complete
#print axioms curve_2174_packet
#print axioms curve_2175_complete
#print axioms curve_2175_packet
#print axioms curve_2176_complete
#print axioms curve_2176_packet
#print axioms curve_2177_complete
#print axioms curve_2177_packet
#print axioms curve_2178_complete
#print axioms curve_2178_packet
#print axioms curve_2179_complete
#print axioms curve_2179_packet
#print axioms curve_2180_complete
#print axioms curve_2180_packet
#print axioms curve_2181_complete
#print axioms curve_2181_packet
#print axioms curve_2182_complete
#print axioms curve_2182_packet
#print axioms curve_2183_complete
#print axioms curve_2183_packet
#print axioms curve_2184_complete
#print axioms curve_2184_packet
#print axioms curve_2185_complete
#print axioms curve_2185_packet
#print axioms curve_2186_complete
#print axioms curve_2186_packet
#print axioms curve_2187_complete
#print axioms curve_2187_packet
#print axioms curve_2188_complete
#print axioms curve_2188_packet
#print axioms curve_2189_complete
#print axioms curve_2189_packet
#print axioms curve_2190_complete
#print axioms curve_2190_packet
#print axioms curve_2191_complete
#print axioms curve_2191_packet
#print axioms curve_2192_complete
#print axioms curve_2192_packet
#print axioms curve_2193_complete
#print axioms curve_2193_packet
#print axioms curve_2194_complete
#print axioms curve_2194_packet
#print axioms curve_2195_complete
#print axioms curve_2195_packet
#print axioms curve_2196_complete
#print axioms curve_2196_packet
#print axioms curve_2197_complete
#print axioms curve_2197_packet
#print axioms curve_2198_complete
#print axioms curve_2198_packet
#print axioms curve_2199_complete
#print axioms curve_2199_packet
end PerfectPower.DivisorSumAtlas
