import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_square_leading_quartic curve_2200 for 1, -2, 2, 0, 0
theorem curve_2200_packet : curve_2200 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2201 for 1, -2, 2, 0, 1
theorem curve_2201_packet : curve_2201 = {(0,-1),(0,1),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2202 for 1, -2, 2, 0, 2
theorem curve_2202_packet : curve_2202 = ∅ := by decide +kernel
native_square_leading_quartic curve_2203 for 1, -2, 2, 1, -2
theorem curve_2203_packet : curve_2203 = {(-2,-6),(-2,6),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2204 for 1, -2, 2, 1, -1
theorem curve_2204_packet : curve_2204 = {(1,-1),(1,1),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2205 for 1, -2, 2, 1, 0
theorem curve_2205_packet : curve_2205 = {(-1,-2),(-1,2),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2206 for 1, -2, 2, 1, 1
theorem curve_2206_packet : curve_2206 = {(0,-1),(0,1),(3,-7),(3,7)} := by decide +kernel
native_square_leading_quartic curve_2207 for 1, -2, 2, 1, 2
theorem curve_2207_packet : curve_2207 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2208 for 1, -2, 2, 2, -2
theorem curve_2208_packet : curve_2208 = {(-1,-1),(-1,1),(1,-1),(1,1),(3,-7),(3,7)} := by decide +kernel
native_square_leading_quartic curve_2209 for 1, -2, 2, 2, -1
theorem curve_2209_packet : curve_2209 = ∅ := by decide +kernel
native_square_leading_quartic curve_2210 for 1, -2, 2, 2, 0
theorem curve_2210_packet : curve_2210 = {(-2,-6),(-2,6),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2211 for 1, -2, 2, 2, 1
theorem curve_2211_packet : curve_2211 = {(-1,-2),(-1,2),(0,-1),(0,1),(1,-2),(1,2),(4,-13),(4,13)} := by decide +kernel
native_square_leading_quartic curve_2212 for 1, -2, 2, 2, 2
theorem curve_2212_packet : curve_2212 = ∅ := by decide +kernel
native_square_leading_quartic curve_2213 for 1, -1, -2, -2, -2
theorem curve_2213_packet : curve_2213 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2214 for 1, -1, -2, -2, -1
theorem curve_2214_packet : curve_2214 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2215 for 1, -1, -2, -2, 0
theorem curve_2215_packet : curve_2215 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2216 for 1, -1, -2, -2, 1
theorem curve_2216_packet : curve_2216 = {(-12,-149),(-12,149),(0,-1),(0,1),(5,-21),(5,21)} := by decide +kernel
native_square_leading_quartic curve_2217 for 1, -1, -2, -2, 2
theorem curve_2217_packet : curve_2217 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2218 for 1, -1, -2, -1, -2
theorem curve_2218_packet : curve_2218 = {(-6,-38),(-6,38),(-2,-4),(-2,4)} := by decide +kernel
native_square_leading_quartic curve_2219 for 1, -1, -2, -1, -1
theorem curve_2219_packet : curve_2219 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2220 for 1, -1, -2, -1, 0
theorem curve_2220_packet : curve_2220 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2221 for 1, -1, -2, -1, 1
theorem curve_2221_packet : curve_2221 = {(-8,-67),(-8,67),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2222 for 1, -1, -2, -1, 2
theorem curve_2222_packet : curve_2222 = {(2,0)} := by decide +kernel
native_square_leading_quartic curve_2223 for 1, -1, -2, 0, -2
theorem curve_2223_packet : curve_2223 = ∅ := by decide +kernel
native_square_leading_quartic curve_2224 for 1, -1, -2, 0, -1
theorem curve_2224_packet : curve_2224 = ∅ := by decide +kernel
native_square_leading_quartic curve_2225 for 1, -1, -2, 0, 0
theorem curve_2225_packet : curve_2225 = {(-2,-4),(-2,4),(-1,0),(0,0),(2,0),(3,-6),(3,6)} := by decide +kernel
native_square_leading_quartic curve_2226 for 1, -1, -2, 0, 1
theorem curve_2226_packet : curve_2226 = {(-4,-17),(-4,17),(-1,-1),(-1,1),(0,-1),(0,1),(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2227 for 1, -1, -2, 0, 2
theorem curve_2227_packet : curve_2227 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2228 for 1, -1, -2, 1, -2
theorem curve_2228_packet : curve_2228 = {(2,0)} := by decide +kernel
native_square_leading_quartic curve_2229 for 1, -1, -2, 1, -1
theorem curve_2229_packet : curve_2229 = {(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2230 for 1, -1, -2, 1, 0
theorem curve_2230_packet : curve_2230 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2231 for 1, -1, -2, 1, 1
theorem curve_2231_packet : curve_2231 = {(-1,0),(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2232 for 1, -1, -2, 1, 2
theorem curve_2232_packet : curve_2232 = {(-2,-4),(-2,4),(-1,-1),(-1,1),(1,-1),(1,1),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2233 for 1, -1, -2, 2, -2
theorem curve_2233_packet : curve_2233 = ∅ := by decide +kernel
native_square_leading_quartic curve_2234 for 1, -1, -2, 2, -1
theorem curve_2234_packet : curve_2234 = ∅ := by decide +kernel
native_square_leading_quartic curve_2235 for 1, -1, -2, 2, 0
theorem curve_2235_packet : curve_2235 = {(0,0),(1,0),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2236 for 1, -1, -2, 2, 1
theorem curve_2236_packet : curve_2236 = {(0,-1),(0,1),(1,-1),(1,1),(4,-13),(4,13)} := by decide +kernel
native_square_leading_quartic curve_2237 for 1, -1, -2, 2, 2
theorem curve_2237_packet : curve_2237 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2238 for 1, -1, -1, -2, -2
theorem curve_2238_packet : curve_2238 = {(-9,-85),(-9,85),(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2239 for 1, -1, -1, -2, -1
theorem curve_2239_packet : curve_2239 = ∅ := by decide +kernel
native_square_leading_quartic curve_2240 for 1, -1, -1, -2, 0
theorem curve_2240_packet : curve_2240 = {(0,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2241 for 1, -1, -1, -2, 1
theorem curve_2241_packet : curve_2241 = {(-2,-5),(-2,5),(-1,-2),(-1,2),(0,-1),(0,1),(2,-1),(2,1),(4,-13),(4,13)} := by decide +kernel
native_square_leading_quartic curve_2242 for 1, -1, -1, -2, 2
theorem curve_2242_packet : curve_2242 = ∅ := by decide +kernel
native_square_leading_quartic curve_2243 for 1, -1, -1, -1, -2
theorem curve_2243_packet : curve_2243 = {(-3,-10),(-3,10),(-1,0),(2,0)} := by decide +kernel
native_square_leading_quartic curve_2244 for 1, -1, -1, -1, -1
theorem curve_2244_packet : curve_2244 = {(-5,-27),(-5,27),(-1,-1),(-1,1),(2,-1),(2,1)} := by decide +kernel
native_square_leading_quartic curve_2245 for 1, -1, -1, -1, 0
theorem curve_2245_packet : curve_2245 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2246 for 1, -1, -1, -1, 1
theorem curve_2246_packet : curve_2246 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2247 for 1, -1, -1, -1, 2
theorem curve_2247_packet : curve_2247 = {(-7,-52),(-7,52),(-1,-2),(-1,2),(1,0),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2248 for 1, -1, -1, 0, -2
theorem curve_2248_packet : curve_2248 = ∅ := by decide +kernel
native_square_leading_quartic curve_2249 for 1, -1, -1, 0, -1
theorem curve_2249_packet : curve_2249 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2250 for 1, -1, -1, 0, 0
theorem curve_2250_packet : curve_2250 = {(-1,-1),(-1,1),(0,0),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2251 for 1, -1, -1, 0, 1
theorem curve_2251_packet : curve_2251 = {(-3,-10),(-3,10),(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2252 for 1, -1, -1, 0, 2
theorem curve_2252_packet : curve_2252 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2253 for 1, -1, -1, 1, -2
theorem curve_2253_packet : curve_2253 = {(-2,-4),(-2,4),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2254 for 1, -1, -1, 1, -1
theorem curve_2254_packet : curve_2254 = ∅ := by decide +kernel
native_square_leading_quartic curve_2255 for 1, -1, -1, 1, 0
theorem curve_2255_packet : curve_2255 = {(-1,0),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2256 for 1, -1, -1, 1, 1
theorem curve_2256_packet : curve_2256 = {(-1,-1),(-1,1),(0,-1),(0,1),(1,-1),(1,1),(3,-7),(3,7)} := by decide +kernel
native_square_leading_quartic curve_2257 for 1, -1, -1, 1, 2
theorem curve_2257_packet : curve_2257 = ∅ := by decide +kernel
native_square_leading_quartic curve_2258 for 1, -1, -1, 2, -2
theorem curve_2258_packet : curve_2258 = {(3,-7),(3,7)} := by decide +kernel
native_square_leading_quartic curve_2259 for 1, -1, -1, 2, -1
theorem curve_2259_packet : curve_2259 = {(1,0),(5,-22),(5,22)} := by decide +kernel
native_square_leading_quartic curve_2260 for 1, -1, -1, 2, 0
theorem curve_2260_packet : curve_2260 = {(-2,-4),(-2,4),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2261 for 1, -1, -1, 2, 1
theorem curve_2261_packet : curve_2261 = {(-1,0),(0,-1),(0,1),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2262 for 1, -1, -1, 2, 2
theorem curve_2262_packet : curve_2262 = {(-1,-1),(-1,1),(7,-45),(7,45)} := by decide +kernel
native_square_leading_quartic curve_2263 for 1, -1, 0, -2, -2
theorem curve_2263_packet : curve_2263 = ∅ := by decide +kernel
native_square_leading_quartic curve_2264 for 1, -1, 0, -2, -1
theorem curve_2264_packet : curve_2264 = ∅ := by decide +kernel
native_square_leading_quartic curve_2265 for 1, -1, 0, -2, 0
theorem curve_2265_packet : curve_2265 = {(-8,-68),(-8,68),(-1,-2),(-1,2),(0,0),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2266 for 1, -1, 0, -2, 1
theorem curve_2266_packet : curve_2266 = {(0,-1),(0,1),(3,-7),(3,7)} := by decide +kernel
native_square_leading_quartic curve_2267 for 1, -1, 0, -2, 2
theorem curve_2267_packet : curve_2267 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2268 for 1, -1, 0, -1, -2
theorem curve_2268_packet : curve_2268 = {(-1,-1),(-1,1),(2,-2),(2,2),(3,-7),(3,7)} := by decide +kernel
native_square_leading_quartic curve_2269 for 1, -1, 0, -1, -1
theorem curve_2269_packet : curve_2269 = {(-2,-5),(-2,5)} := by decide +kernel
native_square_leading_quartic curve_2270 for 1, -1, 0, -1, 0
theorem curve_2270_packet : curve_2270 = {(-4,-18),(-4,18),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2271 for 1, -1, 0, -1, 1
theorem curve_2271_packet : curve_2271 = {(-1,-2),(-1,2),(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2272 for 1, -1, 0, -1, 2
theorem curve_2272_packet : curve_2272 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2273 for 1, -1, 0, 0, -2
theorem curve_2273_packet : curve_2273 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2274 for 1, -1, 0, 0, -1
theorem curve_2274_packet : curve_2274 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2275 for 1, -1, 0, 0, 0
theorem curve_2275_packet : curve_2275 = {(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2276 for 1, -1, 0, 0, 1
theorem curve_2276_packet : curve_2276 = {(-2,-5),(-2,5),(0,-1),(0,1),(1,-1),(1,1),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2277 for 1, -1, 0, 0, 2
theorem curve_2277_packet : curve_2277 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2278 for 1, -1, 0, 1, -2
theorem curve_2278_packet : curve_2278 = ∅ := by decide +kernel
native_square_leading_quartic curve_2279 for 1, -1, 0, 1, -1
theorem curve_2279_packet : curve_2279 = {(-1,0),(1,0),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2280 for 1, -1, 0, 1, 0
theorem curve_2280_packet : curve_2280 = {(-1,-1),(-1,1),(0,0),(1,-1),(1,1),(4,-14),(4,14)} := by decide +kernel
native_square_leading_quartic curve_2281 for 1, -1, 0, 1, 1
theorem curve_2281_packet : curve_2281 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2282 for 1, -1, 0, 1, 2
theorem curve_2282_packet : curve_2282 = ∅ := by decide +kernel
native_square_leading_quartic curve_2283 for 1, -1, 0, 2, -2
theorem curve_2283_packet : curve_2283 = {(-3,-10),(-3,10),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2284 for 1, -1, 0, 2, -1
theorem curve_2284_packet : curve_2284 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2285 for 1, -1, 0, 2, 0
theorem curve_2285_packet : curve_2285 = {(-1,0),(0,0),(8,-60),(8,60)} := by decide +kernel
native_square_leading_quartic curve_2286 for 1, -1, 0, 2, 1
theorem curve_2286_packet : curve_2286 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2287 for 1, -1, 0, 2, 2
theorem curve_2287_packet : curve_2287 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2288 for 1, -1, 1, -2, -2
theorem curve_2288_packet : curve_2288 = {(-3,-11),(-3,11)} := by decide +kernel
native_square_leading_quartic curve_2289 for 1, -1, 1, -2, -1
theorem curve_2289_packet : curve_2289 = {(-5,-28),(-5,28),(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2290 for 1, -1, 1, -2, 0
theorem curve_2290_packet : curve_2290 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2291 for 1, -1, 1, -2, 1
theorem curve_2291_packet : curve_2291 = {(0,-1),(0,1),(1,0),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2292 for 1, -1, 1, -2, 2
theorem curve_2292_packet : curve_2292 = {(-7,-53),(-7,53),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2293 for 1, -1, 1, -1, -2
theorem curve_2293_packet : curve_2293 = ∅ := by decide +kernel
native_square_leading_quartic curve_2294 for 1, -1, 1, -1, -1
theorem curve_2294_packet : curve_2294 = {(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2295 for 1, -1, 1, -1, 0
theorem curve_2295_packet : curve_2295 = {(-1,-2),(-1,2),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2296 for 1, -1, 1, -1, 1
theorem curve_2296_packet : curve_2296 = {(-3,-11),(-3,11),(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2297 for 1, -1, 1, -1, 2
theorem curve_2297_packet : curve_2297 = ∅ := by decide +kernel
native_square_leading_quartic curve_2298 for 1, -1, 1, 0, -2
theorem curve_2298_packet : curve_2298 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2299 for 1, -1, 1, 0, -1
theorem curve_2299_packet : curve_2299 = {(1,0)} := by decide +kernel
#print axioms curve_2200_complete
#print axioms curve_2200_packet
#print axioms curve_2201_complete
#print axioms curve_2201_packet
#print axioms curve_2202_complete
#print axioms curve_2202_packet
#print axioms curve_2203_complete
#print axioms curve_2203_packet
#print axioms curve_2204_complete
#print axioms curve_2204_packet
#print axioms curve_2205_complete
#print axioms curve_2205_packet
#print axioms curve_2206_complete
#print axioms curve_2206_packet
#print axioms curve_2207_complete
#print axioms curve_2207_packet
#print axioms curve_2208_complete
#print axioms curve_2208_packet
#print axioms curve_2209_complete
#print axioms curve_2209_packet
#print axioms curve_2210_complete
#print axioms curve_2210_packet
#print axioms curve_2211_complete
#print axioms curve_2211_packet
#print axioms curve_2212_complete
#print axioms curve_2212_packet
#print axioms curve_2213_complete
#print axioms curve_2213_packet
#print axioms curve_2214_complete
#print axioms curve_2214_packet
#print axioms curve_2215_complete
#print axioms curve_2215_packet
#print axioms curve_2216_complete
#print axioms curve_2216_packet
#print axioms curve_2217_complete
#print axioms curve_2217_packet
#print axioms curve_2218_complete
#print axioms curve_2218_packet
#print axioms curve_2219_complete
#print axioms curve_2219_packet
#print axioms curve_2220_complete
#print axioms curve_2220_packet
#print axioms curve_2221_complete
#print axioms curve_2221_packet
#print axioms curve_2222_complete
#print axioms curve_2222_packet
#print axioms curve_2223_complete
#print axioms curve_2223_packet
#print axioms curve_2224_complete
#print axioms curve_2224_packet
#print axioms curve_2225_complete
#print axioms curve_2225_packet
#print axioms curve_2226_complete
#print axioms curve_2226_packet
#print axioms curve_2227_complete
#print axioms curve_2227_packet
#print axioms curve_2228_complete
#print axioms curve_2228_packet
#print axioms curve_2229_complete
#print axioms curve_2229_packet
#print axioms curve_2230_complete
#print axioms curve_2230_packet
#print axioms curve_2231_complete
#print axioms curve_2231_packet
#print axioms curve_2232_complete
#print axioms curve_2232_packet
#print axioms curve_2233_complete
#print axioms curve_2233_packet
#print axioms curve_2234_complete
#print axioms curve_2234_packet
#print axioms curve_2235_complete
#print axioms curve_2235_packet
#print axioms curve_2236_complete
#print axioms curve_2236_packet
#print axioms curve_2237_complete
#print axioms curve_2237_packet
#print axioms curve_2238_complete
#print axioms curve_2238_packet
#print axioms curve_2239_complete
#print axioms curve_2239_packet
#print axioms curve_2240_complete
#print axioms curve_2240_packet
#print axioms curve_2241_complete
#print axioms curve_2241_packet
#print axioms curve_2242_complete
#print axioms curve_2242_packet
#print axioms curve_2243_complete
#print axioms curve_2243_packet
#print axioms curve_2244_complete
#print axioms curve_2244_packet
#print axioms curve_2245_complete
#print axioms curve_2245_packet
#print axioms curve_2246_complete
#print axioms curve_2246_packet
#print axioms curve_2247_complete
#print axioms curve_2247_packet
#print axioms curve_2248_complete
#print axioms curve_2248_packet
#print axioms curve_2249_complete
#print axioms curve_2249_packet
#print axioms curve_2250_complete
#print axioms curve_2250_packet
#print axioms curve_2251_complete
#print axioms curve_2251_packet
#print axioms curve_2252_complete
#print axioms curve_2252_packet
#print axioms curve_2253_complete
#print axioms curve_2253_packet
#print axioms curve_2254_complete
#print axioms curve_2254_packet
#print axioms curve_2255_complete
#print axioms curve_2255_packet
#print axioms curve_2256_complete
#print axioms curve_2256_packet
#print axioms curve_2257_complete
#print axioms curve_2257_packet
#print axioms curve_2258_complete
#print axioms curve_2258_packet
#print axioms curve_2259_complete
#print axioms curve_2259_packet
#print axioms curve_2260_complete
#print axioms curve_2260_packet
#print axioms curve_2261_complete
#print axioms curve_2261_packet
#print axioms curve_2262_complete
#print axioms curve_2262_packet
#print axioms curve_2263_complete
#print axioms curve_2263_packet
#print axioms curve_2264_complete
#print axioms curve_2264_packet
#print axioms curve_2265_complete
#print axioms curve_2265_packet
#print axioms curve_2266_complete
#print axioms curve_2266_packet
#print axioms curve_2267_complete
#print axioms curve_2267_packet
#print axioms curve_2268_complete
#print axioms curve_2268_packet
#print axioms curve_2269_complete
#print axioms curve_2269_packet
#print axioms curve_2270_complete
#print axioms curve_2270_packet
#print axioms curve_2271_complete
#print axioms curve_2271_packet
#print axioms curve_2272_complete
#print axioms curve_2272_packet
#print axioms curve_2273_complete
#print axioms curve_2273_packet
#print axioms curve_2274_complete
#print axioms curve_2274_packet
#print axioms curve_2275_complete
#print axioms curve_2275_packet
#print axioms curve_2276_complete
#print axioms curve_2276_packet
#print axioms curve_2277_complete
#print axioms curve_2277_packet
#print axioms curve_2278_complete
#print axioms curve_2278_packet
#print axioms curve_2279_complete
#print axioms curve_2279_packet
#print axioms curve_2280_complete
#print axioms curve_2280_packet
#print axioms curve_2281_complete
#print axioms curve_2281_packet
#print axioms curve_2282_complete
#print axioms curve_2282_packet
#print axioms curve_2283_complete
#print axioms curve_2283_packet
#print axioms curve_2284_complete
#print axioms curve_2284_packet
#print axioms curve_2285_complete
#print axioms curve_2285_packet
#print axioms curve_2286_complete
#print axioms curve_2286_packet
#print axioms curve_2287_complete
#print axioms curve_2287_packet
#print axioms curve_2288_complete
#print axioms curve_2288_packet
#print axioms curve_2289_complete
#print axioms curve_2289_packet
#print axioms curve_2290_complete
#print axioms curve_2290_packet
#print axioms curve_2291_complete
#print axioms curve_2291_packet
#print axioms curve_2292_complete
#print axioms curve_2292_packet
#print axioms curve_2293_complete
#print axioms curve_2293_packet
#print axioms curve_2294_complete
#print axioms curve_2294_packet
#print axioms curve_2295_complete
#print axioms curve_2295_packet
#print axioms curve_2296_complete
#print axioms curve_2296_packet
#print axioms curve_2297_complete
#print axioms curve_2297_packet
#print axioms curve_2298_complete
#print axioms curve_2298_packet
#print axioms curve_2299_complete
#print axioms curve_2299_packet
end PerfectPower.DivisorSumAtlas
