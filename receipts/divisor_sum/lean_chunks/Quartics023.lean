import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_square_leading_quartic curve_2300 for 1, -1, 1, 0, 0
theorem curve_2300_packet : curve_2300 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2301 for 1, -1, 1, 0, 1
theorem curve_2301_packet : curve_2301 = {(-1,-2),(-1,2),(0,-1),(0,1),(3,-8),(3,8)} := by decide +kernel
native_square_leading_quartic curve_2302 for 1, -1, 1, 0, 2
theorem curve_2302_packet : curve_2302 = ∅ := by decide +kernel
native_square_leading_quartic curve_2303 for 1, -1, 1, 1, -2
theorem curve_2303_packet : curve_2303 = {(-1,0),(1,0),(3,-8),(3,8)} := by decide +kernel
native_square_leading_quartic curve_2304 for 1, -1, 1, 1, -1
theorem curve_2304_packet : curve_2304 = {(-2,-5),(-2,5),(-1,-1),(-1,1),(1,-1),(1,1),(5,-23),(5,23)} := by decide +kernel
native_square_leading_quartic curve_2305 for 1, -1, 1, 1, 0
theorem curve_2305_packet : curve_2305 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2306 for 1, -1, 1, 1, 1
theorem curve_2306_packet : curve_2306 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2307 for 1, -1, 1, 1, 2
theorem curve_2307_packet : curve_2307 = {(-1,-2),(-1,2),(1,-2),(1,2),(2,-4),(2,4),(7,-46),(7,46)} := by decide +kernel
native_square_leading_quartic curve_2308 for 1, -1, 1, 2, -2
theorem curve_2308_packet : curve_2308 = {(1,-1),(1,1),(9,-77),(9,77)} := by decide +kernel
native_square_leading_quartic curve_2309 for 1, -1, 1, 2, -1
theorem curve_2309_packet : curve_2309 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2310 for 1, -1, 1, 2, 0
theorem curve_2310_packet : curve_2310 = {(-1,-1),(-1,1),(0,0),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2311 for 1, -1, 1, 2, 1
theorem curve_2311_packet : curve_2311 = {(-2,-5),(-2,5),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2312 for 1, -1, 1, 2, 2
theorem curve_2312_packet : curve_2312 = ∅ := by decide +kernel
native_square_leading_quartic curve_2313 for 1, -1, 2, -2, -2
theorem curve_2313_packet : curve_2313 = {(-1,-2),(-1,2),(3,-8),(3,8)} := by decide +kernel
native_square_leading_quartic curve_2314 for 1, -1, 2, -2, -1
theorem curve_2314_packet : curve_2314 = ∅ := by decide +kernel
native_square_leading_quartic curve_2315 for 1, -1, 2, -2, 0
theorem curve_2315_packet : curve_2315 = {(-2,-6),(-2,6),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2316 for 1, -1, 2, -2, 1
theorem curve_2316_packet : curve_2316 = {(-4,-19),(-4,19),(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2317 for 1, -1, 2, -2, 2
theorem curve_2317_packet : curve_2317 = ∅ := by decide +kernel
native_square_leading_quartic curve_2318 for 1, -1, 2, -1, -2
theorem curve_2318_packet : curve_2318 = ∅ := by decide +kernel
native_square_leading_quartic curve_2319 for 1, -1, 2, -1, -1
theorem curve_2319_packet : curve_2319 = {(-1,-2),(-1,2),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2320 for 1, -1, 2, -1, 0
theorem curve_2320_packet : curve_2320 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2321 for 1, -1, 2, -1, 1
theorem curve_2321_packet : curve_2321 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2322 for 1, -1, 2, -1, 2
theorem curve_2322_packet : curve_2322 = {(-2,-6),(-2,6),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2323 for 1, -1, 2, 0, -2
theorem curve_2323_packet : curve_2323 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2324 for 1, -1, 2, 0, -1
theorem curve_2324_packet : curve_2324 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2325 for 1, -1, 2, 0, 0
theorem curve_2325_packet : curve_2325 = {(-1,-2),(-1,2),(0,0),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2326 for 1, -1, 2, 0, 1
theorem curve_2326_packet : curve_2326 = {(0,-1),(0,1),(4,-15),(4,15)} := by decide +kernel
native_square_leading_quartic curve_2327 for 1, -1, 2, 0, 2
theorem curve_2327_packet : curve_2327 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2328 for 1, -1, 2, 1, -2
theorem curve_2328_packet : curve_2328 = {(-3,-11),(-3,11),(-1,-1),(-1,1),(1,-1),(1,1),(2,-4),(2,4),(6,-34),(6,34)} := by decide +kernel
native_square_leading_quartic curve_2329 for 1, -1, 2, 1, -1
theorem curve_2329_packet : curve_2329 = ∅ := by decide +kernel
native_square_leading_quartic curve_2330 for 1, -1, 2, 1, 0
theorem curve_2330_packet : curve_2330 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2331 for 1, -1, 2, 1, 1
theorem curve_2331_packet : curve_2331 = {(-1,-2),(-1,2),(0,-1),(0,1),(1,-2),(1,2),(8,-61),(8,61)} := by decide +kernel
native_square_leading_quartic curve_2332 for 1, -1, 2, 1, 2
theorem curve_2332_packet : curve_2332 = ∅ := by decide +kernel
native_square_leading_quartic curve_2333 for 1, -1, 2, 2, -2
theorem curve_2333_packet : curve_2333 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2334 for 1, -1, 2, 2, -1
theorem curve_2334_packet : curve_2334 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2335 for 1, -1, 2, 2, 0
theorem curve_2335_packet : curve_2335 = {(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2336 for 1, -1, 2, 2, 1
theorem curve_2336_packet : curve_2336 = {(-3,-11),(-3,11),(0,-1),(0,1),(12,-139),(12,139)} := by decide +kernel
native_square_leading_quartic curve_2337 for 1, -1, 2, 2, 2
theorem curve_2337_packet : curve_2337 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2338 for 1, 0, -2, -2, -2
theorem curve_2338_packet : curve_2338 = ∅ := by decide +kernel
native_square_leading_quartic curve_2339 for 1, 0, -2, -2, -1
theorem curve_2339_packet : curve_2339 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2340 for 1, 0, -2, -2, 0
theorem curve_2340_packet : curve_2340 = {(-1,-1),(-1,1),(0,0),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2341 for 1, 0, -2, -2, 1
theorem curve_2341_packet : curve_2341 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2342 for 1, 0, -2, -2, 2
theorem curve_2342_packet : curve_2342 = ∅ := by decide +kernel
native_square_leading_quartic curve_2343 for 1, 0, -2, -1, -2
theorem curve_2343_packet : curve_2343 = {(-3,-8),(-3,8),(2,-2),(2,2)} := by decide +kernel
native_square_leading_quartic curve_2344 for 1, 0, -2, -1, -1
theorem curve_2344_packet : curve_2344 = {(-2,-3),(-2,3)} := by decide +kernel
native_square_leading_quartic curve_2345 for 1, 0, -2, -1, 0
theorem curve_2345_packet : curve_2345 = {(-1,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2346 for 1, 0, -2, -1, 1
theorem curve_2346_packet : curve_2346 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2347 for 1, 0, -2, -1, 2
theorem curve_2347_packet : curve_2347 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2348 for 1, 0, -2, 0, -2
theorem curve_2348_packet : curve_2348 = ∅ := by decide +kernel
native_square_leading_quartic curve_2349 for 1, 0, -2, 0, -1
theorem curve_2349_packet : curve_2349 = ∅ := by decide +kernel
native_square_leading_quartic curve_2350 for 1, 0, -2, 0, 0
theorem curve_2350_packet : curve_2350 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2351 for 1, 0, -2, 0, 2
theorem curve_2351_packet : curve_2351 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2352 for 1, 0, -2, 1, -2
theorem curve_2352_packet : curve_2352 = {(-2,-2),(-2,2),(3,-8),(3,8)} := by decide +kernel
native_square_leading_quartic curve_2353 for 1, 0, -2, 1, -1
theorem curve_2353_packet : curve_2353 = {(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2354 for 1, 0, -2, 1, 0
theorem curve_2354_packet : curve_2354 = {(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2355 for 1, 0, -2, 1, 1
theorem curve_2355_packet : curve_2355 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2356 for 1, 0, -2, 1, 2
theorem curve_2356_packet : curve_2356 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2357 for 1, 0, -2, 2, -2
theorem curve_2357_packet : curve_2357 = ∅ := by decide +kernel
native_square_leading_quartic curve_2358 for 1, 0, -2, 2, -1
theorem curve_2358_packet : curve_2358 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2359 for 1, 0, -2, 2, 0
theorem curve_2359_packet : curve_2359 = {(-2,-2),(-2,2),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2360 for 1, 0, -2, 2, 1
theorem curve_2360_packet : curve_2360 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2361 for 1, 0, -2, 2, 2
theorem curve_2361_packet : curve_2361 = ∅ := by decide +kernel
native_square_leading_quartic curve_2362 for 1, 0, -1, -2, -2
theorem curve_2362_packet : curve_2362 = {(-1,0),(3,-8),(3,8)} := by decide +kernel
native_square_leading_quartic curve_2363 for 1, 0, -1, -2, -1
theorem curve_2363_packet : curve_2363 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2364 for 1, 0, -1, -2, 0
theorem curve_2364_packet : curve_2364 = {(-2,-4),(-2,4),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2365 for 1, 0, -1, -2, 1
theorem curve_2365_packet : curve_2365 = {(0,-1),(0,1),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2366 for 1, 0, -1, -2, 2
theorem curve_2366_packet : curve_2366 = {(-1,-2),(-1,2),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2367 for 1, 0, -1, -1, -2
theorem curve_2367_packet : curve_2367 = ∅ := by decide +kernel
native_square_leading_quartic curve_2368 for 1, 0, -1, -1, -1
theorem curve_2368_packet : curve_2368 = {(-1,0),(2,-3),(2,3)} := by decide +kernel
native_square_leading_quartic curve_2369 for 1, 0, -1, -1, 0
theorem curve_2369_packet : curve_2369 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2370 for 1, 0, -1, -1, 1
theorem curve_2370_packet : curve_2370 = {(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2371 for 1, 0, -1, -1, 2
theorem curve_2371_packet : curve_2371 = {(-2,-4),(-2,4),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2372 for 1, 0, -1, 0, -2
theorem curve_2372_packet : curve_2372 = ∅ := by decide +kernel
native_square_leading_quartic curve_2373 for 1, 0, -1, 0, -1
theorem curve_2373_packet : curve_2373 = ∅ := by decide +kernel
native_square_leading_quartic curve_2374 for 1, 0, -1, 0, 0
theorem curve_2374_packet : curve_2374 = {(-1,0),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2375 for 1, 0, -1, 0, 1
theorem curve_2375_packet : curve_2375 = {(-1,-1),(-1,1),(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2376 for 1, 0, -1, 0, 2
theorem curve_2376_packet : curve_2376 = ∅ := by decide +kernel
native_square_leading_quartic curve_2377 for 1, 0, -1, 1, -2
theorem curve_2377_packet : curve_2377 = ∅ := by decide +kernel
native_square_leading_quartic curve_2378 for 1, 0, -1, 1, -1
theorem curve_2378_packet : curve_2378 = {(-2,-3),(-2,3),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2379 for 1, 0, -1, 1, 0
theorem curve_2379_packet : curve_2379 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2380 for 1, 0, -1, 1, 1
theorem curve_2380_packet : curve_2380 = {(-1,0),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2381 for 1, 0, -1, 1, 2
theorem curve_2381_packet : curve_2381 = {(-1,-1),(-1,1),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2382 for 1, 0, -1, 2, -2
theorem curve_2382_packet : curve_2382 = {(-3,-8),(-3,8),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2383 for 1, 0, -1, 2, -1
theorem curve_2383_packet : curve_2383 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2384 for 1, 0, -1, 2, 0
theorem curve_2384_packet : curve_2384 = {(0,0),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2385 for 1, 0, -1, 2, 1
theorem curve_2385_packet : curve_2385 = {(-2,-3),(-2,3),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2386 for 1, 0, -1, 2, 2
theorem curve_2386_packet : curve_2386 = {(-1,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2387 for 1, 0, 1, -2, -2
theorem curve_2387_packet : curve_2387 = ∅ := by decide +kernel
native_square_leading_quartic curve_2388 for 1, 0, 1, -2, -1
theorem curve_2388_packet : curve_2388 = ∅ := by decide +kernel
native_square_leading_quartic curve_2389 for 1, 0, 1, -2, 0
theorem curve_2389_packet : curve_2389 = {(-1,-2),(-1,2),(0,0),(1,0),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2390 for 1, 0, 1, -2, 1
theorem curve_2390_packet : curve_2390 = {(-2,-5),(-2,5),(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2391 for 1, 0, 1, -2, 2
theorem curve_2391_packet : curve_2391 = ∅ := by decide +kernel
native_square_leading_quartic curve_2392 for 1, 0, 1, -1, -2
theorem curve_2392_packet : curve_2392 = {(-1,-1),(-1,1),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2393 for 1, 0, 1, -1, -1
theorem curve_2393_packet : curve_2393 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2394 for 1, 0, 1, -1, 0
theorem curve_2394_packet : curve_2394 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2395 for 1, 0, 1, -1, 1
theorem curve_2395_packet : curve_2395 = {(-1,-2),(-1,2),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2396 for 1, 0, 1, -1, 2
theorem curve_2396_packet : curve_2396 = ∅ := by decide +kernel
native_square_leading_quartic curve_2397 for 1, 0, 1, 0, -2
theorem curve_2397_packet : curve_2397 = {(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2398 for 1, 0, 1, 0, -1
theorem curve_2398_packet : curve_2398 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2399 for 1, 0, 1, 0, 0
theorem curve_2399_packet : curve_2399 = {(0,0)} := by decide +kernel
#print axioms curve_2300_complete
#print axioms curve_2300_packet
#print axioms curve_2301_complete
#print axioms curve_2301_packet
#print axioms curve_2302_complete
#print axioms curve_2302_packet
#print axioms curve_2303_complete
#print axioms curve_2303_packet
#print axioms curve_2304_complete
#print axioms curve_2304_packet
#print axioms curve_2305_complete
#print axioms curve_2305_packet
#print axioms curve_2306_complete
#print axioms curve_2306_packet
#print axioms curve_2307_complete
#print axioms curve_2307_packet
#print axioms curve_2308_complete
#print axioms curve_2308_packet
#print axioms curve_2309_complete
#print axioms curve_2309_packet
#print axioms curve_2310_complete
#print axioms curve_2310_packet
#print axioms curve_2311_complete
#print axioms curve_2311_packet
#print axioms curve_2312_complete
#print axioms curve_2312_packet
#print axioms curve_2313_complete
#print axioms curve_2313_packet
#print axioms curve_2314_complete
#print axioms curve_2314_packet
#print axioms curve_2315_complete
#print axioms curve_2315_packet
#print axioms curve_2316_complete
#print axioms curve_2316_packet
#print axioms curve_2317_complete
#print axioms curve_2317_packet
#print axioms curve_2318_complete
#print axioms curve_2318_packet
#print axioms curve_2319_complete
#print axioms curve_2319_packet
#print axioms curve_2320_complete
#print axioms curve_2320_packet
#print axioms curve_2321_complete
#print axioms curve_2321_packet
#print axioms curve_2322_complete
#print axioms curve_2322_packet
#print axioms curve_2323_complete
#print axioms curve_2323_packet
#print axioms curve_2324_complete
#print axioms curve_2324_packet
#print axioms curve_2325_complete
#print axioms curve_2325_packet
#print axioms curve_2326_complete
#print axioms curve_2326_packet
#print axioms curve_2327_complete
#print axioms curve_2327_packet
#print axioms curve_2328_complete
#print axioms curve_2328_packet
#print axioms curve_2329_complete
#print axioms curve_2329_packet
#print axioms curve_2330_complete
#print axioms curve_2330_packet
#print axioms curve_2331_complete
#print axioms curve_2331_packet
#print axioms curve_2332_complete
#print axioms curve_2332_packet
#print axioms curve_2333_complete
#print axioms curve_2333_packet
#print axioms curve_2334_complete
#print axioms curve_2334_packet
#print axioms curve_2335_complete
#print axioms curve_2335_packet
#print axioms curve_2336_complete
#print axioms curve_2336_packet
#print axioms curve_2337_complete
#print axioms curve_2337_packet
#print axioms curve_2338_complete
#print axioms curve_2338_packet
#print axioms curve_2339_complete
#print axioms curve_2339_packet
#print axioms curve_2340_complete
#print axioms curve_2340_packet
#print axioms curve_2341_complete
#print axioms curve_2341_packet
#print axioms curve_2342_complete
#print axioms curve_2342_packet
#print axioms curve_2343_complete
#print axioms curve_2343_packet
#print axioms curve_2344_complete
#print axioms curve_2344_packet
#print axioms curve_2345_complete
#print axioms curve_2345_packet
#print axioms curve_2346_complete
#print axioms curve_2346_packet
#print axioms curve_2347_complete
#print axioms curve_2347_packet
#print axioms curve_2348_complete
#print axioms curve_2348_packet
#print axioms curve_2349_complete
#print axioms curve_2349_packet
#print axioms curve_2350_complete
#print axioms curve_2350_packet
#print axioms curve_2351_complete
#print axioms curve_2351_packet
#print axioms curve_2352_complete
#print axioms curve_2352_packet
#print axioms curve_2353_complete
#print axioms curve_2353_packet
#print axioms curve_2354_complete
#print axioms curve_2354_packet
#print axioms curve_2355_complete
#print axioms curve_2355_packet
#print axioms curve_2356_complete
#print axioms curve_2356_packet
#print axioms curve_2357_complete
#print axioms curve_2357_packet
#print axioms curve_2358_complete
#print axioms curve_2358_packet
#print axioms curve_2359_complete
#print axioms curve_2359_packet
#print axioms curve_2360_complete
#print axioms curve_2360_packet
#print axioms curve_2361_complete
#print axioms curve_2361_packet
#print axioms curve_2362_complete
#print axioms curve_2362_packet
#print axioms curve_2363_complete
#print axioms curve_2363_packet
#print axioms curve_2364_complete
#print axioms curve_2364_packet
#print axioms curve_2365_complete
#print axioms curve_2365_packet
#print axioms curve_2366_complete
#print axioms curve_2366_packet
#print axioms curve_2367_complete
#print axioms curve_2367_packet
#print axioms curve_2368_complete
#print axioms curve_2368_packet
#print axioms curve_2369_complete
#print axioms curve_2369_packet
#print axioms curve_2370_complete
#print axioms curve_2370_packet
#print axioms curve_2371_complete
#print axioms curve_2371_packet
#print axioms curve_2372_complete
#print axioms curve_2372_packet
#print axioms curve_2373_complete
#print axioms curve_2373_packet
#print axioms curve_2374_complete
#print axioms curve_2374_packet
#print axioms curve_2375_complete
#print axioms curve_2375_packet
#print axioms curve_2376_complete
#print axioms curve_2376_packet
#print axioms curve_2377_complete
#print axioms curve_2377_packet
#print axioms curve_2378_complete
#print axioms curve_2378_packet
#print axioms curve_2379_complete
#print axioms curve_2379_packet
#print axioms curve_2380_complete
#print axioms curve_2380_packet
#print axioms curve_2381_complete
#print axioms curve_2381_packet
#print axioms curve_2382_complete
#print axioms curve_2382_packet
#print axioms curve_2383_complete
#print axioms curve_2383_packet
#print axioms curve_2384_complete
#print axioms curve_2384_packet
#print axioms curve_2385_complete
#print axioms curve_2385_packet
#print axioms curve_2386_complete
#print axioms curve_2386_packet
#print axioms curve_2387_complete
#print axioms curve_2387_packet
#print axioms curve_2388_complete
#print axioms curve_2388_packet
#print axioms curve_2389_complete
#print axioms curve_2389_packet
#print axioms curve_2390_complete
#print axioms curve_2390_packet
#print axioms curve_2391_complete
#print axioms curve_2391_packet
#print axioms curve_2392_complete
#print axioms curve_2392_packet
#print axioms curve_2393_complete
#print axioms curve_2393_packet
#print axioms curve_2394_complete
#print axioms curve_2394_packet
#print axioms curve_2395_complete
#print axioms curve_2395_packet
#print axioms curve_2396_complete
#print axioms curve_2396_packet
#print axioms curve_2397_complete
#print axioms curve_2397_packet
#print axioms curve_2398_complete
#print axioms curve_2398_packet
#print axioms curve_2399_complete
#print axioms curve_2399_packet
end PerfectPower.DivisorSumAtlas
