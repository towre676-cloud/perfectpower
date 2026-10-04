import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_square_leading_quartic curve_2400 for 1, 0, 1, 0, 1
theorem curve_2400_packet : curve_2400 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2401 for 1, 0, 1, 0, 2
theorem curve_2401_packet : curve_2401 = {(-1,-2),(-1,2),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2402 for 1, 0, 1, 1, -2
theorem curve_2402_packet : curve_2402 = {(-2,-4),(-2,4),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2403 for 1, 0, 1, 1, -1
theorem curve_2403_packet : curve_2403 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2404 for 1, 0, 1, 1, 0
theorem curve_2404_packet : curve_2404 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2405 for 1, 0, 1, 1, 1
theorem curve_2405_packet : curve_2405 = {(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2406 for 1, 0, 1, 1, 2
theorem curve_2406_packet : curve_2406 = ∅ := by decide +kernel
native_square_leading_quartic curve_2407 for 1, 0, 1, 2, -2
theorem curve_2407_packet : curve_2407 = ∅ := by decide +kernel
native_square_leading_quartic curve_2408 for 1, 0, 1, 2, -1
theorem curve_2408_packet : curve_2408 = ∅ := by decide +kernel
native_square_leading_quartic curve_2409 for 1, 0, 1, 2, 0
theorem curve_2409_packet : curve_2409 = {(-2,-4),(-2,4),(-1,0),(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2410 for 1, 0, 1, 2, 1
theorem curve_2410_packet : curve_2410 = {(-1,-1),(-1,1),(0,-1),(0,1),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2411 for 1, 0, 1, 2, 2
theorem curve_2411_packet : curve_2411 = ∅ := by decide +kernel
native_square_leading_quartic curve_2412 for 1, 0, 2, -2, -2
theorem curve_2412_packet : curve_2412 = ∅ := by decide +kernel
native_square_leading_quartic curve_2413 for 1, 0, 2, -2, -1
theorem curve_2413_packet : curve_2413 = {(-1,-2),(-1,2),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2414 for 1, 0, 2, -2, 0
theorem curve_2414_packet : curve_2414 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2415 for 1, 0, 2, -2, 1
theorem curve_2415_packet : curve_2415 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2416 for 1, 0, 2, -2, 2
theorem curve_2416_packet : curve_2416 = ∅ := by decide +kernel
native_square_leading_quartic curve_2417 for 1, 0, 2, -1, -2
theorem curve_2417_packet : curve_2417 = {(-3,-10),(-3,10),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2418 for 1, 0, 2, -1, -1
theorem curve_2418_packet : curve_2418 = {(-2,-5),(-2,5),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2419 for 1, 0, 2, -1, 0
theorem curve_2419_packet : curve_2419 = {(-1,-2),(-1,2),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2420 for 1, 0, 2, -1, 1
theorem curve_2420_packet : curve_2420 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2421 for 1, 0, 2, -1, 2
theorem curve_2421_packet : curve_2421 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2422 for 1, 0, 2, 0, -2
theorem curve_2422_packet : curve_2422 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2423 for 1, 0, 2, 0, -1
theorem curve_2423_packet : curve_2423 = ∅ := by decide +kernel
native_square_leading_quartic curve_2424 for 1, 0, 2, 0, 0
theorem curve_2424_packet : curve_2424 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2425 for 1, 0, 2, 0, 2
theorem curve_2425_packet : curve_2425 = ∅ := by decide +kernel
native_square_leading_quartic curve_2426 for 1, 0, 2, 1, -2
theorem curve_2426_packet : curve_2426 = {(-1,0),(3,-10),(3,10)} := by decide +kernel
native_square_leading_quartic curve_2427 for 1, 0, 2, 1, -1
theorem curve_2427_packet : curve_2427 = {(-1,-1),(-1,1),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2428 for 1, 0, 2, 1, 0
theorem curve_2428_packet : curve_2428 = {(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2429 for 1, 0, 2, 1, 1
theorem curve_2429_packet : curve_2429 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2430 for 1, 0, 2, 1, 2
theorem curve_2430_packet : curve_2430 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2431 for 1, 0, 2, 2, -2
theorem curve_2431_packet : curve_2431 = ∅ := by decide +kernel
native_square_leading_quartic curve_2432 for 1, 0, 2, 2, -1
theorem curve_2432_packet : curve_2432 = {(-1,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2433 for 1, 0, 2, 2, 0
theorem curve_2433_packet : curve_2433 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2434 for 1, 0, 2, 2, 1
theorem curve_2434_packet : curve_2434 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2435 for 1, 0, 2, 2, 2
theorem curve_2435_packet : curve_2435 = ∅ := by decide +kernel
native_square_leading_quartic curve_2436 for 1, 1, -2, -2, -2
theorem curve_2436_packet : curve_2436 = ∅ := by decide +kernel
native_square_leading_quartic curve_2437 for 1, 1, -2, -2, -1
theorem curve_2437_packet : curve_2437 = ∅ := by decide +kernel
native_square_leading_quartic curve_2438 for 1, 1, -2, -2, 0
theorem curve_2438_packet : curve_2438 = {(-2,-2),(-2,2),(-1,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2439 for 1, 1, -2, -2, 1
theorem curve_2439_packet : curve_2439 = {(-4,-13),(-4,13),(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2440 for 1, 1, -2, -2, 2
theorem curve_2440_packet : curve_2440 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2441 for 1, 1, -2, -1, -2
theorem curve_2441_packet : curve_2441 = {(-2,0)} := by decide +kernel
native_square_leading_quartic curve_2442 for 1, 1, -2, -1, -1
theorem curve_2442_packet : curve_2442 = {(-2,-1),(-2,1)} := by decide +kernel
native_square_leading_quartic curve_2443 for 1, 1, -2, -1, 0
theorem curve_2443_packet : curve_2443 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2444 for 1, 1, -2, -1, 1
theorem curve_2444_packet : curve_2444 = {(-1,0),(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2445 for 1, 1, -2, -1, 2
theorem curve_2445_packet : curve_2445 = {(-2,-2),(-2,2),(-1,-1),(-1,1),(1,-1),(1,1),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2446 for 1, 1, -2, 0, -2
theorem curve_2446_packet : curve_2446 = ∅ := by decide +kernel
native_square_leading_quartic curve_2447 for 1, 1, -2, 0, -1
theorem curve_2447_packet : curve_2447 = ∅ := by decide +kernel
native_square_leading_quartic curve_2448 for 1, 1, -2, 0, 0
theorem curve_2448_packet : curve_2448 = {(-3,-6),(-3,6),(-2,0),(0,0),(1,0),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2449 for 1, 1, -2, 0, 1
theorem curve_2449_packet : curve_2449 = {(-2,-1),(-2,1),(0,-1),(0,1),(1,-1),(1,1),(4,-17),(4,17)} := by decide +kernel
native_square_leading_quartic curve_2450 for 1, 1, -2, 0, 2
theorem curve_2450_packet : curve_2450 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2451 for 1, 1, -2, 1, -2
theorem curve_2451_packet : curve_2451 = {(2,-4),(2,4),(6,-38),(6,38)} := by decide +kernel
native_square_leading_quartic curve_2452 for 1, 1, -2, 1, -1
theorem curve_2452_packet : curve_2452 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2453 for 1, 1, -2, 1, 0
theorem curve_2453_packet : curve_2453 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2454 for 1, 1, -2, 1, 1
theorem curve_2454_packet : curve_2454 = {(0,-1),(0,1),(8,-67),(8,67)} := by decide +kernel
native_square_leading_quartic curve_2455 for 1, 1, -2, 1, 2
theorem curve_2455_packet : curve_2455 = {(-2,0)} := by decide +kernel
native_square_leading_quartic curve_2456 for 1, 1, -2, 2, -2
theorem curve_2456_packet : curve_2456 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2457 for 1, 1, -2, 2, -1
theorem curve_2457_packet : curve_2457 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2458 for 1, 1, -2, 2, 0
theorem curve_2458_packet : curve_2458 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2459 for 1, 1, -2, 2, 1
theorem curve_2459_packet : curve_2459 = {(-5,-21),(-5,21),(0,-1),(0,1),(12,-149),(12,149)} := by decide +kernel
native_square_leading_quartic curve_2460 for 1, 1, -2, 2, 2
theorem curve_2460_packet : curve_2460 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2461 for 1, 1, -1, -2, -2
theorem curve_2461_packet : curve_2461 = {(-3,-7),(-3,7)} := by decide +kernel
native_square_leading_quartic curve_2462 for 1, 1, -1, -2, -1
theorem curve_2462_packet : curve_2462 = {(-5,-22),(-5,22),(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2463 for 1, 1, -1, -2, 0
theorem curve_2463_packet : curve_2463 = {(-1,-1),(-1,1),(0,0),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2464 for 1, 1, -1, -2, 1
theorem curve_2464_packet : curve_2464 = {(-2,-3),(-2,3),(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2465 for 1, 1, -1, -2, 2
theorem curve_2465_packet : curve_2465 = {(-7,-45),(-7,45),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2466 for 1, 1, -1, -1, -2
theorem curve_2466_packet : curve_2466 = {(-2,-2),(-2,2),(2,-4),(2,4)} := by decide +kernel
native_square_leading_quartic curve_2467 for 1, 1, -1, -1, -1
theorem curve_2467_packet : curve_2467 = ∅ := by decide +kernel
native_square_leading_quartic curve_2468 for 1, 1, -1, -1, 0
theorem curve_2468_packet : curve_2468 = {(-1,0),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2469 for 1, 1, -1, -1, 1
theorem curve_2469_packet : curve_2469 = {(-3,-7),(-3,7),(-1,-1),(-1,1),(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2470 for 1, 1, -1, -1, 2
theorem curve_2470_packet : curve_2470 = ∅ := by decide +kernel
native_square_leading_quartic curve_2471 for 1, 1, -1, 0, -2
theorem curve_2471_packet : curve_2471 = ∅ := by decide +kernel
native_square_leading_quartic curve_2472 for 1, 1, -1, 0, -1
theorem curve_2472_packet : curve_2472 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2473 for 1, 1, -1, 0, 0
theorem curve_2473_packet : curve_2473 = {(-2,-2),(-2,2),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2474 for 1, 1, -1, 0, 1
theorem curve_2474_packet : curve_2474 = {(-1,0),(0,-1),(0,1),(3,-10),(3,10)} := by decide +kernel
native_square_leading_quartic curve_2475 for 1, 1, -1, 0, 2
theorem curve_2475_packet : curve_2475 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2476 for 1, 1, -1, 1, -2
theorem curve_2476_packet : curve_2476 = {(-2,0),(1,0),(3,-10),(3,10)} := by decide +kernel
native_square_leading_quartic curve_2477 for 1, 1, -1, 1, -1
theorem curve_2477_packet : curve_2477 = {(-2,-1),(-2,1),(1,-1),(1,1),(5,-27),(5,27)} := by decide +kernel
native_square_leading_quartic curve_2478 for 1, 1, -1, 1, 0
theorem curve_2478_packet : curve_2478 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2479 for 1, 1, -1, 1, 1
theorem curve_2479_packet : curve_2479 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2480 for 1, 1, -1, 1, 2
theorem curve_2480_packet : curve_2480 = {(-2,-2),(-2,2),(-1,0),(1,-2),(1,2),(7,-52),(7,52)} := by decide +kernel
native_square_leading_quartic curve_2481 for 1, 1, -1, 2, -2
theorem curve_2481_packet : curve_2481 = {(1,-1),(1,1),(9,-85),(9,85)} := by decide +kernel
native_square_leading_quartic curve_2482 for 1, 1, -1, 2, -1
theorem curve_2482_packet : curve_2482 = ∅ := by decide +kernel
native_square_leading_quartic curve_2483 for 1, 1, -1, 2, 0
theorem curve_2483_packet : curve_2483 = {(-2,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2484 for 1, 1, -1, 2, 1
theorem curve_2484_packet : curve_2484 = {(-4,-13),(-4,13),(-2,-1),(-2,1),(0,-1),(0,1),(1,-2),(1,2),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2485 for 1, 1, -1, 2, 2
theorem curve_2485_packet : curve_2485 = ∅ := by decide +kernel
native_square_leading_quartic curve_2486 for 1, 1, 0, -2, -2
theorem curve_2486_packet : curve_2486 = {(-1,0),(3,-10),(3,10)} := by decide +kernel
native_square_leading_quartic curve_2487 for 1, 1, 0, -2, -1
theorem curve_2487_packet : curve_2487 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2488 for 1, 1, 0, -2, 0
theorem curve_2488_packet : curve_2488 = {(-8,-60),(-8,60),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2489 for 1, 1, 0, -2, 1
theorem curve_2489_packet : curve_2489 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2490 for 1, 1, 0, -2, 2
theorem curve_2490_packet : curve_2490 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2491 for 1, 1, 0, -1, -2
theorem curve_2491_packet : curve_2491 = ∅ := by decide +kernel
native_square_leading_quartic curve_2492 for 1, 1, 0, -1, -1
theorem curve_2492_packet : curve_2492 = {(-2,-3),(-2,3),(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2493 for 1, 1, 0, -1, 0
theorem curve_2493_packet : curve_2493 = {(-4,-14),(-4,14),(-1,-1),(-1,1),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2494 for 1, 1, 0, -1, 1
theorem curve_2494_packet : curve_2494 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2495 for 1, 1, 0, -1, 2
theorem curve_2495_packet : curve_2495 = ∅ := by decide +kernel
native_square_leading_quartic curve_2496 for 1, 1, 0, 0, -2
theorem curve_2496_packet : curve_2496 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2497 for 1, 1, 0, 0, -1
theorem curve_2497_packet : curve_2497 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2498 for 1, 1, 0, 0, 0
theorem curve_2498_packet : curve_2498 = {(-1,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2499 for 1, 1, 0, 0, 1
theorem curve_2499_packet : curve_2499 = {(-2,-3),(-2,3),(-1,-1),(-1,1),(0,-1),(0,1),(2,-5),(2,5)} := by decide +kernel
#print axioms curve_2400_complete
#print axioms curve_2400_packet
#print axioms curve_2401_complete
#print axioms curve_2401_packet
#print axioms curve_2402_complete
#print axioms curve_2402_packet
#print axioms curve_2403_complete
#print axioms curve_2403_packet
#print axioms curve_2404_complete
#print axioms curve_2404_packet
#print axioms curve_2405_complete
#print axioms curve_2405_packet
#print axioms curve_2406_complete
#print axioms curve_2406_packet
#print axioms curve_2407_complete
#print axioms curve_2407_packet
#print axioms curve_2408_complete
#print axioms curve_2408_packet
#print axioms curve_2409_complete
#print axioms curve_2409_packet
#print axioms curve_2410_complete
#print axioms curve_2410_packet
#print axioms curve_2411_complete
#print axioms curve_2411_packet
#print axioms curve_2412_complete
#print axioms curve_2412_packet
#print axioms curve_2413_complete
#print axioms curve_2413_packet
#print axioms curve_2414_complete
#print axioms curve_2414_packet
#print axioms curve_2415_complete
#print axioms curve_2415_packet
#print axioms curve_2416_complete
#print axioms curve_2416_packet
#print axioms curve_2417_complete
#print axioms curve_2417_packet
#print axioms curve_2418_complete
#print axioms curve_2418_packet
#print axioms curve_2419_complete
#print axioms curve_2419_packet
#print axioms curve_2420_complete
#print axioms curve_2420_packet
#print axioms curve_2421_complete
#print axioms curve_2421_packet
#print axioms curve_2422_complete
#print axioms curve_2422_packet
#print axioms curve_2423_complete
#print axioms curve_2423_packet
#print axioms curve_2424_complete
#print axioms curve_2424_packet
#print axioms curve_2425_complete
#print axioms curve_2425_packet
#print axioms curve_2426_complete
#print axioms curve_2426_packet
#print axioms curve_2427_complete
#print axioms curve_2427_packet
#print axioms curve_2428_complete
#print axioms curve_2428_packet
#print axioms curve_2429_complete
#print axioms curve_2429_packet
#print axioms curve_2430_complete
#print axioms curve_2430_packet
#print axioms curve_2431_complete
#print axioms curve_2431_packet
#print axioms curve_2432_complete
#print axioms curve_2432_packet
#print axioms curve_2433_complete
#print axioms curve_2433_packet
#print axioms curve_2434_complete
#print axioms curve_2434_packet
#print axioms curve_2435_complete
#print axioms curve_2435_packet
#print axioms curve_2436_complete
#print axioms curve_2436_packet
#print axioms curve_2437_complete
#print axioms curve_2437_packet
#print axioms curve_2438_complete
#print axioms curve_2438_packet
#print axioms curve_2439_complete
#print axioms curve_2439_packet
#print axioms curve_2440_complete
#print axioms curve_2440_packet
#print axioms curve_2441_complete
#print axioms curve_2441_packet
#print axioms curve_2442_complete
#print axioms curve_2442_packet
#print axioms curve_2443_complete
#print axioms curve_2443_packet
#print axioms curve_2444_complete
#print axioms curve_2444_packet
#print axioms curve_2445_complete
#print axioms curve_2445_packet
#print axioms curve_2446_complete
#print axioms curve_2446_packet
#print axioms curve_2447_complete
#print axioms curve_2447_packet
#print axioms curve_2448_complete
#print axioms curve_2448_packet
#print axioms curve_2449_complete
#print axioms curve_2449_packet
#print axioms curve_2450_complete
#print axioms curve_2450_packet
#print axioms curve_2451_complete
#print axioms curve_2451_packet
#print axioms curve_2452_complete
#print axioms curve_2452_packet
#print axioms curve_2453_complete
#print axioms curve_2453_packet
#print axioms curve_2454_complete
#print axioms curve_2454_packet
#print axioms curve_2455_complete
#print axioms curve_2455_packet
#print axioms curve_2456_complete
#print axioms curve_2456_packet
#print axioms curve_2457_complete
#print axioms curve_2457_packet
#print axioms curve_2458_complete
#print axioms curve_2458_packet
#print axioms curve_2459_complete
#print axioms curve_2459_packet
#print axioms curve_2460_complete
#print axioms curve_2460_packet
#print axioms curve_2461_complete
#print axioms curve_2461_packet
#print axioms curve_2462_complete
#print axioms curve_2462_packet
#print axioms curve_2463_complete
#print axioms curve_2463_packet
#print axioms curve_2464_complete
#print axioms curve_2464_packet
#print axioms curve_2465_complete
#print axioms curve_2465_packet
#print axioms curve_2466_complete
#print axioms curve_2466_packet
#print axioms curve_2467_complete
#print axioms curve_2467_packet
#print axioms curve_2468_complete
#print axioms curve_2468_packet
#print axioms curve_2469_complete
#print axioms curve_2469_packet
#print axioms curve_2470_complete
#print axioms curve_2470_packet
#print axioms curve_2471_complete
#print axioms curve_2471_packet
#print axioms curve_2472_complete
#print axioms curve_2472_packet
#print axioms curve_2473_complete
#print axioms curve_2473_packet
#print axioms curve_2474_complete
#print axioms curve_2474_packet
#print axioms curve_2475_complete
#print axioms curve_2475_packet
#print axioms curve_2476_complete
#print axioms curve_2476_packet
#print axioms curve_2477_complete
#print axioms curve_2477_packet
#print axioms curve_2478_complete
#print axioms curve_2478_packet
#print axioms curve_2479_complete
#print axioms curve_2479_packet
#print axioms curve_2480_complete
#print axioms curve_2480_packet
#print axioms curve_2481_complete
#print axioms curve_2481_packet
#print axioms curve_2482_complete
#print axioms curve_2482_packet
#print axioms curve_2483_complete
#print axioms curve_2483_packet
#print axioms curve_2484_complete
#print axioms curve_2484_packet
#print axioms curve_2485_complete
#print axioms curve_2485_packet
#print axioms curve_2486_complete
#print axioms curve_2486_packet
#print axioms curve_2487_complete
#print axioms curve_2487_packet
#print axioms curve_2488_complete
#print axioms curve_2488_packet
#print axioms curve_2489_complete
#print axioms curve_2489_packet
#print axioms curve_2490_complete
#print axioms curve_2490_packet
#print axioms curve_2491_complete
#print axioms curve_2491_packet
#print axioms curve_2492_complete
#print axioms curve_2492_packet
#print axioms curve_2493_complete
#print axioms curve_2493_packet
#print axioms curve_2494_complete
#print axioms curve_2494_packet
#print axioms curve_2495_complete
#print axioms curve_2495_packet
#print axioms curve_2496_complete
#print axioms curve_2496_packet
#print axioms curve_2497_complete
#print axioms curve_2497_packet
#print axioms curve_2498_complete
#print axioms curve_2498_packet
#print axioms curve_2499_complete
#print axioms curve_2499_packet
end PerfectPower.DivisorSumAtlas
