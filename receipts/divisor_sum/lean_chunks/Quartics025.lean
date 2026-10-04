import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_square_leading_quartic curve_2500 for 1, 1, 0, 0, 2
theorem curve_2500_packet : curve_2500 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2501 for 1, 1, 0, 1, -2
theorem curve_2501_packet : curve_2501 = {(-3,-7),(-3,7),(-2,-2),(-2,2),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2502 for 1, 1, 0, 1, -1
theorem curve_2502_packet : curve_2502 = {(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2503 for 1, 1, 0, 1, 0
theorem curve_2503_packet : curve_2503 = {(0,0),(4,-18),(4,18)} := by decide +kernel
native_square_leading_quartic curve_2504 for 1, 1, 0, 1, 1
theorem curve_2504_packet : curve_2504 = {(-1,0),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2505 for 1, 1, 0, 1, 2
theorem curve_2505_packet : curve_2505 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2506 for 1, 1, 0, 2, -2
theorem curve_2506_packet : curve_2506 = ∅ := by decide +kernel
native_square_leading_quartic curve_2507 for 1, 1, 0, 2, -1
theorem curve_2507_packet : curve_2507 = ∅ := by decide +kernel
native_square_leading_quartic curve_2508 for 1, 1, 0, 2, 0
theorem curve_2508_packet : curve_2508 = {(-2,-2),(-2,2),(0,0),(1,-2),(1,2),(8,-68),(8,68)} := by decide +kernel
native_square_leading_quartic curve_2509 for 1, 1, 0, 2, 1
theorem curve_2509_packet : curve_2509 = {(-3,-7),(-3,7),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2510 for 1, 1, 0, 2, 2
theorem curve_2510_packet : curve_2510 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2511 for 1, 1, 1, -2, -2
theorem curve_2511_packet : curve_2511 = {(-9,-77),(-9,77),(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2512 for 1, 1, 1, -2, -1
theorem curve_2512_packet : curve_2512 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2513 for 1, 1, 1, -2, 0
theorem curve_2513_packet : curve_2513 = {(-2,-4),(-2,4),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2514 for 1, 1, 1, -2, 1
theorem curve_2514_packet : curve_2514 = {(-1,-2),(-1,2),(0,-1),(0,1),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2515 for 1, 1, 1, -2, 2
theorem curve_2515_packet : curve_2515 = ∅ := by decide +kernel
native_square_leading_quartic curve_2516 for 1, 1, 1, -1, -2
theorem curve_2516_packet : curve_2516 = {(-3,-8),(-3,8),(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2517 for 1, 1, 1, -1, -1
theorem curve_2517_packet : curve_2517 = {(-5,-23),(-5,23),(-1,-1),(-1,1),(1,-1),(1,1),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2518 for 1, 1, 1, -1, 0
theorem curve_2518_packet : curve_2518 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2519 for 1, 1, 1, -1, 1
theorem curve_2519_packet : curve_2519 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2520 for 1, 1, 1, -1, 2
theorem curve_2520_packet : curve_2520 = {(-7,-46),(-7,46),(-2,-4),(-2,4),(-1,-2),(-1,2),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2521 for 1, 1, 1, 0, -2
theorem curve_2521_packet : curve_2521 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2522 for 1, 1, 1, 0, -1
theorem curve_2522_packet : curve_2522 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2523 for 1, 1, 1, 0, 0
theorem curve_2523_packet : curve_2523 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2524 for 1, 1, 1, 0, 1
theorem curve_2524_packet : curve_2524 = {(-3,-8),(-3,8),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2525 for 1, 1, 1, 0, 2
theorem curve_2525_packet : curve_2525 = ∅ := by decide +kernel
native_square_leading_quartic curve_2526 for 1, 1, 1, 1, -2
theorem curve_2526_packet : curve_2526 = ∅ := by decide +kernel
native_square_leading_quartic curve_2527 for 1, 1, 1, 1, -1
theorem curve_2527_packet : curve_2527 = {(-2,-3),(-2,3)} := by decide +kernel
native_square_leading_quartic curve_2528 for 1, 1, 1, 1, 0
theorem curve_2528_packet : curve_2528 = {(-1,0),(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2529 for 1, 1, 1, 1, 1
theorem curve_2529_packet : curve_2529 = {(-1,-1),(-1,1),(0,-1),(0,1),(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2530 for 1, 1, 1, 1, 2
theorem curve_2530_packet : curve_2530 = ∅ := by decide +kernel
native_square_leading_quartic curve_2531 for 1, 1, 1, 2, -2
theorem curve_2531_packet : curve_2531 = {(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2532 for 1, 1, 1, 2, -1
theorem curve_2532_packet : curve_2532 = {(1,-2),(1,2),(5,-28),(5,28)} := by decide +kernel
native_square_leading_quartic curve_2533 for 1, 1, 1, 2, 0
theorem curve_2533_packet : curve_2533 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2534 for 1, 1, 1, 2, 1
theorem curve_2534_packet : curve_2534 = {(-2,-3),(-2,3),(-1,0),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2535 for 1, 1, 1, 2, 2
theorem curve_2535_packet : curve_2535 = {(-1,-1),(-1,1),(7,-53),(7,53)} := by decide +kernel
native_square_leading_quartic curve_2536 for 1, 1, 2, -2, -2
theorem curve_2536_packet : curve_2536 = {(1,0)} := by decide +kernel
native_square_leading_quartic curve_2537 for 1, 1, 2, -2, -1
theorem curve_2537_packet : curve_2537 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2538 for 1, 1, 2, -2, 0
theorem curve_2538_packet : curve_2538 = {(-1,-2),(-1,2),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2539 for 1, 1, 2, -2, 1
theorem curve_2539_packet : curve_2539 = {(-12,-139),(-12,139),(0,-1),(0,1),(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2540 for 1, 1, 2, -2, 2
theorem curve_2540_packet : curve_2540 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2541 for 1, 1, 2, -1, -2
theorem curve_2541_packet : curve_2541 = {(-6,-34),(-6,34),(-2,-4),(-2,4),(-1,-1),(-1,1),(1,-1),(1,1),(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2542 for 1, 1, 2, -1, -1
theorem curve_2542_packet : curve_2542 = ∅ := by decide +kernel
native_square_leading_quartic curve_2543 for 1, 1, 2, -1, 0
theorem curve_2543_packet : curve_2543 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2544 for 1, 1, 2, -1, 1
theorem curve_2544_packet : curve_2544 = {(-8,-61),(-8,61),(-1,-2),(-1,2),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2545 for 1, 1, 2, -1, 2
theorem curve_2545_packet : curve_2545 = ∅ := by decide +kernel
native_square_leading_quartic curve_2546 for 1, 1, 2, 0, -2
theorem curve_2546_packet : curve_2546 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2547 for 1, 1, 2, 0, -1
theorem curve_2547_packet : curve_2547 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2548 for 1, 1, 2, 0, 0
theorem curve_2548_packet : curve_2548 = {(-2,-4),(-2,4),(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2549 for 1, 1, 2, 0, 1
theorem curve_2549_packet : curve_2549 = {(-4,-15),(-4,15),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2550 for 1, 1, 2, 0, 2
theorem curve_2550_packet : curve_2550 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2551 for 1, 1, 2, 1, -2
theorem curve_2551_packet : curve_2551 = ∅ := by decide +kernel
native_square_leading_quartic curve_2552 for 1, 1, 2, 1, -1
theorem curve_2552_packet : curve_2552 = {(-1,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2553 for 1, 1, 2, 1, 0
theorem curve_2553_packet : curve_2553 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2554 for 1, 1, 2, 1, 1
theorem curve_2554_packet : curve_2554 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2555 for 1, 1, 2, 1, 2
theorem curve_2555_packet : curve_2555 = {(-2,-4),(-2,4),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2556 for 1, 1, 2, 2, -2
theorem curve_2556_packet : curve_2556 = {(-3,-8),(-3,8),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2557 for 1, 1, 2, 2, -1
theorem curve_2557_packet : curve_2557 = ∅ := by decide +kernel
native_square_leading_quartic curve_2558 for 1, 1, 2, 2, 0
theorem curve_2558_packet : curve_2558 = {(-1,0),(0,0),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2559 for 1, 1, 2, 2, 1
theorem curve_2559_packet : curve_2559 = {(-1,-1),(-1,1),(0,-1),(0,1),(4,-19),(4,19)} := by decide +kernel
native_square_leading_quartic curve_2560 for 1, 1, 2, 2, 2
theorem curve_2560_packet : curve_2560 = ∅ := by decide +kernel
native_square_leading_quartic curve_2561 for 1, 2, -2, -2, -2
theorem curve_2561_packet : curve_2561 = ∅ := by decide +kernel
native_square_leading_quartic curve_2562 for 1, 2, -2, -2, -1
theorem curve_2562_packet : curve_2562 = ∅ := by decide +kernel
native_square_leading_quartic curve_2563 for 1, 2, -2, -2, 0
theorem curve_2563_packet : curve_2563 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2564 for 1, 2, -2, -2, 1
theorem curve_2564_packet : curve_2564 = {(-3,-4),(-3,4),(-1,0),(0,-1),(0,1),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2565 for 1, 2, -2, -2, 2
theorem curve_2565_packet : curve_2565 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2566 for 1, 2, -2, -1, -2
theorem curve_2566_packet : curve_2566 = ∅ := by decide +kernel
native_square_leading_quartic curve_2567 for 1, 2, -2, -1, -1
theorem curve_2567_packet : curve_2567 = ∅ := by decide +kernel
native_square_leading_quartic curve_2568 for 1, 2, -2, -1, 0
theorem curve_2568_packet : curve_2568 = {(-4,-10),(-4,10),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2569 for 1, 2, -2, -1, 1
theorem curve_2569_packet : curve_2569 = {(0,-1),(0,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2570 for 1, 2, -2, -1, 2
theorem curve_2570_packet : curve_2570 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2571 for 1, 2, -2, 0, -2
theorem curve_2571_packet : curve_2571 = ∅ := by decide +kernel
native_square_leading_quartic curve_2572 for 1, 2, -2, 0, -1
theorem curve_2572_packet : curve_2572 = {(-5,-18),(-5,18),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2573 for 1, 2, -2, 0, 0
theorem curve_2573_packet : curve_2573 = {(-3,-3),(-3,3),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2574 for 1, 2, -2, 0, 1
theorem curve_2574_packet : curve_2574 = {(0,-1),(0,1),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2575 for 1, 2, -2, 0, 2
theorem curve_2575_packet : curve_2575 = ∅ := by decide +kernel
native_square_leading_quartic curve_2576 for 1, 2, -2, 1, -2
theorem curve_2576_packet : curve_2576 = {(-6,-28),(-6,28),(-3,-2),(-3,2),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2577 for 1, 2, -2, 1, -1
theorem curve_2577_packet : curve_2577 = {(1,-1),(1,1),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2578 for 1, 2, -2, 1, 0
theorem curve_2578_packet : curve_2578 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2579 for 1, 2, -2, 1, 1
theorem curve_2579_packet : curve_2579 = {(0,-1),(0,1),(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2580 for 1, 2, -2, 1, 2
theorem curve_2580_packet : curve_2580 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2581 for 1, 2, -2, 2, -2
theorem curve_2581_packet : curve_2581 = {(-3,-1),(-3,1),(1,-1),(1,1),(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2582 for 1, 2, -2, 2, -1
theorem curve_2582_packet : curve_2582 = ∅ := by decide +kernel
native_square_leading_quartic curve_2583 for 1, 2, -2, 2, 0
theorem curve_2583_packet : curve_2583 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2584 for 1, 2, -2, 2, 1
theorem curve_2584_packet : curve_2584 = {(-3,-2),(-3,2),(0,-1),(0,1),(1,-2),(1,2),(4,-19),(4,19)} := by decide +kernel
native_square_leading_quartic curve_2585 for 1, 2, -2, 2, 2
theorem curve_2585_packet : curve_2585 = ∅ := by decide +kernel
native_square_leading_quartic curve_2586 for 1, 2, -1, -2, -2
theorem curve_2586_packet : curve_2586 = ∅ := by decide +kernel
native_square_leading_quartic curve_2587 for 1, 2, -1, -2, -1
theorem curve_2587_packet : curve_2587 = ∅ := by decide +kernel
native_square_leading_quartic curve_2588 for 1, 2, -1, -2, 0
theorem curve_2588_packet : curve_2588 = {(-2,0),(-1,0),(0,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2589 for 1, 2, -1, -2, 2
theorem curve_2589_packet : curve_2589 = ∅ := by decide +kernel
native_square_leading_quartic curve_2590 for 1, 2, -1, -1, -2
theorem curve_2590_packet : curve_2590 = {(3,-11),(3,11)} := by decide +kernel
native_square_leading_quartic curve_2591 for 1, 2, -1, -1, -1
theorem curve_2591_packet : curve_2591 = {(1,0),(2,-5),(2,5)} := by decide +kernel
native_square_leading_quartic curve_2592 for 1, 2, -1, -1, 0
theorem curve_2592_packet : curve_2592 = {(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2593 for 1, 2, -1, -1, 1
theorem curve_2593_packet : curve_2593 = {(-1,0),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2594 for 1, 2, -1, -1, 2
theorem curve_2594_packet : curve_2594 = {(-2,0),(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2595 for 1, 2, -1, 0, -2
theorem curve_2595_packet : curve_2595 = {(-3,-4),(-3,4),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2596 for 1, 2, -1, 0, -1
theorem curve_2596_packet : curve_2596 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2597 for 1, 2, -1, 0, 0
theorem curve_2597_packet : curve_2597 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2598 for 1, 2, -1, 0, 1
theorem curve_2598_packet : curve_2598 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2599 for 1, 2, -1, 0, 2
theorem curve_2599_packet : curve_2599 = {(-1,0),(1,-2),(1,2)} := by decide +kernel
#print axioms curve_2500_complete
#print axioms curve_2500_packet
#print axioms curve_2501_complete
#print axioms curve_2501_packet
#print axioms curve_2502_complete
#print axioms curve_2502_packet
#print axioms curve_2503_complete
#print axioms curve_2503_packet
#print axioms curve_2504_complete
#print axioms curve_2504_packet
#print axioms curve_2505_complete
#print axioms curve_2505_packet
#print axioms curve_2506_complete
#print axioms curve_2506_packet
#print axioms curve_2507_complete
#print axioms curve_2507_packet
#print axioms curve_2508_complete
#print axioms curve_2508_packet
#print axioms curve_2509_complete
#print axioms curve_2509_packet
#print axioms curve_2510_complete
#print axioms curve_2510_packet
#print axioms curve_2511_complete
#print axioms curve_2511_packet
#print axioms curve_2512_complete
#print axioms curve_2512_packet
#print axioms curve_2513_complete
#print axioms curve_2513_packet
#print axioms curve_2514_complete
#print axioms curve_2514_packet
#print axioms curve_2515_complete
#print axioms curve_2515_packet
#print axioms curve_2516_complete
#print axioms curve_2516_packet
#print axioms curve_2517_complete
#print axioms curve_2517_packet
#print axioms curve_2518_complete
#print axioms curve_2518_packet
#print axioms curve_2519_complete
#print axioms curve_2519_packet
#print axioms curve_2520_complete
#print axioms curve_2520_packet
#print axioms curve_2521_complete
#print axioms curve_2521_packet
#print axioms curve_2522_complete
#print axioms curve_2522_packet
#print axioms curve_2523_complete
#print axioms curve_2523_packet
#print axioms curve_2524_complete
#print axioms curve_2524_packet
#print axioms curve_2525_complete
#print axioms curve_2525_packet
#print axioms curve_2526_complete
#print axioms curve_2526_packet
#print axioms curve_2527_complete
#print axioms curve_2527_packet
#print axioms curve_2528_complete
#print axioms curve_2528_packet
#print axioms curve_2529_complete
#print axioms curve_2529_packet
#print axioms curve_2530_complete
#print axioms curve_2530_packet
#print axioms curve_2531_complete
#print axioms curve_2531_packet
#print axioms curve_2532_complete
#print axioms curve_2532_packet
#print axioms curve_2533_complete
#print axioms curve_2533_packet
#print axioms curve_2534_complete
#print axioms curve_2534_packet
#print axioms curve_2535_complete
#print axioms curve_2535_packet
#print axioms curve_2536_complete
#print axioms curve_2536_packet
#print axioms curve_2537_complete
#print axioms curve_2537_packet
#print axioms curve_2538_complete
#print axioms curve_2538_packet
#print axioms curve_2539_complete
#print axioms curve_2539_packet
#print axioms curve_2540_complete
#print axioms curve_2540_packet
#print axioms curve_2541_complete
#print axioms curve_2541_packet
#print axioms curve_2542_complete
#print axioms curve_2542_packet
#print axioms curve_2543_complete
#print axioms curve_2543_packet
#print axioms curve_2544_complete
#print axioms curve_2544_packet
#print axioms curve_2545_complete
#print axioms curve_2545_packet
#print axioms curve_2546_complete
#print axioms curve_2546_packet
#print axioms curve_2547_complete
#print axioms curve_2547_packet
#print axioms curve_2548_complete
#print axioms curve_2548_packet
#print axioms curve_2549_complete
#print axioms curve_2549_packet
#print axioms curve_2550_complete
#print axioms curve_2550_packet
#print axioms curve_2551_complete
#print axioms curve_2551_packet
#print axioms curve_2552_complete
#print axioms curve_2552_packet
#print axioms curve_2553_complete
#print axioms curve_2553_packet
#print axioms curve_2554_complete
#print axioms curve_2554_packet
#print axioms curve_2555_complete
#print axioms curve_2555_packet
#print axioms curve_2556_complete
#print axioms curve_2556_packet
#print axioms curve_2557_complete
#print axioms curve_2557_packet
#print axioms curve_2558_complete
#print axioms curve_2558_packet
#print axioms curve_2559_complete
#print axioms curve_2559_packet
#print axioms curve_2560_complete
#print axioms curve_2560_packet
#print axioms curve_2561_complete
#print axioms curve_2561_packet
#print axioms curve_2562_complete
#print axioms curve_2562_packet
#print axioms curve_2563_complete
#print axioms curve_2563_packet
#print axioms curve_2564_complete
#print axioms curve_2564_packet
#print axioms curve_2565_complete
#print axioms curve_2565_packet
#print axioms curve_2566_complete
#print axioms curve_2566_packet
#print axioms curve_2567_complete
#print axioms curve_2567_packet
#print axioms curve_2568_complete
#print axioms curve_2568_packet
#print axioms curve_2569_complete
#print axioms curve_2569_packet
#print axioms curve_2570_complete
#print axioms curve_2570_packet
#print axioms curve_2571_complete
#print axioms curve_2571_packet
#print axioms curve_2572_complete
#print axioms curve_2572_packet
#print axioms curve_2573_complete
#print axioms curve_2573_packet
#print axioms curve_2574_complete
#print axioms curve_2574_packet
#print axioms curve_2575_complete
#print axioms curve_2575_packet
#print axioms curve_2576_complete
#print axioms curve_2576_packet
#print axioms curve_2577_complete
#print axioms curve_2577_packet
#print axioms curve_2578_complete
#print axioms curve_2578_packet
#print axioms curve_2579_complete
#print axioms curve_2579_packet
#print axioms curve_2580_complete
#print axioms curve_2580_packet
#print axioms curve_2581_complete
#print axioms curve_2581_packet
#print axioms curve_2582_complete
#print axioms curve_2582_packet
#print axioms curve_2583_complete
#print axioms curve_2583_packet
#print axioms curve_2584_complete
#print axioms curve_2584_packet
#print axioms curve_2585_complete
#print axioms curve_2585_packet
#print axioms curve_2586_complete
#print axioms curve_2586_packet
#print axioms curve_2587_complete
#print axioms curve_2587_packet
#print axioms curve_2588_complete
#print axioms curve_2588_packet
#print axioms curve_2589_complete
#print axioms curve_2589_packet
#print axioms curve_2590_complete
#print axioms curve_2590_packet
#print axioms curve_2591_complete
#print axioms curve_2591_packet
#print axioms curve_2592_complete
#print axioms curve_2592_packet
#print axioms curve_2593_complete
#print axioms curve_2593_packet
#print axioms curve_2594_complete
#print axioms curve_2594_packet
#print axioms curve_2595_complete
#print axioms curve_2595_packet
#print axioms curve_2596_complete
#print axioms curve_2596_packet
#print axioms curve_2597_complete
#print axioms curve_2597_packet
#print axioms curve_2598_complete
#print axioms curve_2598_packet
#print axioms curve_2599_complete
#print axioms curve_2599_packet
end PerfectPower.DivisorSumAtlas
