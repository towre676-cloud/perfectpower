import PerfectPower.Tactic.LinearPerturbation
import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.DivisorSumAtlas
set_option maxRecDepth 100000
set_option maxHeartbeats 0
native_square_leading_quartic curve_2600 for 1, 2, -1, 1, -2
theorem curve_2600_packet : curve_2600 = {(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2601 for 1, 2, -1, 1, -1
theorem curve_2601_packet : curve_2601 = ∅ := by decide +kernel
native_square_leading_quartic curve_2602 for 1, 2, -1, 1, 0
theorem curve_2602_packet : curve_2602 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2603 for 1, 2, -1, 1, 1
theorem curve_2603_packet : curve_2603 = {(-3,-4),(-3,4),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2604 for 1, 2, -1, 1, 2
theorem curve_2604_packet : curve_2604 = ∅ := by decide +kernel
native_square_leading_quartic curve_2605 for 1, 2, -1, 2, -2
theorem curve_2605_packet : curve_2605 = ∅ := by decide +kernel
native_square_leading_quartic curve_2606 for 1, 2, -1, 2, -1
theorem curve_2606_packet : curve_2606 = ∅ := by decide +kernel
native_square_leading_quartic curve_2607 for 1, 2, -1, 2, 0
theorem curve_2607_packet : curve_2607 = {(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2608 for 1, 2, -1, 2, 1
theorem curve_2608_packet : curve_2608 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2609 for 1, 2, -1, 2, 2
theorem curve_2609_packet : curve_2609 = ∅ := by decide +kernel
native_square_leading_quartic curve_2610 for 1, 2, 0, -2, -2
theorem curve_2610_packet : curve_2610 = ∅ := by decide +kernel
native_square_leading_quartic curve_2611 for 1, 2, 0, -2, -1
theorem curve_2611_packet : curve_2611 = {(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2612 for 1, 2, 0, -2, 0
theorem curve_2612_packet : curve_2612 = {(-2,-2),(-2,2),(-1,-1),(-1,1),(0,0),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2613 for 1, 2, 0, -2, 1
theorem curve_2613_packet : curve_2613 = {(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2614 for 1, 2, 0, -2, 2
theorem curve_2614_packet : curve_2614 = ∅ := by decide +kernel
native_square_leading_quartic curve_2615 for 1, 2, 0, -1, -2
theorem curve_2615_packet : curve_2615 = {(-2,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2616 for 1, 2, 0, -1, -1
theorem curve_2616_packet : curve_2616 = {(-2,-1),(-2,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2617 for 1, 2, 0, -1, 0
theorem curve_2617_packet : curve_2617 = {(-1,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2618 for 1, 2, 0, -1, 1
theorem curve_2618_packet : curve_2618 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2619 for 1, 2, 0, -1, 2
theorem curve_2619_packet : curve_2619 = {(-2,-2),(-2,2),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2620 for 1, 2, 0, 0, -2
theorem curve_2620_packet : curve_2620 = {(-3,-5),(-3,5),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2621 for 1, 2, 0, 0, -1
theorem curve_2621_packet : curve_2621 = ∅ := by decide +kernel
native_square_leading_quartic curve_2622 for 1, 2, 0, 0, 0
theorem curve_2622_packet : curve_2622 = {(-2,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2623 for 1, 2, 0, 0, 1
theorem curve_2623_packet : curve_2623 = {(-2,-1),(-2,1),(-1,0),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2624 for 1, 2, 0, 0, 2
theorem curve_2624_packet : curve_2624 = {(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2625 for 1, 2, 0, 1, -2
theorem curve_2625_packet : curve_2625 = ∅ := by decide +kernel
native_square_leading_quartic curve_2626 for 1, 2, 0, 1, -1
theorem curve_2626_packet : curve_2626 = ∅ := by decide +kernel
native_square_leading_quartic curve_2627 for 1, 2, 0, 1, 0
theorem curve_2627_packet : curve_2627 = {(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2628 for 1, 2, 0, 1, 1
theorem curve_2628_packet : curve_2628 = {(-3,-5),(-3,5),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2629 for 1, 2, 0, 1, 2
theorem curve_2629_packet : curve_2629 = {(-2,0),(-1,0),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2630 for 1, 2, 0, 2, -2
theorem curve_2630_packet : curve_2630 = ∅ := by decide +kernel
native_square_leading_quartic curve_2631 for 1, 2, 0, 2, -1
theorem curve_2631_packet : curve_2631 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2632 for 1, 2, 0, 2, 0
theorem curve_2632_packet : curve_2632 = {(0,0),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2633 for 1, 2, 0, 2, 1
theorem curve_2633_packet : curve_2633 = {(-4,-11),(-4,11),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2634 for 1, 2, 0, 2, 2
theorem curve_2634_packet : curve_2634 = ∅ := by decide +kernel
native_square_leading_quartic curve_2635 for 1, 2, 1, -2, -2
theorem curve_2635_packet : curve_2635 = {(-1,0),(1,0)} := by decide +kernel
native_square_leading_quartic curve_2636 for 1, 2, 1, -2, -1
theorem curve_2636_packet : curve_2636 = {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2637 for 1, 2, 1, -2, 0
theorem curve_2637_packet : curve_2637 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2638 for 1, 2, 1, -2, 1
theorem curve_2638_packet : curve_2638 = {(-2,-3),(-2,3),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2639 for 1, 2, 1, -2, 2
theorem curve_2639_packet : curve_2639 = {(-1,-2),(-1,2),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2640 for 1, 2, 1, -1, -2
theorem curve_2640_packet : curve_2640 = {(-2,-2),(-2,2),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2641 for 1, 2, 1, -1, -1
theorem curve_2641_packet : curve_2641 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2642 for 1, 2, 1, -1, 0
theorem curve_2642_packet : curve_2642 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2643 for 1, 2, 1, -1, 1
theorem curve_2643_packet : curve_2643 = {(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2644 for 1, 2, 1, -1, 2
theorem curve_2644_packet : curve_2644 = {(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2645 for 1, 2, 1, 0, -2
theorem curve_2645_packet : curve_2645 = ∅ := by decide +kernel
native_square_leading_quartic curve_2646 for 1, 2, 1, 0, -1
theorem curve_2646_packet : curve_2646 = ∅ := by decide +kernel
native_square_leading_quartic curve_2647 for 1, 2, 1, 0, 1
theorem curve_2647_packet : curve_2647 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2648 for 1, 2, 1, 0, 2
theorem curve_2648_packet : curve_2648 = ∅ := by decide +kernel
native_square_leading_quartic curve_2649 for 1, 2, 1, 1, -2
theorem curve_2649_packet : curve_2649 = {(-2,0),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2650 for 1, 2, 1, 1, -1
theorem curve_2650_packet : curve_2650 = {(-2,-1),(-2,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2651 for 1, 2, 1, 1, 0
theorem curve_2651_packet : curve_2651 = {(0,0)} := by decide +kernel
native_square_leading_quartic curve_2652 for 1, 2, 1, 1, 1
theorem curve_2652_packet : curve_2652 = {(-1,0),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2653 for 1, 2, 1, 1, 2
theorem curve_2653_packet : curve_2653 = {(-2,-2),(-2,2),(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2654 for 1, 2, 1, 2, -2
theorem curve_2654_packet : curve_2654 = {(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2655 for 1, 2, 1, 2, -1
theorem curve_2655_packet : curve_2655 = ∅ := by decide +kernel
native_square_leading_quartic curve_2656 for 1, 2, 1, 2, 0
theorem curve_2656_packet : curve_2656 = {(-2,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2657 for 1, 2, 1, 2, 1
theorem curve_2657_packet : curve_2657 = {(-2,-1),(-2,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2658 for 1, 2, 1, 2, 2
theorem curve_2658_packet : curve_2658 = {(-1,0)} := by decide +kernel
native_square_leading_quartic curve_2659 for 1, 2, 2, -2, -2
theorem curve_2659_packet : curve_2659 = {(-3,-7),(-3,7),(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel
native_square_leading_quartic curve_2660 for 1, 2, 2, -2, -1
theorem curve_2660_packet : curve_2660 = ∅ := by decide +kernel
native_square_leading_quartic curve_2661 for 1, 2, 2, -2, 0
theorem curve_2661_packet : curve_2661 = {(0,0),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2662 for 1, 2, 2, -2, 1
theorem curve_2662_packet : curve_2662 = {(-4,-13),(-4,13),(-1,-2),(-1,2),(0,-1),(0,1),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2663 for 1, 2, 2, -2, 2
theorem curve_2663_packet : curve_2663 = ∅ := by decide +kernel
native_square_leading_quartic curve_2664 for 1, 2, 2, -1, -2
theorem curve_2664_packet : curve_2664 = {(-1,0),(2,-6),(2,6)} := by decide +kernel
native_square_leading_quartic curve_2665 for 1, 2, 2, -1, -1
theorem curve_2665_packet : curve_2665 = {(-2,-3),(-2,3),(-1,-1),(-1,1)} := by decide +kernel
native_square_leading_quartic curve_2666 for 1, 2, 2, -1, 0
theorem curve_2666_packet : curve_2666 = {(0,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2667 for 1, 2, 2, -1, 1
theorem curve_2667_packet : curve_2667 = {(-3,-7),(-3,7),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2668 for 1, 2, 2, -1, 2
theorem curve_2668_packet : curve_2668 = {(-1,-2),(-1,2)} := by decide +kernel
native_square_leading_quartic curve_2669 for 1, 2, 2, 0, -2
theorem curve_2669_packet : curve_2669 = ∅ := by decide +kernel
native_square_leading_quartic curve_2670 for 1, 2, 2, 0, -1
theorem curve_2670_packet : curve_2670 = {(-1,0),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2671 for 1, 2, 2, 0, 0
theorem curve_2671_packet : curve_2671 = {(-1,-1),(-1,1),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2672 for 1, 2, 2, 0, 1
theorem curve_2672_packet : curve_2672 = {(-2,-3),(-2,3),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2673 for 1, 2, 2, 0, 2
theorem curve_2673_packet : curve_2673 = ∅ := by decide +kernel
native_square_leading_quartic curve_2674 for 1, 2, 2, 1, -2
theorem curve_2674_packet : curve_2674 = {(-2,-2),(-2,2),(1,-2),(1,2)} := by decide +kernel
native_square_leading_quartic curve_2675 for 1, 2, 2, 1, -1
theorem curve_2675_packet : curve_2675 = ∅ := by decide +kernel
native_square_leading_quartic curve_2676 for 1, 2, 2, 1, 0
theorem curve_2676_packet : curve_2676 = {(-1,0),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2677 for 1, 2, 2, 1, 1
theorem curve_2677_packet : curve_2677 = {(-1,-1),(-1,1),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2678 for 1, 2, 2, 1, 2
theorem curve_2678_packet : curve_2678 = ∅ := by decide +kernel
native_square_leading_quartic curve_2679 for 1, 2, 2, 2, -2
theorem curve_2679_packet : curve_2679 = ∅ := by decide +kernel
native_square_leading_quartic curve_2680 for 1, 2, 2, 2, -1
theorem curve_2680_packet : curve_2680 = ∅ := by decide +kernel
native_square_leading_quartic curve_2681 for 1, 2, 2, 2, 0
theorem curve_2681_packet : curve_2681 = {(-2,-2),(-2,2),(0,0)} := by decide +kernel
native_square_leading_quartic curve_2682 for 1, 2, 2, 2, 1
theorem curve_2682_packet : curve_2682 = {(-1,0),(0,-1),(0,1)} := by decide +kernel
native_square_leading_quartic curve_2683 for 1, 2, 2, 2, 2
theorem curve_2683_packet : curve_2683 = {(-1,-1),(-1,1),(1,-3),(1,3)} := by decide +kernel
native_square_leading_quartic curve_2684 for 1, 1, 1, 1, -199
theorem curve_2684_packet : curve_2684 = {(7,-51),(7,51)} := by decide +kernel
native_square_leading_quartic curve_2685 for 1, 1, 1, 1, -198
theorem curve_2685_packet : curve_2685 = ∅ := by decide +kernel
native_square_leading_quartic curve_2686 for 1, 1, 1, 1, -197
theorem curve_2686_packet : curve_2686 = ∅ := by decide +kernel
native_square_leading_quartic curve_2687 for 1, 1, 1, 1, -196
theorem curve_2687_packet : curve_2687 = {(-5,-18),(-5,18),(4,-12),(4,12)} := by decide +kernel
native_square_leading_quartic curve_2688 for 1, 1, 1, 1, -195
theorem curve_2688_packet : curve_2688 = {(-11,-115),(-11,115),(-4,-3),(-4,3)} := by decide +kernel
native_square_leading_quartic curve_2689 for 1, 1, 1, 1, -194
theorem curve_2689_packet : curve_2689 = ∅ := by decide +kernel
native_square_leading_quartic curve_2690 for 1, 1, 1, 1, -193
theorem curve_2690_packet : curve_2690 = ∅ := by decide +kernel
native_square_leading_quartic curve_2691 for 1, 1, 1, 1, -192
theorem curve_2691_packet : curve_2691 = ∅ := by decide +kernel
native_square_leading_quartic curve_2692 for 1, 1, 1, 1, -191
theorem curve_2692_packet : curve_2692 = {(8,-67),(8,67)} := by decide +kernel
native_square_leading_quartic curve_2693 for 1, 1, 1, 1, -190
theorem curve_2693_packet : curve_2693 = ∅ := by decide +kernel
native_square_leading_quartic curve_2694 for 1, 1, 1, 1, -189
theorem curve_2694_packet : curve_2694 = ∅ := by decide +kernel
native_square_leading_quartic curve_2695 for 1, 1, 1, 1, -188
theorem curve_2695_packet : curve_2695 = {(-4,-4),(-4,4)} := by decide +kernel
native_square_leading_quartic curve_2696 for 1, 1, 1, 1, -187
theorem curve_2696_packet : curve_2696 = ∅ := by decide +kernel
native_square_leading_quartic curve_2697 for 1, 1, 1, 1, -186
theorem curve_2697_packet : curve_2697 = ∅ := by decide +kernel
native_square_leading_quartic curve_2698 for 1, 1, 1, 1, -185
theorem curve_2698_packet : curve_2698 = {(6,-37),(6,37)} := by decide +kernel
native_square_leading_quartic curve_2699 for 1, 1, 1, 1, -184
theorem curve_2699_packet : curve_2699 = ∅ := by decide +kernel
#print axioms curve_2600_complete
#print axioms curve_2600_packet
#print axioms curve_2601_complete
#print axioms curve_2601_packet
#print axioms curve_2602_complete
#print axioms curve_2602_packet
#print axioms curve_2603_complete
#print axioms curve_2603_packet
#print axioms curve_2604_complete
#print axioms curve_2604_packet
#print axioms curve_2605_complete
#print axioms curve_2605_packet
#print axioms curve_2606_complete
#print axioms curve_2606_packet
#print axioms curve_2607_complete
#print axioms curve_2607_packet
#print axioms curve_2608_complete
#print axioms curve_2608_packet
#print axioms curve_2609_complete
#print axioms curve_2609_packet
#print axioms curve_2610_complete
#print axioms curve_2610_packet
#print axioms curve_2611_complete
#print axioms curve_2611_packet
#print axioms curve_2612_complete
#print axioms curve_2612_packet
#print axioms curve_2613_complete
#print axioms curve_2613_packet
#print axioms curve_2614_complete
#print axioms curve_2614_packet
#print axioms curve_2615_complete
#print axioms curve_2615_packet
#print axioms curve_2616_complete
#print axioms curve_2616_packet
#print axioms curve_2617_complete
#print axioms curve_2617_packet
#print axioms curve_2618_complete
#print axioms curve_2618_packet
#print axioms curve_2619_complete
#print axioms curve_2619_packet
#print axioms curve_2620_complete
#print axioms curve_2620_packet
#print axioms curve_2621_complete
#print axioms curve_2621_packet
#print axioms curve_2622_complete
#print axioms curve_2622_packet
#print axioms curve_2623_complete
#print axioms curve_2623_packet
#print axioms curve_2624_complete
#print axioms curve_2624_packet
#print axioms curve_2625_complete
#print axioms curve_2625_packet
#print axioms curve_2626_complete
#print axioms curve_2626_packet
#print axioms curve_2627_complete
#print axioms curve_2627_packet
#print axioms curve_2628_complete
#print axioms curve_2628_packet
#print axioms curve_2629_complete
#print axioms curve_2629_packet
#print axioms curve_2630_complete
#print axioms curve_2630_packet
#print axioms curve_2631_complete
#print axioms curve_2631_packet
#print axioms curve_2632_complete
#print axioms curve_2632_packet
#print axioms curve_2633_complete
#print axioms curve_2633_packet
#print axioms curve_2634_complete
#print axioms curve_2634_packet
#print axioms curve_2635_complete
#print axioms curve_2635_packet
#print axioms curve_2636_complete
#print axioms curve_2636_packet
#print axioms curve_2637_complete
#print axioms curve_2637_packet
#print axioms curve_2638_complete
#print axioms curve_2638_packet
#print axioms curve_2639_complete
#print axioms curve_2639_packet
#print axioms curve_2640_complete
#print axioms curve_2640_packet
#print axioms curve_2641_complete
#print axioms curve_2641_packet
#print axioms curve_2642_complete
#print axioms curve_2642_packet
#print axioms curve_2643_complete
#print axioms curve_2643_packet
#print axioms curve_2644_complete
#print axioms curve_2644_packet
#print axioms curve_2645_complete
#print axioms curve_2645_packet
#print axioms curve_2646_complete
#print axioms curve_2646_packet
#print axioms curve_2647_complete
#print axioms curve_2647_packet
#print axioms curve_2648_complete
#print axioms curve_2648_packet
#print axioms curve_2649_complete
#print axioms curve_2649_packet
#print axioms curve_2650_complete
#print axioms curve_2650_packet
#print axioms curve_2651_complete
#print axioms curve_2651_packet
#print axioms curve_2652_complete
#print axioms curve_2652_packet
#print axioms curve_2653_complete
#print axioms curve_2653_packet
#print axioms curve_2654_complete
#print axioms curve_2654_packet
#print axioms curve_2655_complete
#print axioms curve_2655_packet
#print axioms curve_2656_complete
#print axioms curve_2656_packet
#print axioms curve_2657_complete
#print axioms curve_2657_packet
#print axioms curve_2658_complete
#print axioms curve_2658_packet
#print axioms curve_2659_complete
#print axioms curve_2659_packet
#print axioms curve_2660_complete
#print axioms curve_2660_packet
#print axioms curve_2661_complete
#print axioms curve_2661_packet
#print axioms curve_2662_complete
#print axioms curve_2662_packet
#print axioms curve_2663_complete
#print axioms curve_2663_packet
#print axioms curve_2664_complete
#print axioms curve_2664_packet
#print axioms curve_2665_complete
#print axioms curve_2665_packet
#print axioms curve_2666_complete
#print axioms curve_2666_packet
#print axioms curve_2667_complete
#print axioms curve_2667_packet
#print axioms curve_2668_complete
#print axioms curve_2668_packet
#print axioms curve_2669_complete
#print axioms curve_2669_packet
#print axioms curve_2670_complete
#print axioms curve_2670_packet
#print axioms curve_2671_complete
#print axioms curve_2671_packet
#print axioms curve_2672_complete
#print axioms curve_2672_packet
#print axioms curve_2673_complete
#print axioms curve_2673_packet
#print axioms curve_2674_complete
#print axioms curve_2674_packet
#print axioms curve_2675_complete
#print axioms curve_2675_packet
#print axioms curve_2676_complete
#print axioms curve_2676_packet
#print axioms curve_2677_complete
#print axioms curve_2677_packet
#print axioms curve_2678_complete
#print axioms curve_2678_packet
#print axioms curve_2679_complete
#print axioms curve_2679_packet
#print axioms curve_2680_complete
#print axioms curve_2680_packet
#print axioms curve_2681_complete
#print axioms curve_2681_packet
#print axioms curve_2682_complete
#print axioms curve_2682_packet
#print axioms curve_2683_complete
#print axioms curve_2683_packet
#print axioms curve_2684_complete
#print axioms curve_2684_packet
#print axioms curve_2685_complete
#print axioms curve_2685_packet
#print axioms curve_2686_complete
#print axioms curve_2686_packet
#print axioms curve_2687_complete
#print axioms curve_2687_packet
#print axioms curve_2688_complete
#print axioms curve_2688_packet
#print axioms curve_2689_complete
#print axioms curve_2689_packet
#print axioms curve_2690_complete
#print axioms curve_2690_packet
#print axioms curve_2691_complete
#print axioms curve_2691_packet
#print axioms curve_2692_complete
#print axioms curve_2692_packet
#print axioms curve_2693_complete
#print axioms curve_2693_packet
#print axioms curve_2694_complete
#print axioms curve_2694_packet
#print axioms curve_2695_complete
#print axioms curve_2695_packet
#print axioms curve_2696_complete
#print axioms curve_2696_packet
#print axioms curve_2697_complete
#print axioms curve_2697_packet
#print axioms curve_2698_complete
#print axioms curve_2698_packet
#print axioms curve_2699_complete
#print axioms curve_2699_packet
end PerfectPower.DivisorSumAtlas
