# Labelled M22/A5 action and global GRS rank status — v0.4

The release now freezes the complete labelled 7,392-state orbital relation matrix, reconstructed from the degree-22 ATLAS generators and an explicit A5 stabilizer. It contains all 152 orbital labels for every ordered vertex pair and agrees with the frozen orbital relabelling. The Q192 seven-route graph extracted from this full relation matrix agrees row-for-row with the independently constructed labelled Q192 neighbor table.

For Q192 the labelled graph has 7,392 vertices, degree 390, and 1,441,440 undirected edges. Its bipartite double cover carries 2,882,880 F_397 edge symbols under the v0.3 Reed-Solomon Tanner construction.

The particular v0.3 edge-slot ordering is not M22-equivariant as an RS evaluation-coordinate assignment, so the 152-dimensional Wilson algebra cannot by itself certify the rank of its full 1,921,920 x 2,882,880 parity-check matrix. The valid theorem is an existence result for the GRS gauge family: nonzero incidence multipliers can be chosen so that a square 1,921,920-column minor is nonzero, giving maximal global check rank 1,921,920 and exact dimension 960,960. This leaves all MDS, distance, stopping, and trapping guarantees unchanged.

The exact rank of the original all-one/Schreier-slot gauge remains open and is not identified with the GRS existence theorem.
