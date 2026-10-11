# BLAST mining with the newer PerfectPower machinery

This release starts at PerfectPower main `499f2dd87eeb636818c6b9c8b3d191ece932c199`, which already includes the October 10 polynomial atlas. It adds a source-replayed batch workflow, complete compressed HSP populations, exact overlapping motif models, assignment obstructions and triangle-filled similarity topology. Run `python -m perfectpower.blast_cli --help` after installing the package. The offline explorer is `web/blast-mining/index.html`.

## Repository review and integration choices

The review included PerfectPower main and its published model-counting branches, DynaComp's default branch at `ce8a0e57fc0d845870b30271d589a652f969c59f`, and the tau_crystal README. DynaComp now has certified native execution and reusable external workload pilots. Its rational generating-function and binary64 kernels are already distributed in PerfectPower. This release uses PerfectPower's exact rational-series and source-bound resolvent interfaces; it does not copy DynaComp's numerical executor or claim that its rounding guarantees certify biological computations. tau_crystal supplies a useful receipt discipline; its unrelated research gates are not imported.

The new graph layer from `e9deb64` provides separator counting, original-coordinate population queries, matching/cover/Hall certificates, integral flow/cut certificates and cellular homology. Those have direct finite combinatorial meanings for supplied HSPs. The native CNF implementation, wrapper and regression tests are imported unchanged from the published research branch at `d4dc8dc6fa5ba5f6c6f11e81ccd766e1d3bdf3cc`. The later local structural-counting work was inspected but is not bundled because that commit was not on a published branch during this review. Native execution is optional and requires a C++17 compiler and Boost headers. The separator implementation and all motif/graph analyses remain Python standard-library code. Both source and installed-wheel native assets are retained.

PerfectPower's elliptic descent, Weil projectors, polygon obstacle routing and geometry libraries remain available in the package. They have no established direct interpretation for BLAST sequences, so this release does not manufacture a biological meaning for them. The existing polynomial alignment families, PSG jets and moments, parameter regions, SOE quotients, conserved-motif alignments, semiring transports, Hodge decomposition and strand connection machinery remain available through the earlier atlas. These are complementary operations with distinct populations and acceptance rules.

## Complete HSP chains without enumerating every path

`ChainIndex` takes one query/subject/orientation group. Each HSP is a vertex. A directed edge requires nonoverlap and increasing query and subject coordinates in their oriented axes. Optional maximum spacing and frame-congruence constraints remove edges. Fragment spacing is not an affine gap penalty. The source record indices remain recoverable even when coordinate sorting changes their order.

For vertex i, let cᵢ be its query span and let children(i) be its permitted successors. The finite suffix polynomial obeys

\[F_i(u,v)=u v^{c_i}\left(1+\sum_{j\in\mathrm{children}(i)}F_j(u,v)\right).\]

Its coefficients count paths by number of HSPs and union query coverage. Summing the suffix polynomials counts every nonempty path once by its first vertex. A coverage threshold filters coefficients exactly. A separate max-plus recurrence returns an optimal additive feature score, one representative and the number of tied optimal paths. Prefix-block counts implement rank/select without listing all paths. The address order is declared by the stored DAG order and successors, not by score.

An independent scaling test uses 80 ordered single-base HSPs. It checks the exact count `1208925819614629174706175`, which is 2⁸⁰−1, and rank/select round trips at widely separated addresses. This is a finite compression example, not a BLAST throughput benchmark. Work and carrier limits reject construction rather than returning incomplete counts.

## Coherent selections as factors and CNF

`selection_model` creates a binary original variable for every supplied HSP row. Two rows conflict if their intervals overlap, their order crosses, or their orientations differ. A conflict factor excludes only the assignment (1,1). Its equivalent CNF clause is ¬xᵢ∨¬xⱼ. The optional nonempty clause is x₁∨⋯∨xₙ. No auxiliary variables introduce extension multiplicity.

The separator backend omits a dense nonempty factor and subtracts the unique empty assignment. Its selection addresses skip that first lexicographic assignment. Marginals and conditioned counts subtract it only when the conditioning still permits it. The native backend compiles the same clauses and counts original-variable assignments directly. Conditional counts, inclusion counts, uniform sampling by integer rank, and rank/select retain the same original HSP variables across both backends.

Without spacing constraints, compatible subsets sorted along the query are exactly chains. This gives a useful independent bridge between DAG counting and graph/CNF counting. Pairwise maximum spacing constraints would incorrectly reject some legal paths, so selection populations intentionally do not pretend to implement those constraints. Duplicate HSP rows are distinct candidates; they can represent the same biological coordinates and conflict through overlap.

## Motifs anywhere, including overlap

The earlier motif count machine counted words ending in a motif. `motif_series` instead constructs a prefix automaton with a seen bit for occurrence anywhere. Under explicitly supplied IID letter probabilities, a rational transition matrix A describes the state distribution. A second augmented matrix accumulates rewards equal to the number of motifs completed by each transition. Consequently `A`, `AA` in `AAA` contribute five total occurrences, and overlapping starts are retained.

For seed s and readout h, the formal series is h(I−zA)⁻¹s. The existing witness-resolvent engine supplies vector polynomial identities `(I−zA)V = D s` and normalized output fractions. Replay checks identities against the source operator rather than guessing a recurrence from a prefix. The motif adapter also rebuilds the operator from the motifs and probabilities, so a valid unrelated resolvent cannot stand in for the requested model.

The rational-series coefficient engine now normalizes the constant denominator after each Bostan–Mori parity reduction. This preserves the rational function and avoids artificial scalar growth caused by repeated squaring. It retains the explicit bit budget. Tests compare the 483-letter two-motif probability with an independent direct prefix DP and compare short overlapping-motif distributions with every alphabet word. Modular high-index access requires rational denominators to be units modulo the chosen modulus.

These models are literal IID null models, not evolutionary likelihoods, composition-adjusted BLAST scores or BLAST E-values. Batch motif analysis currently uses A/C/G/T. The standalone motif command supports the existing bounded custom alphabet interface. Literal ambiguity symbols are not expanded.

## Assignment and topology

Maximum distinct-subject assignment uses the existing matching implementation. A matching and equal-size vertex cover certify maximum cardinality. A deficient Hall set identifies a set of queries with fewer available subjects. The batch workflow includes FASTA queries with no qualifying hit in the carrier, avoiding a misleading diagnosis that silently drops them. `capacity_assignment` uses integral max flow and an equal-value cut when a caller explicitly allows subject reuse. Capacities are user constraints, not inferred copy numbers. Neither adapter establishes orthology or optimizes alignment score.

Similarity edges still require qualifying individual HSPs in both directions and consistent strand evidence. Exact threshold snapshots now attach a face to every triangle and compute cellular homology using the new graph library. Equal-weight edges enter together. H₀ and H₁ agree with the full clique complex; H₂ is only for the 2-skeleton because tetrahedral cells are absent. Snapshots are not persistence pairings, and cycles in a supplied similarity complex do not establish biological events.

## Reproducible public-data result

The retained inputs are human `NM_000207.3`, predicted Dromiciops `XM_043971863.1`, and mouse insulin I `NM_008386.4`. The first two were preserved from the earlier release; the mouse record was retrieved from NCBI EFetch and its returned versioned identifier checked. The three-record all-against-all BLAST+ 2.12.0 run produced 89 HSPs, including self hits and reverse-strand fragments. Every traceback is replayed before filtering. All three raw input/output hashes are retained.

The conservative view uses E≤0.001, identity≥1/2, individual query and subject coverage≥1/5, and excludes equal-identifier self hits. It retains six cross-record HSPs, one in each directed pair, and every pair population has count one. The permissive diagnostic view uses E≤100 and no minimum individual coverage. It retains 58 cross-record candidates and pair selection counts 14, 11, 14, 53, 11 and 53 in sorted pair order. Those weak fragments are exploratory candidates, without a significance claim. For every pair in both views, DAG, separator and native counts agree. Native rank-selected witnesses also round-trip through separator addresses.

The receipts are `receipts/blast/mining_v2.json`, `mining_exploratory.json`, `mining_crosscheck.json` and `motif_overlap_series.json`. The explorer's filter changes the displayed hit table only. Exact populations always correspond to the recorded thresholds. Counts exceeding JavaScript's safe integer range are displayed as decimal strings; downloading the report's receipt preserves the original JSON integers.

## Run and verify

```bash
python -m pip install .
make blast-mining-test
make blast-mining
python -m perfectpower.blast_cli mine examples/blast/insulin_family_blast.tsv \
  --query-fasta examples/blast/insulin_family.fasta \
  --subject-fasta examples/blast/insulin_family.fasta \
  --minimum-coverage 1/5 --motif ACG --motif CGT --output mining.json
python -m perfectpower.blast_cli verify-mining mining.json \
  examples/blast/insulin_family_blast.tsv \
  --query-fasta examples/blast/insulin_family.fasta \
  --subject-fasta examples/blast/insulin_family.fasta
python -m perfectpower.blast_cli mining-report mining.json --output mining.html
python -m perfectpower.blast_cli motif AA --alphabet AC --length 1000000 \
  --modulus 101 --output motif.json
```

`python python/develop_blast_mining.py --run-blast --native-check` explicitly reruns installed BLAST+. Omit `--run-blast` to regenerate receipts offline from retained output. Set `PYTHONPATH=python` when running directly from a checkout. A nonstandard Boost installation can be supplied through `PP_CNF_BOOST_INCLUDE`.

The local validation recorded in `receipts/blast/mining_validation.json` passes 108 focused Python tests and 1,000 native C++ formula comparisons with exhaustive counting. An installed wheel replays the batch receipt, renders the bundled report template and returns native count 47 for the earlier 17-HSP input. Both conservative and permissive reports pass desktop/mobile browser checks, and the downloaded JSON matches the exact source receipt.

The new adapters are checked by executable tests and source replay. The earlier Lean build receipts remain unchanged and retain their original scope; this release adds no claim that Lean proves the Python DAG, motif, separator or native counting implementations correct. Full historical release verification and a fresh Lean rebuild were not performed. CI contains reproduction checks, but local execution is the evidence reported here. Work-limit statuses are explicit per optional bounded analysis and never interpreted as zero population.

The next scientific step is an annotated, larger gene-family benchmark with independently labelled paralog/ortholog relationships and a predeclared evaluation target. The next formal step is to prove the DAG suffix-polynomial recurrence against a finite path language and certify the source adapters. Arithmetic machinery can make candidate analysis exact; it does not itself supply missing annotations or whole-database recall.

## Primary references

NCBI BLAST+ custom output and BTOP: https://www.ncbi.nlm.nih.gov/books/NBK569862/ . NCBI Common URL API: https://blast.ncbi.nlm.nih.gov/doc/blast-help/urlapi.html . Versioned mouse record: https://www.ncbi.nlm.nih.gov/nuccore/NM_008386.4 . Exact imported native source: https://github.com/towre676-cloud/perfectpower/tree/d4dc8dc6fa5ba5f6c6f11e81ccd766e1d3bdf3cc/native/model_counting . DynaComp reviewed source: https://github.com/towre676-cloud/DynaComp/tree/ce8a0e57fc0d845870b30271d589a652f969c59f .
