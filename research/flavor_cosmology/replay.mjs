// Regenerates the scientific examples and retains the original validation record.
// Run tests separately; replay does not repeat the historical validation itself.
import {pathTensionBound,biasEnvelope,thermalToy,classicalScalingScreen} from "./cp_wall_tools.mjs";
const examples={
  path:pathTensionBound([0,0,4,-8,4],[[-1,2]]),
  bias:biasEnvelope([[1,0,0],[0,2,0],[0,0,3]],[2,2,2],[[1,1,0],[2,2,0]],1),
  zero:biasEnvelope([[1,0],[0,1]],[2,2],[[1,1]],1),
  thermal:thermalToy(2,9,3),
  scaling:classicalScalingScreen(3,1,10)
};
const receipt={
  "schema": "pp-flavor-cosmology/1",
  "base_commit": "a5d0f04aa6c8f666dfd9428747abbbdf3811fe50",
  "coordination": {
    "other_flavor_session": "Exact quartic algebra, mechanisms, matching/running, quantum/higher operators, vacuum/physical-parameter tests and publication.",
    "this_session": "Conditional cosmological consequences and rational wall/bias interfaces.",
    "visibility": "Published commits and user reports only; no live view of other sessions."
  },
  "validation": {
    "checks": 104,
    "status": "passed",
    "arithmetic": "BigInt rational",
    "scope": "module checks only; no full repository suite or physics matching",
    "runtime": "Available V8 functions runtime; source exports and test import removed only for evaluation.",
    "not_run": [
      "Node CLI",
      "Python",
      "Lean",
      "full repository suite"
    ]
  },
  "scientific_scope": "Conditional mathematical adapters and toy examples; no actual repository wall tension, matched bias response or finite-temperature potential.",
  "sources": [
    "https://arxiv.org/abs/2212.00039",
    "https://arxiv.org/abs/2212.03882",
    "https://arxiv.org/abs/1703.02576",
    "https://arxiv.org/abs/2504.07902"
  ]
};
receipt.examples=examples;
console.log(JSON.stringify(receipt,null,2));
