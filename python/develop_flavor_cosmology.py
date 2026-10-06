"""Consume published vacua; construct compact radial tree-action trial bubbles.

No stationarity search, retuning, thermal potential or flavor matching is done.
"""
from pathlib import Path
import hashlib
import json
from fractions import Fraction as F
import numpy as np
from perfectpower.flavor_decay import *
from perfectpower.nonet_potential import joint_higgs
from perfectpower.nonet_mediators import mediation_plan, currents
from valentiner_adjoint_quartics import quartic_projectors, adjoint
from develop_valentiner_frames import group_closure, generators, numeric

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/"receipts/flavor_cosmology/tree_decay.json"
BASE = "22e4edf06dbdeea0f9245dbb06669ed57b7906fc"


def build():
    inputs = ["receipts/m22_interactions/valentiner_nonet_joint.json",
              "receipts/m22_interactions/flavor_frontier.json",
              "receipts/m22_interactions/valentiner_cp.json"]
    provenance = {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in inputs}
    baseline, frontier = [json.loads((ROOT/p).read_text()) for p in inputs[:2]]
    comparison = frontier["vacuum_comparison"]
    lower = comparison["stable_CP_conserving_competitor"]
    false = np.array(baseline["canonical_coordinates"])
    true = np.array(lower["coordinates"])
    c = np.array(baseline["coefficients"])
    portals = np.array(baseline["Higgs_portals"])
    mu2, lam = baseline["Higgs_mu2"], baseline["Higgs_lambda"]
    P, tensor_check = quartic_projectors()
    P = np.array(P)
    fun = lambda z:joint_higgs(z,c,P,portals,mu2,lam)
    model = BinaryRationalNonet(P,c,portals,mu2,lam)
    # Endpoint orbit selection changes no scalar couplings or stationary points.
    # Enumerate only already justified unitary family and sector sign actions.
    group = group_closure(generators())[0]
    orbit = []
    for gi, g in enumerate(group):
        D = adjoint(numeric(g))
        rotated = true.copy()
        rotated[2:10] = D@true[2:10]
        rotated[12:20] = D@true[12:20]
        for su in [-1,1]:
            for sd in [-1,1]:
                z = rotated.copy()
                z[:10] *= su
                z[10:20] *= sd
                orbit.append((float(np.sum((z-false)**2)),gi,su,sd,z))
    orbit.sort(key=lambda row:row[:4])
    selected = orbit[:4]
    selected.append((float(np.sum((true-false)**2)),0,1,1,true))
    candidates = []
    for rank,(distance,gi,su,sd,z) in enumerate(selected):
        W = model.line_excess(false,z)
        path = [[rat(a),rat(b)-rat(a)] for a,b in zip(false,z)]
        polynomials = compact_bubble_polynomials(W,path)
        action = optimize_shape(polynomials)
        errors = [abs(float(evaluate(W,F(j,32)))-(fun(false+(j/32)*(z-false))[0]-fun(false)[0]))
                  for j in range(33)]
        value, gradient = fun(z)
        candidates.append({"rank":rank,"orbit_element":gi,"sector_signs":[su,sd],
          "source_distance_squared":distance,"endpoint":z.tolist(),
          "endpoint_energy":value,"endpoint_gradient_norm":float(np.linalg.norm(gradient)),
          "path_potential_coefficients":list(map(str,W)),
          "potential_replay_maximum_error":max(errors),
          "false_endpoint_path_derivative":str(evaluate(derivative(W),0)),
          "lower_endpoint_path_derivative":str(evaluate(derivative(W),1)),
          "radial_polynomials":{k:list(map(str,polynomials[k])) for k in
                                ["kinetic_polynomial","potential_polynomial"]},
          "bubble":action})
    best = min(candidates,key=lambda row:row["bubble"]["action_divided_by_pi_squared"])
    z = np.array(best["endpoint"])
    W = list(map(F,best["path_potential_coefficients"]))
    plan = mediation_plan(c,P,mass=10.,finite_only=True)
    source_path = [[rat(a),rat(b)-rat(a)] for a,b in zip(false,z)]
    lifted = model.lifted_path(false,z,plan)
    source_poly = compact_bubble_polynomials(W,source_path)
    lifted_poly = compact_bubble_polynomials(W,lifted)
    increase = [b-a for a,b in zip(source_poly["kinetic_polynomial"],lifted_poly["kinetic_polynomial"])]
    assert all(v >= 0 for v in increase)
    fixed_shape = best["bubble"]["shape"]
    lift_fixed = bubble_at_shape(lifted_poly,fixed_shape)
    lift_best = optimize_shape(lifted_poly)
    mass_scan = []
    for mass in [5,10,20,100]:
        factor = F(100,mass*mass)
        poly = dict(source_poly)
        poly["kinetic_polynomial"] = [a+factor*b for a,b in zip(source_poly["kinetic_polynomial"],increase)]
        b = optimize_shape(poly)
        mass_scan.append({"mediator_mass":mass,"kinetic_increase_factor":str(factor),
          "bubble":b,"ratio_to_source_candidate":float(b["action_divided_by_pi_squared"]/best["bubble"]["action_divided_by_pi_squared"])})
    # Check actual currents against the exact lifted-coordinate polynomials.
    lift_errors = []
    completion_square_errors = []
    for j in range(17):
        q = F(j,16)
        point = false+float(q)*(z-false)
        J,_ = currents(point[:20],plan,P)
        S = np.array([float(evaluate(p,q)) for p in lifted[21:]])
        lift_errors.append(float(np.max(abs(S+J/plan["mass"]**2))))
        completion_square_errors.append(float(np.dot(S+J/plan["mass"]**2,S+J/plan["mass"]**2)*plan["mass"]**2/2))
    cp = np.array(baseline["CP_adjoint_matrix"])
    partner = false.copy()
    partner[2:10] = cp@false[2:10]
    partner[12:20] = cp@false[12:20]
    sample_cp_error = max(abs(fun(point)[0]-fun(np.r_[point[:2],cp@point[2:10],point[10:12],cp@point[12:20],point[20]])[0])
                          for point in [false,z,(false+z)/2])
    return {
      "schema":"pp-flavor-tree-decay/1","baseline_commit":BASE,"input_sha256":provenance,
      "scope":"Tree action trial-bubble calculation on the binary-rational realization of the retained numerical tensors and vacuum coordinates. Exact radial integrals; numerical endpoint stationarity and shape search. No certified physical bounce, lifetime, loop-corrected action or thermal transition.",
      "published_vacuum_status":{"false_energy":fun(false)[0],"lower_energy":fun(true)[0],
        "energy_gap":fun(false)[0]-fun(true)[0],"false_gradient_norm":float(np.linalg.norm(fun(false)[1])),
        "lower_gradient_norm":float(np.linalg.norm(fun(true)[1])),
        "false_minimum_hessian":min(baseline["scalar_hessian_eigenvalues"]),
        "lower_minimum_hessian":lower["full_Hessian_minimum"],
        "lower_J":lower["J"],"global_winner_classified":False},
      "symmetry_orbit_path_search":{"endpoint_images":len(orbit),"retained_nearest_images":4,
        "additional_original_endpoint":True,"selection_scope":"Nearest endpoint images and the original endpoint only; neither all field paths nor global bubble shapes are exhausted."},
      "candidates":candidates,"best_candidate_rank":best["rank"],
      "completion":{"mediator_coordinates":len(lifted)-21,"total_canonical_coordinates":len(lifted),
        "path_coefficients":[list(map(str,p)) for p in lifted],
        "kinetic_increase_polynomial":list(map(str,increase)),
        "fixed_source_shape_bubble":lift_fixed,"optimized_lifted_shape_bubble":lift_best,
        "fixed_shape_action_ratio":str(lift_fixed["action_divided_by_pi_squared"]/best["bubble"]["action_divided_by_pi_squared"]),
        "mass_scan":mass_scan,"current_replay_maximum_error":max(lift_errors),
        "positive_square_replay_maximum":max(completion_square_errors),
        "matching_scope":"S(q)=-J(x(q))/M^2 throughout the profile. Scalar potential equals the source potential; induced kinetic energy is retained. Genuine mediator quantum corrections are omitted."},
      "CP_pair":{"energy_difference":fun(partner)[0]-fun(false)[0],
        "sample_full_potential_CP_error":sample_cp_error,
        "interpretation":"The two false CP branches remain energy-degenerate. Decay to a lower CP-conserving basin does not select a surviving weak-CP sign."},
      "quantum_limit":frontier["quantum_vacuum_feedback"],
      "thermal_input":{"minimum_leading_thermal_hessian":min(frontier["leading_high_temperature_mass_eigenvalues"]),
        "scope":frontier["thermal_scope"]},
      "tensor_numerical_checks":tensor_check,
      "action_normalization":"For q=1 in the core and q=1-3t^2+2t^3 in a shell of width R: S4=2*pi^2*(T(L)*R^2+U(L)*R^4), Rcrit^2=-T/(2U), Smax/pi^2=-T^2/(2U). The physical least bounce is below the escape-path minimax only under the stated false-vacuum/mountain-pass hypotheses.",
      "lifetime_not_calculated":"A dimensionful normalization, fluctuation prefactor, valid quantum action and cosmological history are required."
    }


def main():
    answer = build()
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(answer,indent=2,sort_keys=True,default=str)+"\n")
    best = answer["candidates"][answer["best_candidate_rank"]]
    print(json.dumps({"energy_gap":answer["published_vacuum_status"]["energy_gap"],
      "best_source_trial_action":best["bubble"]["dimensionless_action"],
      "mediator_trial_action":answer["completion"]["optimized_lifted_shape_bubble"]["dimensionless_action"],
      "mass_scan":[[r["mediator_mass"],r["ratio_to_source_candidate"]] for r in answer["completion"]["mass_scan"]],
      "scope":answer["scope"]},indent=2))


if __name__ == "__main__":
    main()
