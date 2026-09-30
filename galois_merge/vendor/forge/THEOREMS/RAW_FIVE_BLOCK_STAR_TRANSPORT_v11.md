# Raw five-block star-transport theorem — Forge v0.11

For a frozen primitive Wilson relation object `Q`, let

`L_Q = [L_E | L_RX | L_RY | L_LX | L_LY]`

be its actual five-context relation matrix over `F_p`, `p=1,000,003`, with star source `V=V_+ + V_-`.  A star-compatible transport from `Q` to `Q'` is a triple `(S,T_+,T_-)` satisfying, for all five contexts,

`S L_i(Q) = L_i(Q') diag(T_+,T_-)`.

This equation is linear in all entries of `S,T_+,T_-`.  Isomorphism is certified when all three matrices are invertible.  Because row-basis changes and independent changes of basis on `V_+` and `V_-` merely conjugate/reparameterize this system, existence of an invertible solution is exactly invariant under the nuisance group

`GL(L) x GL(V_+) x GL(V_-)`.

## Frozen positive component

The four held species-3 transports

`Q7,Q57,Q58,Q107 -> Q6`

are solved directly on the stored raw `L_Q` matrices.  Each linear transport system has nullity `486`.  In every case Forge freezes a witness with

`rank(S)=5`, `rank(T_+)=11`, `rank(T_-)=30`

and zero residual in all five block equations.  No context-rank packet, canonical factor, or projective semi-invariant is used to obtain these witnesses.

The release additionally applies independent random invertible changes of row basis, plus-star basis and minus-star basis to both source and target carriers.  Two trials per positive pair, eight trials total, again recover full-rank transport witnesses.  This is a computational gauge audit of the exact change-of-basis theorem, not the source of the theorem.

## Learning interpretation

The prior v0.10 experiment asked a numerical student to learn from an 11-coordinate invariant compression of `L_Q`.  v0.11 removes that approximation at the nuisance-group boundary.  The first layer is now the exact star-transport quotient above.  Trainable/contrastive machinery is applied only after this quotient.  The characteristic-zero canonical-factor/projective-semi-invariant certificates are not input features: they remain negative supervision for the known collisions `Q2/Q35` and `Q159/Q160`.

This is deliberately stronger than a coordinate MLP trained with random basis augmentation.  Since the nuisance action can be quotiented by exact linear algebra, approximate learned invariance would discard known mathematics.
