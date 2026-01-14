----------------------------- MODULE BlockDag -----------------------------

(**************************************************************************************)
(* In this specification we define notions on DAGs useful for DAG-based consensus     *)
(* protocols (which build DAGs of blocks)                                             *)
(**************************************************************************************)

EXTENDS Digraph, FiniteSets, Sequences, Integers

CONSTANTS
    N \* The set of all nodes
,   R \* The set of rounds
,   Leader(_) \* operator mapping each round to its leader

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(**************************************************************************************)
(* For our purpose of checking safety and liveness, DAG vertices just consist of a   *)
(* node and a round.                                                                  *)
(**************************************************************************************)
V == N \times R \* the set of possible DAG vertices
Node(v) == v[1]
Round(v) == IF v = <<>> THEN 0 ELSE v[2] \* accomodates <<>> as default value

(**************************************************************************************)
(* Next we define how we order DAG vertices when we commit a leader vertice           *)
(**************************************************************************************)
LeaderVertex(r) == IF r > 0 THEN <<Leader(r), r>> ELSE <<>>
IsLeader(v) == LeaderVertex(Round(v)) = v
Genesis == <<>>

(**************************************************************************************)
(* OrderSet(S) arbitrarily order the members of the set S.  Note that, in TLA+,       *)
(* `CHOOSE' is deterministic but arbitrary choice, i.e. `CHOOSE e \in S : TRUE' is    *)
(* always the same `e' if `S' is the same                                             *)
(**************************************************************************************)
RECURSIVE OrderSet(_)
OrderSet(S) == IF S = {} THEN <<>> ELSE
    LET e == CHOOSE e \in S : TRUE
    IN  Append(OrderSet(S \ {e}), e)
    
PreviousLeader(dag, r) == 
    IF \E l \in Vertices(dag) : IsLeader(l) /\ Round(l) < r
    THEN 
        CHOOSE l \in Vertices(dag) :
            /\  IsLeader(l) /\ Round(l) < r
            /\  \A v \in Vertices(dag) : IsLeader(v) /\ Round(v) < r => Round(v) <= Round(l)
    ELSE
        <<>>

RECURSIVE Linearize(_, _)
Linearize(dag, l) == IF Vertices(dag) = {<<>>} THEN <<>> ELSE
    LET dagOfL == SubDag(dag, {l})
        prevL == PreviousLeader(dagOfL, Round(l))
        dagOfPrev == SubDag(dag, {prevL})
        remaining == Vertices(dagOfL) \ Vertices(dagOfPrev)
    IN  Linearize(dagOfPrev, prevL) \o OrderSet(remaining \ {l}) \o <<l>>
\* technically, we should use a topological sort instead of OrderSet(_)

=========================================================================
