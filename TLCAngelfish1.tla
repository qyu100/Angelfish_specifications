----------------------------- MODULE TLCAngelfish1 -----------------------------

EXTENDS Integers, FiniteSets

VARIABLES vs, es, votes, timeouts, round, log, pc

CONSTANTS
    n1,n2,n3

N == {n1,n2,n3}
R == 1..3

IsQuorum(S) == \E Q \in {{n1,n3},{n2,n3}} : Q \subseteq S
IsBlocking(S) == \E B \in {{n3}, {n1,n2}} : B \subseteq S
LeaderSchedule == <<n1,n2,n3>>
Leader(r) == LeaderSchedule[((r-1) % Cardinality(N))+1]

INSTANCE Angelfish

(**************************************************************************************)
(* Next we define a constraint to stop the model-checker.                             *)
(**************************************************************************************)
StateConstraint == \A n \in N : round[n] \in 0..Max(R)

(**************************************************************************************)
(* Finally, we give some properties we expect to be violated (useful to get the       *)
(* model-checker to print interesting executions).                                    *)
(**************************************************************************************)

Falsy1 == \neg (
    \A n \in N : round[n] = Max(R)
)

Falsy2 == \neg (
    \E n \in N : Len(log[n]) > 1
)


===========================================================================
