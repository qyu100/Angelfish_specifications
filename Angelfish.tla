----------------------------- MODULE Angelfish -----------------------------

(**************************************************************************************)
(* Specification of the `^Angelfish^' consensus algorithm at a high level of          *)
(* abstraction. We use a number of abstractions and simplifiying assumptions in       *)
(* order to expose the high-level principles of the algorithm clearly.                *)
(**************************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    N \* The set of all nodes
,   R \* The set of rounds
,   IsQuorum(_) \* Whether a set is a quorum (i.e. cardinality at least n-f)
,   IsBlocking(_) \* Whether a set is a blocking set (i.e. cardinality at least f+1)
,   Leader(_) \* operator mapping each round to its leader

ASSUME \E n \in R : R = 1..n \* useful rounds start at 1

(**************************************************************************************)
(* See BlockDag definitions in BlockDag.tla:                                          *)
(**************************************************************************************)
INSTANCE BlockDag WITH N <- N, R <- R, Leader <- Leader

(**************************************************************************************)
(* A vote by a node for a vertex or for no vertex (<<>>):                             *)
(**************************************************************************************)
Vote == N \times R \times (V \cup {<<>>})
Vertex(v) == v[3]
(**************************************************************************************)
(* Timeout messages:                                                                  *)
(**************************************************************************************)
Timeout == N \times R
(**************************************************************************************)
(* Quorum of messages:                                                                *)
(**************************************************************************************)
IsQuorumMsgs(M) == IsQuorum({Node(m) : m \in M})

(*--algorithm Angelfish {
    variables
        vs = {Genesis}, \* the vertices of the DAG
        es = {}; \* the strong edges of the DAG (we do not model weak edges)
        votes = {}; \* vote messages
        timeouts = {}; \* timeout messages
    define {
        dag == <<vs, es>>
        \* whether we have timeout certificates for all rounds from Round(l) to rnd-1:
        ValidPreviousLeader(l, rnd) ==
            /\  IsLeader(l)
            /\  \A r \in (Round(l)+1)..(rnd-1) :
                    IsQuorumMsgs({to \in timeouts : Round(to) = r})
        \* whether a DAG d is valid:
        IsValid(d) == \A v \in Vertices(d) : v # <<>> =>
            /\  Node(v) \in N /\ Round(v) \in Nat \ {0}
            /\  IF \neg IsLeader(v)
                THEN \A v2 \in Children(d, v) : Round(v2) = Round(v) - 1
                ELSE \E l \in Children(d, v) :
                    /\  IsLeader(l) /\ Round(l) < Round(v)
                    /\  ValidPreviousLeader(l, Round(v))
                    /\  \A v2 \in Children(d, v) :
                            v2 # l => Round(v2) = Round(v) - 1
    }
    macro StartRound1() {
        \* the first round is a bit special since there's no previous leader
        round := 1;
        either { \* create a vertex:
            vs := vs \cup {<<self, 1>>};
            es := es \cup {<<<<self, 1>>, Genesis>>} \* edge to genesis
        }
        or \* or send an empty vote:
            votes := votes \cup {<<self, 1, <<>>>>}
    }
    macro Vote(deliveredVertices) {
        if (LeaderVertex(round) \in deliveredVertices /\ <<self, round>> \notin timeouts)
            votes := votes \cup {<<self, round+1, LeaderVertex(round)>>}
        else
            votes := votes \cup {<<self, round+1, <<>>>>}
    }
    macro CreateVertex(receivedVertices) {
        if (LeaderVertex(round) \in receivedVertices /\ <<self, round>> \notin timeouts) {
            \* create a vertex pointing to the leader of the previous round
            with (newV = <<self, round+1>>) {
                vs := vs \cup {newV};
                es := es \cup {<<newV, pv>> : pv \in receivedVertices}
            }
        }
        else {
            if (Leader(round+1) # self)
                \* create a vertex not pointing to any leader
                with (newV = <<self, round+1>>) {
                    vs := vs \cup {newV};
                    es := es \cup {<<newV, pv>> : pv \in deliveredVertices \ {LeaderVertex(round)}}
            }
            else
                \* we need to find a previous leader to point to
                with (prevLeader \in {v \in vs :
                    Round(v) < round /\ v = LeaderVertex(Round(v))})
                with (newV = <<self, round+1>>) {
                    \* we must have timeout certificates down to the previous leader:
                    when ValidPreviousLeader(prevLeader, round+1);
                    vs := vs \cup {newV};
                    es := es
                            \cup {<<newV, pv>> : pv \in deliveredVertices \ {LeaderVertex(round)}}
                            \cup {<<newV, prevLeader>>}; \* point to the previous leader
            }
        }
    }
    macro TryCommitLeader(deliveredVertices, deliveredVotes) {
        with (l = LeaderVertex(round-1))
        with (support =  \* vertices pointing to l plus votes
            {v \in deliveredVertices : <<v, l>> \in es} \cup {vt \in deliveredVotes : vt[3] = l})
        if (IsQuorumMsgs(support))
            log := Linearize(SubDag(dag, {l}), l);
    }
    macro Catchup() {
        \* catch up to a round r strictly greater than round+1
        with (M \in SUBSET ((vs \cup votes \cup timeouts) \ {Genesis}) \ {{}})
        with (r = Min({Round(m) : m \in M}))
        with (B = {Node(m) : m \in M}) {
            when r > round+1 /\ IsBlocking(B);
            round := r;
        }
    }
(**************************************************************************************)
(* Finally, we give the full specification of a node:                                 *)
(**************************************************************************************)
    process (correctNode \in N)
        variables
            round = 0, \* current round; 0 means the node has not started execution
            log = <<>>; \* delivered log
    {
l0:     StartRound1();
l1:     while (TRUE)
            either
                \* start the next round and create a vertex or vote
                with (deliveredVertices \in SUBSET {v \in vs \ {<<>>} : Round(v) = round})
                with (deliveredVotes \in SUBSET {vt \in votes \ {<<>>} : Round(vt) = round})
                with (deliveredTimeouts \in SUBSET {to \in timeouts \ {<<>>} : Round(to) = round}) {
                    \* we heard from a quorum:
                    when IsQuorumMsgs(deliveredVertices \cup deliveredVotes \cup deliveredTimeouts);
                    \* we have the leader or a timeout certificate:
                    when LeaderVertex(round) \in deliveredVertices \/ IsQuorumMsgs(deliveredTimeouts);
                    either {
                        when (Leader(round+1) # self); \* leaders cannot vote
                        Vote(deliveredVertices)
                    }
                    or 
                        CreateVertex(deliveredVertices);
                    \* possibly commit the leader of round-1:
                    if (round > 1)
                        TryCommitLeader(deliveredVertices, deliveredVotes);
                    \* finally, increment the round counter:
                    round := round+1
            }
            or {
                \* if we have the leader, we can also vote without having heard from a quorum:
                when (Leader(round+1) # self); \* leaders cannot vote
                when (Leader(round) \in vs);
                Vote({Leader(round)})
            }
            or 
                \* timeout (this means we cannot support the leader of this round in the next round)
                timeouts := timeouts \cup {<<self, round>>}
            or 
                Catchup()
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9fea5d2d" /\ chksum(tla) = "f4ef0e95")
VARIABLES pc, vs, es, votes, timeouts

(* define statement *)
dag == <<vs, es>>

ValidPreviousLeader(l, rnd) ==
    /\  IsLeader(l)
    /\  \A r \in (Round(l)+1)..(rnd-1) :
            IsQuorumMsgs({to \in timeouts : Round(to) = r})

IsValid(d) == \A v \in Vertices(d) : v # <<>> =>
    /\  Node(v) \in N /\ Round(v) \in Nat \ {0}
    /\  IF \neg IsLeader(v)
        THEN \A v2 \in Children(d, v) : Round(v2) = Round(v) - 1
        ELSE \E l \in Children(d, v) :
            /\  IsLeader(l) /\ Round(l) < Round(v)
            /\  ValidPreviousLeader(l, Round(v))
            /\  \A v2 \in Children(d, v) :
                    v2 # l => Round(v2) = Round(v) - 1

VARIABLES round, log

vars == << pc, vs, es, votes, timeouts, round, log >>

ProcSet == (N)

Init == (* Global variables *)
        /\ vs = {Genesis}
        /\ es = {}
        /\ votes = {}
        /\ timeouts = {}
        (* Process correctNode *)
        /\ round = [self \in N |-> 0]
        /\ log = [self \in N |-> <<>>]
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ round' = [round EXCEPT ![self] = 1]
            /\ \/ /\ vs' = (vs \cup {<<self, 1>>})
                  /\ es' = (es \cup {<<<<self, 1>>, Genesis>>})
                  /\ votes' = votes
               \/ /\ votes' = (votes \cup {<<self, 1, <<>>>>})
                  /\ UNCHANGED <<vs, es>>
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << timeouts, log >>

l1(self) == /\ pc[self] = "l1"
            /\ \/ /\ \E deliveredVertices \in SUBSET {v \in vs \ {<<>>} : Round(v) = round[self]}:
                       \E deliveredVotes \in SUBSET {vt \in votes \ {<<>>} : Round(vt) = round[self]}:
                         \E deliveredTimeouts \in SUBSET {to \in timeouts \ {<<>>} : Round(to) = round[self]}:
                           /\ IsQuorumMsgs(deliveredVertices \cup deliveredVotes \cup deliveredTimeouts)
                           /\ LeaderVertex(round[self]) \in deliveredVertices \/ IsQuorumMsgs(deliveredTimeouts)
                           /\ \/ /\ (Leader(round[self]+1) # self)
                                 /\ IF LeaderVertex(round[self]) \in deliveredVertices /\ <<self, round[self]>> \notin timeouts
                                       THEN /\ votes' = (votes \cup {<<self, round[self]+1, LeaderVertex(round[self])>>})
                                       ELSE /\ votes' = (votes \cup {<<self, round[self]+1, <<>>>>})
                                 /\ UNCHANGED <<vs, es>>
                              \/ /\ IF LeaderVertex(round[self]) \in deliveredVertices /\ <<self, round[self]>> \notin timeouts
                                       THEN /\ LET newV == <<self, round[self]+1>> IN
                                                 /\ vs' = (vs \cup {newV})
                                                 /\ es' = (es \cup {<<newV, pv>> : pv \in deliveredVertices})
                                       ELSE /\ IF Leader(round[self]+1) # self
                                                  THEN /\ LET newV == <<self, round[self]+1>> IN
                                                            /\ vs' = (vs \cup {newV})
                                                            /\ es' = (es \cup {<<newV, pv>> : pv \in deliveredVertices \ {LeaderVertex(round[self])}})
                                                  ELSE /\ \E prevLeader \in                  {v \in vs :
                                                                            Round(v) < round[self] /\ v = LeaderVertex(Round(v))}:
                                                            LET newV == <<self, round[self]+1>> IN
                                                              /\ ValidPreviousLeader(prevLeader, round[self]+1)
                                                              /\ vs' = (vs \cup {newV})
                                                              /\ es' = es
                                                                         \cup {<<newV, pv>> : pv \in deliveredVertices \ {LeaderVertex(round[self])}}
                                                                         \cup {<<newV, prevLeader>>}
                                 /\ votes' = votes
                           /\ IF round[self] > 1
                                 THEN /\ LET l == LeaderVertex(round[self]-1) IN
                                           LET support == {v \in deliveredVertices : <<v, l>> \in es'} \cup {vt \in deliveredVotes : vt[3] = l} IN
                                             IF IsQuorumMsgs(support)
                                                THEN /\ log' = [log EXCEPT ![self] = Linearize(SubDag(dag, {l}), l)]
                                                ELSE /\ TRUE
                                                     /\ log' = log
                                 ELSE /\ TRUE
                                      /\ log' = log
                           /\ round' = [round EXCEPT ![self] = round[self]+1]
                  /\ UNCHANGED timeouts
               \/ /\ (Leader(round[self]+1) # self)
                  /\ (Leader(round[self]) \in vs)
                  /\ IF LeaderVertex(round[self]) \in ({Leader(round[self])}) /\ <<self, round[self]>> \notin timeouts
                        THEN /\ votes' = (votes \cup {<<self, round[self]+1, LeaderVertex(round[self])>>})
                        ELSE /\ votes' = (votes \cup {<<self, round[self]+1, <<>>>>})
                  /\ UNCHANGED <<vs, es, timeouts, round, log>>
               \/ /\ timeouts' = (timeouts \cup {<<self, round[self]>>})
                  /\ UNCHANGED <<vs, es, votes, round, log>>
               \/ /\ \E M \in SUBSET ((vs \cup votes \cup timeouts) \ {Genesis}) \ {{}}:
                       LET r == Min({Round(m) : m \in M}) IN
                         LET B == {Node(m) : m \in M} IN
                           /\ r > round[self]+1 /\ IsBlocking(B)
                           /\ round' = [round EXCEPT ![self] = r]
                  /\ UNCHANGED <<vs, es, votes, timeouts, log>>
            /\ pc' = [pc EXCEPT ![self] = "l1"]

correctNode(self) == l0(self) \/ l1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in N: correctNode(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(**************************************************************************************)
(* Correctness properties:                                                            *)
(**************************************************************************************)

Compatible(s1, s2) == \* whether the sequence s1 is a prefix of the sequence s2, or vice versa
    \A i \in 1..Min({Len(s1), Len(s2)}) : s1[i] = s2[i]

Agreement == \A n1,n2 \in N : Compatible(log[n1], log[n2])

\* Basic typing invariant:
TypeOK ==
    /\  IsValid(dag)
    /\  \A vt \in votes :
        /\  vt = <<vt[1], vt[2], vt[3]>>
        /\  vt[1] \in N
        /\  vt[2] \in Nat \ {0}
        /\  vt[3] \in vs \cup {<<>>}
    /\  \A to \in timeouts :
        /\  to[1] \in N
        /\  to[2] \in Nat \ {0}
    /\  \A n \in N : round[n] \in Nat

===========================================================================
