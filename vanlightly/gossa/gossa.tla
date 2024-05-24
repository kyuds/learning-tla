\* https://jack-vanlightly.com/blog/2023/10/10/the-importance-of-liveness-properties-part1

------------------ MODULE gossa ------------------
EXTENDS Naturals

CONSTANTS   NodeCount
VARIABLES   running, 
            peer_status

vars == <<running, peer_status>>

Nodes == 1..NodeCount

\* Node Peer Statuses
Alive == 1
Dead == 2

\*
\* Actions
\*

Init ==
    /\ running      = [node \in Nodes |-> TRUE]
    /\ peer_status  = [node1 \in Nodes |->
                        [node2 \in Nodes |-> Alive]]

Die ==
    \E node in Nodes :
        /\ running[node] = TRUE
        /\ running' = [running EXCEPT ![node] = FALSE]
        /\ UNCHANGED peer_status

Start ==
    \E node in Nodes :
        /\ running[node] = FALSE
        /\ running' = [running EXCEPT ![node] = TRUE]
        /\ UNCHANGED peer_status

Next == 
    \/ Gossip
    \/ Die
    \/ Start
    \/ CorrectlyDetectDeadNode
    \/ FalselyDetectDeadNode

MergePeerStateBlindly(local_node, local_ps, remote_ps) ==
    [node \in Nodes |->
        IF node = local_node
        THEN local_ps[node]
        ELSE remote_ps[node]]

Gossip ==
    \E source, dest \in Nodes:
        LET gossip_sent         == peer_status[source]
            merged_on_dest      == MergePeerStateBlindly(
                                    dest,
                                    peer_status[dest],
                                    peer_status[source])
            gossip_replied      == merged_on_dest
            merged_on_source    == MergePeerStateBlindly(
                                    source,
                                    peer_status[source],
                                    gossip_replied)
        IN 
            /\ running[source] = TRUE
            /\ running[dest] = TRUE
            \* here to prevent infinite cycling / reduce possibilities
            /\ gossip_sent /= peer_status[dest]
            /\ peer_status' = [peer_status EXCEPT 
                                    ![dest] = merged_on_dest
                                    ![source] = merged_on_source]
            /\ UNCHANGED running

CorrectlyDetectDeadNodes ==
    \E local, remote \in Nodes:
        /\ local /= remote
        /\ running[local] = TRUE
        /\ running[remote] = FALSE
        /\ peer_status[local][remote] = Alive
        /\ peer_status' = [peer_status EXCEPT ![local][remote] = Dead]
        /\ UNCHANGED running

FalselyDetectDeadNodes ==
    \E local, remote \in Nodes:
        /\ local /= remote
        /\ running[local] = TRUE
        /\ running[remote] = TRUE
        /\ peer_status[local][remote] = Alive
        /\ peer_status' = [peer_status EXCEPT ![local][remote] = Dead]
        /\ UNCHANGED running

\* Safety Properties
TypeOK ==
    /\ running \in [Nodes -> BOOLEAN]
    /\ peer_status \in [Nodes ->
                           [Nodes -> {Alive, Dead}]]

\* Liveness Properties
Converged ==
    ~\E local, remote \in Nodes :
       /\ running[local] = TRUE 
       /\ \/ /\ peer_status[local][remote] = Dead 
             /\ running[remote] = TRUE
          \/ /\ peer_status[local][remote] = Alive 
             /\ running[remote] = FALSE

EventuallyConverges ==
    ~Converged ~> Converged

Liveness ==
    WF_vars(\/ Gossip
            \/ CorrectlyDetectDeadNode)

\* Temporal formula 
Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Liveness

==================================================
