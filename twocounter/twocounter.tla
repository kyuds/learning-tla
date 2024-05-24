\* https://jack-vanlightly.com/blog/2023/10/10/a-primer-on-formal-verification-and-tla

---------------------------- MODULE twocounter ----------------------------
EXTENDS Integers
CONSTANT C, Limit
VARIABLES counter

Init == 
    counter = [c \in C |-> 0]

Next ==
    \E c \in C :
        /\ counter[c] < Limit 
        /\ counter' = [counter EXCEPT ![c] = counter[c] + 1]

Spec == 
    Init /\ [][Next]_counter

AlwaysNonNegative ==
    \A c \in C : counter[c] > -1

AllAtLimit ==
    \A c \in C : counter[c] = Limit
    
EventuallyAllAtLimit ==
    <>[]AllAtLimit
===========================================================================
