---------------------------- MODULE SyncChannel ----------------------------
EXTENDS Integers
CONSTANT Data

VARIABLES val, rdy, ack

TypeInv ==  /\ val \in Data 
            /\ rdy \in {0, 1} 
            /\ ack \in {0, 1}

TypeInit == /\ val \in Data
            /\ rdy \in {0, 1}
            /\ ack = rdy
            
Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

Recv == /\ rdy # ack
        /\ ack' = 1 - ack
        /\ UNCHANGED <<val, rdy>>

Next == Send \/ Recv

Spec == TypeInit /\ [][Next]_<<val, rdy, ack>>

=============================================================================
\* Modification History
\* Last modified Fri Sep 03 20:48:42 PDT 2021 by kids
\* Created Fri Sep 03 20:38:16 PDT 2021 by kids
