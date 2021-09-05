---------------------------- MODULE SyncChannel ----------------------------
EXTENDS Naturals
CONSTANT Data

VARIABLES chan
TypeInv == chan \in [val: Data, rdy : {0, 1}, ack: {0, 1} ]



TypeInit == /\ TypeInv
            /\ chan.ack = chan.rdy
            
Send(d) ==  /\ chan.rdy = chan.ack
            /\ chan' = [chan EXCEPT !.rdy = 1 - @, !.val = d] 

Recv == /\ chan.rdy # chan.ack
        /\ chan' = [chan EXCEPT !.ack = 1 - @]
        
Next ==  \/ (\E d \in Data: Send(d))
         \/ Recv

Spec == TypeInit /\ [][Next]_chan

THEOREM Spec => TypeInv
=============================================================================
\* Modification History
\* Last modified Sun Sep 05 09:50:35 PDT 2021 by kids
\* Created Fri Sep 03 20:38:16 PDT 2021 by kids
