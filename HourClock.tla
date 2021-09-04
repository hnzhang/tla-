----------------------------- MODULE HourClock -----------------------------
EXTENDS Integers

VARIABLES hr
HCini == hr \in (1..12)

HCnxt == hr' =  ( hr % 12 ) + 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini
=============================================================================
\* Modification History
\* Last modified Fri Sep 03 20:35:44 PDT 2021 by kids
\* Created Fri Sep 03 20:19:28 PDT 2021 by kids
