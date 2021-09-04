----------------------------- MODULE HourClock -----------------------------
EXTENDS Integers

VARIABLES hr
HCini == hr \in (1..12)

HCnxt == hr' = IF hr # 12 
                THEN hr +1
                ELSE 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini
=============================================================================
\* Modification History
\* Last modified Fri Sep 03 20:25:47 PDT 2021 by kids
\* Created Fri Sep 03 20:19:28 PDT 2021 by kids
