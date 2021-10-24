------------------------------ MODULE TCommit ------------------------------
(* RM is a set of resource manangers*)
CONSTANT RM
(* rmState is the states of all resource managers*)
(* all the resource manager should be in one of the following states*)
(* working, prepared, commited, aborted*)
VARIABLE rmState

TCTypeOK == \A rm \in RM : rmState[rm] \in {"working", "prepared", "committed", "aborted"}

(* all resource managers are initialized with state "working"*)
TCInit == rmState = [rm \in RM |-> "working"]

(* for a resource manager, prepare is to change to state "prepared"*)
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

(* a resource mananger can commit only when all the ressource manager either    *)
(* in state of either "prepared" or "committed"                                 *)
(* True IFF all RMs are in "prepared" or "committed" state.                     *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

(* notCommitted means there is no resource manager in state "committed" yet     *)
(* True iff no resource manager has decided to commit                           *)
notCommitted == \A rm \in RM : rmState[rm] # "committed"


(* a resource manager can decide either commit or abort *)
(*  for commit, a resource manager must be at prepared state*)
Decide(r) == 
    (* decide to commit*)
    \/  /\ rmState[r] = "prepared"
        /\ canCommit
        /\ rmState' = [rmState EXCEPT  ![r] = "committed"]
    \/  /\ rmState[r] \in {"working", "prepared"}
        /\ notCommitted
        /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM:  \/ Decide(r)
                        \/ Prepare(r)

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent ==
    (*two RMs should not in conflicting state*)
    \A r1, r2 \in RM : ~  /\ rmState[r1] = "committed"
                          /\ rmState[r2] = "aborted"

TCSuccess == \A r \in RM : rmState[r] = "committed"

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================
\* Modification History
\* Last modified Sat Jul 17 16:15:55 PDT 2021 by harryzhang
\* Last modified Mon Jul 05 10:19:20 PDT 2021 by zharry
\* Created Wed Jun 30 16:28:55 PDT 2021 by zharry
