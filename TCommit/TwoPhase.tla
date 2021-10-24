------------------------------ MODULE TwoPhase ------------------------------
(* Here is to define a simple Two-Phase Commit                               *)
(* A resource manager works as the same as in TCommit, but it also receives  *)
(* message from the Transaction manager for either Commit or Abort.          *)

(* A transaction manager will send Commit message only when all the resource *)
(* managers are prepared (rmPrepared is the same as RM                       *)

(* a resource manager can notify the transaction manager it is prepared when *)
(* it is in "prepared state"*)
CONSTANT RM \* a set of resource managers

VARIABLES   
    rmState,    \* state of resources manager rmState[rm]
    tmState,    \* state of Transaction Manager, either "init", or "done"
    rmPrepared, \* a collection of prepared resource managers
    
    msgs \* all the messages in tranit. all the messages should be in Messages

Messages ==
(*all the possible messaged used for commumication*)
(* messages from a resource manager to transaction manager tell it is ready*)
(* messages from a transaction manager to a resource manager for either commit or abort*)
    [type: {"Prepared"}, rm: RM] \cup [type: {"Commit", "Abort"}]       


TPTypeOK == 
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"init", "done"}
    /\ rmPrepared \subseteq RM \* rmPrepared is a subset of RM
    /\ msgs \subseteq Messages \* msgs is a subset of Messages


TPInit == 
    /\ rmState = [r \in RM |-> "working"] \* all resource managers are in "working" state
    /\ tmState = "init"
    /\ rmPrepared = {} \* empty set
    /\ msgs = {} \* empty set 
    
TMRecPreparedMsg(r) == \* the Transaction Manager receives a prepared message from a resource manager
    /\ tmState = "init"
    /\ [type |-> "Prepared", rm |-> r] \in Messages
    /\ rmPrepared' = rmPrepared \cup {r}
    /\ UNCHANGED <<msgs, rmState, tmState>>

TMCommit ==
 (* The Transaction Manager commit the transaction; *)
 (* it could happen only if all the sources manangers are in prepared rmPrepared == RM *)
    /\ tmState = "init"
    /\ rmPrepared = RM
    /\ tmState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<rmState, rmPrepared>>

TMAbort == 
(* the Transaction Manager can abort the transaction only when it is not committed yet*)
    /\ tmState = "init"
    /\ tmState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, rmPrepared>>

RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<tmState, rmPrepared>>

RMChooseToAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, rmPrepared, msgs>>

RMRcvCommitMsg(r) ==
    /\ rmState[r] = "prepared"
    /\ [type |-> "Commit"] \in Messages
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, rmPrepared, msgs>>

RMRcvAbortMsg(r) == 
    (* /\ rmState[r] \in {"working", "prepared"} *)
    /\ [type |-> "Abort"] \in Messages
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, rmPrepared, msgs>>    
    
    
TPNext ==  \/ TMAbort 
           \/ TMCommit
           \/ \E r \in RM :
                \/ RMPrepare(r) \/ RMChooseToAbort(r) \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
                \/ TMRecPreparedMsg(r)  

(* INSTANCE TCommit *)
=============================================================================
\* Modification History
\* Last modified Mon Jul 05 14:27:47 PDT 2021 by zharry
\* Created Mon Jul 05 10:53:21 PDT 2021 by zharry
