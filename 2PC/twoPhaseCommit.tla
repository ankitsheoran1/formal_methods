--------------------------- MODULE twoPhaseCommit ---------------------------
CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

Message == [type: {"Prepared"}, rm: RM] \cup [type: {"Commit", "Abort"}]
TypeOk == 
      /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
      /\ tmState \in {"init", "committed", "aborted"}
      /\ tmPrepared \subseteq RM 
      /\ msgs \subseteq Message 
      
Init == 
      /\ rmState = [rm \in RM |-> "working"]
      /\ tmState = "init"
      /\ tmPrepared = {}
      /\ msgs = {}
            

\* TM Actions
TMRcvPrepared(rm) == 
      /\ tmState = "init"
      /\ [type |-> "Prepared", rm |-> rm] \in msgs 
      /\ tmPrepared' = tmPrepared \cup {rm}
      /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit == 
      /\ tmState = "init"
      /\ tmPrepared = RM 
      /\ tmState' = "committed"
      /\ msgs' = msgs \cup {[type |-> "Commit"]}
      /\ UNCHANGED <<rmState, tmPrepared>> 
      
TMAbort == 
      /\ tmState = "init"
      /\ tmState' = "aborted"
      /\ msgs' = msgs \cup {[type |-> "Abort"]}
      /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) ==
      /\ rmState[rm]="working"
      /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
      /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
      /\ UNCHANGED <<tmState, tmPrepared>>
      
RMChooseToAbort(rm) == 
      /\ rmState[rm] = "working"     
      /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
      /\ UNCHANGED <<tmState, tmPrepared, msgs>>
      
RMRcvCommitMsg(rm) == 
      /\ [type |-> "Commit"] \in msgs  
      /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
      /\ UNCHANGED <<tmState, tmPrepared, msgs>>
     
RMRcvAbortMsg(rm) ==
      /\ [type |-> "Abort"] \in msgs
      /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
      /\ UNCHANGED <<tmState, tmPrepared, msgs>>      
 
 Next == 
      \/ TMCommit \/ TMAbort
      \/ \E rm \in RM : 
          TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
          \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
 
 Spec == Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>
          
                       
           
      


=============================================================================
\* Modification History
\* Last modified Tue Apr 23 09:54:40 IST 2024 by ankit
\* Created Mon Apr 22 16:30:52 IST 2024 by ankit