---- MODULE moesi ----
EXTENDS TLC, Naturals

CONSTANTS
    NumCores           \* Number of caches in the system

ASSUME NumCoresAssump == (NumCores \in Nat) /\ (NumCores > 0)
     
VARIABLES
    cores,          \* Represents processors each with their own cache
    data            \* Maintains data in cache line

vars == << cores, data >>

Operations == {"read", "write"}

DataSet == 0..512

ProcSet == (0..NumCores-1)

Init == /\ cores = [i \in ProcSet |-> [ state |-> "IState", data |-> CHOOSE x \in DataSet : TRUE ]]
        /\ data = CHOOSE x \in DataSet : TRUE 

DemoteState(self, state) == \E i \in ProcSet : /\ cores[i].state = state
                        /\ cores' = [cores EXCEPT ![self].state = "SState", ![self].data = cores[i].data, ![i].state = "SState"]
                        /\ data' = cores[i].data

PushToOwnerState(self) == \E i \in ProcSet : /\ cores[i].state = "MState"
                        /\ cores' = [cores EXCEPT ![self].state = "SState", ![self].data = cores[i].data, ![i].state = "OState"]
                        /\ data' = cores[i].data

GainExclusivity(self) == \A i \in ProcSet : cores[i].state = "IState"
                            /\ cores' = [cores EXCEPT ![self].state = "EState", ![self].data = data]
                            /\ data' = data

GainSharedStatus(self) == \A i \in ProcSet : cores[i].state /= "EState"
                /\ cores[i].state /= "MState"
                /\ \E j \in ProcSet : cores[j].state = "SState"
                /\ cores' = [cores EXCEPT ![self].state = "SState", ![self].data = data]
                /\ data' = data

PerformRead(self) == DemoteState(self, "EState") 
                    \/ PushToOwnerState(self) 
                    \/ GainExclusivity(self)
                    \/ GainSharedStatus(self)

PerformWrite(self, invalidateOthers) == LET d == CHOOSE x \in DataSet: TRUE IN
                        /\ cores' = [i \in ProcSet |-> 
                                     IF i = self 
                                     THEN [ state |-> "MState", data |-> d ]
                                     ELSE [ state |-> IF invalidateOthers = TRUE THEN "IState" ELSE cores[i].state, 
                                            data  |-> cores[i].data]]
                        /\ data' = d

MState(self, operation) == /\ cores[self].state = "MState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, FALSE)))

OState(self, operation) == /\ cores[self].state = "OState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, TRUE)))

EState(self, operation) == /\ cores[self].state = "EState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, FALSE)))
                                        
SState(self, operation) == /\ cores[self].state = "SState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self, TRUE)))
    
IState(self, operation) ==  /\ cores[self].state = "IState"
                            /\ ((operation = "read" /\ PerformRead(self))
                                \/ (operation = "write" /\ PerformWrite(self, TRUE)))

Next == (\E self \in ProcSet: 
                \E operation \in Operations:    \/ MState(self, operation)
                                                \/ OState(self, operation) 
                                                \/ EState(self, operation) 
                                                \/ SState(self, operation) 
                                                \/ IState(self, operation) )

Spec == Init /\ [][Next]_vars

\* INVARIENTS
TypeOK == /\ \A i \in ProcSet: cores[i].state \in {"MState", "OState", "EState", "SState", "IState"}
          /\ \A i \in ProcSet: cores[i].data \in DataSet
          /\ data \in DataSet
          /\ data \in Nat
    
PermittedStates(state, permitted) == \A i, j \in ProcSet : cores[i].state = state /\ j /= i
            => cores[j].state \in permitted

MStatePermits == PermittedStates("MState", {"IState"})
OStatePermits == PermittedStates("OState", {"SState", "IState"})
EStatePermits == PermittedStates("EState", {"IState"})
SStatePermits == PermittedStates("SState", {"OState", "SState", "IState"})
IStatePermits == PermittedStates("IState", {"MState", "OState", "EState", "SState", "IState"})

SharedOrOwnedStateImpliesEquivalentData == \A i, j \in ProcSet : 
                                        /\ cores[i].state \in {"OState", "SState"}
                                        /\ cores[j].state \in {"OState", "SState"}
                                        => cores[i].data = cores[j].data

====