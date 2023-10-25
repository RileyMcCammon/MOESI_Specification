---- MODULE mesi ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS
    NumCores,           \* Number of caches in the system
    Operations,         \* r/w request types
    DataValues          \* Set of possible data values

ASSUME NumCoresAssump == (NumCores \in Nat) /\ (NumCores > 0)
ASSUME OperationsAssump == Operations = {"read", "write"}
ASSUME DataValuesAssump == \A i \in DataValues : i \in Nat
                            /\ (Cardinality(DataValues) > 0)
     
VARIABLES
    cores,          \* Represents processors each with their own cache
    data            \* Maintains data in cache line

vars == << cores, data >>

ProcSet == (0..NumCores-1)

Init == /\ cores = [i \in ProcSet |-> [ state |-> "IState", data |-> CHOOSE x \in DataValues : TRUE ]]
        /\ data = CHOOSE x \in DataValues : TRUE 

DemoteState(self, state) == \E i \in ProcSet : /\ cores[i].state = state
                        /\ cores' = [cores EXCEPT ![self].state = "SState", ![self].data = cores[i].data, ![i].state = "SState"]
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
                    \/ DemoteState(self, "MState") 
                    \/ GainExclusivity(self)
                    \/ GainSharedStatus(self)

PerformWrite(self) == LET d == CHOOSE x \in DataValues: TRUE IN
                        /\ cores' = [i \in ProcSet |-> 
                                     IF i = self 
                                     THEN [ state |-> "MState", data |-> d ]
                                     ELSE [ state |-> "IState", data |-> cores[i].data]]
                        /\ data' = d

MState(self, operation) == /\ cores[self].state = "MState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self)))

EState(self, operation) == /\ cores[self].state = "EState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self)))
                                        
SState(self, operation) == /\ cores[self].state = "SState"
                           /\ ((operation = "read" /\ cores' = cores /\ UNCHANGED data)
                                \/  (operation = "write" /\ PerformWrite(self)))
    
IState(self, operation) ==  /\ cores[self].state = "IState"
                            /\ ((operation = "read" /\ PerformRead(self))
                                \/ (operation = "write" /\ PerformWrite(self)))

Next == (\E self \in ProcSet: 
                \E operation \in Operations:    \/ MState(self, operation)
                                                \/ EState(self, operation) 
                                                \/ SState(self, operation) 
                                                \/ IState(self, operation) )

Spec == Init /\ [][Next]_vars

StateIsMutex(state) == \A i, j \in ProcSet : cores[i].state = state /\ j /= i
            => cores[j].state /= state

SharedStateImpliesEquivalentData == \A i, j \in ProcSet : 
                                        /\ cores[i].state = "SState" 
                                        /\ cores[j].state = "SState" 
                                        => cores[i].data = cores[j].data

Inv == /\ StateIsMutex("EState")
       /\ StateIsMutex("MState")
       /\ SharedStateImpliesEquivalentData

====