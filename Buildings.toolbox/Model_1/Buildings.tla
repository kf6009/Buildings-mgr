----------------------------- MODULE Buildings -----------------------------
CONSTANTS       \* Define the world
    People,     \* All people to manage
    Buildings   \* All buildings to manage

Outside == CHOOSE x : x \notin People \union Buildings \* Create a value for being outside a building
(*
    using \notin People \union Buildings creates a unique value,
    that is guaranteed to be in either People or Buildings
*)

VARIABLES       \* Define a state
    register,   \* set of registered people
    permission, \* function giving permisions
    location    \* function giving locations

TypeOK == 
    /\ register \subseteq People                                \* register is a subset of all people
    /\ permission \in [register -> SUBSET Buildings]            \* permission is a function from People to some subset of Buildings
    /\ location \in [register -> (Buildings \union {Outside})]  \* location is a function from People to a Building or outside

--------
Init == 
    /\ register = {}       \* register is empty set
    /\ permission = << >>  \* permission is empty function
    /\ location   = << >>  \* location is empty function
--------
Register(p) == 
    /\ p \in People \ register                   \* p is a person not in the register
    /\ register' = register \union {p}           \* adds p to the register
    /\ permission' =                             \* update permissions 
        [x \in DOMAIN permission \union {p} |->  \* is a function from new set of registered people 
             IF x \in DOMAIN permission          \* x is already registered
             THEN permission[x]                  \* use existing permission
             ELSE {}                             \* new person has no permissions
        ]
    /\ location' =                               \* update permissions 
        [x \in DOMAIN location \union {p} |->    \* is a function from new set of registered people 
             IF x \in DOMAIN location            \* x is already registered
             THEN location[x]                    \* use existing location
             ELSE Outside                        \* new person is outside
        ]

DeRegister(p) ==
    /\ p \in register                                \* p is registered
    /\ register' = register \ {p}                    \* take out of register
    /\ permission' = [ x \in DOMAIN permission \ {p} \* rewrite domain of function without p
                         |-> permission[p] ]         \* value is just existing permission
    /\ location' = [ x \in DOMAIN location \ {p}     \* rewrite domain of function without p
                       |-> location[p] ]             \* value is just existing location
--------
AddPermission(p,b) == \* Add permission for p to enter b
    /\ p \in register            \* p is registered
    /\ p \in DOMAIN permission   \* p has permissions
    /\ permission' = [ permission \* existing permissions for everyone else
                       EXCEPT ![p] = \* update permission for p
                       permission[p] \union {b} ] \* existing permission plus b
    /\ UNCHANGED register \* don't change register
    /\ UNCHANGED location \* don't change locations

RevokePermission(p,b) ==
    /\ p \in register            \* p is registered
    /\ p \in DOMAIN permission   \* p has permissions
    /\ location[p] /= b
    /\ permission' = [ permission \* existing permissions for everyone else
                       EXCEPT ![p] = \* update permission for p
                       permission[p] \ {b} ] \* existing permission without b
    /\ UNCHANGED register \* don't change register
    /\ UNCHANGED location \* don't change locations
--------
Enter(p,b) ==                                 \* Person p enters building b
    /\ p \in register                         \* is person registered
    /\ b \in permission[p]                    \* does p have permission to enter b
    /\ location' = [location EXCEPT ![p] = b] \* update p's location
    /\ UNCHANGED register                     \* don't touch the register
    /\ UNCHANGED permission                   \* don't touch the permissions


Leave(p,b) == \* Person p leaves building b
    /\ p \in register                                 \* is person registered
    /\ location[p] = b                                \* is person p in building b
    /\ location' = [location EXCEPT ![p] = Outside]   \* update p's location
    /\ UNCHANGED <<register,permission>>              \* don't touch the register and permissions

----------
Next == \E p \in People, b \in Buildings : \* There is a person and a builing that:
    \/ Register(p)           \* the person can be registered, or
    \/ DeRegister(p)         \* the person can be deregistered, or
    \/ Enter(p,b)            \* the person can enter the building, or
    \/ Leave(p,b)            \* the person can leave the building, or
    \/ AddPermission(p,b)    \* the person can have permissions added, or
    \/ RevokePermission(p,b) \* the person can have permissions revoked, or
=============================================================================
\* Modification History
\* Last modified Mon Oct 14 20:32:37 BST 2019 by alun
\* Created Wed Oct 02 12:01:41 BST 2019 by alun
