# CoqGym Documentation

The main functions lies within `eval_env.py` .


Data Structures
=======

S-expression:
-------
A string representing a nested list/tree in [this format](https://en.wikipedia.org/wiki/S-expression).

Goal:
-------
```json
{'id': number
 'type': string of type of the goal (statement to prove)
 'hyposeses': [a list of Premises (the local context)]
}
```
Premise:
-------
```json
{'idents':[list of identifiers of the premises]
 'term':[list of Coq terms]
 'type': the type of the premise (statement of the premise)
 'sexp': Hash of the s-expression
}
```

Environment API
===
ProofEnv (in `eval_env.py`)
---
The interactive environment for proving one theorem.
##### 1. \_\_init__
Start an environment with "goal" to prove.
Argument list:
- proof -- the goal
- serapi -- API for interacting with Coq
- max_num_tactcs 
- timeout
##### 2. init
Return the initial goals and global environment of the theorem.
##### 3. step 
Perform a single interaction with Coq.

Argument:
- command
  * tactics
  * Admitted - to give up the proof
  * Undo - to backtrack one step
  * other valid Coq commands
  
Returns: 
A dictionary contains the feedback. The "result" key: 
  - ALREADY_SUCCEEDED
  - ALREADY_FAILED
  - MAX_TIME_REACHED
  - MAX_NUM_TACTICS_REACHED
  - ERROR
    - "error" : CoqExn or CoqTimeout
  - GIVEN_UP
  - SUCCESS
  - ERROR
    - "error" : (shelved_goals, given_up_goals) # if there are shelved or given up goals
  - PROVING 
    - fg_goals : foreground goals,
    - bg_goals : background goals,
    - shelved_goals : shelved goals (by tactic shelve),
    - given_up_goals : Admitted goals.

FileEnv (in `eval_env.py`)
---
A generator of the theorems in a Coq file
The agent should iterate through this environment and interact with each theorem sequentially

Usage:
```python
with FileEnv(file_name, max_num_tactics, timeout) as file_env:
        for proof_env in file_env:
            proof_env.init()
            # Do proof.
            proof_env.step('Admitted.')
```

##### 1. \_\_init__
Argument list:
- filename -- json file in CoqGym
- max_num_tactcs -- max number of interactions per theorem
- timeout -- max amount of time (in seconds) for each theorem 
- with_hammer
- hammer_timeout

##### 2. initialize_serapi
Initialize the SerAPI used for interactive proving.
Will tell the API to choose the hammer to use here.

##### 3. \_\_iter__, \_\_next__
Python iterator. Iterates through the CoqGym json document
Refreshes SerAPI every 30 uses or when it is dead.

Raises:
 - StopIteration: When there are no more theorems to prove.

Returns:
 - A ProofEnv for the next proof.


Implementation Note
===

[SerAPI](https://github.com/ejgallego/coq-serapi) is used to communicate with Coq. CoqGym uses `seraapi.py` to communicate with SerAPI.