# CoqGym Documentation

## Misc.
### Proofs
### Goals


## ProofEnv (in eval_env.py)
The interactive environment for proving one theorem.
#### \_\_init__
Start an environment with "proof" to prove.
Argument list:
- proof 
- serapi -- API for interacting with Coq
- max_num_tactcs 
- timeout
#### init
Return the initial goals and global environment of the theorem.
#### step 
perform a single interaction
the agent provides a command and get feedback from Coq
valid commands include:
    tactics
    Admitted - to give up the proof
    Undo - to backtrack one step
    other valid Coq commands

Argument list:
- command

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
    - fg_goals
    - bg_goals
    - shelved_goals
    - given_up_goals

## FileEnv (in eval_env.py)
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

#### \_\_init__
Argument list:
- filename -- json file in CoqGym
- max_num_tactcs -- max number of interactions per theorem
- timeout -- max amount of time (in seconds) for each theorem 
- with_hammer
- hammer_timeout

#### initialize_serapi
Initialize the SerAPI used for interactive proving.
Will tell the API to choose the hammer to use here.

#### \_\_iter__, \_\_next__
Python iterator. Iterates through the CoqGym json document
Refreshes SerAPI every 30 uses or when it is dead.

Raises:
 - StopIteration: When there are no more theorems to prove.

Returns:
 - A ProofEnv for the next proof.




