# ML in ITP Gym API Draft


Basic functionality
===
1. A server that can communicate with the language server/REPL or verify and execute proof documents.
2. Maintain the proof tree. 
3. Allow execution of single statements on the ongoing/selected proof/goal and returns execution status.

Main functionalities
===
Interacting with ITP
---  
This part of the Gym interacts with the ITP and tries to prove theorem based on the given command/tactic.
We have two interface choices for this part.
- HOList-like
  1. Initialize environment and goal. 
     - `\_\_init__`
  2. Pick goal in the proof tree, give a tactic and try to prove using the tactic. Return the status/result. 
     - `ApplyTactic(goal, tactic) -> result`

- CoqGym,OpenAI/Gym-like
  1. Initialize environment and goal.
     - `\_\_init__`
  2. Give command to step forward, or backtrack, and return the status/result.
     - `ApplyTactic(command) -> result`

We can also add in `VerifyProof` that verifies a given proof, goal pair.

Getting Data Set
---

Reading Data Set
---

Theorem Fingerprints
---
Since theorems are long and the number of premises in the enviornment is large, we can use a table to map hashes to theorems to reduce memory use. 
This requires `RegisterTheorem` function or something similar.

Data Structures
====
Documents
---
A document should contain a list of definitions and lemmas.

Lemma
---
A lemma should contain its environment, statement, and proof. 

We probably should use delta_environment instead of environment, since the environment is enormous.

Environment
---
An environment should be a list of previous definitions or lemmas that are considered as facts.

Definitions
---
A definition should be a statement.

Statement
---
A statement should be represented as an s-expression of what Isabelle represent. We can choose other serialization method other than an s-expression. 

Goal
---
TODO:

Response
---
TODO:

Data Gathering:
===
TODO:





Credit
===
Message from Jason Rute in Zulip Chat on how to design APIs, and his HOList communication example.
