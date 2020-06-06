# ML in ITP Gym API Draft


Basic functionality
===
1. A server that can communicate with the language server/REPL or verify and excecute proof documents.
2. Maintain the proof tree. 
3. Allow excecution of single statements on the ongoing/selected proof/goal and returns excecution status.

Design Choices
===

HOList-like
--- 
1. Initialize enviornment.
2. Pick goal in the proof tree, give a tactic and try to prove using the tactic. Return the status/result. 


CoqGym,OpenAI/Gym-like
1. Initialize enviornment.
2. Initialize Goal.
3. Give command to step foward, or backtrack, and return the status/result.

Details
====
Goal Data Strucuture:
---
TODO:

Response Data Strucuture:
---
TODO:


Theorem Fingerprints
---
Since theorems are long and the number of premises in the enviornment is large, we can use a table to map hashes to theorems to reduce memory use. 
This requires `RegisterTheorem` function or something similar.

Documents
---
TODO:

Credit
===
Message from Jason Rute in Zulip Chat on how to design APIs, and his HOList communication example.
