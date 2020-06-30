# HOList API Reference
This is a transcription of the file proof_assistant.proto that can be found [here](https://github.com/tensorflow/deepmath/blob/master/deepmath/proof_assistant/proof_assistant.proto).
  
Data Structure: 
- ProverTask -- A task to be proven. 
  - premise_set (PremiseSet) -- A set of premise.
    - Implemented as a section of database and a set of premises (fingerprints) from some databases.
  - goals (Theorem with tag=GOAL) -- Theorem to prove.
    - See below
- Theorem
  - conclusion -- Conclusion of the Goal, or the entire statement otherwise.
  - hypotheses -- Hypothesis of the Goal. Used when tag=GOAL
  - definition -- Additional info when tag=DEFINITION
  - type_definition -- Aditional info when tag=TYPE_DEFINITION
  - tag -- The type of the theorem. Either Goal, Theorem, Definition, or Type Definition.
  - fingerprint -- fingerprint of this theorem
  - other fields (everything is optional here)
    - name 
    - training_split (trianing, validation, test)
    - library_tag -- the library the theorem is in (HOList specific)
    - pretty_printed (HOL specific)
    - goal_fingerprint -- fingerprint of the goal that resulted in this theorem. 
    - proof_function -- how this theorem is proved
  
Service Structure:
- service 
  - ProofAssistantService
    - ApplyTactic : ApplyTacticRequest -> ApplyTacticResponse 
    - VerifyProof : VerifyProofRequest -> VerifyProofResponse
    - RegisterTheorem : RegisterTheoremRequest -> RegisterTheoremResponse
- ApplyTacticRequest
  - goal (Theorem)
  - tactic (string)
  - timeout (int)
- ApplyTacticResponse
  - error (string) or goals (GoalList) -- if goals is empty, the proof is done.
- VerifyProofRequest
  - goal (Theorem)
  - theorem (Theorem) -- Looks like it is the same to goal
  - tactics (string)
- VerifyProofResponse
  - sound (bool)
  - error (string)
- RegisterTheoremRequest
  - theorem (Theorem)
- RegisterTheoremResponse
  - fingerprint (int)
  - error (string)

- all messages
  - Definition
  - Type Definition
  - Theorem
  - GoalList
  - ApplyTacticRequest
  - ApplyTacticResponse
  - VerifyProofRequest
  - VerifyProofResponse
  - RegisterTheoremRequest
  - RegisterTheoremResponse
  - ProofAssistantService
  - TheoremDatabase
  - DatabaseSection
  - PremiseReferenceSet
  - PremiseSet
  - ProverTask 
  - ProverTaskList
