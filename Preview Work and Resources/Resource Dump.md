Resource Dump
- General info
  - Thibault's PhD Thesis [https://www.thibaultgauthier.fr/]
    - TacticToe -> HOL4
- Formal Systems
  - Metamath
  - Mizar
  - ProofPower
  - PVS
  - nqthm/ACL2
  - NuPRL/MetaPRL
  - ITPs
    - Coq
    - Lean
    - Isabelle
    - HOL Light
    - HOL4
- Lean threads
  - Machine Learning [https://leanprover.zulipchat.com/#narrow/stream/219941-Machine-Learning.20for.20Theorem.20Proving]
    - ML for Lean: How to do it? [https://leanprover.zulipchat.com/#narrow/stream/219941-Machine-Learning.20for.20Theorem.20Proving/topic/ML.20for.20Lean.3A.20How.20to.20do.20it.3F]
    - HOList [https://leanprover.zulipchat.com/#narrow/stream/219941-Machine-Learning.20for.20Theorem.20Proving/topic/HOList]
  - IMO-grand-challenge 
    - [https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/Reading.20list.2Fsample.20AI]
    - [https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/general.20discussion]
  - AI and theorem proving [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/AI.20and.20theorem.20proving]
  - Declarative Lean [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Declarative.20Lean]
  - Cellphone Mathematics [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Cell.20Phone.20Mathematics]
  - AI and TP continued [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/AI.20and.20theorem.20proving.20continued]
  - Examples of communicating with Lean [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Examples.20of.20communicating.20with.20Lean]
  - User: Jason Rute
- Conferences
  - AITP [http://aitp-conference.org/]
  - FMCAD [https://fmcad.forsyte.at/FMCAD20/]
- People
  - Yutaka Nagashima [https://scholar.google.com/citations?hl=ja&user=U2cikqsAAAAJ&view_op=list_works&sortby=pubdate]
    - PamPer [https://arxiv.org/pdf/2004.10667.pdf]
- Fact/Premise Selection
    - For Isabelle/HOL
      - MePo
      - MaSh 
      - MeSh [https://link.springer.com/article/10.1007/s10817-016-9362-8#Sec17]
- Proof Guidance
  - Coq
    - GamePad [https://arxiv.org/abs/1806.00608]
    - CompCert [http://compcert.inria.fr/]
      - ProverBot9001 [https://arxiv.org/pdf/1907.07794.pdf]
      - SmartCoq [https://easychair.org/publications/preprint/SQCJ]
    - CoqGym [https://github.com/princeton-vl/CoqGym]
      - ASTactic [https://github.com/princeton-vl/CoqGym]
  - HOL4
    - HOList [https://arxiv.org/abs/1904.03241]
      - Example [https://github.com/jasonrute/holist-communication-example]
      - DeepHOL [https://arxiv.org/abs/1904.03241]
        - Example [https://github.com/aahadley/deepmath-jupyter/blob/master/HOLJup.ipynb]
    - TacticToe
  - Isabelle
    - PamPer (Feature set) [https://arxiv.org/pdf/2004.10667.pdf]
  - Lean
    - Some discussion here [https://gist.github.com/jasonrute/00109af2bdc0974d2e8e79faf26ba556]
- Leaderboard [https://paperswithcode.com/task/automated-theorem-proving]
- Human Proved theorems (data)
  - Isabelle
    - Archive of formal proofs [https://www.isa-afp.org/index.html]
    - Sledgehammer: judgement day [http://www21.in.tum.de/~boehmes/judgement.html]
  - Lean
    - mathlib [https://github.com/leanprover-community/mathlib]
  - Coq 
    - CoqGym
- Declarative ITP
  - Coq [https://kluedo.ub.uni-kl.de/frontdoor/deliver/index/docId/2100/file/B-065.pdf]
  - Isar [http://isabelle.in.tum.de/Isar/]
  - Lean (Some discussion) [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Declarative.20Lean]
- Lean
  - Communicate with Lean Server [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Examples.20of.20communicating.20with.20Lean]
  - More communication [https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Hammer.20talk]
  - Communicate with Lean through Lean server [https://github.com/jasonrute/communicating-with-lean]
- Uncategorized:
  - tensorflow/deepmath [https://github.com/tensorflow/deepmath]

- Questions
  - Premise and Goal selection?
  - Should I dump everything on Github?
  - Needs to be quick. Might not achieve easily.
  - Need supervised learning? 

## Conversation Quotes

### 1. Jason Rute on reimplementing HOList:
As I see it, the HOList projects have the following parts that would need to be reimplemented:

- [Data Set] A list of theorems For both training and testing, one needs a list of theorems (and the full context in some nicely parsable form) to train on.
- [Proof recording] (optional) If one wants to do supervised learning, then one needs a list of proofs as well to train on. These proofs will contain the theorem to prove (with the context) as well as the various tactics which have been applied along with their arguments. This needs to be at some intermediate level which records the name of the tactic and the arguments (so at a higher level than type theory), but probably not at the level of the raw lean code. I’ve heard from some in the Lean community that the tactic environment could be hacked to provide this information, but I don’t know that it has ever been done. HOL Light has some advantages here. It has a simpler tactic framework (I think), it is a larger library (more training data), it is written by one person mostly (so is more uniform), and HOL Light only uses tactics (whereas Lean uses a mixture of tactics and the type theoretic framework). However, the ASTactic (CogGym) and ProverBot9001 projects also used proof recording for Coq.
- An [interactive environment] If one wants to do reinforcement learning and/or tree search, one needs to be able to quickly interact with the system. For tree search, given a particular state, one needs to be able to try possible tactics, see what the results are and back track if needed (using for example beam search). Also, for reinforcement learning, one needs to be able to try out a very large number of scenarios (in this case theorems, either real or synthetic, to prove). This necessitates an even faster back-and-forth between the agent and the system. Google rewrote HOL Light in C++ for this purpose. (The various Coq ML projects don’t use reinforcement learning.)
- A system for [scoring] tactics and tactic arguments Scoring the tactics can be done as a probability distribution over the tactics (computed by a neural network), but scoring the arguments to these tactics can be a bit more tricky because of the large number of possibilities. HOList has one system for doing this. The two Coq projects have another system. I don’t know if either is readily adaptable to Lean.
- Access to neural networks and computer power for training and evaluation The agent will have to compute tactic and argument scores via (graph?) neural networks. Therefore, it needs access to TensorFlow or PyTorch and a distributed computing system.



### 2. Jason Rute on framework: [https://leanprover.zulipchat.com/#narrow/stream/208328-IMO-grand-challenge/topic/general.20discussion/near/179011250]
As far as I see they have the following uniform framework:
- A term and formula language
- A local goal state: What one is trying to prove at the moment (as an ordered list of formulas in some formal language)
- Premise List: all the possible previously proven theorem statements one could use (which needs to be significantly narrowed down in a process called “premise selection”)
- Tactics or inference rules: a fixed finite set of rules one can apply to ones current goal state
- Tactic parameters: the possible parameters that can be added to the above tactics. (This is by far the most inconsistent and flexible part of the framework. These parameters can include numbers, terms, and premises from the premise list.)
- a training and test set: formulas to prove (and possibly proofs for supervised learning)
- application: one needs to be able to quickly apply a rule/tactic
- persistence/backtracking: So that any tree search algorithm can be applied, one needs a notion of backtracking. (Practically, this means that states need to be persistent. If one applies a tactic it creates a new state, without changing the old state. Think immutable data structures.)