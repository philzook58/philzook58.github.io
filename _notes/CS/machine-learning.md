---
layout: post
title: Machine Learning
---

- [Applications](#applications)
- [Data](#data)
- [Good Practice? What's the right word here](#good-practice-whats-the-right-word-here)
- [Supervised](#supervised)
  - [Linear in WHAT?](#linear-in-what)
  - [Nearest neighbor](#nearest-neighbor)
  - [SVM](#svm)
  - [Kernel](#kernel)
  - [decision trees](#decision-trees)
    - [Boosting](#boosting)
    - [Random Forest](#random-forest)
- [Unsupervised](#unsupervised)
- [Visualization](#visualization)
- [Learning Theory](#learning-theory)
- [Overfitting](#overfitting)
- [Bayesian Shit](#bayesian-shit)
  - [Regularization](#regularization)
- [Deep Learning](#deep-learning)
  - [Convolutional](#convolutional)
  - [Recurrent](#recurrent)
  - [tidbits](#tidbits)
- [Verification](#verification)
- [Famous Models](#famous-models)
  - [Tasks](#tasks)
    - [speech recognition](#speech-recognition)
    - [code](#code)
    - [math](#math)
  - [GAN](#gan)
  - [Deepfakes](#deepfakes)
    - [LoRA](#lora)
    - [Stable Diffusion](#stable-diffusion)
    - [Mixed Precision](#mixed-precision)
    - [renting gpu](#renting-gpu)
    - [prompt engineering](#prompt-engineering)
    - [Transformers](#transformers)
  - [Large Language Models](#large-language-models)
    - [Tools](#tools)
    - [Models](#models)
    - [Data sets](#data-sets)
    - [Openai](#openai)
    - [langchain](#langchain)
    - [Vector Databases](#vector-databases)
  - [Backprop Technqiues](#backprop-technqiues)
  - [Frameworks](#frameworks)
- [Hugging Face](#hugging-face)
  - [fastai](#fastai)
  - [Resources](#resources)
- [Reinforcement Learning](#reinforcement-learning)
  - [Resources](#resources-1)
- [Old Reinforcement learning](#old-reinforcement-learning)

See also:

- Optimization

[ml for proofs bibliography](https://github.com/tlringer/ml-for-proofs)

# Applications

- Speech recognition
- Image recognition
- branch prediction
- phase transition recognition
- Dimensionality reduction?
- recommender systems
- Fluid sim accelerate
- system identification
- learning program invariants <http://pranav-garg.com/papers/cav14.pdf> <https://www.cs.purdue.edu/homes/suresh/papers/pldi18.pdf>

# Data

outliers

augmentation - sometimes you can apply trasnformations to the data in ways. For example rotating images if you want the answer to not depend on direction. Or adding noise if you want it to ignore noise. Warping.

In some problems it's nice that you can cripple your data and train it to undo the crippling

- colorizing images
- interpolating frames
- super resolution

# Good Practice? What's the right word here

Test and training sets
cross validation
data cleaning
meta parameter tuning
don't set auxiliary goals.

Reading training curves
debugging?

# Supervised
<https://arxiv.org/abs/1906.00855> drnets. overlapping sudoku patterns but also x ray diffractin data. give rules as feature, turn up penalty for violating rules. but also they don't pre say how to derive the variabes coming into the equations? <https://github.com/gomes-lab/DRNets-Nature-Machine-Intelligence>

$$ \hat{y}_i = f(x_i; \theta) $$

Classification
discrete output

Regression - continous output

one hot encoding

## Linear in WHAT?

## Nearest neighbor

## SVM

## Kernel

## decision trees

### Boosting

<https://en.wikipedia.org/wiki/Boosting_(machine_learning)>

Adaboost
[XGboost](https://en.wikipedia.org/wiki/XGBoost)

<https://en.wikipedia.org/wiki/Multiplicative_weight_update_method> a generalizatio of the idea of combinigh expert opinions

### Random Forest

# Unsupervised

PCA
k-means clustering
hierarchical clustering

dimsenionlaity reduction?

# Visualization

t-sne
umap

# Learning Theory

VC dimension

PAC probably apprximately correct
<https://en.wikipedia.org/wiki/Probably_approximately_correct_learning>

# Overfitting

bias variance

# Bayesian Shit

pyro pymc3
stan
particle filters?
probalistic programming

## Regularization

[diffrax](https://twitter.com/PatrickKidger/status/1493239723497857025?s=20&t=vnpYi0b4BbBHdrISb_Kxfw) JAX powered differential equations.

# Deep Learning

<https://github.com/AUTOMATIC1111/stable-diffusion-webui>

## Convolutional

## Recurrent

lstm
gru
blowup problem / vanishing gradient

## tidbits

 Attention
 Capsule
 transformers

batch normalization

dropout
grokking? overfit and keep going. Sometimes it gets better later. Bizarre. Don't count on this. <https://mathai-iclr.github.io/papers/papers/MATHAI_29_paper.pdf>
autoencoders
GANs

graph neural networks?

transfer learning

# Verification

Adversarial examples

Generate and Test -> use or augment generate with chatgpt

Spec suggestions.
Use python syntax for coq questions. Python type annotations
Axiom schema instantiations. All the things that require "creativity"
Program invariant suggestions. Some come out weak or wrong. Mutation rules. Ask to refine or simplify.

Automata verification of langchains. Blackbox the language model. Verified parsing of the output

"Function call" api

Talia's AI for math <https://docs.google.com/document/d/1kD7H4E28656ua8jOGZ934nbH2HcBLyxcRgFDduH5iQ0/edit>

<https://huggingface.co/datasets/hoskinson-center/proof-pile> proof pile

lean dojo

[Neural Network Verification with Proof Production](https://arxiv.org/pdf/2206.00512.pdf)

# Famous Models

word2vec
node2vec

code2vec

copilot

gato

wavenet
DALL-E
stable diffusion
midjourney

alexnet
vgg
alphafold
alpha zero / go
BERT - masked language modelling. mask some words. predict them. next sentence prediction - did this sentence follow from the previous?  <https://huggingface.co/bert-base-uncased>

<https://github.com/facebookresearch/segment-anything>

whisper

instructgpt

## Tasks

<https://huggingface.co/models> look at tasks tab

- question answering
- summarization
- conversational
- table questin answering
- text generation
- image segmentation
- text 2 speech

### speech recognition

<https://huggingface.co/openai/whisper-large-v2>
<https://github.com/openai/whisper>

```bash
whisper audio.flac --model small
whisper --model large-v2
```

<https://github.com/openai/whisper/discussions/categories/show-and-tell> discussions

<https://github.com/ggerganov/whisper.cpp> inference on cpu.

<https://colab.research.google.com/drive/1WLYoBvA3YNKQ0X2lC9udUOmjK7rZgAwr?usp=sharing>
Colab is nice. medium run.s

Man, whisper is pretty dang good

### code

<https://huggingface.co/bigcode/starcoder>

### math

[let's verify step by step](https://cdn.openai.com/improving-mathematical-reasoning-with-process-supervision/Lets_Verify_Step_by_Step.pdf )

## GAN

<https://vcai.mpi-inf.mpg.de/projects/DragGAN/> drag your gan

## Deepfakes

### LoRA

Low rank adaptation
<https://arxiv.org/abs/2106.09685>
But people are also using the technique on stable diffusion
[Using LoRA for Efficient Stable Diffusion Fine-Tuning](https://huggingface.co/blog/lora)

Lora let's you fine tune big models by injecting in small layers that are easier to train

PEFT parameter efficient fine tuning <https://www.youtube.com/watch?v=YVU5wAA6Txo&ab_channel=code_your_own_AI>
<https://github.com/huggingface/peft>

<https://civitai.com/> people post their lora updates

<https://twitter.com/rasbt/status/1642161887889567745> soft finetuning
prefix finetuning

[Fine-tuning 20B LLMs with RLHF on a 24GB consumer GPU](https://huggingface.co/blog/trl-peft)

<https://github.com/artidoro/qlora> qlora
<https://towardsdatascience.com/qlora-fine-tune-a-large-language-model-on-your-gpu-27bed5a03e2b>
<https://huggingface.co/blog/4bit-transformers-bitsandbytes>

### Stable Diffusion

<https://www.fast.ai/posts/part2-2023.html> course

inpainting
outpainting

<https://github.com/AUTOMATIC1111/stable-diffusion-webui>

negative prompt, negative embedding

You can generate a supervised learning problem to predict noise given a noisy image. Text info may help.
You can then iteratively subtract this noise.
If you ask it to remove all noise, then add 99% noise, then ask it to remove 99% noise and so on you have a stable noise removal process.
You can boost listening to the text by comparing againt a version tat doesn't have the text and boosting the differences
You can do this process in latent space (small space of autoencoder) to speed it up

Schedules

### Mixed Precision

<https://github.com/NVIDIA/apex>
<https://github.com/ggerganov/llama.cpp/issues/9>
GPTQ quantization <https://github.com/IST-DASLab/gptq> <https://huggingface.co/TheBloke>

<https://github.com/TimDettmers/bitsandbytes>

### renting gpu

vast.ai
lambdalabs
runpod  <https://www.youtube.com/watch?v=TP2yID7Ubr4&ab_channel=Aitrepreneur>

google colab provides ~15gb vram free? colab pro gives a100

<https://github.com/skypilot-org/skypilot>

### prompt engineering

<https://github.com/f/awesome-chatgpt-prompts>

<https://www.promptingguide.ai/>
Question answer format to give a couple examples
Start a conversation
See openai examples page
People use seperators to denote different sections. Weird.

Avoid impreciseness

chain of thought prompting <https://arxiv.org/abs/2201.11903>

<https://learn.deeplearning.ai/chatgpt-prompt-eng>

<https://twitter.com/ShriramKMurthi/status/1664978520131477505?s=20> shriram racket.
"You are a programming assitant that generates programs  in the Rakcet programming language. Your response should contain *only* a Racket program. It should NOT include anything else: explanation, test cases, or anything else.
The output should be a Racke function that can be evaluared direvtly.
It should begin with \"(define\" and end with \"), e.h., (defibe (f x) x), but replaced with the actual function you produce."

<https://ianarawjo.medium.com/introducing-chainforge-a-visual-programming-environment-for-prompt-engineering-bc6910be01cf>
<https://github.com/ianarawjo/ChainForge>
Automated the prompt engineering workflow. You could ask questions you know the answer to, or evaluate code generation against test suite or what have you. The prompt is a kind of hyperparameter and you can apply the same methodolgy you might with others (random search, test sets, validation sets, etc). The llm is a fixed parametrized function like `y = ax+b` where a and b are the prompts.

### Transformers

<https://en.wikipedia.org/wiki/Attention_(machine_learning)>

## Large Language Models

The make it "more" meme. Puppy cuter until dissolved nto cosmos

<https://openai.com/research/instruction-following> instructgpt RLHF reinfrocement learning human feedback

distillation. Take output from bigger more powerful model to train smaler model

evaluate models by asking gpt4 about them

alpaca <https://crfm.stanford.edu/2023/03/13/alpaca.html> llamma fine tuned. Make a bunch of examples. Make gpt3 build a dataset out of them, finetune llama on those answers

Emery berger is going ham. I think basically what he is doing is grabbing pertinent data and constructing a gpt prompt

[](https://huggingface.co/blog/stackllama)

langchain <https://www.pinecone.io/learn/langchain-intro/>
<https://github.com/microsoft/semantic-kernel> microsoft version of langchain?

<https://github.com/unitaryai/detoxify> detect toxix comments. I suppose you just need to detect if the output is mean and then you can block it. AI vs AI

<https://bellard.org/ts_server/>  text synth server fabrice bellard

<https://www.emergentmind.com/>
<https://www.builder.io/blog/ai-shell>

Chinchilla scaling - There is an amount of data and number of parameters that is compute optima

<https://news.ycombinator.com/item?id=35483933> chatdbg, another gdb chatgpt integration

<https://github.com/openai/tiktoken> tokenizer BPE byte pair encoding <https://platform.openai.com/tokenizer> try out te tokenizer

<https://github.com/openai/openai-cookbook> open ai cookebook

[sentence transformers](https://www.sbert.net/) make embeddings easily?

"Pre-training" is the heavy lift huge datacetner part that produces raw gpt3 models or whatever. Weird terminology to call that pretraining

ICL - in context learning - running inferece. A set of examples in the prompt

[deep to long learning](https://news.ycombinator.com/item?id=35502187) Context length is important. It scales poorly

Perplexity - measurement of inaccuracy of model prediction on test set <https://en.wikipedia.org/wiki/Perplexity>

NLP -
unigram model - probility of individual words
n-gram model - condtional probability of word window

<https://github.com/imartinez/privateGPT> ingest a bunch of documents. chroma vector db

### Tools

<https://github.com/ggerganov/llama.cpp>

<https://github.com/Mozilla-Ocho/llamafile> single file llama via cosmopolitan
<https://github.com/simonw/llm>
<https://github.com/TheR1D/shell_gpt/>
<https://arxiv.org/pdf/2309.06551.pdf> Commands as AI Conversations. uses ld_prelod I think t intercede on readline ibrary

<https://github.com/xtekky/gpt4free> is this using web interfaves to steal gpt4?

<https://github.com/jmorganca/ollama>

<https://github.com/simonw/symbex> ask about specific python functions

llm vs shell-gpt. shell-gpt has more stars. nice colors
What's a role?
--chat hmm saved sessions
--repl
--describe shell
--code
-s will just execute them??? oh no it suggests and asks. Ok.
Can pipe stuff in
sgpt --install-integration

```

```

llm might support local llms better. Can download them?

<https://github.com/pytorch-labs/gpt-fast> faster inference using pytorch <https://news.ycombinator.com/item?id=38477197>

### Models

<https://www.reddit.com/r/LocalLLaMA/top/?sort=top&t=month>
<https://www.reddit.com/r/aivideo/>

- llama 2
- qwen
- mistral
- wizard coder python
-

<https://vectara.com/top-large-language-models/> useful summary. Probaby will be outdate in a month

<https://www.promptingguide.ai/models/collection>

- gpt-3
- chatgpt
- llama <https://news.ycombinator.com/item?id=35100086> llama weights leaked. 4 bt quantization. <https://github.com/rustformers/llama-rs>

- Bloom <https://huggingface.co/bigscience/bloom>
- eleuther gpt-j <https://en.wikipedia.org/wiki/GPT-J> <https://www.width.ai/post/gpt-j-vs-gpt-3> <https://github.com/EleutherAI/gpt-neox>

- flan-t5 / flan-ul2 / t5-xxl
- PaLM
- falcon
-

gpt-cerebras - the point it was trained efficiently, not that its good? <https://news.ycombinator.com/item?id=35487846>
claude <https://www.anthropic.com/index/introducing-claude>

rwkv <https://github.com/BlinkDL/RWKV-LM> <https://news.ycombinator.com/item?id=35370357>  <https://github.com/saharNooby/rwkv.cpp>

finetunes

- gpt4all - another lora finetuning of llama
- alpaca - paid chatgpt api to generate examples to finetune llama
- vicuna - <https://lmsys.org/blog/2023-03-30-vicuna/> llama finetuned on sharegpt data
- wizard - <https://github.com/nlpxucan/WizardLM#fine-tuning>
- <https://huggingface.co/PygmalionAI/pygmalion-13b> pygmalion for conversation?
- guanaco - qlora. finetuning with quantization. <https://guanaco-model.github.io/> <https://huggingface.co/datasets/JosephusCheung/GuanacoDataset> hmm. actually the qlora stuff might be separate

<https://erichartford.com/uncensored-models> uncensored models remove examples where chat refused to answr

oobabooga text-generation-webui <https://github.com/oobabooga/text-generation-webui>
run on colab <https://www.youtube.com/watch?v=TP2yID7Ubr4&ab_channel=Aitrepreneur>

<https://github.com/lm-sys/FastChat/> related somehow to vicuna? Fast way to get chat server?

### Data sets

The Pile - eleuther ai. huge corpus for training

<https://huggingface.co/datasets>

databricks dolly <https://huggingface.co/datasets/databricks/databricks-dolly-15k>

oasst1 <https://huggingface.co/datasets/OpenAssistant/oasst1> <https://open-assistant.io/> crowd sourced chat stuff

<https://sharegpt.com/> sharegpt. crowd source gpt responses. Used in some models, but then commerical use restricted

<https://huggingface.co/datasets/bigcode/the-stack> the stack. starcoder.

red pajama <https://huggingface.co/datasets/togethercomputer/RedPajama-Data-1T> clean room open source llama dataset

benchmarks
<https://lmsys.org/blog/2023-05-03-arena/> open source battle between llm
<https://huggingface.co/datasets/glue> general langhguae understanding evaluation benchmark <https://gluebenchmark.com/>

### Openai

```python
import openai

# list models
models = openai.Model.list()
#print(models)
# print the first model's id
print(models.data[0].id)

# create a completion
completion = openai.Completion.create(model="ada", prompt="Hello world")

# print the completion
print(completion.choices[0].text)
print(completion)
```

```bash
# list models
openai api models.list

# create a completion
openai api completions.create -m ada -p "Hello world"

# create a chat completion
openai api chat_completions.create -m gpt-3.5-turbo -g user "Hello world"

# generate images via DALL·E API
#openai api image.create -p "two dogs playing chess, cartoon" -n 1

# audio.transcribe
# audio.translate

```

Embeddings
<https://www.buildt.ai/blog/3llmtricks> embedding tricks. Hyde - predict answer from query, then use embedding of predicted answer

```python
import openai

# choose text to embed
text_string = "sample text"

# choose an embedding
model_id = "text-similarity-davinci-001"

# compute the embedding of the text
embedding = openai.Embedding.create(input=text_string, model=model_id)['data'][0]['embedding']
print(embedding)
```

### langchain

```python
from langchain.llms import OpenAI
llm = OpenAI(temperature=0.9) # hgh temprateur
text = "What would be a good company name for a company that makes colorful socks?"
print(llm(text))
```

```python
from langchain.prompts import PromptTemplate

prompt = PromptTemplate(
    input_variables=["product"],
    template="What is a good name for a company that makes {product}?",
)
print(prompt.format(product="colorful socks"))
```

<https://github.com/Unstructured-IO/unstructured>

### Vector Databases

Databases that include the abilitt to do fuzzy search for vectors (from embeddings)

Approximate nearest neighbor: [FAISS](https://github.com/facebookresearch/faiss),  <https://github.com/spotify/annoy> <https://github.com/nmslib/hnswlib/>

- Pinecone
- Milvus
- Weaviate
- Qdrant

[missing where clause](https://www.pinecone.io/learn/vector-search-filtering/), pre vs post filtering

sqlite vector search
<https://github.com/asg017/sqlite-vss> <https://observablehq.com/@asg017/introducing-sqlite-vss>

postgres vector pg_vector

vs
elastic search, opensearch, lucene.
BM25

<https://www.sbert.net/> sentence transformers
<https://github.com/imartinez/privateGPT>

## Backprop Technqiues

adam adamw
sgd
with momentum?

## Frameworks

Tensorflow
Pytorch
JAX

Julia

<https://github.com/huggingface/accelerate>

gradio for UIs. huggingface spaces

# Hugging Face

transformers
pipeline is the easy version
datasets library

```python

from peft import PeftModel    
from transformers import AutoModelForCausalLM, AutoTokenizer, LlamaTokenizer,  AutoModelForSeq2SeqLM

```

```python
from transformers import AutoTokenizer, AutoModelForMaskedLM
tokenizer = AutoTokenizer.from_pretrained("bert-base-uncased")
model = AutoModelForMaskedLM.from_pretrained("bert-base-uncased")

```

### fastai

## Resources

- Deep Learning Book
-

# Reinforcement Learning

Dreamerv3
Decision Transformer

cleanrl
sheeprl

PPO SAC
DDPG

imitation learning
reinforce
helmut with 3 cameras.

Markov Decision Process
Partially observed mdp (POMDP)

Temporal difference
Reward function
Value function
Q function
policy function
Learn Dynamics - system identification

Q-learning
sarsa
policy gradient
Actor critic

Monte-carlo search

## Resources

[openai spinning up](https://spinningup.openai.com/en/latest/index.html)
Sutton and Barto

[Machine intellgience course](https://www.youtube.com/playlist?list=PLPQUqhKcaBdUYQRyS_g3GFN4L5B-_asUt)

# Old Reinforcement learning

I watched David Silver's lectures on Reinforcement Learning.

<http://www0.cs.ucl.ac.uk/staff/d.silver/web/Teaching.html>

Pretty interesting stuff.

We had already tried naive reinforcement learning for tic tac toe. We made a random player, and watched whether it won or lost. Then we'd pick only moves that ultimately won and tried to train a neural network to map board state to winning move. In hindsight, this was kind of a ghetto monte carlo policy learning. It worked kind of.

Big takeaways from the lectures:

Value functions and Q functions are things you may want to consider. They tell you the value of your current state. You may want to move to states of high value.

Very evocative of iterative methods for solving matrix equations. So if you're looking for inspiration, look there. If you had the transition probabilities, it is a linear model for the probabilities.

There are table based methods for

There is also a layer of function approximation you can stack on there.

I think you could implement temporal difference learning using common libraries using $latex r_t + \gamma \max_a Q(S,a,\theta)$ as the truth value, and then update the truth values occasionally.

Old:

Reinforcement learning is when you get a rating of a move instead of the right answer. For example a supervised learning task would be to tell whether a picture is of a cat or not.

Also there is a stronger element of time occurring. Reinforcement learning often is sequential in nature. And the rewards may come later down the line rather than immediately

Explore exploit trade off. Exploration allows you to find new things. The new inns are only occasionally better than the stuff you already know about.

The many armed bandit is an example. You have many slot machines to choose from and 100 quarters. Should you try all the slot machines or

greedy method chooses curren best slot

epsilon greedy chooses best while occasionally choosing a random other

Policy is what actions you make given the current state. State is the encapsulation of the important information you've received from all previous measurements. Policy can be deterministic, a function from state to action, or probabilistic, the probability of an action given a state.

Value is the expected reward given a particular policy given your current state.

observations, actions, and rewards.

Three kinds of RL. Policy, Value, and Model based.

There are the questions of policy evaluation and policy optimization. They are related.

Given either a deterministic policy or probabilistic policy, you could hypothetically write down the exact probabilistic step from one time step to another.

There is a connection between Monte Carlo methods I'm more familiar with and the solution methods.

Monte Carlo methods replace expectations with samples. When used numerically, they use expectations as a stand in for a tough summation or integration.

One place where summatiuon occurs is in matrix multiplication. Row times column and then add them all up. Replace this addition with a sampling process.

The evolution of the probability distribution in a markov process can be written as a finite difference equation with a matrix full of the condition steps $latex P(x_{t+1} | x_t)$

The matrix multiplication rule then is one that takes the prior distribution marginalizes it out to give the distribution in the next time step.

The optimization step is also somewhat . It is an interesting analogy that you can produce matrix like systems using (max,+) in the place of the usual (+,*). If you use softmax(a,b) = $latex \ln (e^a + e^b)$ it might even be somewhat invertible (although I have strong suspicions it might easily become numerically unstable).

This is for example used as a way of discussing shortest path problems using edge weight matrices. Mixing between the two is curious.

The world is an oracle that can give us samples for us.

Q(s,a) is a very clever, non obvious function.

To perform a step of the bellman equation without the model of the system, you need a function like that.

Q learning vs SARSA

Q learning is off policy. It pretends you're using a greedy policy

SARSA is on policy

Deep RL course

Imitaiton learning. Learn human expert.

Can often lead to trajectory drifting off course. Clever way of fixing this includes building in some stability to the thing with three headed camera.

Dagger. Make a loop of using human expert. then let thing thing run, then give human the newly acquired data and have him label it. And so on.

Necessary because the poorly imitating robot will end up in states human expert would never see. Distributional mismatch

Model based. If you have am model you can use it. Optimal Control

shooting method, optimize over actions only. Plug in dynamics into cost function

collocation method, optimize over both path and controls with constraints

LQR  - dynamics linear, cost function quadratic. Can be back solved if initial condition problem.

Q_t matrix gives future cost assuming optimal policy in space of u and x

V_t matrix only in space of x

K matrix connects x to u. The feedback matrix. Can be built from blocks of Q.

iterative LQR / Differential dynamic programming (DDP uses second order expansion of dynamics)

go backwards to find the right K. Using it forwards to compute correct x and u. Iterate until convergence

<https://homes.cs.washington.edu/~todorov/papers/TassaIROS12.pdf>

Model Predictive Control. Do it all like you were playing chess. After each actual time step re-run the iterative LQR

<https://people.eecs.berkeley.edu/~svlevine/papers/mfcgps.pdf>

<https://studywolf.wordpress.com/2016/02/03/the-iterative-linear-quadratic-regulator-method/>

<https://github.com/pydy/pydy-tutorial-human-standing>

<https://github.com/openai/roboschool>

pybullet

learning the model.

So for example i don't know the mass or inertia parameters (or timestep) of the cartpole in gym. I could build the general model though and then fit pairs of (x, x', u)  to it to determine those. Under random policy.

Usually need to recurse on this step (use current best policy to get more data) like in dagger because random policy discovering dynamics won't go to the same place that better policy does.

Better yet is to use mpc to replan at every step.

Can also directly train a parametrized policy function as part of the loop rather than using the more algorithmic iLQR

Neural network based model of the dynamics might be fine especially since you can backpropagate which is nice for the iterative LQR step.

<https://rse-lab.cs.washington.edu/papers/robot-rl-rss-11.pdf>

in global models the planning stage will tend to try to exploit regions that are crappily modelled.

maximum entropy. May want to have the most random solution that doesn't hurt cost?

Local models try to avoid this by just modelling gradients? And simply. But use a contrained optimization problem to make sure the robot stays in a region where the local estimates still apply. Trust regions. Defined using how unlikely the current trajectory is
